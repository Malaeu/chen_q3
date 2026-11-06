// Smooth-taper Part B: direct reciprocity objects, Parseval/J4, and R8 core.
// All reported values are floating-point diagnostics, not interval certificates.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

using ld = long double;
static constexpr ld PI = 3.141592653589793238462643383279502884L;

static void add(ld x, ld &s, ld &c) {
    const ld y = x - c;
    const ld t = s + y;
    c = (t - s) - y;
    s = t;
}

static void progress(size_t done, size_t total, double started, const std::string &label);

static std::vector<std::string> split_csv(const std::string &line) {
    std::vector<std::string> out;
    std::stringstream ss(line);
    std::string item;
    while (std::getline(ss, item, ',')) out.push_back(item);
    if (!line.empty() && line.back() == ',') out.emplace_back();
    return out;
}

static ld parse_ld(const std::string &s) {
    char *end = nullptr;
    const ld x = std::strtold(s.c_str(), &end);
    if (end == s.c_str() || *end != '\0' || !std::isfinite(x))
        throw std::runtime_error("invalid finite number in CSV: " + s);
    return x;
}

using Vecs = std::map<int, std::map<std::string, std::vector<ld>>>;

static Vecs read_vectors(const std::string &path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open selected vectors: " + path);
    std::string line;
    if (!std::getline(in, line)) throw std::runtime_error("empty vector CSV");
    const auto h = split_csv(line);
    std::map<std::string, size_t> col;
    for (size_t i = 0; i < h.size(); ++i) col[h[i]] = i;
    for (const char *name : {"N", "n", "log", "best"})
        if (!col.count(name)) throw std::runtime_error(std::string("vector CSV missing ") + name);
    Vecs data;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        const auto row = split_csv(line);
        if (row.size() != h.size()) throw std::runtime_error("vector CSV row width mismatch");
        const int N = std::stoi(row[col["N"]]);
        const int n = std::stoi(row[col["n"]]);
        if (N < 2 || n < 1 || n > N) throw std::runtime_error("invalid N,n in vectors");
        for (const std::string family : {"log_taper", "best"}) {
            auto &v = data[N][family];
            if (v.empty()) v.assign((size_t)N + 1, std::numeric_limits<ld>::quiet_NaN());
            if (std::isfinite(v[n])) throw std::runtime_error("duplicate vector row");
            const std::string &cell = row[col[family == "log_taper" ? "log" : "best"]];
            v[n] = parse_ld(cell);
        }
    }
    for (auto &[N, families] : data) {
        for (auto &[family, v] : families) {
            for (int n = 1; n <= N; ++n)
                if (!std::isfinite(v[n]))
                    throw std::runtime_error("incomplete vector N=" + std::to_string(N) + " family=" + family);
            if (v[1] != 1.0L)
                throw std::runtime_error("raw a_1 must equal exactly 1 for N=" + std::to_string(N) + " family=" + family);
        }
    }
    return data;
}

static std::map<int, ld> read_references(const std::string &path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open J2 reference CSV: " + path);
    std::string line;
    if (!std::getline(in, line)) throw std::runtime_error("empty J2 reference CSV");
    const auto h = split_csv(line);
    if (h.size() < 2 || h[0] != "N" || h[1] != "E")
        throw std::runtime_error("J2 reference header must be N,E");
    std::map<int, ld> ref;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        const auto row = split_csv(line);
        if (row.size() != 2) throw std::runtime_error("J2 reference row width mismatch");
        ref[std::stoi(row[0])] = parse_ld(row[1]);
    }
    return ref;
}

static std::vector<int> read_targets(const std::string &path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open target list: " + path);
    std::set<int> vals;
    int n;
    while (in >> n) vals.insert(n);
    return {vals.begin(), vals.end()};
}

struct Objects {
    int N;
    std::string family;
    const std::vector<ld> &a;
    std::vector<ld> q;
    ld S = 0, s = 0, u = 0, b = 0, B = 0, center = 0, sumq = 0;
    ld norm2 = 0;
    Objects(int n, std::string f, const std::vector<ld> &coef)
        : N(n), family(std::move(f)), a(coef), q((size_t)n + 1, 0) {
        ld Sc = 0, sc = 0, uc = 0;
        for (int k = 1; k <= N; ++k) {
            add(a[k], S, Sc);
            add(a[k] / (ld)k, s, sc);
            if (k > 1) add(a[k] * logl((ld)k) / (ld)k, u, uc);
        }
        b = 1 + (S - s) / 2;
        B = 2 * b * (1 + u) - s;
        q[1] = 1 - s;
        for (int k = 2; k <= N; ++k) q[k] = a[k];
        ld cc = 0, qc = 0;
        for (int k = 1; k <= N; ++k) {
            add(q[k] / (ld)k, center, cc);
            add(q[k], sumq, qc);
        }
        norm2 = parseval_sq();
    }

    ld parseval_sq() const {
        std::vector<ld> j2((size_t)N + 1);
        for (int d = 1; d <= N; ++d) j2[d] = (ld)d * d;
        std::vector<bool> composite((size_t)N + 1, false);
        for (int p = 2; p <= N; ++p) {
            if (composite[p]) continue;
            for (int m = p; m <= N; m += p) {
                composite[m] = true;
                j2[m] *= 1 - 1 / ((ld)p * p);
            }
        }
        ld total = 0, totalc = 0;
        for (int d = 1; d <= N; ++d) {
            ld c = 0, corr = 0;
            for (int n = d; n <= N; n += d)
                add(q[n] / ((ld)n * n), c, corr);
            add(j2[d] * c * c / 12, total, totalc);
        }
        total += (0.5L - q[1]) / (PI * PI);
        if (total < 0 && total > -1e-18L) total = 0;
        if (total < 0) throw std::runtime_error("negative Parseval norm squared");
        return total;
    }

    ld F_rational(int r, int k, uint64_t *zero_count = nullptr) const {
        ld value = 0, corr = 0;
        for (int n = 1; n <= N; ++n) {
            const int64_t rem = ((int64_t)n * r) % k;
            ld b1;
            if (rem == 0) {
                b1 = 0;
                if (zero_count) ++*zero_count;
            } else {
                b1 = (ld)rem / (ld)k - 0.5L;
            }
            add(q[n] / (ld)n * b1, value, corr);
        }
        return value + sinl(2 * PI * (ld)r / (ld)k) / PI;
    }

    ld F_direct(ld x) const {
        ld value = 0, corr = 0;
        for (int n = 1; n <= N; ++n) {
            const ld nx = (ld)n * x;
            const ld nearest = roundl(nx);
            ld b1;
            if (fabsl(nx - nearest) <= 8 * std::numeric_limits<ld>::epsilon() * std::max(1.0L, fabsl(nx)))
                b1 = 0;
            else
                b1 = nx - floorl(nx) - 0.5L;
            add(q[n] / (ld)n * b1, value, corr);
        }
        return value + sinl(2 * PI * x) / PI;
    }

    ld j2_direct(uint64_t &zero_count) const {
        ld outer = 0, oc = 0;
        const int step = std::max(1, N / 10);
        for (int k = 2; k <= N; ++k) {
            if (q[k] != 0) {
                ld inner = 0, ic = 0;
                for (int r = 1; r < k; ++r) {
                    const ld x = PI * (ld)r / (ld)k;
                    const ld cot = cosl(x) / sinl(x);
                    const ld F = F_rational(r, k, &zero_count);
                    add(cot * F, inner, ic);
                }
                add(q[k] / (ld)k * inner, outer, oc);
            }
            if (k % step == 0 || k == N)
                progress((size_t)(k - 1), (size_t)(N - 1), 0,
                         "direct J2 rational sums N=" + std::to_string(N));
        }
        return outer;
    }

    struct Event { int num, den; ld jump; };

    static bool event_less(const Event &x, const Event &y) {
        return (int64_t)x.num * y.den < (int64_t)y.num * x.den;
    }
    static bool event_equal(const Event &x, const Event &y) {
        return (int64_t)x.num * y.den == (int64_t)y.num * x.den;
    }

    static constexpr std::array<ld, 8> X8 = {
        -0.960289856497536231683560868569472990L, -0.796666477413626739591553936475830437L,
        -0.525532409916328985817739049189246349L, -0.183434642495649804939476142360183981L,
         0.183434642495649804939476142360183981L,  0.525532409916328985817739049189246349L,
         0.796666477413626739591553936475830437L,  0.960289856497536231683560868569472990L
    };
    static constexpr std::array<ld, 8> W8 = {
        0.101228536290376259152531354309962190L, 0.222381034453374470544355994426240884L,
        0.313706645877887287337962201986601313L, 0.362683783378361982965150449277195612L,
        0.362683783378361982965150449277195612L, 0.313706645877887287337962201986601313L,
        0.222381034453374470544355994426240884L, 0.101228536290376259152531354309962190L
    };
    static constexpr std::array<ld, 12> X12 = {
        -0.981560634246719250690549090149280822L, -0.904117256370474856678465866119096192L,
        -0.769902674194304687036893833212818076L, -0.587317954286617447296702418940534281L,
        -0.367831498998180193752691536643717561L, -0.125233408511468915472441369463853129L,
         0.125233408511468915472441369463853129L,  0.367831498998180193752691536643717561L,
         0.587317954286617447296702418940534281L,  0.769902674194304687036893833212818076L,
         0.904117256370474856678465866119096192L,  0.981560634246719250690549090149280822L
    };
    static constexpr std::array<ld, 12> W12 = {
        0.047175336386511827194615961485017061L, 0.106939325995318430960254718193996225L,
        0.160078328543346226334652529543359071L, 0.203167426723065921749064455809798377L,
        0.233492536538354808760849898924878056L, 0.249147045813402785000562436042951210L,
        0.249147045813402785000562436042951210L, 0.233492536538354808760849898924878056L,
        0.203167426723065921749064455809798377L, 0.160078328543346226334652529543359071L,
        0.106939325995318430960254718193996225L, 0.047175336386511827194615961485017061L
    };

    template <size_t M>
    static ld gauss_piece(ld lo, ld hi, ld slope, ld offset,
                          const std::array<ld, M> &xs, const std::array<ld, M> &ws) {
        const ld mid = (lo + hi) / 2, half = (hi - lo) / 2;
        ld sum = 0, corr = 0;
        for (size_t i = 0; i < M; ++i) {
            const ld x = mid + half * xs[i];
            const ld f = slope * x + offset + sinl(2 * PI * x) / PI;
            add(ws[i] * f * f, sum, corr);
        }
        return half * sum;
    }

    std::tuple<ld, ld, size_t, ld, uint64_t> j4_event_sweep() const {
        std::vector<Event> events;
        size_t reserve = (size_t)N * (N - 1) / 2;
        events.reserve(reserve);
        for (int n = 2; n <= N; ++n) {
            const ld jump = -q[n] / (ld)n;
            if (jump == 0) continue;
            for (int r = 1; r < n; ++r) {
                const int g = std::gcd(r, n);
                events.push_back({r / g, n / g, jump});
            }
        }
        std::sort(events.begin(), events.end(), event_less);
        ld sumq = 0, sumqc = 0, center_sum = 0, center_c = 0;
        for (int n = 1; n <= N; ++n) {
            add(q[n], sumq, sumqc);
            add(q[n] / (ld)n, center_sum, center_c);
        }
        ld offset = -0.5L * center_sum;
        ld prev = 0, q8 = 0, q8c = 0, q12 = 0, q12c = 0;
        size_t unique = 0;
        ld midpoint_err = 0;
        const size_t sample_targets[] = {0, events.size() / 4, events.size() / 2,
                                         (events.size() * 3) / 4, events.size() ? events.size() - 1 : 0};
        size_t sample_cursor = 0;
        for (size_t i = 0; i < events.size();) {
            size_t j = i + 1;
            ld jump = events[i].jump, jc = 0;
            while (j < events.size() && event_equal(events[i], events[j])) {
                add(events[j].jump, jump, jc);
                ++j;
            }
            const ld t = (ld)events[i].num / (ld)events[i].den;
            add(gauss_piece(prev, t, sumq, offset, X8, W8), q8, q8c);
            add(gauss_piece(prev, t, sumq, offset, X12, W12), q12, q12c);
            ++unique;
            while (sample_cursor < 5 && i >= sample_targets[sample_cursor]) {
                if (t > prev) {
                    const ld xmid = (prev + t) / 2;
                    const ld f_sweep = sumq * xmid + offset + sinl(2 * PI * xmid) / PI;
                    midpoint_err = std::max(midpoint_err, fabsl(f_sweep - F_direct(xmid)));
                }
                ++sample_cursor;
            }
            offset += jump;
            prev = t;
            i = j;
        }
        add(gauss_piece(prev, 1, sumq, offset, X8, W8), q8, q8c);
        add(gauss_piece(prev, 1, sumq, offset, X12, W12), q12, q12c);
        // Explicit rational samples exercise exact integer residues (B_1(m)=0).
        uint64_t zero_checks = 0;
        const int maxk = std::min(N, 17);
        for (int k = 2; k <= maxk; ++k)
            for (int r = 1; r < k; ++r) (void)F_rational(r, k, &zero_checks);
        return {q8, q12, unique + 1, midpoint_err, zero_checks};
    }

    ld core(int64_t K, ld &head, ld &shoulder) const {
        std::vector<ld> A((size_t)K, 0);
        for (int n = 1; n <= N; ++n)
            for (int64_t r = n; r < K; r += n) A[(size_t)r] += a[n];
        head = 0; shoulder = 0;
        ld hc = 0, sc = 0, cum = 0, cumc = 0;
        ld max_check = 0;
        std::set<int64_t> samples = {1, 2, std::max<int64_t>(1, N / 2), N,
                                     std::min<int64_t>(K - 1, N + 1), K / 2, K - 1};
        for (int64_t k = 1; k < K; ++k) {
            add(A[(size_t)k], cum, cumc);
            const ld R = 1 + (ld)k * s - cum;
            const ld term = R * R / ((ld)k * (ld)(k + 1));
            if (k <= N) add(term, head, hc);
            else add(term, shoulder, sc);
            if (samples.count(k)) {
                ld direct = 1, dc = 0;
                for (int n = 2; n <= N; ++n)
                    add(a[n] * ((ld)(k % n) / (ld)n), direct, dc);
                max_check = std::max(max_check, fabsl(R - direct));
            }
        }
        if (max_check > 2e-10L)
            throw std::runtime_error("core remainder cross-check failed N=" + std::to_string(N) +
                                     " family=" + family);
        return max_check;
    }
};

static void write_head_checks(const Vecs &vecs, const std::string &outdir) {
    std::ofstream out(outdir + "/objects_head_checks.csv");
    out << "profile,N,r,direct_A,literal_A,corrected_A,literal_abs_error,corrected_abs_error\n";
    // Check the generalized corrected identity for the log taper at every N supplied.
    for (const auto &[N, families] : vecs) {
        const auto it = families.find("log_taper");
        if (it == families.end()) continue;
        std::vector<int> lp((size_t)N + 1, 0), mu((size_t)N + 1, 0), primes;
        lp[1] = 1; mu[1] = 1;
        for (int i = 2; i <= N; ++i) {
            if (!lp[i]) { lp[i] = i; primes.push_back(i); mu[i] = -1; }
            for (int p : primes) {
                const int64_t v = (int64_t)i * p;
                if (v > N || p > lp[i]) break;
                lp[(size_t)v] = p;
                if (p == lp[i]) { mu[(size_t)v] = 0; break; }
                mu[(size_t)v] = -mu[i];
            }
        }
        std::vector<ld> lambda((size_t)N + 1, 0), direct((size_t)N + 1, 0);
        for (int d = 1; d <= N; ++d) {
            if (mu[d] == 0) continue;
            for (int r = d; r <= N; r += d) {
                lambda[r] += (ld)mu[d] * logl((ld)(r / d));
                direct[r] += it->second[d];
            }
        }
        const ld L = logl((ld)N);
        for (int r = 1; r <= N; ++r) {
            const ld corrected = ((r == 1 ? L : 0) + lambda[r]) / L;
            const ld literal = lambda[r] / L;
            out << "log_taper," << N << ',' << r << ',' << std::setprecision(21)
                << direct[r] << ',' << literal << ',' << corrected << ','
                << fabsl(direct[r] - literal) << ',' << fabsl(direct[r] - corrected) << '\n';
        }
    }
    // Explicit P=x and P=x^2 at N=4, including the preregistered r=2 counterexample.
    const int N = 4;
    std::vector<int> mu = {0, 1, -1, -1, 0};
    std::vector<std::vector<ld>> profiles = {{0, 1}, {0, 0, 1}};
    const char *names[] = {"P=x", "P=x^2"};
    const ld L = logl((ld)N);
    for (size_t z = 0; z < profiles.size(); ++z) {
        const auto &p = profiles[z];
        for (int r = 1; r <= N; ++r) {
            std::array<ld, 5> lam{};
            for (int d = 1; d <= r; ++d) if (r % d == 0)
                for (size_t j = 0; j < lam.size(); ++j)
                    lam[j] += (ld)mu[d] * powl(logl((ld)(r / d)), (ld)j);
            ld direct = 0;
            for (int d = 1; d <= r; ++d) if (r % d == 0) {
                if (d == 1) direct += 1;
                else {
                    const ld x = logl((ld)N / d) / L;
                    ld val = 0;
                    for (size_t j = 1; j < p.size(); ++j) val += p[j] * powl(x, (ld)j);
                    direct += (ld)mu[d] * val;
                }
            }
            ld literal = 0, corrected = 1;
            ld P1 = 0;
            for (size_t j = 1; j < p.size(); ++j) P1 += p[j];
            corrected = 1 - P1;
            const ld shift = logl((ld)N / r);
            for (size_t j = 1; j < p.size(); ++j) {
                literal += p[j] * lam[j] / powl(L, (ld)j);
                ld inner = 0;
                for (size_t k = 0; k <= j; ++k) {
                    ld bin = 1;
                    for (size_t m = 1; m <= k; ++m)
                        bin = bin * (ld)(j + 1 - m) / (ld)m;
                    inner += bin * powl(shift, (ld)(j - k)) * lam[k];
                }
                corrected += p[j] * inner / powl(L, (ld)j);
            }
            out << names[z] << ',' << N << ',' << r << ',' << std::setprecision(21)
                << direct << ',' << literal << ',' << corrected << ','
                << fabsl(direct - literal) << ',' << fabsl(direct - corrected) << '\n';
        }
    }
}

static int64_t core_cutoff(int N) {
    const int64_t m = (int64_t)N * N * N;
    int64_t x = (int64_t)sqrtl((ld)m);
    while (x * x < m) ++x;
    while (x > 0 && (x - 1) * (x - 1) >= m) --x;
    return x;
}

static void progress(size_t done, size_t total, double started, const std::string &label) {
    static std::map<std::string, std::chrono::steady_clock::time_point> stage_starts;
    const auto now = std::chrono::steady_clock::now();
    if (!stage_starts.count(label)) stage_starts[label] = now;
    (void)started;
    const double f = total ? (double)done / (double)total : 1;
    const double elapsed = std::chrono::duration<double>(now - stage_starts[label]).count();
    const double eta = f > 0 ? elapsed * (1 - f) / f : 0;
    const int fill = (int)(30 * f);
    std::cerr << '[' << std::string((size_t)fill, '#') << std::string((size_t)(30-fill), '.')
              << "] " << std::fixed << std::setprecision(1) << 100 * f
              << "% ETA " << eta << "s " << label << '\n' << std::flush;
}

int main(int argc, char **argv) {
    try {
        if (argc != 5) throw std::runtime_error("usage: objects_native vectors.csv refs.csv targets.txt outdir");
        const Vecs vecs = read_vectors(argv[1]);
        const auto refs = read_references(argv[2]);
        const auto targets = read_targets(argv[3]);
        const std::string outdir = argv[4];
        std::ofstream boundary(outdir + "/objects_boundary.csv");
        boundary << "N,family,S,s,u,b,B,q1,sum_q,center_sum,normF_squared,normF,7_over_logN,normF_over_7_over_logN\n";
        std::map<int, std::map<std::string, std::array<ld, 3>>> boundary_values;
        size_t all = 0;
        for (const auto &[N, fams] : vecs) all += fams.size();
        size_t done = 0;
        for (const auto &[N, fams] : vecs) {
            for (const auto &[family, a] : fams) {
                Objects o(N, family, a);
                const ld seven = 7 / logl((ld)N);
                boundary << N << ',' << family << ',' << std::setprecision(21)
                         << o.S << ',' << o.s << ',' << o.u << ',' << o.b << ',' << o.B << ','
                         << o.q[1] << ',' << o.sumq << ',' << o.center << ',' << o.norm2 << ','
                         << sqrtl(o.norm2) << ',' << seven << ',' << sqrtl(o.norm2) / seven << '\n';
                boundary_values[N][family] = {o.s, o.B, o.norm2};
                ++done;
                if (done % std::max<size_t>(1, all / 20) == 0 || done == all)
                    progress(done, all, 0, "boundary and Jordan-2 Parseval");
            }
        }

        std::ofstream j2out(outdir + "/objects_j2.csv");
        j2out << "N,E_full_gram,B,L_direct,E_reciprocity,abs_error,tolerance,pass,exact_integer_B1_zero_terms\n";
        size_t j2done = 0;
        for (int N : {50, 200, 1000}) {
            const auto itN = vecs.find(N);
            if (itN == vecs.end() || !itN->second.count("log_taper"))
                throw std::runtime_error("J2 log vector missing N=" + std::to_string(N));
            if (!refs.count(N)) throw std::runtime_error("J2 full-Gram reference missing N=" + std::to_string(N));
            Objects o(N, "log_taper", itN->second.at("log_taper"));
            uint64_t zero_count = 0;
            const ld L = o.j2_direct(zero_count);
            const ld identity = o.B - PI * L;
            const ld err = fabsl(refs.at(N) - identity);
            j2out << N << ',' << std::setprecision(21) << refs.at(N) << ',' << o.B << ',' << L << ','
                  << identity << ',' << err << ",1e-9," << (err <= 1e-9L ? "PASS" : "FAIL")
                  << ',' << zero_count << '\n';
            if (err > 1e-9L) throw std::runtime_error("J2 failed at N=" + std::to_string(N));
            progress(++j2done, 3, 0, "direct J2 reciprocity sum");
        }

        std::ofstream j4out(outdir + "/objects_j4.csv");
        j4out << "N,family,parseval_squared,norm_parseval,j4_gauss8_squared,j4_gauss12_squared,norm_j4_gauss12,squared_error_gauss8,squared_error_gauss12,norm_error_gauss12,event_intervals,event_midpoint_check_error,exact_rational_zero_terms,tolerance,pass\n";
        size_t j4done = 0;
        for (int N : {50, 200, 500, 1000}) {
            const auto itN = vecs.find(N);
            if (itN == vecs.end()) throw std::runtime_error("J4 vectors missing N=" + std::to_string(N));
            for (const std::string family : {"log_taper", "best"}) {
                if (!itN->second.count(family)) throw std::runtime_error("J4 family missing");
                Objects o(N, family, itN->second.at(family));
                const auto [q8, q12, intervals, miderr, zeros] = o.j4_event_sweep();
                const ld norm = sqrtl(o.norm2), norm12 = sqrtl(q12);
                const ld ne = fabsl(norm - norm12);
                j4out << N << ',' << family << ',' << std::setprecision(21) << o.norm2 << ',' << norm << ','
                      << q8 << ',' << q12 << ',' << norm12 << ',' << fabsl(o.norm2-q8) << ','
                      << fabsl(o.norm2-q12) << ',' << ne << ',' << intervals << ',' << miderr << ','
                      << zeros << ",1e-6," << (ne <= 1e-6L ? "PASS" : "FAIL") << '\n';
                if (ne > 1e-6L) throw std::runtime_error("J4 failed N=" + std::to_string(N) + " family=" + family);
            }
            progress(++j4done, 4, 0, "event-swept J4 quadrature");
        }

        std::ofstream coreout(outdir + "/objects_core.csv");
        coreout << "N,family,K,head,shoulder,full_H,direct_remainder_max_abs\n";
        std::map<int, std::map<std::string, std::array<ld,3>>> corevals;
        done = 0;
        for (int N : targets) {
            const auto itN = vecs.find(N);
            if (itN == vecs.end()) throw std::runtime_error("core target vector missing N=" + std::to_string(N));
            const int64_t K = core_cutoff(N);
            for (const std::string family : {"log_taper", "best"}) {
                if (!itN->second.count(family)) throw std::runtime_error("core target missing family=" + family);
                Objects o(N, family, itN->second.at(family));
                ld head, shoulder;
                const ld check = o.core(K, head, shoulder);
                corevals[N][family] = {head, shoulder, head + shoulder};
                coreout << N << ',' << family << ',' << K << ',' << std::setprecision(21)
                        << head << ',' << shoulder << ',' << (head+shoulder) << ',' << check << '\n';
            }
            ++done;
            if (done % std::max<size_t>(1, targets.size() / 20) == 0 || done == targets.size())
                progress(done, targets.size(), 0, "divisor-sieve full core");
        }
        std::ofstream ratios(outdir + "/objects_core_ratios.csv");
        ratios << "N,head_best_over_log,shoulder_best_over_log,full_best_over_log\n";
        for (int N : targets) {
            const auto &x = corevals.at(N);
            ratios << N << ',' << std::setprecision(21) << x.at("best")[0] / x.at("log_taper")[0] << ','
                   << x.at("best")[1] / x.at("log_taper")[1] << ','
                   << x.at("best")[2] / x.at("log_taper")[2] << '\n';
        }
        write_head_checks(vecs, outdir);
        std::cerr << "OBJECTS_NATIVE_PASS vectors=" << all << " core_N=" << targets.size()
                  << " J2=3 J4=8 raw_a1=1\n";
        return 0;
    } catch (const std::exception &e) {
        std::cerr << "OBJECTS_NATIVE_FAIL: " << e.what() << '\n';
        return 2;
    }
}
