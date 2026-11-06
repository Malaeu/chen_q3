// Fast candidate-only construction/evaluation for certificate.py.
// No floating output is used as a proof without the explicit error bounds in
// certificate.py and certificate_method.md.
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cfenv>
#include <cstdint>
#include <cfloat>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <mutex>
#include <numeric>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

using Clock = std::chrono::steady_clock;

static int ceil_sqrt_cube(int N) {
    long long x = 1LL * N * N * N;
    long long r = (long long)std::sqrt((long double)x);
    while (r * r < x) ++r;
    while ((r - 1) * (r - 1) >= x) --r;
    return (int)r;
}

static void show_progress(size_t done, size_t total, Clock::time_point start,
                          const std::string& label) {
    long double f = (long double)done / std::max<size_t>(1, total);
    long double elapsed = std::chrono::duration<long double>(Clock::now() - start).count();
    long double eta = f > 0 ? elapsed * (1 - f) / f : 0;
    int bars = (int)(30 * f);
    std::cout << '[' << std::string(bars, '#') << std::string(30 - bars, '.') << "] "
              << std::fixed << std::setprecision(1) << (100 * f) << "% ETA " << eta
              << "s " << label << "\n" << std::flush;
}

static long double finite_pair(const std::vector<long double>& H, int K, int n, int m) {
    const int last = K - 1;
    int k = 1;
    long double sum = 0;
    while (k <= last) {
        int qn = k / n, qm = k / m;
        int R = std::min(last, std::min((qn + 1) * n - 1, (qm + 1) * m - 1));
        long long a = 1LL * qn * n, b = 1LL * qm * m;
        long double s1 = H[R] - H[k - 1];
        // Substitute s2=s1+1/(R+1)-1/k. This algebraically equivalent
        // form avoids subtracting O(k^2*s1) terms when k is large.
        long double delta = 1.0L / (R + 1) - 1.0L / k;
        long double num = (R - k + 1) - (long double)(a + b + 1) * s1
                          - (long double)(a + 1) * (b + 1) * delta;
        sum += num / ((long double)n * m);
        k = R + 1;
    }
    return sum;
}

static long double finite_linear(const std::vector<long double>& H, int K, int n) {
    const int last = K - 1;
    int k = 1;
    long double sum = 0;
    while (k <= last) {
        int q = k / n;
        int R = std::min(last, (q + 1) * n - 1);
        long long a = 1LL * q * n;
        long double s1 = H[R] - H[k - 1];
        long double delta = 1.0L / (R + 1) - 1.0L / k;
        sum += (s1 + (long double)(a + 1) * delta) / n;
        k = R + 1;
    }
    return sum;
}

static int worker_count() {
    unsigned int n = std::thread::hardware_concurrency();
    if (n == 0) n = 4;
    return (int)std::max(1u, std::min(12u, n));
}

static int build_gram(int N, const std::string& outfile) {
    const int K = ceil_sqrt_cube(N);
    std::vector<long double> H(K + 1, 0);
    for (int k = 1; k <= K; ++k) H[k] = H[k - 1] + 1.0L / k;
    std::vector<double> G((size_t)N * N, 0.0);
    const long double alpha = 1.0L / K + (long double)N / ((long double)K * (K + 1));
    const long double beta = 1.0L / K + 2.0L * N * N / ((long double)K * (K + 1));
    G[0] = (double)(1.0L - 1.0L / K + alpha);
    for (int n = 2; n <= N; ++n) {
        long double q = (long double)(n - 1) / (2.0L * n);
        long double v = finite_linear(H, K, n) + alpha * q;
        G[(size_t)(n - 1) * N] = G[n - 1] = (double)v;
    }

    std::atomic<int> next_n(2);
    std::atomic<size_t> rows_done(0);
    std::mutex print_mutex;
    auto start = Clock::now();
    const size_t total = (size_t)N - 1;
    auto worker = [&]() {
        while (true) {
            int n = next_n.fetch_add(1);
            if (n > N) break;
            long double qn = (long double)(n - 1) / (2.0L * n);
            for (int m = 2; m <= n; ++m) {
                long double qm = (long double)(m - 1) / (2.0L * m);
                int g = std::gcd(n, m);
                long double cov = ((long double)g * g - 1.0L) / (12.0L * n * m);
                long double v = finite_pair(H, K, n, m) + alpha * qn * qm + beta * cov;
                G[(size_t)(n - 1) * N + (m - 1)] = (double)v;
                G[(size_t)(m - 1) * N + (n - 1)] = (double)v;
            }
            size_t d = rows_done.fetch_add(1) + 1;
            if (d == 1 || d % std::max<size_t>(1, total / 50) == 0 || d == total) {
                std::lock_guard<std::mutex> lock(print_mutex);
                show_progress(d, total, start, "segmented candidate Gram");
            }
        }
    };
    std::vector<std::thread> threads;
    for (int t = 0; t < worker_count(); ++t) threads.emplace_back(worker);
    for (auto& t : threads) t.join();

    std::ofstream out(outfile, std::ios::binary);
    uint32_t d = (uint32_t)N;
    out.write((const char*)&d, sizeof(d));
    out.write((const char*)G.data(), (std::streamsize)(G.size() * sizeof(double)));
    if (!out) return 2;
    std::cout << "GRAM N=" << N << " K=" << K << " threads=" << worker_count()
              << " long_double_mantissa=" << LDBL_MANT_DIG << "\n";
    return 0;
}

static int evaluate(int N, const std::string& infile, const std::string& outfile) {
    const int K = ceil_sqrt_cube(N);
    std::vector<double> coeff(N + 1, 0.0);
    {
        std::ifstream in(infile, std::ios::binary);
        for (int n = 2; n <= N; ++n) in.read((char*)&coeff[n], sizeof(double));
        if (!in) return 3;
    }
    for (int n = 2; n <= N; ++n) if (!std::isfinite(coeff[n])) return 6;
    const long double u = std::ldexp(1.0L, -LDBL_MANT_DIG);
    if (std::fegetround() != FE_TONEAREST) return 5;
    long double A = 0;
    for (int n = 2; n <= N; ++n) A += std::fabs((long double)coeff[n]);
    std::vector<long double> gr(N + 1, 0.0L);
    long double H = 0;
    std::atomic<int> rows_done(0);
    std::mutex print_mutex;
    auto start = Clock::now();
    int nt = worker_count();
    std::vector<long double> Hpart(nt, 0.0L);
    std::vector<std::vector<long double>> Gpart(nt, std::vector<long double>(N + 1, 0.0L));
    std::vector<std::thread> threads;
    std::atomic<bool> bad(false);
    for (int tid = 0; tid < nt; ++tid) {
        int lo = 1 + (K - 1) * tid / nt;
        int hi = (K - 1) * (tid + 1) / nt;
        threads.emplace_back([&, tid, lo, hi]() {
            long double hsum = 0;
            std::vector<long double> residues(N + 1);
            auto& gs = Gpart[tid];
            for (int k = lo; k <= hi; ++k) {
                long double R = 1.0L;
                for (int n = 2; n <= N; ++n) {
                    long double r = (long double)(k % n) / (long double)n;
                    residues[n] = r;
                    R += (long double)coeff[n] * r;
                }
                if (!std::isfinite(R)) { bad.store(true); return; }
                long double w = 1.0L / ((long double)k * (k + 1));
                hsum += R * R * w;
                for (int n = 2; n <= N; ++n) gs[n] += R * residues[n] * w;
                int d = rows_done.fetch_add(1) + 1;
                if (d == 1 || d % std::max(1, (K - 1) / 50) == 0 || d == K - 1) {
                    std::lock_guard<std::mutex> lock(print_mutex);
                    show_progress((size_t)d, (size_t)(K - 1), start, "direct candidate rows");
                }
            }
            Hpart[tid] = hsum;
        });
    }
    for (auto& t : threads) t.join();
    if (bad.load()) return 7;
    for (int t = 0; t < nt; ++t) {
        H += Hpart[t];
        for (int n = 2; n <= N; ++n) gr[n] += Gpart[t][n];
    }
    if (!std::isfinite(H)) return 8;
    for (int n = 2; n <= N; ++n) if (!std::isfinite(gr[n])) return 9;

    std::ofstream out(outfile);
    if (!out) return 4;
    out << std::scientific << std::setprecision(30);
    out << "META mantissa=" << LDBL_MANT_DIG << " eps=" << std::numeric_limits<long double>::epsilon()
        << " minsub=" << std::numeric_limits<long double>::denorm_min()
        << " A=" << A << "\n";
    out << "H=" << H << "\nGRAD";
    for (int n = 2; n <= N; ++n) out << ' ' << gr[n];
    out << '\n';
    std::cout << "EVAL N=" << N << " K=" << K << " threads=" << nt << "\n";
    return 0;
}

int main(int argc, char** argv) {
    if (argc != 5) {
        std::cerr << "usage: certificate_native MODE N INFILE OUTFILE\n";
        return 1;
    }
    std::string mode = argv[1];
    int N = std::stoi(argv[2]);
    if (N < 3 || N > 2000) return 1;
    if (mode == "gram") return build_gram(N, argv[4]);
    if (mode == "eval") return evaluate(N, argv[3], argv[4]);
    return 1;
}
