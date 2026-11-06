// Round 8 Part 2: full b_N/head scan and the bounded full-core checks.
// b_N sign intervals use directed MPFR operations. Head and core values are
// diagnostic long-double evaluations, not interval certificates.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include <gmp.h>
#include <mpfr.h>
#include <zlib.h>

namespace fs = std::filesystem;
using Clock = std::chrono::steady_clock;

static void kahan_add(long double x, long double &sum, long double &corr) {
    const long double y = x - corr;
    const long double t = sum + y;
    corr = (t - sum) - y;
    sum = t;
}

struct Sieve {
    int nmax;
    std::vector<int8_t> mu;
    std::vector<int> primes;
    std::vector<long double> lambda;

    explicit Sieve(int n) : nmax(n), mu((size_t)n + 1, 0), lambda((size_t)n + 1, 0) {
        std::vector<int> lp((size_t)n + 1, 0);
        primes.reserve((size_t)(n / std::max(1.0, std::log((double)n)) * 1.1));
        mu[1] = 1;
        for (int i = 2; i <= n; ++i) {
            if (lp[i] == 0) {
                lp[i] = i;
                primes.push_back(i);
                mu[i] = -1;
            }
            for (int p : primes) {
                const int64_t v = (int64_t)i * p;
                if (v > n || p > lp[i]) break;
                lp[(size_t)v] = p;
                if (p == lp[i]) {
                    mu[(size_t)v] = 0;
                    break;
                }
                mu[(size_t)v] = (int8_t)-mu[i];
            }
        }
        lp.clear();
        lp.shrink_to_fit();
        for (int p : primes) {
            const long double lpv = logl((long double)p);
            int64_t power = p;
            while (power <= n) {
                lambda[(size_t)power] = lpv;
                if (power > n / p) break;
                power *= p;
            }
        }
    }
};

struct MpInterval {
    mpfr_t lo, hi;
    explicit MpInterval(mpfr_prec_t prec) { mpfr_init2(lo, prec); mpfr_init2(hi, prec); }
    ~MpInterval() { mpfr_clear(lo); mpfr_clear(hi); }
    MpInterval(const MpInterval &) = delete;
    MpInterval &operator=(const MpInterval &) = delete;
};

struct MpState {
    mpfr_prec_t prec;
    MpInterval F, G, logn, qabs, A, product, X;
    mpfr_t tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, qlo, qhi, glo, ghi;
    explicit MpState(mpfr_prec_t p)
        : prec(p), F(p), G(p), logn(p), qabs(p), A(p), product(p), X(p) {
        mpfr_inits2(p, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8,
                    qlo, qhi, glo, ghi, (mpfr_ptr)0);
        mpfr_set_ui(F.lo, 0, MPFR_RNDD); mpfr_set_ui(F.hi, 0, MPFR_RNDU);
        mpfr_set_ui(G.lo, 0, MPFR_RNDD); mpfr_set_ui(G.hi, 0, MPFR_RNDU);
    }
    ~MpState() { mpfr_clears(tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8,
                             qlo, qhi, glo, ghi, (mpfr_ptr)0); }
};

// Exact rational q=mu(n)*(n-1)/n is enclosed by directed MPFR division.
// log(n) is enclosed by correctly rounded directed MPFR logarithms.
static int8_t update_b_interval(MpState &m, int n, int8_t mu, mpfr_t &lnmid) {
    mpfr_set_ui(m.tmp1, (unsigned long)n, MPFR_RNDN);
    mpfr_log(m.logn.lo, m.tmp1, MPFR_RNDD);
    mpfr_log(m.logn.hi, m.tmp1, MPFR_RNDU);
    mpfr_log(lnmid, m.tmp1, MPFR_RNDN);
    if (mu != 0 && n > 1) {
        mpfr_set_ui(m.tmp1, (unsigned long)(n - 1), MPFR_RNDN);
        mpfr_set_ui(m.tmp2, (unsigned long)n, MPFR_RNDN);
        mpfr_div(m.qabs.lo, m.tmp1, m.tmp2, MPFR_RNDD);
        mpfr_div(m.qabs.hi, m.tmp1, m.tmp2, MPFR_RNDU);
        if (mu > 0) {
            mpfr_set(m.qlo, m.qabs.lo, MPFR_RNDD);
            mpfr_set(m.qhi, m.qabs.hi, MPFR_RNDU);
            mpfr_mul(m.glo, m.qabs.lo, m.logn.lo, MPFR_RNDD);
            mpfr_mul(m.ghi, m.qabs.hi, m.logn.hi, MPFR_RNDU);
        } else {
            mpfr_neg(m.qlo, m.qabs.hi, MPFR_RNDD);
            mpfr_neg(m.qhi, m.qabs.lo, MPFR_RNDU);
            mpfr_mul(m.glo, m.qabs.hi, m.logn.hi, MPFR_RNDU);
            mpfr_neg(m.glo, m.glo, MPFR_RNDD);
            mpfr_mul(m.ghi, m.qabs.lo, m.logn.lo, MPFR_RNDD);
            mpfr_neg(m.ghi, m.ghi, MPFR_RNDU);
        }
        mpfr_add(m.F.lo, m.F.lo, m.qlo, MPFR_RNDD);
        mpfr_add(m.F.hi, m.F.hi, m.qhi, MPFR_RNDU);
        mpfr_add(m.G.lo, m.G.lo, m.glo, MPFR_RNDD);
        mpfr_add(m.G.hi, m.G.hi, m.ghi, MPFR_RNDU);
    }
    // X=log(N)*(2+sum q_n)-sum(q_n*log n)=2 log(N) b_N.
    mpfr_add_ui(m.A.lo, m.F.lo, 2, MPFR_RNDD);
    mpfr_add_ui(m.A.hi, m.F.hi, 2, MPFR_RNDU);
    const int lo_sign = mpfr_sgn(m.A.lo), hi_sign = mpfr_sgn(m.A.hi);
    if (lo_sign >= 0) {
        mpfr_mul(m.product.lo, m.logn.lo, m.A.lo, MPFR_RNDD);
        mpfr_mul(m.product.hi, m.logn.hi, m.A.hi, MPFR_RNDU);
    } else if (hi_sign <= 0) {
        mpfr_mul(m.product.lo, m.logn.hi, m.A.lo, MPFR_RNDD);
        mpfr_mul(m.product.hi, m.logn.lo, m.A.hi, MPFR_RNDU);
    } else {
        mpfr_mul(m.product.lo, m.logn.hi, m.A.lo, MPFR_RNDD);
        mpfr_mul(m.product.hi, m.logn.hi, m.A.hi, MPFR_RNDU);
    }
    mpfr_sub(m.X.lo, m.product.lo, m.G.hi, MPFR_RNDD);
    mpfr_sub(m.X.hi, m.product.hi, m.G.lo, MPFR_RNDU);
    if (mpfr_sgn(m.X.lo) > 0) return 1;
    if (mpfr_sgn(m.X.hi) < 0) return -1;
    return 0;
}

static long double midpoint_to_ld(mpfr_t lo, mpfr_t hi) {
    mpfr_t mid;
    mpfr_init2(mid, mpfr_get_prec(lo));
    mpfr_add(mid, lo, hi, MPFR_RNDN);
    mpfr_div_2ui(mid, mid, 1, MPFR_RNDN);
    const long double x = mpfr_get_ld(mid, MPFR_RNDN);
    mpfr_clear(mid);
    return x;
}

static std::string chunk_name(const fs::path &out, const char *stem, int64_t first, int64_t last) {
    char buf[256];
    std::snprintf(buf, sizeof(buf), "%s_%08lld_%08lld.csv.gz", stem,
                  (long long)first, (long long)last);
    return (out / buf).string();
}

static void progress(const char *label, uint64_t done, uint64_t total,
                     Clock::time_point start, int width = 32) {
    const double f = total ? std::min(1.0, (double)done / total) : 1.0;
    const auto sec = std::chrono::duration<double>(Clock::now() - start).count();
    const double eta = f > 0 ? sec * (1.0 - f) / f : 0.0;
    const int bars = (int)(f * width);
    std::cerr << '[' << std::string((size_t)bars, '#') << std::string((size_t)(width-bars), '.')
              << "] " << std::fixed << std::setprecision(1) << (100.0*f)
              << "% ETA " << eta << "s " << label << "\n" << std::flush;
}

static std::vector<int64_t> make_log_grid(int64_t lo, int64_t hi, int points) {
    std::set<int64_t> vals;
    const long double a = logl((long double)lo), b = logl((long double)hi);
    for (int i = 0; i < points; ++i) {
        long double x = expl(a + (b-a) * i / (points - 1));
        vals.insert((int64_t)llroundl(x));
    }
    vals.insert(lo); vals.insert(hi);
    return {vals.begin(), vals.end()};
}

static void append_row(std::string &buf, int64_t n, long double x, long double y, long double z) {
    char row[256];
    const int len = std::snprintf(row, sizeof(row), "%lld,%.21Lg,%.21Lg,%.21Lg\n",
                                  (long long)n, x, y, z);
    buf.append(row, (size_t)len);
}

static void run_scan(const fs::path &out, int64_t scanmax, int prec) {
    if (scanmax < 3 || scanmax > 10000000) throw std::runtime_error("scanmax must be 3..10000000");
    fs::create_directories(out);
    const int64_t nmax = scanmax + 1;
    auto t0 = Clock::now();
    Sieve sieve((int)nmax);
    progress("linear Mobius sieve complete", (uint64_t)nmax, (uint64_t)nmax, t0);

    const auto j4grid = make_log_grid(100000, 10000000, 101);
    std::set<int64_t> j4targets(j4grid.begin(), j4grid.end());
    std::ofstream j4((out / "core_j4.csv").string());
    j4 << "N,logN,base_head,plant_cross,plant_self,planted_head,plant_self_log_corrected,analytic_local_slope\n";
    gzFile gz = nullptr;
    std::string buf;
    buf.reserve(1024 * 1024);
    int64_t chunk_first = 3, chunk_last = 0, rows_chunk = 0;
    const int64_t chunk_rows = 250000;
    auto open_chunk = [&](int64_t first) {
        chunk_first = first;
        chunk_last = std::min<int64_t>(scanmax, first + chunk_rows - 1);
        gz = gzopen(chunk_name(out, "core_scan", first, chunk_last).c_str(), "wb6");
        if (!gz) throw std::runtime_error("cannot open compressed scan chunk");
        const char *header = "N,b_approx_long_double,head_approx_long_double,head_times_logN\n";
        gzwrite(gz, header, (unsigned)std::strlen(header));
        rows_chunk = 0;
    };
    auto close_chunk = [&]() {
        if (gz) { if (gzwrite(gz, buf.data(), (unsigned)buf.size()) != (int)buf.size()) throw std::runtime_error("gzip write failed");
                 buf.clear(); gzclose(gz); gz = nullptr; }
    };

    std::vector<int8_t> signs((size_t)nmax + 1, 0);
    std::vector<int64_t> ambiguous;
    MpState mp((mpfr_prec_t)prec);
    mpfr_t lnmid;
    mpfr_init2(lnmid, (mpfr_prec_t)prec);

    long double psi = 0, psi_corr = 0;
    long double A = 0, Ac = 0, B = 0, Bc = 0, C = 0, Cc = 0;
    long double sm0 = 0, sm0c = 0, sm1 = 0, sm1c = 0;
    long double P = 0, Pc = 0, Q = 0, Qc = 0, R = 0, Rc = 0;
    const long double ra = 5.0L/6.0L, denom = ra*ra + 49.0L;
    open_chunk(3);
    auto start = Clock::now();
    for (int64_t n = 1; n <= nmax; ++n) {
        const int8_t sign = update_b_interval(mp, (int)n, sieve.mu[(size_t)n], lnmid);
        signs[(size_t)n] = sign;
        if (n >= 3 && sign == 0) ambiguous.push_back(n);

        const long double logn = logl((long double)n);
        if (sieve.mu[(size_t)n] != 0) {
            const long double muv = (long double)sieve.mu[(size_t)n];
            kahan_add(muv / n, sm0, sm0c);
            kahan_add(muv * logn / n, sm1, sm1c);
        }
        kahan_add(sieve.lambda[(size_t)n], psi, psi_corr);
        const long double nl = (long double)n;
        const long double weight = 1.0L / (nl * (nl + 1.0L));
        kahan_add(psi*psi*weight, A, Ac);
        kahan_add(psi/(nl+1.0L), B, Bc);
        kahan_add(nl/(nl+1.0L), C, Cc);

        // Literal plant f(k)=2 Re(k^rho/rho), with f(1)=60/1789.
        const long double theta = 7.0L * logn;
        const long double fk = 2.0L * powl(nl, ra) * (ra*cosl(theta) + 7.0L*sinl(theta)) / denom;
        kahan_add(fk*fk*weight, P, Pc);
        kahan_add(psi*fk*weight, Q, Qc);
        kahan_add(fk/(nl+1.0L), R, Rc);

        if (n >= 3 && n <= scanmax) {
            const long double L = logn;
            const long double sm = sm0 - sm1 / L;
            const long double x = L * sm;
            const long double hnum = A - 2.0L*x*B + x*x*C;
            const long double head = hnum / (L*L);
            const long double b = midpoint_to_ld(mp.X.lo, mp.X.hi) / (2.0L * midpoint_to_ld(mp.logn.lo, mp.logn.hi));
            if (n > scanmax - chunk_rows + 1 && rows_chunk == 0 && chunk_first != n) {
                close_chunk(); open_chunk(n);
            }
            append_row(buf, n, b, head, head*L);
            ++rows_chunk;
            if (buf.size() >= 1024*1024) {
                if (gzwrite(gz, buf.data(), (unsigned)buf.size()) != (int)buf.size()) throw std::runtime_error("gzip write failed");
                buf.clear();
            }
            if (rows_chunk == chunk_rows) { close_chunk(); if (n < scanmax) open_chunk(n+1); }

            if (j4targets.count(n)) {
                const long double planted = (hnum - 2.0L*(Q - x*R) + P) / (L*L);
                const long double self = P/(L*L);
                const long double local = 2.0L/3.0L - 2.0L/L;
                j4 << n << ',' << std::setprecision(21) << L << ',' << head << ','
                   << (Q - x*R)/(L*L) << ',' << self << ',' << planted << ','
                   << (self*L*L) << ',' << local << '\n';
            }
        }
        if (n % 250000 == 0 || n == nmax) progress("certified b_N + head + planted prefix scan", (uint64_t)n, (uint64_t)nmax, start);
    }
    close_chunk();
    mpfr_clear(lnmid);
    j4.close();

    // If the initial outward interval contains zero, replay just those prefix
    // indices at increasing precision. The log interval pass is still O(N).
    int used_prec = prec;
    std::vector<int64_t> pending = ambiguous;
    for (mpfr_prec_t high = (mpfr_prec_t)prec * 2; !pending.empty() && high <= 2048; high *= 2) {
        std::cerr << "high_precision_sign_recheck bits=" << high << " candidates=" << pending.size() << "\n";
        MpState hm(high);
        mpfr_t tmpmid; mpfr_init2(tmpmid, high);
        size_t target = 0;
        auto hs = Clock::now();
        for (int64_t n = 1; n <= nmax && target < pending.size(); ++n) {
            const int8_t sg = update_b_interval(hm, (int)n, sieve.mu[(size_t)n], tmpmid);
            if (n == pending[target]) {
                signs[(size_t)n] = sg;
                if (sg != 0) ++target;
                else ++target; // marked unresolved below, but do not block later targets
            }
            if (n % 500000 == 0 || n == nmax) progress("high-precision ambiguous-sign replay", (uint64_t)n, (uint64_t)nmax, hs);
        }
        mpfr_clear(tmpmid);
        pending.clear();
        for (int64_t n : ambiguous) if (signs[(size_t)n] == 0) pending.push_back(n);
        used_prec = (int)high;
    }

    gz = gzopen(chunk_name(out, "core_signs", 3, nmax).c_str(), "wb6");
    if (!gz) throw std::runtime_error("cannot open sign output");
    const char *sh = "N,b_sign_certified\n";
    gzwrite(gz, sh, (unsigned)std::strlen(sh));
    for (int64_t n = 3; n <= nmax; ++n) {
        const char *s = signs[(size_t)n] > 0 ? "+1" : (signs[(size_t)n] < 0 ? "-1" : "UNRESOLVED");
        gzprintf(gz, "%lld,%s\n", (long long)n, s);
    }
    gzclose(gz);

    std::ofstream crossings((out / "core_crossings.csv").string());
    crossings << "N,bN_sign,bN1_sign,classification\n";
    std::ofstream unresolved((out / "core_unresolved_signs.csv").string());
    unresolved << "N,precision_bits,status\n";
    for (int64_t n : pending) unresolved << n << ',' << used_prec << ",INTERVAL_CONTAINS_ZERO\n";
    std::ofstream decade((out / "core_crossing_decades.csv").string());
    decade << "decade_start,decade_end,|S|\n";
    const int64_t starts[] = {3, 10, 100, 1000, 10000, 100000, 1000000};
    const int64_t ends[] = {9, 99, 999, 9999, 99999, 999999, 10000000};
    uint64_t counts[7] = {};
    for (int64_t n = 3; n <= scanmax; ++n) {
        const int8_t a = signs[(size_t)n], b = signs[(size_t)n+1];
        if (a == 0 || b == 0) continue;
        if (a != b) {
            crossings << n << ',' << (int)a << ',' << (int)b << ",CERTIFIED_CROSSING\n";
            for (int d = 0; d < 7; ++d) if (n >= starts[d] && n <= ends[d]) { ++counts[d]; break; }
        }
    }
    for (int d = 0; d < 7; ++d) decade << starts[d] << ',' << ends[d] << ',' << counts[d] << '\n';

    std::ofstream meta((out / "core_scan_metadata.json").string());
    meta << "{\n  \"scan_max\": " << scanmax << ",\n  \"endpoint_b_computed\": " << nmax
         << ",\n  \"mpfr_initial_precision_bits\": " << prec
         << ",\n  \"mpfr_last_precision_bits\": " << used_prec
         << ",\n  \"initially_ambiguous_sign_count\": " << ambiguous.size()
         << ",\n  \"unresolved_sign_count\": " << pending.size()
         << ",\n  \"sign_method\": \"directed MPFR interval evaluation of X=log(N)*(2+sum q_n)-sum(q_n log n)=2 log(N)b_N; q_n=mu(n)(n-1)/n\",\n  \"sign_interval_rounding\": \"all MPFR operations used RNDD/RNDU; log uses MPFR directed correctly-rounded endpoints; signs listed only when interval excludes zero\",\n  \"head_and_plant_arithmetic\": \"80-bit-or-platform-long-double with Kahan prefix sums; diagnostic, not certified\"\n}\n";
    std::cerr << "crossings=" << std::accumulate(std::begin(counts), std::end(counts), uint64_t(0))
              << " ambiguous_initial=" << ambiguous.size() << " unresolved=" << pending.size()
              << " mpfr_bits=" << used_prec << "\n";
}

static uint64_t ceil_n_sqrt_n(uint64_t n) {
    const __uint128_t x = (__uint128_t)n * n * n;
    uint64_t lo = 0, hi = 1;
    while ((__uint128_t)hi*hi < x) hi <<= 1;
    while (lo + 1 < hi) {
        const uint64_t mid = lo + (hi-lo)/2;
        if ((__uint128_t)mid*mid < x) lo = mid; else hi = mid;
    }
    return hi;
}

struct Kahan { long double sum=0, corr=0; void add(long double x) { kahan_add(x, sum, corr); } };

struct FullRow { int64_t N; bool is_s; bool is_grid; uint64_t K; long double head, shoulder, full; uint64_t floor_blocks; double seconds; };

static long double floorblock_divisor_sum(int64_t k, int N, const std::vector<long double> &pref, uint64_t &blocks) {
    long double s=0, c=0;
    int64_t i=1;
    const int64_t nlim=std::min<int64_t>(N,k);
    while (i <= nlim) {
        const int64_t q = k / i;
        const int64_t j = std::min<int64_t>(nlim, k / q);
        kahan_add((long double)q * (pref[(size_t)j] - pref[(size_t)i-1]), s, c);
        ++blocks;
        i = j + 1;
    }
    return s;
}

static uint64_t floorblock_group_count(uint64_t k, uint64_t N) {
    uint64_t r=(uint64_t)sqrtl((long double)k);
    while ((__uint128_t)(r+1)*(r+1) <= k) ++r;
    while ((__uint128_t)r*r > k) --r;
    const uint64_t nlim=std::min(N,k);
    if (nlim <= r) return nlim;
    // Floors are distinct for n<=floor(sqrt(k)); for larger n they visit
    // every quotient down through floor(k/nlim), with no skipped integer.
    return r + (k/(r+1) - k/nlim + 1);
}

static void run_bench(const fs::path &out, int sampleN, int sampleCount) {
    if (sampleN < 3 || sampleN > 10000 || sampleCount < 100)
        throw std::runtime_error("bench requires 3<=N<=10000 and at least 100 samples");
    fs::create_directories(out);
    auto grid=make_log_grid(3,10000,100);
    std::set<int64_t> selected(grid.begin(),grid.end());
    uint64_t total_groups=0, shoulder_terms=0;
    auto count_start=Clock::now();
    for(int64_t N:selected){
        const uint64_t K=ceil_n_sqrt_n((uint64_t)N);
        for(uint64_t k=(uint64_t)N+1;k<K;++k){
            total_groups+=floorblock_group_count(k,(uint64_t)N);
            ++shoulder_terms;
        }
    }
    const double count_seconds=std::chrono::duration<double>(Clock::now()-count_start).count();
    Sieve sieve(sampleN);
    const long double L=logl((long double)sampleN);
    std::vector<long double> pref((size_t)sampleN+1,0); long double ps=0,pc=0;
    for(int n=1;n<=sampleN;++n){kahan_add((long double)sieve.mu[(size_t)n]*(1.0L-logl((long double)n)/L),ps,pc);pref[(size_t)n]=ps;}
    const uint64_t K=ceil_n_sqrt_n((uint64_t)sampleN);
    const uint64_t span=K-(uint64_t)sampleN-2;
    uint64_t observed=0, sampled_rows=0;
    Kahan checksum;
    auto bench_start=Clock::now();
    for(int i=0;i<sampleCount;++i){
        const uint64_t k=(uint64_t)sampleN+1+(span*(uint64_t)i)/(uint64_t)(sampleCount-1);
        uint64_t groups=0;
        checksum.add(floorblock_divisor_sum((int64_t)k,sampleN,pref,groups));
        observed+=groups; ++sampled_rows;
    }
    const double bench_seconds=std::chrono::duration<double>(Clock::now()-bench_start).count();
    const double rate=bench_seconds>0?(double)observed/bench_seconds:0;
    const double estimate=rate>0?(double)total_groups/rate:0;
    std::ofstream f((out/"core_benchmark.json").string());
    f << "{\n  \"grid_unique_points\": " << selected.size()
      << ",\n  \"source_grid_points\": 100"
      << ",\n  \"total_shoulder_terms\": " << shoulder_terms
      << ",\n  \"exact_total_floor_quotient_groups\": " << total_groups
      << ",\n  \"exact_group_count_method\": \"closed quotient-count formula per k, independent of the floor-block evaluation loop\""
      << ",\n  \"group_count_prepass_seconds\": " << std::setprecision(8) << count_seconds
      << ",\n  \"throughput_sample_N\": " << sampleN
      << ",\n  \"throughput_sample_rows\": " << sampled_rows
      << ",\n  \"throughput_sample_groups\": " << observed
      << ",\n  \"throughput_sample_seconds\": " << bench_seconds
      << ",\n  \"groups_per_second\": " << rate
      << ",\n  \"estimated_seconds_all_grid_shoulders\": " << estimate
      << ",\n  \"checksum\": " << std::setprecision(21) << checksum.sum
      << ",\n  \"estimate_scope\": \"92 unique rounded log-grid points only; all S<=10000 are empty in the completed certified scan\"\n}\n";
    std::cerr << "estimated_full_shoulder_seconds=" << estimate << " groups=" << total_groups
              << " sampled_rate=" << rate << " groups_per_second\n";
}

static void run_full(const fs::path &out, const fs::path &crossfile, int maxN) {
    if (maxN > 10000 || maxN < 3) throw std::runtime_error("full max must be 3..10000");
    fs::create_directories(out);
    std::ifstream cf(crossfile);
    if (!cf) throw std::runtime_error("crossing file missing");
    std::string line;
    std::getline(cf,line);
    std::set<int64_t> crossings;
    while (std::getline(cf,line)) {
        std::istringstream ss(line); std::string a,b,c,d;
        std::getline(ss,a,',');
        if (!a.empty()) { auto n=std::stoll(a); if (n<=maxN) crossings.insert(n); }
    }
    auto grid = make_log_grid(3, maxN, 100);
    grid.erase(std::remove_if(grid.begin(),grid.end(),[&](int64_t n){return n>maxN;}),grid.end());
    std::set<int64_t> gridset(grid.begin(),grid.end());
    std::set<int64_t> selected = crossings;
    selected.insert(grid.begin(),grid.end());
    const int sieveN = maxN;
    Sieve sieve(sieveN);
    const std::array<std::pair<int,uint64_t>,4> kchecks{{{3,6},{10,32},{200,2829},{10000,1000000}}};
    for (auto [n,k] : kchecks) if (n <= maxN && ceil_n_sqrt_n((uint64_t)n) != k)
        throw std::runtime_error("ceil(N^1.5) exact integer check failed at N="+std::to_string(n));
    long double psi=0, psic=0, sm0=0,sm0c=0,sm1=0,sm1c=0;
    long double A=0,Ac=0,B=0,Bc=0,C=0,Cc=0;
    std::vector<long double> head((size_t)maxN+1,0), svals((size_t)maxN+1,0), logvals((size_t)maxN+1,0);
    for (int n=1;n<=maxN;++n) {
        kahan_add(sieve.lambda[(size_t)n],psi,psic);
        if (sieve.mu[(size_t)n]) {
            kahan_add((long double)sieve.mu[(size_t)n]/n,sm0,sm0c);
            kahan_add((long double)sieve.mu[(size_t)n]*logl((long double)n)/n,sm1,sm1c);
        }
        const long double nl=n, l=logl(nl), w=1/(nl*(nl+1));
        kahan_add(psi*psi*w,A,Ac); kahan_add(psi/(nl+1),B,Bc); kahan_add(nl/(nl+1),C,Cc);
        if(n>=3){ const long double ss=sm0-sm1/l, x=l*ss; svals[n]=ss; logvals[n]=l; head[n]=(A-2*x*B+x*x*C)/(l*l); }
    }
    std::vector<FullRow> rows;
    uint64_t total_ops=0;
    for (int64_t N : selected) {
        const uint64_t K=ceil_n_sqrt_n((uint64_t)N);
        for(uint64_t k=(uint64_t)N+1;k<K;++k)
            total_ops += floorblock_group_count(k,(uint64_t)N);
    }
    auto run_start=Clock::now(); uint64_t done=0, processed_blocks=0;
    std::ofstream full((out/"core_full_H.csv").string());
    full << "N,in_S,log_grid,K,head,shoulder,full_H,floor_blocks,seconds\n";
    std::set<int64_t> written;
    for (int64_t N : selected) {
        const auto begin=Clock::now();
        const uint64_t K=ceil_n_sqrt_n((uint64_t)N);
        std::vector<long double> pref((size_t)N+1,0);
        const long double L=logl((long double)N);
        long double wsum=0,wc=0;
        for(int n=1;n<=N;++n){
            const long double wn=(long double)sieve.mu[(size_t)n]*(1.0L-logl((long double)n)/L);
            kahan_add(wn,wsum,wc); pref[(size_t)n]=wsum;
        }
        Kahan shoulder; uint64_t blocks=0;
        for(int64_t k=N+1;k<(int64_t)K;++k){
            const uint64_t before=blocks;
            const long double D=floorblock_divisor_sum(k,(int)N,pref,blocks);
            const long double R=1.0L+(long double)k*svals[(size_t)N]-D;
            shoulder.add(R*R/((long double)k*(k+1)));
            ++done;
            processed_blocks += blocks-before;
            if (processed_blocks && processed_blocks % 5000000 == 0)
                progress("floor-block quotient groups",processed_blocks,total_ops,run_start);
        }
        const long double h=head[(size_t)N], sh=shoulder.sum;
        const double sec=std::chrono::duration<double>(Clock::now()-begin).count();
        rows.push_back({N,crossings.count(N)>0,gridset.count(N)>0,K,h,sh,h+sh,blocks,sec});
        full << N << ',' << (crossings.count(N)?"true":"false") << ',' << (gridset.count(N)?"true":"false")
             << ',' << K << ',' << std::setprecision(21) << h << ',' << sh << ',' << (h+sh)
             << ',' << blocks << ',' << std::setprecision(8) << sec << '\n';
        written.insert(N);
        if (N == *selected.rbegin()) progress("floor-block quotient groups",processed_blocks,total_ops,run_start);
    }
    full.close();

    // J3: independent direct residue construction against the head-prefix plus
    // floor-block shoulder for every N=3..200. This is a finite norm identity,
    // not subtraction of either b_N^2/K or the paid 5/log^2 N upper bound.
    Sieve s3(200);
    std::ofstream j3((out/"core_j3.csv").string());
    j3 << "N,K,direct_residue_norm,prefix_head_plus_floorblock_shoulder,abs_difference,tolerance,status\n";
    bool j3pass=true; long double maxdiff=0; int maxdiffN=0;
    for(int N=3;N<=200;++N){
        const uint64_t K=ceil_n_sqrt_n((uint64_t)N); const long double L=logl((long double)N);
        long double sm=0,smc=0;
        for(int n=1;n<=N;++n) kahan_add((long double)s3.mu[(size_t)n]*(1.0L-logl((long double)n)/L)/n,sm,smc);
        Kahan direct;
        for(uint64_t k=1;k<K;++k){
            long double R=1;
            for(int n=2;n<=N;++n) if(s3.mu[(size_t)n]) {
                const long double an=(long double)s3.mu[(size_t)n]*(1.0L-logl((long double)n)/L);
                R+=an*(long double)(k%(uint64_t)n)/n;
            }
            direct.add(R*R/((long double)k*(k+1)));
        }
        // Use the requested A/B/C head prefix formula and independently
        // grouped floor-block shoulder; compare with the literal residue norm.
        std::vector<long double> pref((size_t)N+1,0); long double wsum=0,wc=0;
        for(int n=1;n<=N;++n){kahan_add((long double)s3.mu[(size_t)n]*(1.0L-logl((long double)n)/L),wsum,wc);pref[(size_t)n]=wsum;}
        Kahan shoulder_check; uint64_t blocks=0;
        for(uint64_t k=(uint64_t)N+1;k<K;++k){
            const long double D=floorblock_divisor_sum((int64_t)k,N,pref,blocks);
            const long double R=1+(long double)k*sm-D;
            shoulder_check.add(R*R/((long double)k*(k+1)));
        }
        Kahan aa,bb,cc; long double ps=0,psc=0;
        for(int k=1;k<=N;++k){
            kahan_add(s3.lambda[(size_t)k],ps,psc);
            const long double kl=k, ww=1/(kl*(kl+1));
            aa.add(ps*ps*ww); bb.add(ps/(kl+1)); cc.add(kl/(kl+1));
        }
        const long double x=L*sm;
        const long double hprefix=(aa.sum-2*x*bb.sum+x*x*cc.sum)/(L*L);
        const long double floor_head_shoulder=hprefix+shoulder_check.sum;
        const long double diff=fabsl(direct.sum-floor_head_shoulder);
        if(diff>maxdiff){maxdiff=diff;maxdiffN=N;}
        const char *status=diff<=1e-10L?"PASS":"FAIL"; if(diff>1e-10L)j3pass=false;
        j3 << N << ',' << K << ',' << std::setprecision(21) << direct.sum << ',' << floor_head_shoulder << ',' << diff << ",1e-10," << status << '\n';
    }
    std::ofstream j3json((out/"core_j3_judge.json").string());
    j3json << "{\n  \"judge\": \"J3_finite_identity\",\n  \"finite_identity_status\": \"" << (j3pass?"PASS":"FAIL")
           << "\",\n  \"checked_N\": \"every integer 3..200\",\n  \"comparison\": \"independent literal residue norm versus A/B/C prefix head plus floor-block shoulder through K_N-1\",\n  \"max_abs_difference\": " << std::setprecision(21) << maxdiff
           << ",\n  \"maxdiff_at_N\": " << maxdiffN
           << ",\n  \"tolerance\": 1e-10,\n  \"original_J3_scope\": \"CLARIFIED_SUBJUDGE_ONLY; the infinite tail was not independently summed\",\n  \"infinite_tail_identity\": \"E=H+exact_tail; 5/log^2 N is only a bound and was not subtracted as equality\",\n  \"arithmetic\": \"long double with compensated norm sums; finite diagnostic\"\n}\n";
}

int main(int argc,char **argv) {
    try {
        if (argc < 2) { std::cerr << "usage: core_scan scan OUT [MAX [BITS]] | full OUT CROSSINGS [MAX] | bench OUT [N [SAMPLES]]\n"; return 2; }
        const std::string mode=argv[1];
        if(mode=="scan"){
            if(argc<3)return 2; const int64_t max=argc>3?std::stoll(argv[3]):10000000; const int bits=argc>4?std::stoi(argv[4]):192;
            run_scan(argv[2],max,bits); return 0;
        }
        if(mode=="full"){
            if(argc<4)return 2; const int max=argc>4?std::stoi(argv[4]):10000;
            run_full(argv[2],argv[3],max); return 0;
        }
        if(mode=="bench"){
            if(argc<3)return 2; const int N=argc>3?std::stoi(argv[3]):10000; const int samples=argc>4?std::stoi(argv[4]):20000;
            run_bench(argv[2],N,samples); return 0;
        }
        std::cerr << "unknown mode " << mode << "\n"; return 2;
    } catch(const std::exception &e) { std::cerr << "ERROR: " << e.what() << "\n"; return 1; }
}
