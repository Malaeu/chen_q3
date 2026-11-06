// Integer-supported systems and probes for ZERO_SENSITIVE_FAKES.
// The program records finite diagnostics; it does not encode an RH claim.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {
namespace fs = std::filesystem;
using u32 = uint32_t;
using u64 = uint64_t;

constexpr u32 kTrueLimit = 100000000;
constexpr u32 kFakeLimit = 10000000;
constexpr u32 kBlockSize = 1u << 20;
constexpr std::array<int, 4> kP2Moduli{3, 4, 5, 6};

struct Kahan {
    long double sum = 0;
    long double correction = 0;
    void add(long double value) {
        const long double y = value - correction;
        const long double t = sum + y;
        correction = (t - sum) - y;
        sum = t;
    }
};

struct GridPoint {
    long double x;
    int exact_power;
};

struct SamplePoint {
    long double x;
};

struct Segment {
    u32 lo = 0;
    u32 hi = 0;
    std::vector<u32> remaining;
    std::vector<int8_t> mobius;
    std::vector<uint8_t> prime;
};

struct P5Row {
    long double x;
    int64_t numerator_pairs;
    int64_t denominator_pairs;
};

u64 pow10u(int exponent) {
    u64 result = 1;
    for (int i = 0; i < exponent; ++i) result *= 10;
    return result;
}

std::vector<GridPoint> make_grid(int max_decade) {
    std::vector<GridPoint> grid;
    const long double log10 = std::log(10.0L);
    for (int decade = 1; decade < max_decade; ++decade) {
        const long double base = static_cast<long double>(pow10u(decade));
        for (int j = 0; j < 100; ++j) {
            const long double x = j == 0
                ? base
                : std::exp(std::log(base) + (static_cast<long double>(j) / 100.0L) * log10);
            grid.push_back({x, j == 0 ? decade : -1});
        }
    }
    grid.push_back({static_cast<long double>(pow10u(max_decade)), max_decade});
    return grid;
}

std::vector<SamplePoint> make_samples(int max_decade) {
    std::vector<SamplePoint> samples;
    samples.reserve(static_cast<size_t>(max_decade) * 1000);
    const long double log10 = std::log(10.0L);
    for (int decade = 0; decade < max_decade; ++decade) {
        const long double base_log = static_cast<long double>(decade) * log10;
        for (int j = 0; j < 1000; ++j) {
            const long double offset = (static_cast<long double>(j) + 0.5L) / 1000.0L;
            samples.push_back({std::exp(base_log + offset * log10)});
        }
    }
    return samples;
}

std::vector<u32> make_primes(u32 limit) {
    std::vector<uint8_t> composite(static_cast<size_t>(limit) + 1, 0);
    std::vector<u32> primes;
    for (u32 p = 2; static_cast<u64>(p) * p <= limit; ++p) {
        if (composite[p]) continue;
        for (u64 n = static_cast<u64>(p) * p; n <= limit; n += p) {
            composite[static_cast<size_t>(n)] = 1;
        }
    }
    for (u32 n = 2; n <= limit; ++n) {
        if (!composite[n]) primes.push_back(n);
    }
    return primes;
}

void fill_segment(u32 lo, u32 hi, const std::vector<u32>& primes, Segment& seg) {
    seg.lo = lo;
    seg.hi = hi;
    const size_t size = static_cast<size_t>(hi - lo) + 1;
    seg.remaining.resize(size);
    seg.mobius.assign(size, 1);
    seg.prime.assign(size, 1);
    for (size_t i = 0; i < size; ++i) seg.remaining[i] = lo + static_cast<u32>(i);
    for (size_t i = 0; i < size; ++i) {
        const u32 n = lo + static_cast<u32>(i);
        if (n == 0) {
            seg.mobius[i] = 0;
            seg.prime[i] = 0;
        } else if (n == 1) {
            seg.prime[i] = 0;
        }
    }
    for (u32 p : primes) {
        if (static_cast<u64>(p) * p > hi) break;
        u64 first = ((static_cast<u64>(lo) + p - 1) / p) * p;
        first = std::max<u64>(first, static_cast<u64>(p) * p);
        for (u64 n = first; n <= hi; n += p) {
            const size_t i = static_cast<size_t>(n - lo);
            seg.prime[i] = 0;
        }
        first = ((static_cast<u64>(lo) + p - 1) / p) * p;
        for (u64 n = first; n <= hi; n += p) {
            const size_t i = static_cast<size_t>(n - lo);
            u32 exponent = 0;
            while (seg.remaining[i] % p == 0) {
                seg.remaining[i] /= p;
                ++exponent;
            }
            if (exponent == 0) continue;
            if (exponent > 1) {
                seg.mobius[i] = 0;
            } else if (seg.mobius[i] != 0) {
                seg.mobius[i] = static_cast<int8_t>(-seg.mobius[i]);
            }
        }
    }
    for (size_t i = 0; i < size; ++i) {
        if (seg.remaining[i] > 1) {
            seg.mobius[i] = static_cast<int8_t>(-seg.mobius[i]);
        }
    }
}

long double kappa_value() {
    const long double root5 = std::sqrt(5.0L);
    return (std::sqrt(10.0L - 2.0L * root5) - 2.0L) / (root5 - 1.0L);
}

long double dh_a(u32 n, long double kappa) {
    switch (n % 5) {
        case 1: return 1.0L;
        case 2: return kappa;
        case 3: return -kappa;
        case 4: return -1.0L;
        default: return 0.0L;
    }
}

struct StreamWriter {
    std::string name;
    u32 max_n;
    int decades;
    bool write_w;
    std::ofstream grid_file;
    std::ofstream sample_file;
    std::ofstream probe_file;
    std::vector<GridPoint> grid;
    std::vector<SamplePoint> samples;
    size_t grid_index = 0;
    size_t sample_index = 0;
    Kahan prefix;
    Kahan integral;
    Kahan adjacent_sum;
    u64 adjacent_support = 0;
    u64 adjacent_pairs = 0;
    long double previous_b = 0;
    bool previous_nonzero = false;

    StreamWriter(const fs::path& out, std::string system, u32 limit, int max_decade,
                 bool save_w, bool save_samples = true)
        : name(std::move(system)), max_n(limit), decades(max_decade), write_w(save_w),
          grid(make_grid(max_decade)), samples(make_samples(max_decade)) {
        if (save_w) {
            grid_file.open(out / (name + ".csv"));
            if (!grid_file) throw std::runtime_error("cannot open " + name + ".csv");
            grid_file << "X,M,W\n" << std::setprecision(21);
        }
        if (save_samples) {
            sample_file.open(out / (name + "_samples.csv"));
            if (!sample_file) throw std::runtime_error("cannot open " + name + "_samples.csv");
            sample_file << "x,M,M_over_sqrt_x,M_over_x\n" << std::setprecision(21);
        }
        probe_file.open(out / (name + "_probes.csv"));
        if (!probe_file) throw std::runtime_error("cannot open " + name + "_probes.csv");
        probe_file << "X,unit_shift_sum_over_X,adjacent_support_fraction,adjacent_support_count,adjacent_pair_count\n"
                   << std::setprecision(21);
    }

    void advance(u32 n, long double b, bool nonzero) {
        prefix.add(b);
        if (n > 1) {
            adjacent_sum.add(previous_b * b);
            ++adjacent_pairs;
            if (previous_nonzero && nonzero) ++adjacent_support;
        }
        previous_b = b;
        previous_nonzero = nonzero;
        while (sample_index < samples.size() && samples[sample_index].x < static_cast<long double>(n) + 1.0L) {
            const long double x = samples[sample_index].x;
            if (sample_file) {
                const long double root_x = std::sqrt(x);
                sample_file << x << ',' << prefix.sum << ',' << prefix.sum / root_x << ',' << prefix.sum / x << '\n';
            }
            ++sample_index;
        }
        while (grid_index < grid.size() && grid[grid_index].x < static_cast<long double>(n) + 1.0L) {
            const GridPoint& point = grid[grid_index];
            const u32 floor_x = static_cast<u32>(std::floor(point.x));
            if (floor_x < 2 || floor_x > n) throw std::runtime_error("grid prefix/index mismatch for " + name);
            if (write_w) {
                const long double partial = (point.x - n) /
                    (static_cast<long double>(n) * point.x);
                const long double numerator = integral.sum + prefix.sum * prefix.sum * partial;
                const long double w = numerator / std::log(point.x);
                if (!std::isfinite(w) || w < 0) throw std::runtime_error("invalid W for " + name);
                grid_file << point.x << ',' << prefix.sum << ',' << w << '\n';
            }
            const long double normalized = adjacent_sum.sum / point.x;
            const long double support_fraction = static_cast<long double>(adjacent_support) /
                static_cast<long double>(floor_x - 1);
            probe_file << point.x << ',' << normalized << ',' << support_fraction << ','
                       << adjacent_support << ',' << (floor_x - 1) << '\n';
            ++grid_index;
        }
        if (write_w && n < max_n) {
            const long double m = prefix.sum;
            integral.add(m * m / (static_cast<long double>(n) * (n + 1.0L)));
        }
    }

    void finish() {
        if (grid_index != grid.size() || sample_index != samples.size()) {
            throw std::runtime_error(name + " did not emit every registered grid/sample point");
        }
        if (grid_file) grid_file.close();
        if (sample_file) sample_file.close();
        probe_file.close();
    }
};

void write_t1_trial_prefix(const fs::path& output, u32 limit) {
    const auto primes = make_primes(static_cast<u32>(std::sqrt(static_cast<long double>(limit))) + 1);
    Segment segment;
    std::ofstream out(output);
    if (!out) throw std::runtime_error("cannot open T1 trial-factor judge input");
    out << "n,b\n";
    for (u32 lo = 1; lo <= limit;) {
        const u32 hi = std::min<u32>(limit, lo + kBlockSize - 1);
        fill_segment(lo, hi, primes, segment);
        for (u32 n = lo; n <= hi; ++n) {
            const size_t i = static_cast<size_t>(n - lo);
            int chi = n % 4 == 1 ? 1 : (n % 4 == 3 ? -1 : 0);
            const int value = static_cast<int>(segment.mobius[i]) * chi;
            out << n << ',' << value << '\n';
        }
        lo = hi + 1;
    }
}

void run_true_integer_systems(const fs::path& out) {
    const auto start = std::chrono::steady_clock::now();
    const auto primes = make_primes(10000);
    StreamWriter t0(out, "T0", kTrueLimit, 8, false);
    StreamWriter t1(out, "T1", kTrueLimit, 8, true);
    std::ofstream p2(out / "T0_prime_p2.csv");
    if (!p2) throw std::runtime_error("cannot open T0_prime_p2.csv");
    p2 << "X,modulus,residue,count,total_count,expected_uniform,normalized_imbalance,probe_scalar\n"
       << std::setprecision(21);
    std::array<std::array<u64, 6>, 4> prime_counts{};
    const auto grid = make_grid(8);
    size_t grid_index = 0;
    Segment segment;
    u32 next_progress = 5000000;
    std::cout << "PHASE integer_true start systems=T0,T1,P2-prime-reference max=" << kTrueLimit << '\n';
    for (u32 lo = 1; lo <= kTrueLimit;) {
        const u32 hi = std::min<u32>(kTrueLimit, lo + kBlockSize - 1);
        fill_segment(lo, hi, primes, segment);
        for (u32 n = lo; n <= hi; ++n) {
            const size_t i = static_cast<size_t>(n - lo);
            const int8_t mu = segment.mobius[i];
            const int chi = n % 4 == 1 ? 1 : (n % 4 == 3 ? -1 : 0);
            const long double b0 = mu;
            const long double b1 = static_cast<long double>(mu) * chi;
            t0.advance(n, b0, mu != 0);
            t1.advance(n, b1, b1 != 0);
            if (segment.prime[i]) {
                for (size_t mi = 0; mi < kP2Moduli.size(); ++mi) {
                    const int mod = kP2Moduli[mi];
                    ++prime_counts[mi][n % static_cast<u32>(mod)];
                }
            }
            while (grid_index < grid.size() && grid[grid_index].x < static_cast<long double>(n) + 1.0L) {
                const auto& point = grid[grid_index];
                for (size_t mi = 0; mi < kP2Moduli.size(); ++mi) {
                    const int mod = kP2Moduli[mi];
                    u64 count = 0;
                    for (int r = 0; r < mod; ++r) count += prime_counts[mi][static_cast<size_t>(r)];
                    if (count == 0) continue;
                    long double sumsq = 0;
                    for (int r = 0; r < mod; ++r) {
                        const long double expected = static_cast<long double>(count) / mod;
                        const long double delta = static_cast<long double>(prime_counts[mi][static_cast<size_t>(r)]) - expected;
                        sumsq += delta * delta;
                    }
                    const long double scalar = std::sqrt(sumsq / static_cast<long double>(count));
                    for (int r = 0; r < mod; ++r) {
                        const long double expected = static_cast<long double>(count) / mod;
                        const long double imbalance =
                            (static_cast<long double>(prime_counts[mi][static_cast<size_t>(r)]) - expected) /
                            std::sqrt(static_cast<long double>(count));
                        p2 << point.x << ',' << mod << ',' << r << ','
                           << prime_counts[mi][static_cast<size_t>(r)] << ',' << count << ','
                           << expected << ',' << imbalance << ',' << scalar << '\n';
                    }
                }
                ++grid_index;
            }
            if (n >= next_progress) {
                const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
                const double fraction = static_cast<double>(n) / kTrueLimit;
                std::cout << "PROGRESS system=T1+T0+P2 n=" << n << '/' << kTrueLimit
                          << " pct=" << std::fixed << std::setprecision(1) << 100.0 * fraction
                          << " elapsed_s=" << std::setprecision(1) << elapsed
                          << " eta_s=" << elapsed * (1.0 / fraction - 1.0) << std::defaultfloat << '\n';
                next_progress += 5000000;
            }
        }
        lo = hi + 1;
    }
    t0.finish();
    t1.finish();
    if (grid_index != grid.size()) throw std::runtime_error("P2 reference did not emit all grid points");
    p2.close();
    std::cout << "PHASE integer_true done elapsed_s="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() << '\n';
}

std::vector<u32> make_spf(u32 limit) {
    std::vector<u32> spf(static_cast<size_t>(limit) + 1, 0);
    std::vector<u32> primes;
    primes.reserve(static_cast<size_t>(limit / std::log(static_cast<long double>(limit))) + 16);
    for (u32 n = 2; n <= limit; ++n) {
        if (spf[n] == 0) {
            spf[n] = n;
            primes.push_back(n);
        }
        for (u32 p : primes) {
            if (p > spf[n] || static_cast<u64>(p) * n > limit) break;
            spf[p * n] = p;
        }
    }
    return spf;
}

std::vector<double> read_tau_weights(const fs::path& path, u32 limit) {
    std::ifstream in(path, std::ios::binary | std::ios::ate);
    if (!in) throw std::runtime_error("cannot open normalized tau-prime weights");
    const std::streamoff expected = static_cast<std::streamoff>(limit + 1) * sizeof(double);
    if (in.tellg() != expected) throw std::runtime_error("tau-prime weight file has wrong size");
    in.seekg(0);
    std::vector<double> weights(static_cast<size_t>(limit) + 1);
    in.read(reinterpret_cast<char*>(weights.data()), expected);
    if (!in) throw std::runtime_error("failed to read normalized tau-prime weights");
    if (weights[1] != 0.0) throw std::runtime_error("tau-prime weights must be indexed from zero with index 1 unused");
    return weights;
}

long double t2_coefficient(u32 n, const std::vector<u32>& spf, const std::vector<double>& weights) {
    if (n == 1) return 1.0L;
    long double value = 1.0L;
    u32 x = n;
    while (x > 1) {
        const u32 p = spf[x];
        u32 exponent = 0;
        do {
            x /= p;
            ++exponent;
        } while (x > 1 && spf[x] == p);
        if (exponent == 1) value *= static_cast<long double>(weights[p]);
        else if (exponent > 2) return 0.0L;
    }
    return value;
}

struct Factor {
    u32 prime;
    u32 exponent;
};

void run_t2(const fs::path& out, const std::vector<u32>& spf,
            const std::vector<double>& weights) {
    const auto start = std::chrono::steady_clock::now();
    StreamWriter writer(out, "T2", kFakeLimit, 7, true);
    u32 next_progress = 500000;
    std::cout << "PHASE T2_stream start limit=" << kFakeLimit << '\n';
    for (u32 n = 1; n <= kFakeLimit; ++n) {
        const long double b = t2_coefficient(n, spf, weights);
        writer.advance(n, b, b != 0.0L);
        if (n >= next_progress) {
            const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
            const double fraction = static_cast<double>(n) / kFakeLimit;
            std::cout << "PROGRESS system=T2 n=" << n << '/' << kFakeLimit
                      << " pct=" << std::fixed << std::setprecision(1) << 100.0 * fraction
                      << " elapsed_s=" << std::setprecision(1) << elapsed
                      << " eta_s=" << elapsed * (1.0 / fraction - 1.0) << std::defaultfloat << '\n';
            next_progress += 500000;
        }
    }
    writer.finish();
    std::cout << "PHASE T2_stream done elapsed_s="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() << '\n';
}

void make_divisors(u32 n, const std::vector<u32>& spf,
                   std::array<Factor, 16>& factors, size_t& nf,
                   std::vector<u32>& divisors) {
    nf = 0;
    u32 x = n;
    while (x > 1) {
        const u32 p = spf[x];
        u32 exponent = 0;
        do {
            x /= p;
            ++exponent;
        } while (x > 1 && spf[x] == p);
        if (nf >= factors.size()) throw std::runtime_error("factor buffer overflow");
        factors[nf++] = {p, exponent};
    }
    divisors.clear();
    divisors.push_back(1);
    for (size_t j = 0; j < nf; ++j) {
        const size_t old_size = divisors.size();
        u32 power = 1;
        for (u32 e = 1; e <= factors[j].exponent; ++e) {
            power *= factors[j].prime;
            for (size_t i = 0; i < old_size; ++i) divisors.push_back(divisors[i] * power);
        }
    }
}

long double f1_inverse_at(u32 n, const std::vector<u32>& spf,
                          const std::vector<long double>& b,
                          std::array<Factor, 16>& factors,
                          std::vector<u32>& divisors,
                          long double kappa,
                          long double& sum_abs) {
    size_t nf = 0;
    make_divisors(n, spf, factors, nf, divisors);
    Kahan sum;
    sum_abs = 0.0L;
    for (size_t i = 1; i < divisors.size(); ++i) {
        const u32 d = divisors[i];
        const long double term = dh_a(d, kappa) * b[n / d];
        sum.add(term);
        sum_abs += std::fabs(term);
    }
    return -sum.sum;
}

void write_f1_prefix(const fs::path& output, u32 limit) {
    const auto spf = make_spf(limit);
    std::vector<long double> b(static_cast<size_t>(limit) + 1, 0.0L);
    std::array<Factor, 16> factors{};
    std::vector<u32> divisors;
    divisors.reserve(1024);
    const long double kappa = kappa_value();
    b[1] = 1.0L;
    std::ofstream out(output);
    if (!out) throw std::runtime_error("cannot open F1 small inverse output");
    out << "n,b\n" << std::setprecision(21);
    out << "1," << b[1] << '\n';
    for (u32 n = 2; n <= limit; ++n) {
        long double sum_abs = 0.0L;
        b[n] = f1_inverse_at(n, spf, b, factors, divisors, kappa, sum_abs);
        out << n << ',' << b[n] << '\n';
    }
}

void run_f1(const fs::path& out, const std::vector<u32>& spf) {
    const auto start = std::chrono::steady_clock::now();
    StreamWriter writer(out, "F1", kFakeLimit, 7, true);
    const long double kappa = kappa_value();
    std::vector<long double> b(static_cast<size_t>(kFakeLimit) + 1, 0.0L);
    std::array<Factor, 16> factors{};
    std::vector<u32> divisors;
    divisors.reserve(1024);
    b[1] = 1.0L;
    u32 next_progress = 100000;
    std::cout << "PHASE F1_divisor_inverse start limit=" << kFakeLimit
              << " coefficient_type=long_double zero_tol=64*epsilon*sum_abs_terms epsilon="
              << std::setprecision(21) << std::numeric_limits<long double>::epsilon()
              << std::defaultfloat << '\n';
    for (u32 n = 1; n <= kFakeLimit; ++n) {
        bool nonzero = true;
        if (n > 1) {
            long double sum_abs = 0.0L;
            b[n] = f1_inverse_at(n, spf, b, factors, divisors, kappa, sum_abs);
            const long double tolerance = 64.0L * std::numeric_limits<long double>::epsilon() * sum_abs;
            nonzero = std::fabs(b[n]) > tolerance;
        }
        writer.advance(n, b[n], nonzero);
        if (n >= next_progress) {
            const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
            const double fraction = static_cast<double>(n) / kFakeLimit;
            std::cout << "PROGRESS system=F1 n=" << n << '/' << kFakeLimit
                      << " pct=" << std::fixed << std::setprecision(1) << 100.0 * fraction
                      << " elapsed_s=" << std::setprecision(1) << elapsed
                      << " eta_s=" << elapsed * (1.0 / fraction - 1.0) << std::defaultfloat << '\n';
            next_progress += 100000;
        }
    }
    writer.finish();
    b.clear();
    std::cout << "PHASE F1_divisor_inverse done elapsed_s="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() << '\n';
}

int residue_count(u32 n, int residue) {
    if (residue == 0 || n < static_cast<u32>(residue)) return residue == 0 ? static_cast<int>(n / 5) : 0;
    return static_cast<int>((n - static_cast<u32>(residue)) / 5 + 1);
}

std::vector<int32_t> make_mobius_residue_prefixes(u32 limit) {
    const auto primes = make_primes(static_cast<u32>(std::sqrt(static_cast<long double>(limit))) + 1);
    std::array<std::vector<int32_t>, 5> by_residue;
    for (int c = 0; c < 5; ++c) {
        const size_t count = c == 0 ? limit / 5 : (limit >= static_cast<u32>(c)
            ? (limit - static_cast<u32>(c)) / 5 + 1 : 0);
        by_residue[static_cast<size_t>(c)].reserve(count);
    }
    std::vector<int32_t> total_prefix(static_cast<size_t>(limit) + 1, 0);
    std::array<int32_t, 5> accum{};
    int32_t total = 0;
    Segment segment;
    for (u32 lo = 1; lo <= limit;) {
        const u32 hi = std::min<u32>(limit, lo + kBlockSize - 1);
        fill_segment(lo, hi, primes, segment);
        for (u32 n = lo; n <= hi; ++n) {
            const int mu = segment.mobius[static_cast<size_t>(n - lo)];
            const int c = static_cast<int>(n % 5);
            accum[static_cast<size_t>(c)] += mu;
            total += mu;
            by_residue[static_cast<size_t>(c)].push_back(accum[static_cast<size_t>(c)]);
            total_prefix[n] = total;
        }
        lo = hi + 1;
    }
    // Pack five same-residue prefix vectors contiguously after computing their lengths.
    size_t total_size = 0;
    for (const auto& v : by_residue) total_size += v.size();
    std::vector<int32_t> packed;
    packed.reserve(total_size + total_prefix.size());
    for (const auto& v : by_residue) packed.insert(packed.end(), v.begin(), v.end());
    packed.insert(packed.end(), total_prefix.begin(), total_prefix.end());
    return packed;
}

int32_t residue_prefix_value(const std::vector<int32_t>& packed,
                             const std::array<size_t, 6>& offsets,
                             int residue, u32 n) {
    const int count = residue_count(n, residue);
    if (count <= 0) return 0;
    return packed[offsets[static_cast<size_t>(residue)] + static_cast<size_t>(count - 1)];
}

int32_t total_prefix_value(const std::vector<int32_t>& packed,
                           const std::array<size_t, 6>& offsets,
                           u32 n, u32 limit) {
    if (n > limit) n = limit;
    return packed[offsets[5] + n];
}

int inverse_mod5(int residue) {
    for (int n = 1; n < 5; ++n) if ((n * residue) % 5 == 1) return n;
    throw std::runtime_error("attempted inverse of zero modulo 5");
}

int mobius_trial_small(int n) {
    if (n == 1) return 1;
    int remaining = n;
    int sign = 1;
    for (int p = 2; p * p <= remaining; ++p) {
        if (remaining % p != 0) continue;
        remaining /= p;
        if (remaining % p == 0) return 0;
        sign = -sign;
        while (remaining % p == 0) remaining /= p;
    }
    if (remaining > 1) sign = -sign;
    return sign;
}

void self_test_p5_small() {
    constexpr int limit = 60;
    int64_t brute_total = 0;
    int64_t brute_defect_pairs = 0;
    for (int m = 1; m <= limit; ++m) {
        for (int n = 1; n <= limit; ++n) {
            if (std::gcd(m, n) != 1) continue;
            ++brute_total;
            const int rm = m % 5;
            const int rn = n % 5;
            if ((rm == 2 || rm == 3) && (rn == 2 || rn == 3)) ++brute_defect_pairs;
        }
    }
    int64_t formula_total = 0;
    int64_t formula_defect_pairs = 0;
    for (int d = 1; d <= limit; ++d) {
        const int mu = mobius_trial_small(d);
        const int q = limit / d;
        formula_total += static_cast<int64_t>(mu) * q * q;
        const int c = d % 5;
        if (c == 0) continue;
        const int inv = inverse_mod5(c);
        const int t2 = (inv * 2) % 5;
        const int t3 = (inv * 3) % 5;
        int brute_class_count = 0;
        for (int u = 1; u <= q; ++u) {
            const int r = (c * u) % 5;
            if (r == 2 || r == 3) ++brute_class_count;
        }
        if (brute_class_count != residue_count(q, t2) + residue_count(q, t3)) {
            throw std::runtime_error("P5 residue preimage count failed its small brute check");
        }
        const int bcount = brute_class_count;
        formula_defect_pairs += static_cast<int64_t>(mu) * bcount * bcount;
    }
    if (formula_total != brute_total || formula_defect_pairs != brute_defect_pairs) {
        throw std::runtime_error("P5 Mobius residue summation failed its small ordered-pair check");
    }
}

void run_f1_p5(const fs::path& out) {
    const auto start = std::chrono::steady_clock::now();
    const auto grid = make_grid(7);
    auto packed = make_mobius_residue_prefixes(kFakeLimit);
    std::array<size_t, 6> offsets{};
    size_t cursor = 0;
    for (int c = 0; c < 5; ++c) {
        offsets[static_cast<size_t>(c)] = cursor;
        cursor += c == 0 ? kFakeLimit / 5 : (kFakeLimit - static_cast<u32>(c)) / 5 + 1;
    }
    offsets[5] = cursor;
    const long double kappa = kappa_value();
    // For the frozen periodic a mod 5, |a(rs)-a(r)a(s)| vanishes unless
    // r,s are 2 or 3; on those four ordered residue pairs it is 1+kappa^2.
    // Thus exact Mobius residue counts, rather than sampled pairs, suffice.
    const long double defect = 1.0L + kappa * kappa;
    std::ofstream probes(out / "F1_p5_probes.csv");
    std::ofstream pairs(out / "F1_p5_residue_pair_counts.csv");
    if (!probes || !pairs) throw std::runtime_error("cannot open F1 P5 output CSVs");
    probes << "X,mean_absolute_defect,defect_pair_count,total_ordered_coprime_pairs,relative_defect_pair_density\n"
           << std::setprecision(21);
    pairs << "residue_m,residue_n,ordered_coprime_pair_count\n";
    std::array<std::array<int64_t, 2>, 2> pair_counts_at_max{};
    u32 next_progress = 100;
    size_t grid_index = 0;
    std::cout << "PHASE F1_P5_mu_residue_summation start grid_rows=" << grid.size()
              << " prefix_int32_bytes=" << (packed.size() * sizeof(int32_t)) << '\n';
    for (const auto& point : grid) {
        const u32 x = static_cast<u32>(std::floor(point.x));
        int64_t denominator = 0;
        int64_t numerator = 0;
        std::array<std::array<int64_t, 2>, 2> pair_counts{};
        for (u32 left = 1; left <= x;) {
            const u32 q = x / left;
            const u32 right = x / q;
            const int64_t mu_total = static_cast<int64_t>(total_prefix_value(packed, offsets, right, kFakeLimit)) -
                static_cast<int64_t>(total_prefix_value(packed, offsets, left - 1, kFakeLimit));
            denominator += mu_total * static_cast<int64_t>(q) * q;
            for (int c = 1; c < 5; ++c) {
                const int64_t mu_c = static_cast<int64_t>(residue_prefix_value(packed, offsets, c, right)) -
                    static_cast<int64_t>(residue_prefix_value(packed, offsets, c, left - 1));
                const int inv = inverse_mod5(c);
                const int t2 = (inv * 2) % 5;
                const int t3 = (inv * 3) % 5;
                const int bcount = residue_count(q, t2) + residue_count(q, t3);
                numerator += mu_c * static_cast<int64_t>(bcount) * bcount;
                if (point.x == grid.back().x) {
                    const std::array<int, 2> preimages{t2, t3};
                    for (size_t i = 0; i < 2; ++i) {
                        for (size_t j = 0; j < 2; ++j) {
                            const int a = residue_count(q, preimages[i]);
                            const int bcount2 = residue_count(q, preimages[j]);
                            pair_counts[i][j] += mu_c * static_cast<int64_t>(a) * bcount2;
                        }
                    }
                }
            }
            left = right + 1;
        }
        if (denominator <= 0 || numerator < 0 || numerator > denominator) {
            throw std::runtime_error("invalid exact P5 pair counts at X=" + std::to_string(x));
        }
        if (point.x == grid.back().x) {
            int64_t matrix_total = 0;
            for (const auto& row : pair_counts) {
                matrix_total += row[0] + row[1];
            }
            if (matrix_total != numerator) {
                throw std::runtime_error("P5 residue-pair matrix does not sum to the detector numerator");
            }
        }
        const long double mean = defect * static_cast<long double>(numerator) /
            static_cast<long double>(denominator);
        probes << point.x << ',' << mean << ',' << numerator << ',' << denominator << ','
               << static_cast<long double>(numerator) / denominator << '\n';
        if (point.x == grid.back().x) pair_counts_at_max = pair_counts;
        ++grid_index;
        if (grid_index >= next_progress) {
            const double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
            const double fraction = static_cast<double>(grid_index) / grid.size();
            std::cout << "PROGRESS system=F1_P5 grid_rows=" << grid_index << '/' << grid.size()
                      << " pct=" << std::fixed << std::setprecision(1) << 100.0 * fraction
                      << " elapsed_s=" << std::setprecision(1) << elapsed
                      << " eta_s=" << elapsed * (1.0 / fraction - 1.0) << std::defaultfloat << '\n';
            next_progress += 100;
        }
    }
    for (size_t i = 0; i < 2; ++i) {
        for (size_t j = 0; j < 2; ++j) {
            pairs << (i + 2) << ',' << (j + 2) << ',' << pair_counts_at_max[i][j] << '\n';
        }
    }
    probes.close();
    pairs.close();
    std::cout << "PHASE F1_P5_mu_residue_summation done elapsed_s="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count() << '\n';
}

void run_production(const fs::path& out, const fs::path& tau_weights_path) {
    fs::create_directories(out);
    run_true_integer_systems(out);
    auto weights = read_tau_weights(tau_weights_path, kFakeLimit);
    std::cout << "PHASE SPF start limit=" << kFakeLimit << " expected_bytes="
              << (static_cast<u64>(kFakeLimit) + 1) * sizeof(u32) << '\n';
    auto spf = make_spf(kFakeLimit);
    std::cout << "PHASE SPF done entries=" << spf.size() << " note=SPF_ready\n";
    run_t2(out, spf, weights);
    weights.clear();
    weights.shrink_to_fit();
    run_f1(out, spf);
    spf.clear();
    spf.shrink_to_fit();
    run_f1_p5(out);
}

}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") {
            if (make_grid(8).size() != 701 || make_grid(7).size() != 601) {
                throw std::runtime_error("registered grid size mismatch");
            }
            const long double k = kappa_value();
            if (!std::isfinite(k) || k <= 0.28L || k >= 0.29L) {
                throw std::runtime_error("kappa formula sanity check failed");
            }
            self_test_p5_small();
            std::cout << "SELF_TEST_PASS grids=701,601 kappa_formula=finite P5_small_pairs=PASS\n";
            return 0;
        }
        if (argc == 4 && std::string(argv[1]) == "trial-prefix") {
            write_t1_trial_prefix(argv[2], static_cast<u32>(std::stoul(argv[3])));
            return 0;
        }
        if (argc == 4 && std::string(argv[1]) == "f1-prefix") {
            write_f1_prefix(argv[2], static_cast<u32>(std::stoul(argv[3])));
            return 0;
        }
        if (argc == 4 && std::string(argv[1]) == "run") {
            run_production(argv[2], argv[3]);
            return 0;
        }
        std::cerr << "usage: integer_systems --self-test | trial-prefix OUTPUT.csv LIMIT | f1-prefix OUTPUT.csv LIMIT | run OUTPUT_DIR TAU_WEIGHTS.bin\n";
        return 2;
    } catch (const std::exception& error) {
        std::cerr << "ERROR " << error.what() << '\n';
        return 1;
    }
}
