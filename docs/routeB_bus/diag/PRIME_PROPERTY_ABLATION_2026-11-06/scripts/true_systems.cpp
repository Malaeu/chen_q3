// True integer systems for the prime-property ablation.
// Finite diagnostic only; no RH or asymptotic claim is encoded here.
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
#include <vector>

namespace {
constexpr uint32_t kMax = 100000000;
constexpr uint32_t kPlantMax = 10000000;
constexpr uint32_t kBlockSize = 1u << 20;
constexpr int kRandomStreams = 5;
constexpr int kStreamCount = 7;  // S0, five S4 seeds, S5
constexpr std::array<uint32_t, kRandomStreams> kSeeds{4401, 4402, 4403, 4404, 4405};
constexpr std::array<int64_t, 9> kExpectedMobius{1, -1, 1, 2, -23, -48, 212, 1037, 1928};
constexpr std::array<int64_t, 9> kExpectedLiouville{1, 0, -2, -14, -94, -288, -530, -842, -3884};

struct Kahan {
    long double sum = 0;
    long double correction = 0;
    void add(long double x) {
        const long double y = x - correction;
        const long double t = sum + y;
        correction = (t - sum) - y;
        sum = t;
    }
};

struct SplitMix64 {
    uint64_t state;
    explicit SplitMix64(uint64_t seed) : state(seed) {}
    uint64_t next() {
        uint64_t z = (state += 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        return z ^ (z >> 31);
    }
};

struct GridPoint {
    long double x;
    int decade;
    int exact_power;  // -1 except at exact powers of ten
};

struct SamplePoint {
    long double x;
    int decade;
};

struct SampleValue {
    long double x;
    long double ratio;
    int decade;
};

struct PlantPoint {
    long double x;
    long double w;
};

uint64_t pow10u(int exponent) {
    uint64_t value = 1;
    for (int i = 0; i < exponent; ++i) value *= 10;
    return value;
}

std::vector<uint32_t> make_primes(uint32_t limit) {
    std::vector<bool> composite(static_cast<size_t>(limit / 2) + 1, false);
    std::vector<uint32_t> primes;
    if (limit >= 2) primes.push_back(2);
    for (uint32_t p = 3; static_cast<uint64_t>(p) * p <= limit; p += 2) {
        if (!composite[p / 2]) {
            for (uint64_t n = static_cast<uint64_t>(p) * p; n <= limit; n += 2ULL * p) {
                composite[static_cast<size_t>(n / 2)] = true;
            }
        }
    }
    for (uint32_t n = 3; n <= limit; n += 2) {
        if (!composite[n / 2]) primes.push_back(n);
    }
    return primes;
}

// One byte per integer holds five independent sign bits. A set bit means f_s(p)=-1.
std::vector<uint8_t> make_random_prime_masks(
    uint32_t limit,
    const std::vector<uint32_t>& primes,
    const std::array<uint32_t, kRandomStreams>& seeds) {
    std::vector<uint8_t> masks(static_cast<size_t>(limit) + 1, 0);
    std::array<SplitMix64, kRandomStreams> rngs{
        SplitMix64(seeds[0]), SplitMix64(seeds[1]), SplitMix64(seeds[2]),
        SplitMix64(seeds[3]), SplitMix64(seeds[4])
    };
    for (uint32_t p : primes) {
        uint8_t mask = 0;
        for (int s = 0; s < kRandomStreams; ++s) {
            if ((rngs[s].next() & 1ULL) != 0) mask |= static_cast<uint8_t>(1u << s);
        }
        masks[p] = mask;
    }
    return masks;
}

struct Segment {
    uint32_t lo = 0;
    uint32_t hi = 0;
    std::vector<uint32_t> remaining;
    std::vector<int8_t> mobius;
    std::vector<int8_t> liouville;
    std::vector<uint8_t> random_negative_mask;
};

void fill_segment(
    uint32_t lo,
    uint32_t hi,
    const std::vector<uint32_t>& primes,
    const std::vector<uint8_t>& prime_masks,
    Segment& seg) {
    seg.lo = lo;
    seg.hi = hi;
    const size_t size = static_cast<size_t>(hi - lo) + 1;
    seg.remaining.resize(size);
    seg.mobius.assign(size, 1);
    seg.liouville.assign(size, 1);
    seg.random_negative_mask.assign(size, 0);
    for (size_t i = 0; i < size; ++i) seg.remaining[i] = lo + static_cast<uint32_t>(i);

    for (uint32_t p : primes) {
        if (static_cast<uint64_t>(p) * p > hi) break;
        const uint64_t first = ((static_cast<uint64_t>(lo) + p - 1) / p) * p;
        for (uint64_t n = first; n <= hi; n += p) {
            const size_t i = static_cast<size_t>(n - lo);
            uint32_t exponent = 0;
            while (seg.remaining[i] % p == 0) {
                seg.remaining[i] /= p;
                ++exponent;
            }
            if (exponent == 0) continue;
            if (exponent > 1) {
                seg.mobius[i] = 0;
            } else if (seg.mobius[i] != 0) {
                seg.mobius[i] = static_cast<int8_t>(-seg.mobius[i]);
                seg.random_negative_mask[i] ^= prime_masks[p];
            }
            if ((exponent & 1u) != 0) seg.liouville[i] = static_cast<int8_t>(-seg.liouville[i]);
        }
    }

    for (size_t i = 0; i < size; ++i) {
        const uint32_t residual = seg.remaining[i];
        if (residual > 1) {
            seg.mobius[i] = static_cast<int8_t>(-seg.mobius[i]);
            seg.liouville[i] = static_cast<int8_t>(-seg.liouville[i]);
            seg.random_negative_mask[i] ^= prime_masks[residual];
        }
    }
}

int8_t random_value(const Segment& seg, size_t i, int seed_index) {
    if (seg.mobius[i] == 0) return 0;
    const bool negative = (seg.random_negative_mask[i] & (1u << seed_index)) != 0;
    return negative ? -1 : 1;
}

std::vector<GridPoint> make_grid(int max_decade) {
    std::vector<GridPoint> grid;
    for (int decade = 1; decade < max_decade; ++decade) {
        const long double base = static_cast<long double>(pow10u(decade));
        const long double log10 = std::log(10.0L);
        for (int j = 0; j < 100; ++j) {
            const long double x = (j == 0)
                ? base
                : std::exp(std::log(base) + (static_cast<long double>(j) / 100.0L) * log10);
            grid.push_back({x, decade, j == 0 ? decade : -1});
        }
    }
    grid.push_back({static_cast<long double>(pow10u(max_decade)), max_decade, max_decade});
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
            samples.push_back({std::exp(base_log + offset * log10), decade});
        }
    }
    return samples;
}

long double cosine_primitive(long double a, long double b, long double x) {
    const long double lx = std::log(x);
    const long double phase = b * lx;
    return std::pow(x, a) * (a * std::cos(phase) + b * std::sin(phase)) / (a * a + b * b);
}

long double h_primitive(long double x) {
    return cosine_primitive(-0.2L, 7.0L, x) + 1.0L / x;
}

long double p2_primitive(long double x) {
    const long double plain = std::pow(x, 0.6L) / 0.6L;
    const long double cos14 = cosine_primitive(0.6L, 14.0L, x);
    const long double cos7 = cosine_primitive(-0.2L, 7.0L, x);
    return 0.0025L * (0.5L * plain + 0.5L * cos14 - 2.0L * cos7 - 1.0L / x);
}

long double p2_integral(long double x) {
    return p2_primitive(x) - p2_primitive(1.0L);
}

long double planted_term(long double x) {
    return 0.05L * (std::pow(x, 0.8L) * std::cos(7.0L * std::log(x)) - 1.0L);
}

long double simpson(long double (*f)(long double), long double a, long double b, int intervals) {
    if (intervals % 2 != 0) throw std::runtime_error("Simpson interval count must be even");
    const long double h = (b - a) / intervals;
    long double sum = f(a) + f(b);
    for (int i = 1; i < intervals; ++i) sum += (i % 2 ? 4.0L : 2.0L) * f(a + i * h);
    return sum * h / 3.0L;
}

long double p2_integrand(long double x) {
    const long double p = planted_term(x);
    return (p * p) / (x * x);
}

long double cross_integrand_17(long double x) {
    return 2.0L * 17.0L * planted_term(x) / (x * x);
}

long double quantile(std::vector<long double> values, long double p) {
    if (values.empty()) return std::numeric_limits<long double>::quiet_NaN();
    std::sort(values.begin(), values.end());
    const long double position = p * static_cast<long double>(values.size() - 1);
    const size_t lower = static_cast<size_t>(std::floor(position));
    const size_t upper = static_cast<size_t>(std::ceil(position));
    const long double weight = position - lower;
    return values[lower] * (1.0L - weight) + values[upper] * weight;
}

long double ols_slope(const std::vector<PlantPoint>& points, long double lo, long double hi) {
    Kahan sx, sy;
    size_t count = 0;
    for (const auto& point : points) {
        if (point.x < lo || point.x > hi || point.w <= 0) continue;
        sx.add(std::log(point.x));
        sy.add(std::log(point.w));
        ++count;
    }
    if (count < 2) return std::numeric_limits<long double>::quiet_NaN();
    const long double mx = sx.sum / count;
    const long double my = sy.sum / count;
    Kahan numerator, denominator;
    for (const auto& point : points) {
        if (point.x < lo || point.x > hi || point.w <= 0) continue;
        const long double dx = std::log(point.x) - mx;
        numerator.add(dx * (std::log(point.w) - my));
        denominator.add(dx * dx);
    }
    return numerator.sum / denominator.sum;
}

bool near(long double a, long double b, long double absolute_tolerance) {
    return std::fabs(a - b) <= absolute_tolerance;
}

struct BruteTriple {
    int8_t mobius;
    int8_t liouville;
    std::array<int8_t, kRandomStreams> random;
};

BruteTriple brute_values(uint32_t n, const std::vector<uint8_t>& masks) {
    uint32_t remaining = n;
    uint32_t omega = 0;
    bool squarefree = true;
    uint8_t negative_mask = 0;
    for (uint32_t p = 2; static_cast<uint64_t>(p) * p <= remaining; ++p) {
        if (remaining % p != 0) continue;
        uint32_t exponent = 0;
        do {
            remaining /= p;
            ++exponent;
        } while (remaining % p == 0);
        omega += exponent;
        if (exponent > 1) squarefree = false;
        negative_mask ^= masks[p];
    }
    if (remaining > 1) {
        ++omega;
        negative_mask ^= masks[remaining];
    }
    BruteTriple out;
    out.mobius = squarefree ? ((omega & 1u) ? -1 : 1) : 0;
    out.liouville = (omega & 1u) ? -1 : 1;
    for (int s = 0; s < kRandomStreams; ++s) {
        if (!squarefree) out.random[s] = 0;
        else out.random[s] = (negative_mask & (1u << s)) ? -1 : 1;
    }
    return out;
}

void run_self_tests() {
    constexpr uint32_t test_limit = 50000;
    constexpr uint32_t test_block_size = 4096;
    const auto primes = make_primes(test_limit);
    const auto masks = make_random_prime_masks(test_limit, primes, kSeeds);
    Segment seg;
    std::vector<int8_t> checked_mu(static_cast<size_t>(test_limit) + 1, 0);
    uint32_t next = 1;
    uint64_t tested = 0;
    while (next <= test_limit) {
        const uint32_t hi = std::min<uint32_t>(test_limit, next + test_block_size - 1);
        fill_segment(next, hi, primes, masks, seg);
        for (uint32_t n = next; n <= hi; ++n) {
            const size_t i = static_cast<size_t>(n - next);
            const auto brute = brute_values(n, masks);
            if (seg.mobius[i] != brute.mobius || seg.liouville[i] != brute.liouville) {
                throw std::runtime_error("small brute Mobius/Liouville mismatch at n=" + std::to_string(n));
            }
            checked_mu[n] = seg.mobius[i];
            for (int s = 0; s < kRandomStreams; ++s) {
                if (random_value(seg, i, s) != brute.random[s]) {
                    throw std::runtime_error("small brute random-sign mismatch at n=" + std::to_string(n));
                }
            }
            ++tested;
        }
        next = hi + 1;
    }

    Kahan exact_w, direct_w;
    int64_t exact_prefix = 0;
    int64_t brute_prefix = 0;
    for (uint32_t n = 1; n < 2000; ++n) {
        exact_prefix += checked_mu[n];
        brute_prefix += brute_values(n, masks).mobius;
        exact_w.add(static_cast<long double>(exact_prefix) * exact_prefix /
                    (static_cast<long double>(n) * (n + 1)));
        direct_w.add(static_cast<long double>(brute_prefix) * brute_prefix /
                     (static_cast<long double>(n) * (n + 1)));
    }
    if (!near(exact_w.sum, direct_w.sum, 1.0e-15L)) {
        throw std::runtime_error("small exact-step W accumulation mismatch");
    }

    const long double cross_exact = 0.1L * 17.0L * (h_primitive(2.0L) - h_primitive(1.0L));
    const long double cross_quad = simpson(cross_integrand_17, 1.0L, 2.0L, 20000);
    const long double p2_exact = p2_integral(2.0L);
    const long double p2_quad = simpson(p2_integrand, 1.0L, 2.0L, 20000);
    if (!near(cross_exact, cross_quad, 2.0e-13L) || !near(p2_exact, p2_quad, 2.0e-13L)) {
        throw std::runtime_error("J4 analytic integration disagrees with converged Simpson quadrature");
    }
    if (!near(planted_term(1.0L), 0.0L, 1.0e-18L)) {
        throw std::runtime_error("J4 planted term is not recentered at x=1");
    }

    const auto grid = make_grid(8);
    const auto samples = make_samples(8);
    if (grid.size() != 701 || samples.size() != 8000 ||
        grid.front().x != 10.0L || grid.back().x != 100000000.0L ||
        grid.back().exact_power != 8) {
        throw std::runtime_error("registered grid or sample count mismatch");
    }

    std::cout << "SELF_TEST_PASS brute_n=" << tested
              << " checks=Mobius,Liouville,S4_5_seeds,exact_step_W,J4_analytic_vs_Simpson,grid"
              << " cross_abs_error=" << std::setprecision(8) << static_cast<double>(std::fabs(cross_exact - cross_quad))
              << " p2_abs_error=" << static_cast<double>(std::fabs(p2_exact - p2_quad))
              << std::endl;
}

std::string stream_name(int stream) {
    if (stream == 0) return "S0";
    if (stream == 6) return "S5";
    return "S4_seed" + std::to_string(kSeeds[stream - 1]);
}

std::string csv_number(long double value) {
    std::ostringstream out;
    out << std::setprecision(21) << value;
    return out.str();
}

void write_decade_csv(
    const std::filesystem::path& output_dir,
    int stream,
    int max_decade,
    const std::array<std::vector<SampleValue>, kStreamCount>& sample_values,
    const std::array<std::vector<uint64_t>, kStreamCount>& sign_changes,
    const std::array<std::vector<long double>, kStreamCount>& power_w,
    const std::array<std::vector<long double>, kStreamCount>& w_min,
    const std::array<std::vector<long double>, kStreamCount>& w_max) {
    const std::string name = stream_name(stream);
    std::ofstream out(output_dir / (name + "_decades.csv"));
    out << "decade,x_lo,x_hi,sample_count,ratio_mean,ratio_variance,q05,q25,q50,q75,q95,"
           "sign_changes,w_start,w_end,w_grid_min,w_grid_max\n";
    out << std::setprecision(21);
    for (int decade = 0; decade <= max_decade; ++decade) {
        std::vector<long double> ratios;
        Kahan sum;
        for (const auto& sample : sample_values[stream]) {
            if (sample.decade == decade) {
                ratios.push_back(sample.ratio);
                sum.add(sample.ratio);
            }
        }
        const size_t count = ratios.size();
        long double mean = std::numeric_limits<long double>::quiet_NaN();
        long double variance = std::numeric_limits<long double>::quiet_NaN();
        if (count > 0) {
            mean = sum.sum / count;
            Kahan variance_sum;
            for (long double value : ratios) {
                const long double delta = value - mean;
                variance_sum.add(delta * delta);
            }
            variance = variance_sum.sum / count;  // population variance
        }
        const long double x_lo = static_cast<long double>(pow10u(decade));
        const long double x_hi = decade < max_decade
            ? static_cast<long double>(pow10u(decade + 1))
            : x_lo;
        out << decade << ',' << x_lo << ',' << x_hi << ',' << count << ',';
        if (count == 0) out << "NA,NA,NA,NA,NA,NA,NA";
        else out << mean << ',' << variance << ','
                 << quantile(ratios, 0.05L) << ',' << quantile(ratios, 0.25L) << ','
                 << quantile(ratios, 0.50L) << ',' << quantile(ratios, 0.75L) << ','
                 << quantile(ratios, 0.95L);
        out << ',' << sign_changes[stream][decade] << ',';
        if (decade >= 1 && decade <= max_decade &&
            std::isfinite(power_w[stream][decade])) out << power_w[stream][decade];
        else out << "NA";
        out << ',';
        if (decade < max_decade &&
            std::isfinite(power_w[stream][decade + 1])) out << power_w[stream][decade + 1];
        else out << "NA";
        out << ',';
        if (decade < static_cast<int>(w_min[stream].size()) &&
            std::isfinite(w_min[stream][decade])) out << w_min[stream][decade];
        else out << "NA";
        out << ',';
        if (decade < static_cast<int>(w_max[stream].size()) &&
            std::isfinite(w_max[stream][decade])) out << w_max[stream][decade];
        else out << "NA";
        out << '\n';
    }
}

void write_checks(
    const std::filesystem::path& output_dir,
    const std::array<std::array<int64_t, 9>, kStreamCount>& power_m,
    const std::vector<PlantPoint>& plant_points,
    const std::vector<uint32_t>& seeds) {
    std::ofstream out(output_dir / "true_systems_checks.json");
    out << std::setprecision(21);
    const long double slope = ols_slope(plant_points, 100000.0L, 10000000.0L);
    const bool j4_pass = std::isfinite(slope) && slope >= 0.4L;
    bool j1_pass = true, j2_pass = true;
    for (int k = 0; k <= 8; ++k) {
        if (power_m[0][k] != kExpectedMobius[k]) j1_pass = false;
        if (power_m[6][k] != kExpectedLiouville[k]) j2_pass = false;
    }
    out << "{\n"
        << "  \"classification\": \"FINITE_DIAGNOSTIC_NOT_RH\",\n"
        << "  \"J1\": {\n"
        << "    \"status\": \"" << (j1_pass ? "PASS" : "FAIL") << "\",\n"
        << "    \"source\": \"OEIS A084237, values pinned in PREREGISTRATION.json\",\n"
        << "    \"max_x\": " << kMax << ",\n"
        << "    \"expected_M_10k\": [";
    for (int k = 0; k <= 8; ++k) out << (k ? "," : "") << kExpectedMobius[k];
    out << "],\n    \"observed_M_10k\": [";
    for (int k = 0; k <= 8; ++k) out << (k ? "," : "") << power_m[0][k];
    out << "]\n  },\n"
        << "  \"J2\": {\n"
        << "    \"status\": \"" << (j2_pass ? "PASS" : "FAIL") << "\",\n"
        << "    \"source\": \"OEIS A090410, values pinned in PREREGISTRATION.json\",\n"
        << "    \"max_x\": " << kMax << ",\n"
        << "    \"expected_L_10k\": [";
    for (int k = 0; k <= 8; ++k) out << (k ? "," : "") << kExpectedLiouville[k];
    out << "],\n    \"observed_L_10k\": [";
    for (int k = 0; k <= 8; ++k) out << (k ? "," : "") << power_m[6][k];
    out << "],\n    \"first_positive_906150258\": \"outside requested range; not run\"\n  },\n"
        << "  \"J4\": {\n"
        << "    \"status\": \"" << (j4_pass ? "PASS" : "FAIL") << "\",\n"
        << "    \"plant\": \"P(x)=0.05*(x^0.8*cos(7*log(x))-1)\",\n"
        << "    \"analytic_prefix\": \"P(x) is the integral from 1 of the registered derivative; exact analytic P^2 and M0 cross integrals per integer step\",\n"
        << "    \"plant_limit\": " << kPlantMax << ",\n"
        << "    \"ols_range\": [100000,10000000],\n"
        << "    \"plant_grid_points\": " << plant_points.size() << ",\n"
        << "    \"ols_points\": 201,\n"
        << "    \"ols_logW_vs_logX_slope\": " << slope << ",\n"
        << "    \"required_slope\": 0.4,\n"
        << "    \"expected_leading_envelope\": \"0.6-1/log(X), about 0.513 to 0.538 on the tested endpoints\"\n  },\n"
        << "  \"full_limits\": {\"S0\": " << kMax << ", \"S4_each_seed\": " << kMax
        << ", \"S5\": " << kMax << "},\n"
        << "  \"S4_seeds\": [";
    for (int i = 0; i < kRandomStreams; ++i) out << (i ? "," : "") << seeds[i];
    out << "],\n"
        << "  \"sampling\": {\"grid_points\": " << make_grid(8).size()
        << ", \"samples_per_decade\": 1000, \"sample_count\": " << make_samples(8).size()
        << ", \"sample_statistic\": \"population variance; linearly interpolated quantiles (type 7)\"},\n"
        << "  \"numeric_status\": \"long-double floating-point diagnostic; not an interval certificate\",\n"
        << "  \"truncations\": [\"Liouville first positive at 906150258 not run; above registered maximum\", "
        << "\"J4 planted series ends at 10000000, the full registered slope-check endpoint; baseline S0 continues to 100000000\"]\n"
        << "}\n";
    if (!j1_pass || !j2_pass || !j4_pass) {
        throw std::runtime_error("one or more production judges failed; see true_systems_checks.json");
    }
}

void run_production(const std::filesystem::path& output_dir) {
    std::filesystem::create_directories(output_dir);
    const auto run_start = std::chrono::steady_clock::now();
    std::cout << "PHASE prime_sieve start limit=" << kMax << std::endl;
    const auto primes = make_primes(kMax);
    if (primes.size() != 5761455 || primes.front() != 2 || primes.back() != 99999989) {
        throw std::runtime_error("prime sieve census failed");
    }
    const auto prime_masks = make_random_prime_masks(kMax, primes, kSeeds);
    std::cout << "PHASE prime_sieve done prime_count=" << primes.size()
              << " elapsed_s=" << std::setprecision(6)
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - run_start).count()
              << std::endl;

    const auto grid = make_grid(8);
    const auto samples = make_samples(8);
    std::array<std::ofstream, kStreamCount> grid_files;
    std::array<std::ofstream, kStreamCount> sample_files;
    std::array<std::vector<SampleValue>, kStreamCount> sample_values;
    std::array<std::vector<uint64_t>, kStreamCount> sign_changes;
    std::array<std::vector<long double>, kStreamCount> power_w;
    std::array<std::vector<long double>, kStreamCount> w_min;
    std::array<std::vector<long double>, kStreamCount> w_max;
    std::array<std::array<int64_t, 9>, kStreamCount> power_m{};
    std::array<int64_t, kStreamCount> prefix{};
    std::array<Kahan, kStreamCount> integral;
    std::array<int, kStreamCount> last_nonzero_sign{};
    for (int s = 0; s < kStreamCount; ++s) {
        const std::string name = stream_name(s);
        grid_files[s].open(output_dir / (name + ".csv"));
        sample_files[s].open(output_dir / (name + "_samples.csv"));
        if (!grid_files[s] || !sample_files[s]) throw std::runtime_error("cannot open CSV output for " + name);
        grid_files[s] << "X,M,W\n" << std::setprecision(21);
        sample_files[s] << "x,ratio\n" << std::setprecision(21);
        sample_values[s].reserve(samples.size());
        sign_changes[s].assign(9, 0);
        power_w[s].assign(9, std::numeric_limits<long double>::quiet_NaN());
        w_min[s].assign(9, std::numeric_limits<long double>::infinity());
        w_max[s].assign(9, -std::numeric_limits<long double>::infinity());
    }

    std::ofstream planted_file(output_dir / "S0_planted.csv");
    if (!planted_file) throw std::runtime_error("cannot open S0_planted.csv");
    planted_file << "X,M,W\n" << std::setprecision(21);
    std::vector<PlantPoint> plant_points;
    size_t grid_index = 0;
    size_t sample_index = 0;
    uint32_t decade_boundary = 10;
    int current_decade = 0;
    uint32_t next_progress = 5000000;
    Segment segment;
    segment.remaining.reserve(kBlockSize);
    segment.mobius.reserve(kBlockSize);
    segment.liouville.reserve(kBlockSize);
    segment.random_negative_mask.reserve(kBlockSize);
    long double plant_h_current = h_primitive(1.0L);
    Kahan plant_cross_integral;
    const auto loop_start = std::chrono::steady_clock::now();
    std::cout << "PHASE segmented_stream start systems=S0,S4x5,S5 max=" << kMax
              << " block=" << kBlockSize << std::endl;

    for (uint32_t block_lo = 1; block_lo <= kMax;) {
        const uint32_t block_hi = std::min<uint32_t>(kMax, block_lo + kBlockSize - 1);
        fill_segment(block_lo, block_hi, primes, prime_masks, segment);
        for (uint32_t n = block_lo; n <= block_hi; ++n) {
            const size_t i = static_cast<size_t>(n - block_lo);
            prefix[0] += segment.mobius[i];
            for (int seed = 0; seed < kRandomStreams; ++seed) {
                prefix[seed + 1] += random_value(segment, i, seed);
            }
            prefix[6] += segment.liouville[i];
            if (n == 1) {
                for (int s = 0; s < kStreamCount; ++s) power_m[s][0] = prefix[s];
            }

            while (decade_boundary <= n && current_decade < 8) {
                decade_boundary *= 10;
                ++current_decade;
            }
            for (int s = 0; s < kStreamCount; ++s) {
                if (prefix[s] != 0) {
                    const int sign = prefix[s] > 0 ? 1 : -1;
                    if (last_nonzero_sign[s] != 0 && sign != last_nonzero_sign[s]) {
                        ++sign_changes[s][current_decade];
                    }
                    last_nonzero_sign[s] = sign;
                }
            }

            while (sample_index < samples.size() && samples[sample_index].x < static_cast<long double>(n) + 1.0L) {
                if (samples[sample_index].x < static_cast<long double>(n)) {
                    throw std::runtime_error("sample grid passed before corresponding integer prefix");
                }
                for (int s = 0; s < kStreamCount; ++s) {
                    const long double ratio = static_cast<long double>(prefix[s]) / std::sqrt(samples[sample_index].x);
                    sample_values[s].push_back({samples[sample_index].x, ratio, samples[sample_index].decade});
                    sample_files[s] << samples[sample_index].x << ',' << ratio << '\n';
                }
                ++sample_index;
            }

            while (grid_index < grid.size() && grid[grid_index].x < static_cast<long double>(n) + 1.0L) {
                const GridPoint& point = grid[grid_index];
                if (point.x < static_cast<long double>(n)) {
                    throw std::runtime_error("log grid passed before corresponding integer prefix");
                }
                for (int s = 0; s < kStreamCount; ++s) {
                    const long double m = static_cast<long double>(prefix[s]);
                    const long double partial = (point.x - n) / (static_cast<long double>(n) * point.x);
                    const long double numerator = integral[s].sum + m * m * partial;
                    const long double w = numerator / std::log(point.x);
                    if (!std::isfinite(w) || w < 0) throw std::runtime_error("nonfinite or negative W at X=" + csv_number(point.x));
                    grid_files[s] << point.x << ',' << prefix[s] << ',' << w << '\n';
                    if (point.exact_power >= 0) power_m[s][point.exact_power] = prefix[s];
                    if (point.exact_power >= 0) power_w[s][point.exact_power] = w;
                    if (point.decade >= 0 && point.decade <= 8) {
                        w_min[s][point.decade] = std::min(w_min[s][point.decade], w);
                        w_max[s][point.decade] = std::max(w_max[s][point.decade], w);
                    }
                    if (s == 0 && point.x <= static_cast<long double>(kPlantMax)) {
                        const long double p = planted_term(point.x);
                        const long double h_at_x = h_primitive(point.x);
                        const long double plant_partial_cross =
                            0.1L * m * (h_at_x - plant_h_current);
                        const long double planted_integral =
                            numerator + plant_cross_integral.sum + plant_partial_cross + p2_integral(point.x);
                        const long double planted_w = planted_integral / std::log(point.x);
                        const long double planted_m = m + p;
                        if (!std::isfinite(planted_w) || planted_w <= 0) {
                            throw std::runtime_error("invalid J4 planted W at X=" + csv_number(point.x));
                        }
                        planted_file << point.x << ',' << planted_m << ',' << planted_w << '\n';
                        plant_points.push_back({point.x, planted_w});
                    }
                }
                ++grid_index;
            }

            if (n < kMax) {
                const long double denominator = static_cast<long double>(n) * (n + 1.0L);
                for (int s = 0; s < kStreamCount; ++s) {
                    const long double m = static_cast<long double>(prefix[s]);
                    integral[s].add(m * m / denominator);
                }
            }

            if (n < kPlantMax) {
                const long double h_next = h_primitive(static_cast<long double>(n) + 1.0L);
                plant_cross_integral.add(
                    0.1L * static_cast<long double>(prefix[0]) * (h_next - plant_h_current));
                plant_h_current = h_next;
            }

            if (n >= next_progress) {
                const double elapsed = std::chrono::duration<double>(
                    std::chrono::steady_clock::now() - loop_start).count();
                const double fraction = static_cast<double>(n) / kMax;
                const double eta = elapsed * (1.0 / fraction - 1.0);
                std::cout << "PROGRESS systems=S0,S4x5,S5 n=" << n << "/" << kMax
                          << " pct=" << std::fixed << std::setprecision(1) << 100.0 * fraction
                          << " elapsed_s=" << std::setprecision(1) << elapsed
                          << " eta_s=" << eta << std::defaultfloat << std::endl;
                next_progress += 5000000;
            }
        }
        block_lo = block_hi + 1;
    }
    if (sample_index != samples.size() || grid_index != grid.size()) {
        throw std::runtime_error("not all registered samples/grid points were emitted");
    }
    for (int s = 0; s < kStreamCount; ++s) {
        grid_files[s].close();
        sample_files[s].close();
        write_decade_csv(output_dir, s, 8, sample_values, sign_changes, power_w, w_min, w_max);
    }
    planted_file.close();
    write_checks(output_dir, power_m, plant_points, std::vector<uint32_t>(kSeeds.begin(), kSeeds.end()));

    const long double expected_low = 0.6L - 1.0L / std::log(100000.0L);
    const long double expected_high = 0.6L - 1.0L / std::log(10000000.0L);
    const long double slope = ols_slope(plant_points, 100000.0L, 10000000.0L);
    std::cout << "JUDGES J1=" << (power_m[0] == std::array<int64_t, 9>{1,-1,1,2,-23,-48,212,1037,1928} ? "PASS" : "FAIL")
              << " J2=" << (power_m[6] == std::array<int64_t, 9>{1,0,-2,-14,-94,-288,-530,-842,-3884} ? "PASS" : "FAIL")
              << " J4=" << (slope >= 0.4L ? "PASS" : "FAIL")
              << " slope=" << std::setprecision(12) << slope
              << " expected_envelope=[" << expected_low << "," << expected_high << "]"
              << std::endl;
    std::cout << "PHASE segmented_stream done elapsed_s="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - loop_start).count()
              << " total_s="
              << std::chrono::duration<double>(std::chrono::steady_clock::now() - run_start).count()
              << std::endl;
}

}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--self-test") {
            run_self_tests();
            return 0;
        }
        if (argc == 3 && std::string(argv[1]) == "run") {
            run_production(argv[2]);
            return 0;
        }
        std::cerr << "usage: true_systems --self-test | true_systems run OUTPUT_DIR\n";
        return 2;
    } catch (const std::exception& error) {
        std::cerr << "ERROR " << error.what() << std::endl;
        return 1;
    }
}
