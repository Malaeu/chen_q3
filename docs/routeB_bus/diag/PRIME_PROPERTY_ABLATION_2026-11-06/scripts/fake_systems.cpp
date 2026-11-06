#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using Clock = std::chrono::steady_clock;

struct Event {
    double x;
    int32_t delta_mu;
    uint32_t multiplicity;
};
static_assert(sizeof(Event) == 16, "event layout should remain compact");

struct Kahan {
    long double sum = 0.0L;
    long double correction = 0.0L;
    void add(long double value) {
        const long double y = value - correction;
        const long double next = sum + y;
        correction = (next - sum) - y;
        sum = next;
    }
};

uint64_t parse_u64(const char* value, const char* name) {
    char* end = nullptr;
    const unsigned long long result = std::strtoull(value, &end, 10);
    if (!end || *end != '\0') throw std::runtime_error(std::string("bad ") + name);
    return static_cast<uint64_t>(result);
}

double unit53(std::mt19937_64& rng) {
    return static_cast<double>(rng() >> 11) * 0x1.0p-53;
}

std::vector<uint32_t> primes_up_to(uint32_t n) {
    std::vector<uint8_t> composite(static_cast<size_t>(n) + 1, 0);
    composite[0] = 1;
    if (n >= 1) composite[1] = 1;
    for (uint64_t p = 2; p * p <= n; ++p) {
        if (!composite[static_cast<size_t>(p)]) {
            for (uint64_t k = p * p; k <= n; k += p)
                composite[static_cast<size_t>(k)] = 1;
        }
    }
    std::vector<uint32_t> primes;
    for (uint32_t p = 2; p <= n; ++p)
        if (!composite[p]) primes.push_back(p);
    return primes;
}

std::vector<double> make_generators(const std::string& system, uint64_t seed,
                                    uint32_t limit, uint32_t y,
                                    uint64_t* prime_scan_limit = nullptr) {
    std::vector<double> generators;
    if (system == "S1") {
        std::mt19937_64 rng(seed);
        const auto start = Clock::now();
        for (uint32_t m = 3; m <= limit; ++m) {
            if (unit53(rng) < 1.0 / std::log(static_cast<double>(m)))
                generators.push_back(static_cast<double>(m));
            if (m % 1000000 == 0) {
                const double elapsed = std::chrono::duration<double>(Clock::now() - start).count();
                const double fraction = static_cast<double>(m) / static_cast<double>(limit);
                const double eta = elapsed * (1.0 - fraction) / std::max(fraction, 1e-9);
                std::cerr << "[S1 generators] " << m << "/" << limit
                          << " elapsed=" << std::fixed << std::setprecision(1) << elapsed
                          << "s ETA~" << eta << "s\n";
            }
        }
    } else if (system == "S2") {
        if (y < 2 || y >= limit) throw std::runtime_error("S2 y must satisfy 2 <= y < limit");
        const std::vector<uint32_t> small_primes = primes_up_to(y);
        for (uint32_t p : small_primes) generators.push_back(static_cast<double>(p));
        std::mt19937_64 rng(seed);
        const auto start = Clock::now();
        for (uint32_t m = y + 1; m <= limit; ++m) {
            if (unit53(rng) < 1.0 / std::log(static_cast<double>(m)))
                generators.push_back(static_cast<double>(m));
            if (m % 1000000 == 0) {
                const double elapsed = std::chrono::duration<double>(Clock::now() - start).count();
                const double fraction = static_cast<double>(m - y) / static_cast<double>(limit - y);
                const double eta = elapsed * (1.0 - fraction) / std::max(fraction, 1e-9);
                std::cerr << "[S2 generators y=" << y << "] " << m << "/" << limit
                          << " elapsed=" << std::fixed << std::setprecision(1) << elapsed
                          << "s ETA~" << eta << "s\n";
            }
        }
    } else if (system == "S3") {
        if (limit < 3) throw std::runtime_error("S3 limit must be at least 3");
        // For p > X, log(p) > log(X), so
        // q_p >= p*(1 - 0.1/log(p)) > p*(1 - 0.1/log(X)).
        // Thus ceil(X/(1 - 0.1/log(X)))+2 safely includes every p whose q_p <= X.
        const double x = static_cast<double>(limit);
        const uint64_t bound = static_cast<uint64_t>(
            std::ceil(x / (1.0 - 0.1 / std::log(x)))) + 2;
        if (bound > std::numeric_limits<uint32_t>::max())
            throw std::runtime_error("S3 prime scan bound exceeds uint32");
        if (prime_scan_limit) *prime_scan_limit = bound;
        const auto primes = primes_up_to(static_cast<uint32_t>(bound));
        std::mt19937_64 rng(seed);
        std::vector<std::pair<double, uint32_t>> perturbed;
        perturbed.reserve(primes.size());
        for (uint32_t p : primes) {
            const double a = 0.1 / std::log(static_cast<double>(p));
            const double epsilon = (2.0 * unit53(rng) - 1.0) * a;
            const double q = static_cast<double>(p) * (1.0 + epsilon);
            if (q <= x) perturbed.emplace_back(q, p);
        }
        std::sort(perturbed.begin(), perturbed.end(),
                  [](const auto& a, const auto& b) {
                      if (a.first != b.first) return a.first < b.first;
                      return a.second < b.second;
                  });
        generators.reserve(perturbed.size());
        for (const auto& item : perturbed) generators.push_back(item.first);
    } else {
        throw std::runtime_error("system must be S1, S2, or S3");
    }
    if (!std::is_sorted(generators.begin(), generators.end()))
        throw std::runtime_error("generator order is not increasing");
    for (double q : generators)
        if (!(q > 1.0) || !std::isfinite(q))
            throw std::runtime_error("generator must be finite and > 1");
    return generators;
}

void save_generators(const std::vector<double>& generators, const std::string& path) {
    std::ofstream out(path);
    if (!out) throw std::runtime_error("cannot open generator file: " + path);
    out << std::setprecision(17);
    for (double q : generators) out << q << '\n';
}

std::vector<double> load_generators(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open generator file: " + path);
    std::vector<double> generators;
    double q = 0.0;
    while (in >> q) generators.push_back(q);
    if (!std::is_sorted(generators.begin(), generators.end()))
        throw std::runtime_error("generator file must be sorted");
    return generators;
}

struct Enumeration {
    const std::vector<double>& generators;
    double limit;
    Enumeration(const std::vector<double>& g, double x) : generators(g), limit(x) {}
    std::vector<Event> events;
    uint64_t nodes = 0;
    uint64_t next_note = 1000000;
    double target_estimate;
    Clock::time_point start = Clock::now();

    void walk(double value, size_t first_allowed, bool has_last, int32_t mu) {
        events.push_back({value, mu, 1});
        ++nodes;
        if (nodes >= next_note) {
            const double elapsed = std::chrono::duration<double>(Clock::now() - start).count();
            if (static_cast<double>(nodes) > target_estimate * 0.8)
                target_estimate = static_cast<double>(nodes) * 1.5;
            const double eta = elapsed * std::max(0.0, target_estimate - nodes) /
                               static_cast<double>(nodes);
            std::cerr << "[enumerate] nodes=" << nodes << " total~"
                      << std::fixed << std::setprecision(0) << target_estimate
                      << " elapsed=" << std::setprecision(1) << elapsed
                      << "s ETA~" << eta << "s\n";
            next_note += 1000000;
        }
        const size_t begin = has_last ? first_allowed : 0;
        for (size_t j = begin; j < generators.size(); ++j) {
            const double next = value * generators[j];
            if (next > limit) break;
            int32_t next_mu;
            if (!has_last) next_mu = -1;
            else if (j == first_allowed) next_mu = 0;
            else next_mu = mu == 0 ? 0 : -mu;
            walk(next, j, true, next_mu);
        }
    }

    void run() {
        target_estimate = std::max(1.0, limit);
        walk(1.0, 0, false, 1);
    }
};

struct Grouped {
    std::vector<Event> events;
    uint64_t total_objects = 0;
    uint64_t distinct_products = 0;
};

Grouped sort_and_group(std::vector<Event>&& events) {
    std::sort(events.begin(), events.end(),
              [](const Event& a, const Event& b) { return a.x < b.x; });
    size_t write = 0;
    for (size_t i = 0; i < events.size();) {
        const double x = events[i].x;
        uint64_t count = 0;
        int64_t delta = 0;
        size_t j = i;
        while (j < events.size() && events[j].x == x) {
            count += events[j].multiplicity;
            delta += events[j].delta_mu;
            ++j;
        }
        if (count > std::numeric_limits<uint32_t>::max() ||
            delta < std::numeric_limits<int32_t>::min() ||
            delta > std::numeric_limits<int32_t>::max())
            throw std::runtime_error("coincident-product aggregate overflow");
        events[write++] = {x, static_cast<int32_t>(delta), static_cast<uint32_t>(count)};
        i = j;
    }
    events.resize(write);
    uint64_t total = 0;
    for (const Event& e : events) total += e.multiplicity;
    return {std::move(events), total, static_cast<uint64_t>(write)};
}

int decade_of(double x) {
    int d = 0;
    double threshold = 10.0;
    while (x >= threshold && d < 99) {
        ++d;
        threshold *= 10.0;
    }
    return d;
}

std::pair<int, bool> limit_decade(uint32_t limit) {
    uint64_t power = 1;
    int floor_decade = 0;
    while (power <= static_cast<uint64_t>(limit) / 10) {
        power *= 10;
        ++floor_decade;
    }
    return {floor_decade, power == limit};
}

std::vector<double> grid_points(uint32_t limit) {
    std::vector<double> xs;
    const double bound = static_cast<double>(limit);
    const int max_decade = limit_decade(limit).first;
    for (int d = 1; d <= max_decade; ++d) {
        for (int i = 0; i < 100; ++i) {
            const double x = std::pow(10.0, static_cast<double>(d) +
                                               static_cast<double>(i) / 100.0);
            if (x < bound) xs.push_back(x);
        }
    }
    if (xs.empty() || xs.back() != bound) xs.push_back(bound);
    return xs;
}

struct Sample {
    int decade;
    double x;
    int64_t m;
    long double ratio;
};

std::vector<Sample> sample_m(const std::vector<Event>& events, uint32_t limit) {
    std::vector<Sample> result;
    const int max_decade = limit_decade(limit).first;
    result.reserve(static_cast<size_t>(max_decade + 1) * 1000);
    size_t idx = 0;
    int64_t m = 0;
    for (int d = 0; d <= max_decade; ++d) {
        for (int i = 0; i < 1000; ++i) {
            const double x = std::pow(10.0, static_cast<double>(d) +
                                               (static_cast<double>(i) + 0.5) / 1000.0);
            if (x >= static_cast<double>(limit)) continue;
            while (idx < events.size() && events[idx].x <= x) {
                m += events[idx].delta_mu;
                ++idx;
            }
            result.push_back({d, x, m, static_cast<long double>(m) / std::sqrt(static_cast<long double>(x))});
        }
    }
    return result;
}

struct GridRow {
    double x;
    int64_t m;
    long double w;
    uint64_t n;
};

std::vector<GridRow> grid_metrics(const std::vector<Event>& events,
                                  const std::vector<double>& grid,
                                  uint64_t total_objects, uint32_t limit,
                                  std::vector<uint64_t>& sign_changes) {
    std::vector<GridRow> rows;
    rows.reserve(grid.size());
    const long double rho_hat = static_cast<long double>(total_objects) / limit;
    size_t idx = 0;
    int64_t m = 0;
    uint64_t n = 0;
    double last_t = 1.0;
    Kahan integral;
    int last_nonzero_sign = 0;
    for (double x : grid) {
        while (idx < events.size() && events[idx].x <= x) {
            const Event& e = events[idx];
            if (e.x > last_t && m != 0) {
                const long double mm = static_cast<long double>(m);
                integral.add(mm * mm * (1.0L / static_cast<long double>(last_t) -
                                        1.0L / static_cast<long double>(e.x)));
            }
            last_t = std::max(last_t, e.x);
            m += e.delta_mu;
            n += e.multiplicity;
            if (m != 0) {
                const int sign = m > 0 ? 1 : -1;
                if (last_nonzero_sign != 0 && sign != last_nonzero_sign) {
                    const int d = decade_of(e.x);
                    if (static_cast<size_t>(d) < sign_changes.size()) ++sign_changes[static_cast<size_t>(d)];
                }
                last_nonzero_sign = sign;
            }
            ++idx;
        }
        if (x > last_t && m != 0) {
            const long double mm = static_cast<long double>(m);
            integral.add(mm * mm * (1.0L / static_cast<long double>(last_t) -
                                    1.0L / static_cast<long double>(x)));
        }
        last_t = std::max(last_t, x);
        rows.push_back({x, m, integral.sum / std::log(static_cast<long double>(x)), n});
        (void)rho_hat;
    }
    return rows;
}

std::string json_escape(const std::string& s) {
    std::ostringstream out;
    for (unsigned char c : s) {
        if (c == '"' || c == '\\') out << '\\' << c;
        else if (c >= 0x20) out << c;
    }
    return out.str();
}

void write_outputs(const std::string& system, uint64_t seed, uint32_t y,
                   uint32_t limit, const std::string& prefix,
                   const std::vector<double>& generators,
                   Grouped grouped, uint64_t prime_scan_limit,
                   double elapsed_total) {
    const long double rho_hat = static_cast<long double>(grouped.total_objects) / limit;
    std::vector<double> grid = grid_points(limit);
    if (limit == 10000000 &&
        (grid.size() != 601 || grid.back() != static_cast<double>(limit) ||
         !std::is_sorted(grid.begin(), grid.end()) ||
         std::adjacent_find(grid.begin(), grid.end(), std::greater_equal<double>()) != grid.end()))
        throw std::runtime_error("production grid failed its 601-point monotonicity check");
    const auto [floor_decade, exact_power] = limit_decade(limit);
    const size_t sign_decades = static_cast<size_t>(floor_decade + 1);
    std::vector<uint64_t> sign_changes(sign_decades, 0);
    const auto rows = grid_metrics(grouped.events, grid, grouped.total_objects, limit, sign_changes);
    const auto samples = sample_m(grouped.events, limit);
    if (limit == 10000000 && samples.size() != 7000)
        throw std::runtime_error("production sample grid failed its 7000-point check");

    std::ofstream out(prefix + ".csv");
    if (!out) throw std::runtime_error("cannot open grid output");
    out << "X,M,W,N,N_over_x,count_error\n" << std::setprecision(17);
    for (const GridRow& r : rows) {
        const long double n_over_x = static_cast<long double>(r.n) / r.x;
        const long double count_error = static_cast<long double>(r.n) - rho_hat * r.x;
        out << r.x << ',' << r.m << ',' << std::setprecision(21) << r.w << ','
            << r.n << ',' << n_over_x << ',' << count_error << std::setprecision(17) << '\n';
    }

    std::ofstream sout(prefix + "_samples.csv");
    if (!sout) throw std::runtime_error("cannot open sample output");
    sout << "decade,x,M,ratio\n" << std::setprecision(17);
    for (const Sample& s : samples)
        sout << s.decade << ',' << s.x << ',' << s.m << ','
             << std::setprecision(21) << s.ratio << std::setprecision(17) << '\n';

    struct Moment {
        uint64_t n = 0;
        long double mean = 0.0L;
        long double m2 = 0.0L;
        void add(long double x) {
            ++n;
            const long double delta = x - mean;
            mean += delta / static_cast<long double>(n);
            m2 += delta * (x - mean);
        }
    };
    const size_t decade_count = static_cast<size_t>(floor_decade + (exact_power ? 0 : 1));
    std::vector<Moment> moments(decade_count);
    for (const Sample& sample : samples)
        moments[static_cast<size_t>(sample.decade)].add(sample.ratio);
    std::ofstream dout(prefix + "_decades.csv");
    if (!dout) throw std::runtime_error("cannot open decade output");
    dout << "decade,x_lo,x_hi,sample_count,mean_ratio,variance_ratio,sign_changes,sign_changes_at_limit\n"
         << std::setprecision(21);
    for (size_t d = 0; d < decade_count; ++d) {
        const double lo = std::pow(10.0, static_cast<double>(d));
        const double hi = std::pow(10.0, static_cast<double>(d + 1));
        const long double var = moments[d].n ? moments[d].m2 / moments[d].n : 0.0L;
        const uint64_t endpoint_changes =
            d + 1 == decade_count && decade_count < sign_changes.size()
                ? sign_changes[decade_count] : 0;
        dout << d << ',' << lo << ',' << std::min(hi, static_cast<double>(limit)) << ','
             << moments[d].n << ',' << moments[d].mean << ',' << var << ','
             << sign_changes[d] << ',' << endpoint_changes << '\n';
    }

    std::array<double, 8> power_density{};
    size_t density_idx = 0;
    uint64_t prefix_n = 0;
    for (int d = 1; d <= 7; ++d) {
        const double q = std::pow(10.0, static_cast<double>(d));
        while (density_idx < grouped.events.size() && grouped.events[density_idx].x <= q) {
            prefix_n += grouped.events[density_idx].multiplicity;
            ++density_idx;
        }
        power_density[static_cast<size_t>(d)] = static_cast<double>(prefix_n) / q;
    }

    uint64_t boundary_groups = 0;
    uint64_t boundary_objects = 0;
    double min_boundary_gap = std::numeric_limits<double>::infinity();
    const double edge = static_cast<double>(limit);
    const double ulp = std::nextafter(edge, std::numeric_limits<double>::infinity()) - edge;
    for (const Event& e : grouped.events) {
        const double gap = std::abs(e.x - edge);
        min_boundary_gap = std::min(min_boundary_gap, gap);
        if (gap <= 32.0 * ulp) {
            ++boundary_groups;
            boundary_objects += e.multiplicity;
        }
    }

    std::cout << std::setprecision(17)
              << "{\"system\":\"" << json_escape(system) << "\","
              << "\"seed\":" << seed << ",\"y\":" << y << ",\"limit\":" << limit
              << ",\"generator_count\":" << generators.size()
              << ",\"semigroup_objects\":" << grouped.total_objects
              << ",\"distinct_products\":" << grouped.distinct_products
              << ",\"rho_hat_finite_only\":" << static_cast<double>(rho_hat)
              << ",\"power_density\":{";
    for (int d = 1; d <= 7; ++d) {
        if (d > 1) std::cout << ',';
        uint64_t q = 1;
        for (int k = 0; k < d; ++k) q *= 10;
        std::cout << '"' << q << "\":" << power_density[static_cast<size_t>(d)];
    }
    std::cout << "},\"adjacent_density_drift\":{";
    for (int d = 1; d <= 6; ++d) {
        if (d > 1) std::cout << ',';
        std::cout << '"' << d << "\":"
                  << (power_density[static_cast<size_t>(d + 1)] -
                      power_density[static_cast<size_t>(d)]);
    }
    std::cout << "},\"prime_scan_limit\":" << prime_scan_limit
              << ",\"boundary_ulps_at_limit\":" << ulp
              << ",\"boundary_groups_within_32_ulp\":" << boundary_groups
              << ",\"boundary_objects_within_32_ulp\":" << boundary_objects
              << ",\"minimum_product_gap_to_limit\":" << min_boundary_gap
              << ",\"wall_seconds\":" << elapsed_total << "}\n";
}

void run_system(const std::string& system, uint64_t seed, uint32_t y,
                uint32_t limit, const std::string& prefix) {
    uint64_t prime_scan_limit = 0;
    const auto all_start = Clock::now();
    const auto generators = make_generators(system, seed, limit, y, &prime_scan_limit);
    std::cerr << "[generators] system=" << system << " seed=" << seed
              << " count=" << generators.size() << '\n';
    Enumeration enumeration{generators, static_cast<double>(limit)};
    enumeration.run();
    const double enum_seconds = std::chrono::duration<double>(Clock::now() - all_start).count();
    std::cerr << "[sort] events=" << enumeration.events.size() << " ETA~"
              << std::fixed << std::setprecision(1) << enum_seconds * 0.35 << "s\n";
    auto grouped = sort_and_group(std::move(enumeration.events));
    std::cerr << "[write] distinct_products=" << grouped.distinct_products
              << " objects=" << grouped.total_objects << " ETA~"
              << std::fixed << std::setprecision(1) << enum_seconds * 0.15 << "s\n";
    const double total_seconds = std::chrono::duration<double>(Clock::now() - all_start).count();
    write_outputs(system, seed, y, limit, prefix, generators, std::move(grouped),
                  prime_scan_limit, total_seconds);
}

void usage() {
    std::cerr << "usage:\n"
              << "  fake_systems run S1|S2|S3 seed y limit output_prefix\n"
              << "  fake_systems generators S1|S2|S3 seed y limit output_path\n"
              << "  fake_systems enumerate limit generator_file output_prefix\n";
}

} // namespace

int main(int argc, char** argv) {
    try {
        if (argc < 2) { usage(); return 2; }
        const std::string mode = argv[1];
        if (mode == "run") {
            if (argc != 7) { usage(); return 2; }
            const std::string system = argv[2];
            const uint64_t seed = parse_u64(argv[3], "seed");
            const uint32_t y = static_cast<uint32_t>(parse_u64(argv[4], "y"));
            const uint32_t limit = static_cast<uint32_t>(parse_u64(argv[5], "limit"));
            run_system(system, seed, y, limit, argv[6]);
            return 0;
        }
        if (mode == "generators") {
            if (argc != 7) { usage(); return 2; }
            const std::string system = argv[2];
            const uint64_t seed = parse_u64(argv[3], "seed");
            const uint32_t y = static_cast<uint32_t>(parse_u64(argv[4], "y"));
            const uint32_t limit = static_cast<uint32_t>(parse_u64(argv[5], "limit"));
            uint64_t scan = 0;
            const auto generators = make_generators(system, seed, limit, y, &scan);
            save_generators(generators, argv[6]);
            std::cout << "{\"system\":\"" << system << "\",\"seed\":" << seed
                      << ",\"limit\":" << limit << ",\"generator_count\":"
                      << generators.size() << ",\"prime_scan_limit\":" << scan << "}\n";
            return 0;
        }
        if (mode == "enumerate") {
            if (argc != 5) { usage(); return 2; }
            const uint32_t limit = static_cast<uint32_t>(parse_u64(argv[2], "limit"));
            auto generators = load_generators(argv[3]);
            Enumeration enumeration{generators, static_cast<double>(limit)};
            enumeration.run();
            auto grouped = sort_and_group(std::move(enumeration.events));
            std::ofstream out(std::string(argv[4]) + ".groups.csv");
            if (!out) throw std::runtime_error("cannot open groups output");
            out << "x,N_delta,M_delta\n" << std::setprecision(17);
            for (const Event& e : grouped.events)
                out << e.x << ',' << e.multiplicity << ',' << e.delta_mu << '\n';
            std::cout << "{\"generator_count\":" << generators.size()
                      << ",\"objects\":" << grouped.total_objects
                      << ",\"distinct_products\":" << grouped.distinct_products << "}\n";
            return 0;
        }
        usage();
        return 2;
    } catch (const std::exception& e) {
        std::cerr << "ERROR: " << e.what() << '\n';
        return 3;
    }
}
