// Full Vasyunin Gram matrix, adapted to Apple clang without OpenMP.
// The formula and arithmetic order follow the pinned NB_RATE_THERMOMETER
// implementation; independent q rows and Gram lower-triangle rows use threads.
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <string>
#include <thread>
#include <vector>

int main(int argc, char** argv) {
    if (argc != 3) return 2;
    const int N = std::stoi(argv[1]);
    if (N < 2 || N > 5000) return 3;

    const long double pi = acosl(-1.L);
    const long double kap = logl(2.L * pi) -
        0.577215664901532860606512090082402431L;
    std::vector<std::vector<long double>> V(N + 1);
    for (int q = 1; q <= N; ++q) V[q].resize(q, 0.L);

    unsigned int hc = std::thread::hardware_concurrency();
    const unsigned int workers = std::max(1U, std::min(hc ? hc : 1U, 16U));
    std::atomic<int> next_q(2);
    std::atomic<int> completed_q(0);
    std::atomic<unsigned long long> q_work(0);
    const unsigned long long q_total =
        (static_cast<unsigned long long>(N) * (N + 1) * (2ULL * N + 1)) / 6 - 1;
    const auto q_start = std::chrono::steady_clock::now();

    auto build_q_rows = [&]() {
        for (;;) {
            const int q = next_q.fetch_add(1);
            if (q > N) break;
            const int half = (q - 1) / 2;
            std::vector<long double> cot(half + 1, 0.L);
            for (int j = 1; j <= half; ++j) cot[j] = 1.L / tanl(pi * j / q);
            for (int h = 1; 2 * h < q; ++h) {
                if (std::gcd(h, q) != 1) continue;
                long double sum = 0.L;
                int rem = h;
                for (int j = 1; j <= half; ++j) {
                    sum += (2.L * rem / q - 1.L) * cot[j];
                    rem += h;
                    if (rem >= q) rem -= q;
                }
                V[q][h] = sum;
                V[q][q - h] = -sum;
            }
            q_work.fetch_add(static_cast<unsigned long long>(q) * q);
            completed_q.fetch_add(1);
        }
    };
    std::vector<std::thread> threads;
    for (unsigned int i = 0; i < workers; ++i) threads.emplace_back(build_q_rows);
    int last_pct = -1;
    while (completed_q.load() < N - 1) {
        std::this_thread::sleep_for(std::chrono::seconds(1));
        const double frac = std::min(1.L, static_cast<long double>(q_work.load()) / q_total);
        const int pct = static_cast<int>(100 * frac);
        if (pct != last_pct) {
            const double sec = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - q_start).count();
            const int bars = static_cast<int>(30 * frac);
            std::cout << "\r[" << std::string(bars, '#') << std::string(30 - bars, '.')
                      << "] " << std::fixed << std::setprecision(1) << 100 * frac
                      << "% ETA " << (frac > 0 ? sec * (1 - frac) / frac : 0)
                      << "s cotangent rows" << std::flush;
            last_pct = pct;
        }
    }
    for (auto& thread : threads) thread.join();
    std::cout << "\r[##############################] 100.0% ETA 0s cotangent rows\n";

    auto Q = [&](int n, int m) {
        const int g = std::gcd(n, m), h = n / g, k = m / g;
        const long double v1 = k == 1 ? 0.L : V[k][h % k];
        const long double v2 = h == 1 ? 0.L : V[h][k % h];
        return (kap * (1.L / h + 1.L / k) / 2.L +
                (k - h) * logl(static_cast<long double>(h) / k) / (2.L * h * k) -
                pi * (v1 + v2) / (2.L * h * k)) / g;
    };

    std::vector<long double> q1(N + 1);
    for (int n = 1; n <= N; ++n) q1[n] = Q(n, 1);
    const int d = N - 1;
    std::vector<double> G(static_cast<std::size_t>(d) * d);
    std::atomic<int> next_n(2);
    std::atomic<int> completed_rows(0);
    std::atomic<unsigned long long> pairs_done(0);
    const unsigned long long pairs_total =
        static_cast<unsigned long long>(d) * (d + 1) / 2;
    const auto gram_start = std::chrono::steady_clock::now();
    auto build_gram_rows = [&]() {
        for (;;) {
            const int n = next_n.fetch_add(1);
            if (n > N) break;
            for (int m = 2; m <= n; ++m) {
                const double x = static_cast<double>(
                    Q(n, m) - q1[n] / m - q1[m] / n + kap / (static_cast<long double>(n) * m));
                G[static_cast<std::size_t>(n - 2) * d + m - 2] = x;
                G[static_cast<std::size_t>(m - 2) * d + n - 2] = x;
            }
            pairs_done.fetch_add(static_cast<unsigned long long>(n - 1));
            completed_rows.fetch_add(1);
        }
    };
    threads.clear();
    for (unsigned int i = 0; i < workers; ++i) threads.emplace_back(build_gram_rows);
    last_pct = -1;
    while (completed_rows.load() < N - 1) {
        std::this_thread::sleep_for(std::chrono::seconds(1));
        const double frac = std::min(1.L, static_cast<long double>(pairs_done.load()) / pairs_total);
        const int pct = static_cast<int>(100 * frac);
        if (pct != last_pct) {
            const double sec = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - gram_start).count();
            const int bars = static_cast<int>(30 * frac);
            std::cout << "\r[" << std::string(bars, '#') << std::string(30 - bars, '.')
                      << "] " << std::fixed << std::setprecision(1) << 100 * frac
                      << "% ETA " << (frac > 0 ? sec * (1 - frac) / frac : 0)
                      << "s full Gram" << std::flush;
            last_pct = pct;
        }
    }
    for (auto& thread : threads) thread.join();
    std::cout << "\r[##############################] 100.0% ETA 0s full Gram\n";

    std::ofstream f(argv[2], std::ios::binary);
    const std::uint32_t ud = static_cast<std::uint32_t>(d);
    f.write(reinterpret_cast<const char*>(&ud), sizeof(ud));
    f.write(reinterpret_cast<const char*>(G.data()), G.size() * sizeof(double));
    for (int n = 0; n <= N; ++n) {
        const double v = static_cast<double>(q1[n]);
        f.write(reinterpret_cast<const char*>(&v), sizeof(v));
    }
    if (!f) return 4;
    std::cout << "native_N=" << N
              << " seconds=" << std::chrono::duration<double>(
                     std::chrono::steady_clock::now() - q_start).count()
              << " long_double_digits=" << __LDBL_MANT_DIG__
              << " workers=" << workers << "\n";
    return 0;
}
