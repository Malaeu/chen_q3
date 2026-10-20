#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <exception>
#include <limits>
#include <vector>

namespace {

constexpr std::int64_t kMaxBound = 1328763571296LL;  // 2 * 48 * 49^6
constexpr std::int64_t kMaxPeriodNorm = 1000000LL;

void set_error(char* error, std::size_t error_size, const char* message) {
  if (error == nullptr || error_size == 0) return;
  std::snprintf(error, error_size, "%s", message);
}

std::int64_t floor_div(std::int64_t a, std::int64_t b) {
  std::int64_t q = a / b;
  const std::int64_t r = a % b;
  if (r < 0) --q;
  return q;
}

std::int64_t floor_mod(std::int64_t a, std::int64_t b) {
  std::int64_t r = a % b;
  if (r < 0) r += b;
  return r;
}

std::int64_t floor_mod128(__int128 a, std::int64_t b) {
  __int128 r = a % b;
  if (r < 0) r += b;
  return static_cast<std::int64_t>(r);
}

std::int64_t ceil_div(std::int64_t a, std::int64_t b) {
  return -floor_div(-a, b);
}

std::uint64_t floor_sqrt(unsigned __int128 value) {
  std::uint64_t root = static_cast<std::uint64_t>(
      std::sqrt(static_cast<long double>(value)));
  while (static_cast<unsigned __int128>(root + 1) * (root + 1) <= value) {
    ++root;
  }
  while (static_cast<unsigned __int128>(root) * root > value) --root;
  return root;
}

std::int64_t cyclic_range_sum(const std::vector<std::int64_t>& prefix,
                              std::size_t row_offset,
                              std::int64_t period,
                              std::int64_t start,
                              std::int64_t length) {
  const std::int64_t end = start + length;
  const std::size_t base = row_offset;
  if (end <= period) {
    return prefix[base + static_cast<std::size_t>(end)] -
           prefix[base + static_cast<std::size_t>(start)];
  }
  return prefix[base + static_cast<std::size_t>(period)] -
         prefix[base + static_cast<std::size_t>(start)] +
         prefix[base + static_cast<std::size_t>(end - period)];
}

}  // namespace

extern "C" int periodic_disk_sums(const std::uint8_t* table,
                                  std::int64_t h1,
                                  std::int64_t h2,
                                  std::int64_t b_hnf,
                                  const std::int64_t* bounds,
                                  std::int64_t n_bounds,
                                  std::int64_t* output,
                                  char* error,
                                  std::size_t error_size) noexcept {
  try {
    if (table == nullptr || bounds == nullptr || output == nullptr) {
      set_error(error, error_size, "null input pointer");
      return 1;
    }
    if (h1 <= 0 || h2 <= 0 || n_bounds < 0) {
      set_error(error, error_size, "period dimensions and bound count must be nonnegative");
      return 2;
    }
    const __int128 period_norm = static_cast<__int128>(h1) * h2;
    if (period_norm > kMaxPeriodNorm) {
      set_error(error, error_size, "ideal norm period exceeds the exact counter limit");
      return 3;
    }
    if (b_hnf < 0 || b_hnf >= h1) {
      set_error(error, error_size, "HNF shift is outside [0,h1)");
      return 4;
    }
    if (h1 > std::numeric_limits<std::int64_t>::max() - 1) {
      set_error(error, error_size, "period dimension overflows prefix width");
      return 5;
    }

    const std::size_t width = static_cast<std::size_t>(h1 + 1);
    const std::size_t height = static_cast<std::size_t>(h2);
    if (height > std::numeric_limits<std::size_t>::max() / width) {
      set_error(error, error_size, "prefix table size overflows address space");
      return 6;
    }
    std::vector<std::int64_t> prefix(width * height, 0);
    std::vector<std::int64_t> row_totals(height, 0);
    for (std::int64_t j = 0; j < h2; ++j) {
      const std::size_t table_offset = static_cast<std::size_t>(j * h1);
      const std::size_t prefix_offset = static_cast<std::size_t>(j) * width;
      for (std::int64_t x = 0; x < h1; ++x) {
        const std::uint8_t encoded = table[table_offset + static_cast<std::size_t>(x)];
        if (encoded > 4) {
          set_error(error, error_size, "table entries must encode values in {-2,-1,0,1,2}");
          return 7;
        }
        const std::int64_t value = static_cast<std::int64_t>(encoded) - 2;
        prefix[prefix_offset + static_cast<std::size_t>(x + 1)] =
            prefix[prefix_offset + static_cast<std::size_t>(x)] + value;
      }
      row_totals[static_cast<std::size_t>(j)] = prefix[prefix_offset + width - 1];
    }

    for (std::int64_t bound_index = 0; bound_index < n_bounds; ++bound_index) {
      const std::int64_t bound = bounds[static_cast<std::size_t>(bound_index)];
      if (bound < 0 || bound > kMaxBound) {
        set_error(error, error_size, "radius is outside the exact counter limit");
        return 8;
      }

      const unsigned __int128 y_square_limit =
          (static_cast<unsigned __int128>(4) * static_cast<std::uint64_t>(bound)) / 3;
      const std::int64_t y_max = static_cast<std::int64_t>(floor_sqrt(y_square_limit));
      __int128 total = 0;
      for (std::int64_t y = -y_max; y <= y_max; ++y) {
        const __int128 discriminant = static_cast<__int128>(4) * bound -
                                      static_cast<__int128>(3) * y * y;
        if (discriminant < 0) continue;
        const std::int64_t root = static_cast<std::int64_t>(
            floor_sqrt(static_cast<unsigned __int128>(discriminant)));
        const std::int64_t x_low = ceil_div(y - root, 2);
        const std::int64_t x_high = floor_div(y + root, 2);
        const std::int64_t length = x_high - x_low + 1;
        if (length <= 0) continue;

        const std::int64_t k = floor_div(y, h2);
        const std::int64_t j = y - k * h2;
        const std::int64_t shift = floor_mod128(
            static_cast<__int128>(k) * b_hnf, h1);
        const std::int64_t start = floor_mod(x_low - shift, h1);
        const std::int64_t full_periods = length / h1;
        const std::int64_t remainder = length % h1;
        const std::size_t prefix_offset = static_cast<std::size_t>(j) * width;
        const __int128 row_sum =
            static_cast<__int128>(full_periods) * row_totals[static_cast<std::size_t>(j)] +
            cyclic_range_sum(prefix, prefix_offset, h1, start, remainder);
        total += row_sum;
      }

      // The disk includes (0,0); the requested sum excludes it.  For the
      // trivial ideal character that table entry is 2, while zero-extended
      // nontrivial characters give 0 there.
      total -= static_cast<std::int64_t>(table[0]) - 2;
      if (total < std::numeric_limits<std::int64_t>::min() ||
          total > std::numeric_limits<std::int64_t>::max()) {
        set_error(error, error_size, "periodic disk sum overflows int64");
        return 9;
      }
      output[static_cast<std::size_t>(bound_index)] = static_cast<std::int64_t>(total);
    }
    return 0;
  } catch (const std::exception& exc) {
    set_error(error, error_size, exc.what());
    return 10;
  } catch (...) {
    set_error(error, error_size, "unknown native counter failure");
    return 11;
  }
}
