#include <atomic>
#include <cassert>
#include <memory>
#include <span>
#include <vector>

void smoke_cpp20stdlib() {
  auto v = std::vector<int>(10);
  v[1] = 42;
  auto s = std::span<int>{v.begin(), v.end()};
  assert(s[1] == 42);
}
