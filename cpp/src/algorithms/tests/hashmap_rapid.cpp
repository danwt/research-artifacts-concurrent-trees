#include "../ikvs.hpp"
#include "kvs_rapid_harness.hpp"

#include <spdlog/spdlog.h>

int main() {
  check([] {
    KVSModel s0{};
    HashMapKVS kvs{};
    state::check(s0, kvs, state::gen::execOneOfWithArgs<Get, Insert, Erase>());
  });
  return 0;
}
