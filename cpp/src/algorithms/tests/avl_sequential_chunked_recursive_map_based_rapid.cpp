#include "../avl_sequential_chunked_recursive_map_based.hpp"
#include "../ikvs.hpp"
#include "kvs_rapid_harness.hpp"

#include "../../util/log.hpp"

auto without_erases() -> void {
  check([] {
    KVSModel s0{};
    ChunkedAvl kvs{};
    state::check(s0, kvs, state::gen::execOneOfWithArgs<Get, Insert>());
  });
}

auto with_erases() -> void {
  check([] {
    KVSModel s0{};
    ChunkedAvl kvs{};
    state::check(s0, kvs, state::gen::execOneOfWithArgs<Get, Insert, Erase>());
  });
}

int main() {
  log_to_file("avl_sequential_chunked_recursive_map_based_rapid.txt");
  // without_erases();
  with_erases();
  return 0;
}
