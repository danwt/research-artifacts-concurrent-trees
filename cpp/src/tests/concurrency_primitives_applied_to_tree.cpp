#include "../util/log.hpp"
#include <atomic>
#include <gtest/gtest.h>
#include <map>
#include <memory>
#include <optional>

using K = int;

struct V {
  int x;
};

struct Chunk;

struct Node {
  std::atomic<K> k;
  std::shared_ptr<V> v;
  std::shared_ptr<Node> left;
  std::shared_ptr<Node> rite;
  std::shared_ptr<Node> parent;

  std::atomic<int> h;
  int height{1};

  // Note: does not need to be atomic/shared for the mrsw version
  std::shared_ptr<Chunk> chunk;
};

struct Chunk {
  using ChunkMap = std::map<K, std::shared_ptr<Node>>;
  ChunkMap left_wing;
  ChunkMap rite_wing;
  int id;

  std::shared_ptr<Node> root;
};

TEST(AtomicTreeBasics, compiles_basics) {
  Node n;
  Chunk c;
}

TEST(AtomicTreeBasics, zero_initialized) {
  Node n;
  Chunk c;
  assert(n.k == 0);
  assert(n.v == nullptr);
  assert(n.left == nullptr);
  assert(n.chunk == nullptr);
  assert(c.root == nullptr);
}