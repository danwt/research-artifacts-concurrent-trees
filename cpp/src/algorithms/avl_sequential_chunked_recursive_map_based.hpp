#pragma once
#include "../util/log.hpp"
#include "ikvs.hpp"
#include "render_debug.hpp"
#include <cassert>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <stack>
#include <string>
#include <unordered_set>
#include <vector>

constexpr int const MAX_CHUNK_SIZE{8};

struct Chunk;

struct Node {
  K k;
  std::optional<V> v;

  Node *left{nullptr};
  Node *rite{nullptr};
  Node *parent{nullptr};

  int height{1};

  Chunk *chunk{nullptr};

  Node() = default;
  Node(K k_, Node *left_, Node *rite_, int height_)
      : k(k_), left(left_), rite(rite_), height(height_) {}

  [[nodiscard]] bool is_leaf() const { return v.has_value(); }

  [[nodiscard]] bool is_chunk_root() const { return chunk != nullptr; }
};

bool is_left_child_of(Node const *parent, Node const *child) {
  return parent->left == child;
}

bool is_rite_child_of(Node const *parent, Node const *child) {
  return parent->rite == child;
}

bool is_parent_of(Node const *parent, Node const *child) {
  return is_left_child_of(parent, child) || is_rite_child_of(parent, child);
}

int left_height(Node const *node) {
  if (node->left != nullptr) {
    return node->left->height;
  }
  return 0;
}

int rite_height(Node const *node) {
  if (node->rite != nullptr) {
    return node->rite->height;
  }
  return 0;
}

int balance_factor(Node const *node) {
  return rite_height(node) - left_height(node);
}

bool is_balanced(Node const *node) { return abs(balance_factor(node)) < 2; }

void adjust_node_height(Node *node) {
  node->height = std::max(left_height(node), rite_height(node)) + 1;
}

struct Chunk {

  using ChunkMap = std::map<K, Node>;
  ChunkMap left_wing;
  ChunkMap rite_wing;
  int id;
  Node *root{nullptr};

  Chunk(int id_) : id(id_) {}

  [[nodiscard]] int size() const {
    return static_cast<int>(left_wing.size() + rite_wing.size());
  }

  void erase(ChunkMap &chunk_map, K k) { chunk_map.erase(k); }

  Node *insert_left(K k, V v, Node *parent) {
    auto &node = left_wing[k];
    write_node(node, k, v, parent);
    return &node;
  }

  Node *insert_rite(K k, V v, Node *parent) {
    auto &node = rite_wing[k];
    write_node(node, k, v, parent);
    return &node;
  }

  void shift_left(K min_key_to_keep) {
    shift(rite_wing, left_wing,
          [min_key_to_keep](K k) { return k < min_key_to_keep; });
  }

  void shift_rite(K min_key_to_move) {
    shift(left_wing, rite_wing,
          [min_key_to_move](K k) { return min_key_to_move <= k; });
  }

private:
  static void write_node(Node &node, K k, V v, Node *parent) {
    node.k = k;
    node.v = v;
    node.parent = parent;

    if (node.parent == nullptr) {
      return;
    }

    if (node.parent->left != nullptr && node.parent->left->k == k) {
      node.parent->left = &node;
      return;
    }

    node.parent->rite = &node;
  }

  void shift(ChunkMap &from, ChunkMap &to, std::function<bool(K)> pred) const {
    assert(root != nullptr);

    for (auto it = from.cbegin(), next_it = it; it != from.cend();
         it = next_it) {
      ++next_it;
      auto const &n = it->second;
      if (pred(n.k)) {
        auto &node = to[n.k];
        write_node(node, n.k, *n.v, n.parent);
        from.erase(it);
      }
    }
  }
};

class ChunkedAvl : public IKVS {

public:
  ChunkedAvl() { spdlog::get("log")->debug("Constructor"); }

  [[nodiscard]] std::optional<V> get(K k) const final;

  void insert(K k, V v) final;
  void erase(K k) final;

  bool internally_consistent() final {
    height_invariant_check();
    chunk_invariant_check();
    pointer_invariant_check();
    return true;
  }

private:
  void insert_impl(K k, V v, Node *curr, Chunk *c);
  void erase_impl(K k, Node *curr, Node *non_leaf_with_key_k, Chunk *c);
  void do_erase(K k, Node *curr, Node *non_leaf_with_key_k, Chunk *c);
  void rotate_left(Node *&pivot);
  void rotate_rite(Node *&pivot);
  void rotate(Node *&pivot);
  void rebalance(Node *curr);
  void split_left_wing_into_new_chunk(Node *node);

  Node *create_non_leaf(K k, Node *left, Node *rite);
  Chunk *create_next_chunk();
  Chunk *create_chunk(int id);

  void destroy_chunk(Chunk *chunk);
  void destroy_non_leaf(Node *node);

  int next_chunk_id = 0;
  Node root_holder{-99, nullptr, nullptr, -99};
  std::vector<std::unique_ptr<Chunk>> chunks;
  std::vector<std::unique_ptr<Node>> inner_nodes;

  /*
  Checks
  */

  void RENDER_DEBUG_GRAPH(std::string title) const;

  void height_invariant_check() const;

  void pointer_invariant_check() const;
  void chunk_invariant_check() const;

  void non_height_invariant_checks() const {
    pointer_invariant_check();
    chunk_invariant_check();
  }

  void all_checks() const {
    height_invariant_check();
    non_height_invariant_checks();
  }
};

/**
 * @brief Create a new inner node with non-null left and rite children. Also
 * mutate children to have inner pointer. Height will be set to 2.
 */
Node *ChunkedAvl::create_non_leaf(K k, Node *left, Node *rite) {
  assert(left->left == nullptr);
  assert(left->rite == nullptr);
  assert(rite->left == nullptr);
  assert(rite->rite == nullptr);
  assert(left->is_leaf());
  assert(rite->is_leaf());
  inner_nodes.push_back(std::make_unique<Node>(k, left, rite, 2));
  auto *const ret = inner_nodes.back().get();
  left->parent = ret;
  rite->parent = ret;
  return ret;
}

Chunk *ChunkedAvl::create_next_chunk() { return create_chunk(next_chunk_id++); }

Chunk *ChunkedAvl::create_chunk(int id) {
  chunks.push_back(std::make_unique<Chunk>(id));
  return chunks.back().get();
}

void ChunkedAvl::destroy_chunk(Chunk *chunk) {
  for (int i{0}; i < static_cast<int>(chunks.size()); ++i) {
    if (chunks[i]->id == chunk->id) {
      chunks.erase(chunks.begin() + i);
      return;
    }
  }
}

void ChunkedAvl::destroy_non_leaf(Node *node) {
  assert(!node->is_leaf());
  for (int i{0}; i < static_cast<int>(inner_nodes.size()); ++i) {
    if (inner_nodes[i].get() == node) {
      inner_nodes.erase(inner_nodes.begin() + i);
      return;
    }
  }
}

void ChunkedAvl::split_left_wing_into_new_chunk(Node *node) {
  non_height_invariant_checks();

  assert(node->is_chunk_root());
  assert(node->chunk->root == node);
  assert(node->left);
  assert(node->rite);
  assert(!node->is_leaf());

  auto const DEBUG_pre_sz = node->chunk->size();
  auto const DEBUG_pre_left_sz = node->chunk->left_wing.size();
  auto const DEBUG_pre_rite_sz = node->chunk->rite_wing.size();

  RENDER_DEBUG_GRAPH("pre split");

  auto *const c = node->chunk;
  auto *const new_chunk = create_next_chunk();

  for (auto &[k, n] : node->chunk->left_wing) {
    if (n.k < node->left->k) {
      new_chunk->insert_left(n.k, *n.v, n.parent);
    } else {
      new_chunk->insert_rite(n.k, *n.v, n.parent);
    }
  }

  new_chunk->root = node->left;
  new_chunk->root->chunk = new_chunk;

  c->root->chunk = nullptr;
  c->root = node->rite;
  c->root->chunk = c;

  c->left_wing.clear();
  c->shift_left(node->rite->k);

  RENDER_DEBUG_GRAPH("post split");

  assert(DEBUG_pre_sz == c->size() + new_chunk->size());
  assert(new_chunk->size() == DEBUG_pre_left_sz);
  assert(c->size() == DEBUG_pre_rite_sz);
  assert(node->left->is_chunk_root());
  assert(node->rite->is_chunk_root());
  assert(!node->is_chunk_root());

  non_height_invariant_checks();
}

[[nodiscard]] std::optional<V> get_impl(K k, Node const *curr) {
  if (curr == nullptr) {
    return std::nullopt;
  }
  if (curr->is_leaf() && curr->k == k) {
    return curr->v;
  }
  if (k < curr->k) {
    return get_impl(k, curr->left);
  }
  return get_impl(k, curr->rite);
}

[[nodiscard]] std::optional<V> ChunkedAvl::get(K k) const {

  RENDER_DEBUG_GRAPH("pre get    " + std::to_string(k));

  return get_impl(k, root_holder.rite);
}

void ChunkedAvl::rotate_left(Node *&pivot) {

  assert(pivot->rite);
  assert(!pivot->rite->is_leaf());

  if (auto *const chunk = pivot->chunk; chunk != nullptr) {
    pivot->chunk->shift_left(pivot->rite->k);
    chunk->root = pivot->rite;
    pivot->rite->chunk = pivot->chunk;
    pivot->chunk = nullptr;
  } else if (pivot->rite->is_chunk_root()) {
    split_left_wing_into_new_chunk(pivot->rite);
  }

  auto *new_pivot = pivot->rite;
  new_pivot->parent = pivot->parent;
  pivot->rite = new_pivot->left;
  new_pivot->left->parent = pivot;
  new_pivot->left = pivot;
  pivot->parent = new_pivot;
  pivot = new_pivot;

  adjust_node_height(pivot->left);
  adjust_node_height(pivot);
}

void ChunkedAvl::rotate_rite(Node *&pivot) {

  assert(pivot->left);
  assert(!pivot->left->is_leaf());

  if (auto *const chunk = pivot->chunk; chunk != nullptr) {
    pivot->chunk->shift_rite(pivot->left->k);
    chunk->root = pivot->left;
    pivot->left->chunk = pivot->chunk;
    pivot->chunk = nullptr;
  } else if (pivot->left->is_chunk_root()) {
    split_left_wing_into_new_chunk(pivot->left);
  }

  auto *new_pivot = pivot->left;
  new_pivot->parent = pivot->parent;
  pivot->left = new_pivot->rite;
  new_pivot->rite->parent = pivot;
  new_pivot->rite = pivot;
  pivot->parent = new_pivot;
  pivot = new_pivot;

  adjust_node_height(pivot->rite);
  adjust_node_height(pivot);
}

void ChunkedAvl::rotate(Node *&pivot) {

  auto bal = balance_factor(pivot);
  if (bal < -1) {                          // Left heavy
    if (0 < balance_factor(pivot->left)) { // If left is rite heavy
      rotate_left(pivot->left);
    }
    rotate_rite(pivot);
    return;
  }
  if (1 < bal) {                           // Rite heavy
    if (balance_factor(pivot->rite) < 0) { // If rite is left heavy
      rotate_rite(pivot->rite);
    }
    rotate_left(pivot);
    return;
  }
}

void ChunkedAvl::rebalance(Node *curr) {

  while (curr->parent != nullptr) {

    adjust_node_height(curr);

    Node *parent = curr->parent;

    if (is_balanced(curr)) {
      curr = parent;
      continue;
    }

    if (is_left_child_of(parent, curr)) {
      rotate(parent->left);
    } else {
      rotate(parent->rite);
    }

    curr = parent;
  }

  assert(curr == &root_holder);
}

void ChunkedAvl::insert_impl(K k, V v, Node *curr, Chunk *c) {

  if (curr->is_chunk_root()) {
    c = curr->chunk;
    // If it's full, split it
    if (c->size() == MAX_CHUNK_SIZE) {
      assert((!curr->is_leaf()) || MAX_CHUNK_SIZE == 1);
      split_left_wing_into_new_chunk(curr);
      c = nullptr;
    }
  }

  if (!curr->is_leaf()) {
    assert(curr->left);
    assert(curr->rite);
    // All inner nodes have a left and rite child to continue the search
    if (k < curr->k) {
      insert_impl(k, v, curr->left, c);
      return;
    }
    insert_impl(k, v, curr->rite, c);
    return;
  }

  if (k == curr->k) {
    // K already present, just set value
    curr->v = v;
    return;
  }

  assert(c != nullptr);
  assert(c->size() < MAX_CHUNK_SIZE);

  Node *inserted;

  if (k < c->root->k) {
    inserted = c->insert_left(k, v, nullptr);
  } else {
    inserted = c->insert_rite(k, v, nullptr);
  }

  Node *parent = curr->parent;

  bool curr_is_left_child = is_left_child_of(parent, curr);

  Node *new_leaf_parent;

  if (k < curr->k) {
    new_leaf_parent = create_non_leaf(curr->k, inserted, curr);
  } else {
    new_leaf_parent = create_non_leaf(k, curr, inserted);
  }

  assert(new_leaf_parent->left->parent == new_leaf_parent);
  assert(new_leaf_parent->rite->parent == new_leaf_parent);

  assert(is_parent_of(new_leaf_parent, curr));

  if (curr_is_left_child) {
    parent->left = new_leaf_parent;
  } else {
    parent->rite = new_leaf_parent;
  }

  new_leaf_parent->parent = parent;

  if (curr->is_chunk_root()) {
    // Steal chunk-rootyness from the leaf that the new inner has replaced
    assert(c == new_leaf_parent->left->chunk ||
           c == new_leaf_parent->rite->chunk);
    assert(curr->chunk == c);
    new_leaf_parent->chunk = c;
    c->root = new_leaf_parent;
    curr->chunk = nullptr;
    // Don't forget to shift as necessary
    new_leaf_parent->chunk->shift_left(k);
  }

  non_height_invariant_checks();

  assert(is_parent_of(parent, new_leaf_parent));
  assert(new_leaf_parent->parent == parent);
  assert(is_parent_of(new_leaf_parent, new_leaf_parent->left));
  assert(is_parent_of(new_leaf_parent, new_leaf_parent->rite));
  assert(new_leaf_parent->left->parent == new_leaf_parent);
  assert(new_leaf_parent->rite->parent == new_leaf_parent);

  rebalance(new_leaf_parent->parent);
}

void ChunkedAvl::insert(K k, V v) {

  RENDER_DEBUG_GRAPH("insert    " + std::to_string(k) + "," +
                     std::to_string(v));

  if (root_holder.rite == nullptr) {
    Chunk *chunk = create_next_chunk();
    root_holder.rite = chunk->insert_rite(k, v, nullptr);
    root_holder.rite->parent = &root_holder;
    root_holder.rite->chunk = chunk;
    chunk->root = root_holder.rite;
    assert(root_holder.rite->chunk == chunk);
    assert(chunk->root == root_holder.rite);
    all_checks();
    return;
  }

  insert_impl(k, v, root_holder.rite, nullptr);
  all_checks();
}

void bind_parent_to_new_child(Node *parent, Node const *const old_child,
                              Node *replacement_child) {
  assert(is_parent_of(parent, old_child));
  if (is_left_child_of(parent, old_child)) {
    parent->left = replacement_child;
    parent->left->parent = parent;
    return;
  }
  parent->rite = replacement_child;
  parent->rite->parent = parent;
}

void ChunkedAvl::do_erase(K k, Node *curr, Node *non_leaf_with_key_k,
                          Chunk *c) {

  assert(curr->is_leaf());
  assert(curr->k == k);

  Node *const parent = curr->parent;

  assert(is_parent_of(parent, curr));

  if (curr->is_chunk_root()) {
    assert(c == curr->chunk);
    destroy_chunk(c);
    if (parent == &root_holder) {
      // Special case, root holder is leaf parent
      assert(root_holder.rite == curr);
      root_holder.rite = nullptr;
      all_checks();
      return;
    }
  } else {
    if (k < c->root->k) {
      c->erase(c->left_wing, k);
    } else {
      c->erase(c->rite_wing, k);
    }
  }

  Node *const parent_parent = parent->parent;
  assert(parent_parent != nullptr);

  if (non_leaf_with_key_k == nullptr) {
    // 1. Non-leaf with key k was not found
    assert(parent->rite != nullptr);

    if (parent->is_chunk_root()) {
      assert(c == parent->chunk);
      c->root = parent->rite;
      c->root->chunk = c;
      c->shift_left(c->root->k);
    }

    bind_parent_to_new_child(parent_parent, parent, parent->rite);

  } else if (non_leaf_with_key_k == parent) {
    // 2. Leaf is rite of non-leaf with key k
    assert(parent->left != nullptr);

    if (parent->is_chunk_root()) {
      assert(c == parent->chunk);
      c->shift_rite(parent->left->k);
      c->root = parent->left;
      c->root->chunk = c;
    }

    bind_parent_to_new_child(parent_parent, parent, parent->left);

  } else {
    // 3. Leaf is rite-left of non-leaf with key k
    // 4. Leaf is beyond rite-left of non-leaf with key k

    assert(parent->rite != nullptr);

    assert(non_leaf_with_key_k->k == k);

    if (parent->is_chunk_root()) {
      assert(c == parent->chunk);
      c->root = parent->rite;
      c->root->chunk = c;
      c->shift_left(c->root->k);
    }

    non_leaf_with_key_k->k = parent->k;

    if (parent_parent == non_leaf_with_key_k) {
      parent_parent->rite = parent->rite;
    } else {
      parent_parent->left = parent->rite;
    }

    parent->rite->parent = parent_parent;
  }

  destroy_non_leaf(parent);

  rebalance(parent_parent);
}

void ChunkedAvl::erase_impl(K k, Node *curr, Node *non_leaf_with_key_k,
                            Chunk *c) {

  if (curr == nullptr) {
    return;
  }

  if (curr->is_chunk_root()) {
    c = curr->chunk;
  }

  if (curr->k == k) {

    if (curr->is_leaf()) {
      do_erase(k, curr, non_leaf_with_key_k, c);
      return;
    }

    // Should only encounter 1 router with key k during descent
    assert(non_leaf_with_key_k == nullptr);
    assert(curr->rite != nullptr);
    non_leaf_with_key_k = curr;
  }

  if (k < curr->k) {
    erase_impl(k, curr->left, non_leaf_with_key_k, c);
    return;
  }

  erase_impl(k, curr->rite, non_leaf_with_key_k, c);
}

void ChunkedAvl::erase(K k) {

  RENDER_DEBUG_GRAPH("pre erase " + std::to_string(k));

  erase_impl(k, root_holder.rite, nullptr, nullptr);

  all_checks();
}

/*
-----------------------------------------------------------------------------------------------------
Checks
*/

void ChunkedAvl::RENDER_DEBUG_GRAPH(std::string title) const {
  debug_graph g;
  g.title = title;
  std::function<void(Node *)> dfs = [&](Node *node) {
    if (node == nullptr) {
      return;
    }
    auto n = debug_graph::node{node->k, node->v, node->is_chunk_root(),
                               node->is_leaf()};
    if (node->left != nullptr) {
      g.edges.emplace_back(debug_graph::edge{n,
                                             {node->left->k, node->left->v,
                                              node->left->is_chunk_root(),
                                              node->left->is_leaf()},
                                             true,
                                             false});
    }
    if (node->rite != nullptr) {
      g.edges.emplace_back(debug_graph::edge{n,
                                             {node->rite->k, node->rite->v,
                                              node->rite->is_chunk_root(),
                                              node->rite->is_leaf()},
                                             false,
                                             false});
    }
    if (node->parent != nullptr) {
      g.edges.emplace_back(debug_graph::edge{n,
                                             {node->parent->k, node->parent->v,
                                              node->parent->is_chunk_root(),
                                              node->parent->is_leaf()},
                                             false,
                                             true});
    }
    dfs(node->left);
    dfs(node->rite);
  };
  if (root_holder.rite != nullptr) {

    g.edges.emplace_back(debug_graph::edge{
        {root_holder.k, root_holder.v, false, false},
        {root_holder.rite->k, root_holder.rite->v,
         root_holder.rite->is_chunk_root(), root_holder.rite->is_leaf()},
        false});
  }
  dfs(root_holder.rite);
  spdlog::get("log")->debug(g.json());
}

void ChunkedAvl::pointer_invariant_check() const {

  std::function<void(Node const *)> dfs;
  dfs = [&dfs, this](Node const *node) {
    if (node == nullptr) {
      return;
    }

    bool same_child = node->left != nullptr && (node->left == node->rite);

    assert(!same_child);
    assert(node->left != node);
    assert(node->rite != node);

    if (node->is_leaf()) {
      assert(node->left == nullptr);
      assert(node->rite == nullptr);
      assert(node->parent != nullptr);
      assert(node->left != node->parent);
      assert(node->rite != node->parent);
    } else {
      assert(node->left != nullptr || node->rite != nullptr);
    }

    assert(is_parent_of(node->parent, node));

    dfs(node->left);
    dfs(node->rite);
  };

  dfs(root_holder.rite);
}

void ChunkedAvl::chunk_invariant_check() const {

  std::function<void(Node const *, bool)> dfs;
  dfs = [&dfs](Node const *node, bool chunk_encountered) {
    if (node == nullptr) {
      return;
    }

    if (node->is_chunk_root()) {

      assert(!chunk_encountered);
      chunk_encountered = true;

      assert(node->chunk->root == node);

      auto truly_reachable = std::unordered_set<Node const *>{};

      std::function<void(Node const *)> dfs2;
      dfs2 = [&dfs2, &truly_reachable](Node const *n) {
        if (n == nullptr) {
          return;
        }

        if (n->is_leaf()) {
          assert(!truly_reachable.contains(n));
          truly_reachable.emplace(n);
        }
        dfs2(n->left);
        dfs2(n->rite);
      };

      dfs2(node);
      assert(static_cast<int>(truly_reachable.size()) == node->chunk->size());

      for (auto &[k, n] : node->chunk->left_wing) {
        auto *p = n.parent;
        assert(is_parent_of(p, &n));
        assert(n.k < node->chunk->root->k);
        assert(truly_reachable.contains(&n));
      }

      for (auto &[k, n] : node->chunk->rite_wing) {
        auto *p = n.parent;
        assert(is_parent_of(p, &n));
        assert(node->chunk->root->k <= n.k);
        assert(truly_reachable.contains(&n));
      }

      if (node->is_leaf()) {
        for (auto &[k, n] : node->chunk->rite_wing) {
          assert(n.k != node->k || node == &n);
        }
      }
    }
    dfs(node->left, chunk_encountered);
    dfs(node->rite, chunk_encountered);
  };

  dfs(root_holder.rite, false);
}

void ChunkedAvl::height_invariant_check() const {

  std::function<int(Node const *)> dfs;
  dfs = [&dfs](Node const *node) -> int {
    if (node == nullptr) {
      return 0;
    }
    auto left = dfs(node->left);
    auto rite = dfs(node->rite);
    assert(abs(rite - left) < 2);
    return std::max(left, rite) + 1;
  };

  dfs(root_holder.rite);
}
