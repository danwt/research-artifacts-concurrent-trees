#pragma once
#include "ikvs.hpp"
#include <cassert>
#include <memory>
#include <optional>
#include <stack>

struct Node {
  K k;
  V v;

  std::unique_ptr<Node> left;
  std::unique_ptr<Node> right;

  int height{1};

  Node(K k_, V v_) : k(k_), v(v_) {}
};

class Avl : public IKVS {

public:
  [[nodiscard]] std::optional<V> get(K k) const final;
  void insert(K k, V v) final;
  void erase(K k) final;
  bool internally_consistent() final { return height_invariant_holds(); }

private:
  void rebalance(std::stack<Node *> &stack);
  bool height_invariant_holds();

  std::unique_ptr<Node> root{nullptr};
};

int left_height(Node const *node) {
  if (node->left != nullptr) {
    return node->left->height;
  }
  return 0;
}

int right_height(Node const *node) {
  if (node->right != nullptr) {
    return node->right->height;
  }
  return 0;
}

int balance_factor(Node const *node) {
  return right_height(node) - left_height(node);
}

bool is_balanced(Node const *node) { return abs(balance_factor(node)) < 2; }

void adjust_node_height(Node *node) {
  node->height = std::max(left_height(node), right_height(node)) + 1;
}

bool is_left_child_of(Node const *parent, Node const *child) {
  return parent->left.get() == child;
}

bool is_right_child_of(Node const *parent, Node const *child) {
  return parent->right.get() == child;
}

bool Avl::height_invariant_holds() {

  if (!root) {
    return true;
  }

  bool succeeded = true;

  auto check_balance = [&succeeded](Node const *node) {
    if (1 < abs(balance_factor(node))) {
      succeeded = false;
    }
  };

  auto stack = std::stack<Node const *>{};
  stack.push(root.get());

  while (!stack.empty()) {
    Node const *const curr = stack.top();
    stack.pop();
    check_balance(curr);
    if (auto const *left = curr->left.get()) {
      stack.push(left);
    }
    if (auto const *right = curr->right.get()) {
      stack.push(right);
    }
  }

  return succeeded;
}

[[nodiscard]] std::optional<V> Avl::get(K k) const {

  if (!root) {
    return std::nullopt;
  }

  Node const *curr = root.get();

  while (curr->k != k) {
    if (k < curr->k) {
      if (curr->left) {
        curr = curr->left.get();
        continue;
      }
      return std::nullopt;
    }
    if (curr->right) {
      curr = curr->right.get();
      continue;
    }
    return std::nullopt;
  }

  return curr->v;
}

void rotate_left(std::unique_ptr<Node> &pivot) {
  assert(pivot->right);
  auto right = std::move(pivot->right);
  pivot->right = std::move(right->left);
  right->left = std::move(pivot);
  pivot = std::move(right);
  adjust_node_height(pivot->left.get());
  adjust_node_height(pivot.get());
}

void rotate_right(std::unique_ptr<Node> &pivot) {
  assert(pivot->left);
  auto left = std::move(pivot->left);
  pivot->left = std::move(left->right);
  left->right = std::move(pivot);
  pivot = std::move(left);
  adjust_node_height(pivot->right.get());
  adjust_node_height(pivot.get());
}

void rotate(std::unique_ptr<Node> &pivot) {
  assert(!is_balanced(pivot.get()));
  auto bal = balance_factor(pivot.get());
  if (bal < -1) {                                // Left heavy
    if (0 < balance_factor(pivot->left.get())) { // If left is right heavy
      rotate_left(pivot->left);
    }
    rotate_right(pivot);
    return;
  }
  if (1 < bal) {                                  // Right heavy
    if (balance_factor(pivot->right.get()) < 0) { // If right is left heavy
      rotate_right(pivot->right);
    }
    rotate_left(pivot);
    return;
  }
}

void Avl::rebalance(std::stack<Node *> &stack) {

  assert(!stack.empty());

  while (!stack.empty()) {

    Node *curr = stack.top();
    stack.pop();

    adjust_node_height(curr);

    if (is_balanced(curr)) {
      continue;
    }

    // Must do rotation
    // Cases:
    // 1. curr is root (stack size is 0, (node has just been popped))
    // 2. curr is left child of parent
    // 3. curr is right child of parent

    if (stack.empty()) {
      assert(curr->k == root->k);
      rotate(root);
      return;
    }

    Node *parent = stack.top();

    if (is_left_child_of(parent, curr)) {
      rotate(parent->left);
    } else {
      assert(is_right_child_of(parent, curr));
      rotate(parent->right);
    }
  }
}

void Avl::insert(K k, V v) {
  assert(height_invariant_holds());

  if (!root) {
    root = std::make_unique<Node>(k, v);
    return;
  }

  auto stack = std::stack<Node *>{};
  Node *curr = root.get();

  while (curr->k != k) {
    stack.push(curr);
    if (k < curr->k) {
      if (curr->left) {
        curr = curr->left.get();
        continue;
      }
      // Insertion
      curr->left = std::make_unique<Node>(k, v);
      rebalance(stack);
      assert(height_invariant_holds());
      return;
    }
    if (curr->right) {
      curr = curr->right.get();
      continue;
    }
    // Insertion
    curr->right = std::make_unique<Node>(k, v);
    rebalance(stack);
    assert(height_invariant_holds());
    return;
  }

  // K already present, return
  curr->v = v;
}

void Avl::erase(K k) {

  if (!root) {
    return;
  }

  auto stack = std::stack<Node *>{};
  Node *curr = root.get();

  while (curr->k != k) {
    stack.push(curr);
    if (k < curr->k) {
      if (curr->left) {
        curr = curr->left.get();
      } else {
        // Not present
        return;
      }
    } else {
      if (curr->right) {
        curr = curr->right.get();
      } else {
        // Not present
        return;
      }
    }
  }

  if (!curr->left) { // No successor, simply erase and replace with right
    if (stack.empty()) {
      // Item to be deleted is root
      assert(curr->k == root->k);
      root = std::move(root->right);
      return;
    }
    auto *const parent = stack.top();
    if (is_left_child_of(parent, curr)) {
      parent->left = std::move(curr->right);
    } else {
      assert(is_right_child_of(parent, curr));
      parent->right = std::move(curr->right);
    }
    /*
    At this point stack top is parent of two nodes (or nulls) with correct
    heights, but the parent necessarily does not have correct height.
    */
    rebalance(stack);
    assert(height_invariant_holds());
    return;
  }

  /*
  At this point stack top is parent of node to be deleted.
  */

  // Found key
  Node *const to_del = curr;

  stack.push(curr);
  curr = curr->left.get();
  while (curr->right) {
    stack.push(curr);
    curr = curr->right.get();
  }
  std::swap(curr->k, to_del->k);
  std::swap(curr->v, to_del->v);
  auto *const parent = stack.top();
  if (is_left_child_of(parent, curr)) {
    parent->left = std::move(curr->left);
  } else {
    assert(is_right_child_of(parent, curr));
    parent->right = std::move(curr->left);
  }

  /*
  At this point stack top is parent of two nodes (or nulls) with correct
  heights, but the parent necessarily does not have correct height.
  */
  rebalance(stack);
  assert(height_invariant_holds());
}
