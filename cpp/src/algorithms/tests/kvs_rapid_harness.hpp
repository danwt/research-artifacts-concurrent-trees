#pragma once

#include "../../util/log.hpp"
#include "../ikvs.hpp"
#include "gtest/gtest.h"
#include <optional>
#include <rapidcheck.h>
#include <rapidcheck/Show.h>
#include <rapidcheck/gtest.h>
#include <rapidcheck/state.h>

using namespace rc;

class HashMapKVS : public IKVS {

public:
  [[nodiscard]] std::optional<V> get(K k) const final {
    auto found = map.find(k);
    if (found == map.end()) {
      return std::nullopt;
    }
    return found->second;
  }
  void insert(K k, V v) final { map[k] = v; }
  void erase(K k) final { map.erase(k); }
  bool internally_consistent() final { return true; }

private:
  std::unordered_map<K, V> map;
};

struct KVSModel {
  HashMapKVS hashmap;
};

static int const KEY_RANGE_MIN = 0;
static int const KEY_RANGE_MAX = 100;
static int const VALUE_RANGE_MIN = 0;
static int const VALUE_RANGE_MAX = 100;

using KVSCommand = state::Command<KVSModel, IKVS>;

struct Get : public KVSCommand {
  K k;

  explicit Get(KVSModel const &s0) {
    (void)s0;
    k = *rc::gen::inRange(KEY_RANGE_MIN, KEY_RANGE_MAX);
  }

  void run(KVSModel const &s0, IKVS &kvs) const override {
    RC_ASSERT(kvs.get(k) == s0.hashmap.get(k));
  }

  void show(std::ostream &os) const override {
    os << "get(" << toString(k) << ")";
  }
};

struct Insert : public KVSCommand {
  K k;
  V v;

  explicit Insert(KVSModel const &s0) {
    (void)s0;
    k = *rc::gen::inRange(KEY_RANGE_MIN, KEY_RANGE_MAX);
    v = *rc::gen::inRange(VALUE_RANGE_MIN, VALUE_RANGE_MAX);
  }

  void apply(KVSModel &s0) const override { s0.hashmap.insert(k, v); }

  void run(KVSModel const &s0, IKVS &kvs) const override {
    (void)s0;
    kvs.insert(k, v);
    RC_ASSERT(kvs.get(k) == v);
  }

  void show(std::ostream &os) const override {
    os << "insert(" << toString(k) << ", " << toString(v) << ")";
  }
};

struct Erase : public KVSCommand {
  K k;

  explicit Erase(KVSModel const &s0) {
    (void)s0;
    k = *rc::gen::inRange(KEY_RANGE_MIN, KEY_RANGE_MAX);
  }

  void apply(KVSModel &s0) const override { s0.hashmap.erase(k); }

  void run(KVSModel const &s0, IKVS &kvs) const override {
    (void)s0;
    kvs.erase(k);
    RC_ASSERT(kvs.get(k) == std::nullopt);
  }

  void show(std::ostream &os) const override {
    os << "erase(" << toString(k) << ")";
  }
};