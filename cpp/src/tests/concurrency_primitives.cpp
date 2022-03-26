#include "../util/log.hpp"
#include <atomic>
#include <gtest/gtest.h>
#include <map>
#include <memory>
#include <optional>

TEST(AtomicSharedPointerSpecialization, smoke) {

  /*
  Unfortunately this is not yet supported by GCC or Clang.
  */

  /*
    struct T {
      int x;
    };
    auto ptr = std::atomic<std::shared_ptr<T>>{};
  */
}

TEST(AtomicFreeFunctions, smoke) {

  struct T {
    int x;
  };

  auto ptr = std::make_shared<T>();
  ptr->x = 42;

  auto other = std::make_shared<T>();
  other->x = 99;

  std::atomic_store(&ptr, other);
}

TEST(AtomicSharedPointer, store_to_reference) {

  struct T {
    int x;
  };

  auto ptr = std::make_shared<T>();
  ptr->x = 42;

  auto other = std::make_shared<T>();
  other->x = 99;

  auto &ptr_ref = ptr;

  assert(ptr_ref->x == 42);

  std::atomic_store(&ptr_ref, other);

  assert(ptr_ref->x == 99);
}

TEST(MapOfSharedPointers, erase_then_access) {

  struct T {
    int x;
  };

  auto m = std::map<int, std::shared_ptr<T>>{};

  for (int i{0}; i < 10; ++i) {
    // Just check both kinds of insertion are fine
    m.emplace(i, std::make_shared<T>(T{i}));
    m[i] = std::make_shared<T>(T{i});
  }

  assert(m.size() == 10);

  std::shared_ptr<T> ptr = m[5];

  assert(ptr->x == 5);

  m.erase(5);

  assert(m.size() == 9);

  assert(ptr->x == 5);
}

TEST(MapOfSharedPointersAtomicLoad, erase_then_access) {

  struct T {
    int x;
  };

  auto m = std::map<int, std::shared_ptr<T>>{};

  for (int i{0}; i < 10; ++i) {
    // Just check both kinds of insertion are fine
    m.emplace(i, std::make_shared<T>(T{i}));
    m[i] = std::make_shared<T>(T{i});
  }

  assert(m.size() == 10);

  std::shared_ptr<T> ptr;

  std::atomic_store(&ptr, m[5]);

  assert(ptr->x == 5);

  m.erase(5);

  assert(m.size() == 9);

  assert(ptr->x == 5);
}

TEST(AtomicOptional, smoke) {

  /*

    This doesn't work due to restrictions on T in std::atomic<T>

    struct V {
      int x;
    };

    auto ao = std::atomic<std::optional<V>>{};

    assert(ao.load() == std::nullopt);

  */

  SUCCEED();
}

TEST(SharedPointerDefault, is_null) {

  struct T {
    int x;
  };

  auto ptr = std::shared_ptr<T>{};

  assert(ptr == nullptr);
}
