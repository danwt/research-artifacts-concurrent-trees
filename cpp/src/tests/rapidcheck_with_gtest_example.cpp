#include "../util/log.hpp"

// clang-format off
#include <gtest/gtest.h>
#include <rapidcheck/gtest.h>
// clang-format on

RC_GTEST_PROP(RapidCheckAndGTestExample, inRangeValueIsInRange, ()) {
  const auto range = *rc::gen::arbitrary<std::pair<int, int>>();
  const auto x = *rc::gen::inRange(range.first, range.second);
  RC_ASSERT(x >= range.first);
  RC_ASSERT(x < range.second);
}