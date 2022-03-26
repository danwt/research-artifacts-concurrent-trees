#include <catch2/catch.hpp>
#include <rapidcheck/catch.h>

#include "rapidcheck/detail/Serialization.h"

#include "util/Meta.h"
#include "util/Serialization.h"
#include "util/TypeListMacros.h"

using namespace rc;
using namespace rc::detail;
using namespace rc::test;

TEST_CASE("serialization(integers)") {
  forEachType<SerializationProperties, RC_INTEGRAL_TYPES>();
}
