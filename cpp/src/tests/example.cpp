
#include "../util/log.hpp"
#include <gtest/gtest.h>

TEST(Example, always_succeeds) { SUCCEED() << "example"; }

int main(int argc, char **argv) {
  try {
    log_to_file("example_test");
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
  } catch (spdlog::spdlog_ex const &ex) {
    std::cout << "Log initialization failed: " << ex.what() << std::endl;
  }
}
