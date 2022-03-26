#include "install_smokes/smoke_cpp20stdlib.hpp"
#include "install_smokes/smoke_spdlog.hpp"
#include "util/log.hpp"

void install_smokes() {
  smoke_cpp20stdlib();
  smoke_spdlog();
}

int main([[maybe_unused]] int argc, [[maybe_unused]] char **argv) {
  log_to_console();

  spdlog::get("log")->info("main main() start");

  install_smokes();

  spdlog::get("log")->info("main main() exit");
}