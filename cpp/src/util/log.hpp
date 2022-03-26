#pragma once
#include "spdlog/sinks/stdout_color_sinks.h"
#include <iostream>
#include <spdlog/common.h>
#include <spdlog/sinks/basic_file_sink.h>
#include <spdlog/spdlog.h>

void log_to_file(std::string const &file_name) {
  try {
    auto log = spdlog::basic_logger_mt("log", "logs/" + file_name, true);
    log->set_pattern("[%M:%S %z] [thread %t] %v");
    log->set_level(spdlog::level::debug);
    log->flush_on(spdlog::level::debug);
  } catch (spdlog::spdlog_ex const &ex) {
    std::cout << "Log init failed: " << ex.what() << std::endl;
  }
}

void log_to_console() {
  try {
    auto log = spdlog::stdout_color_mt("log");
    log->set_pattern("[%M:%S %z] [thread %t] %v");
    log->set_level(spdlog::level::debug);
    log->flush_on(spdlog::level::debug);
  } catch (spdlog::spdlog_ex const &ex) {
    std::cout << "Log init failed: " << ex.what() << std::endl;
  }
}