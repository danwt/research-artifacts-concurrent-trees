#pragma once

#include <cstdio>
#include <spdlog/spdlog.h>

void smoke_spdlog() { spdlog::get("log")->debug("Spdlog is working"); }
