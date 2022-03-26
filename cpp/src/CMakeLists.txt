
add_library(Main SHARED main_lib.cpp)
add_boost(Main)
add_coverage(Main)
add_rapidcheck(Main)
add_executable(main main_main.cpp)
target_link_libraries(main Main)
target_include_directories(Main SYSTEM PUBLIC ../lib)

# add_project_warnings(Main)

add_subdirectory(algorithms)
add_subdirectory(tests)
# add_subdirectory(benchmark)
