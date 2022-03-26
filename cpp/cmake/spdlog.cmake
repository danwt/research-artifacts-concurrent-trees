find_package(spdlog REQUIRED)

message(STATUS "Using spdlog")

function(add_spdlog EXE_OR_LIB)
    target_link_libraries(${EXE_OR_LIB} spdlog::spdlog)
    target_compile_options(${EXE_OR_LIB} PRIVATE -fPIC)
endfunction()
