set(RC_ENABLE_GTEST TRUE)

add_subdirectory("lib/rapidcheck")

function(add_rapidcheck EXE_OR_LIB)
    target_compile_options(rapidcheck PUBLIC "-Wno-sign-conversion")
    target_compile_options(rapidcheck PUBLIC "-Wno-implicit-int-float-conversion")
    target_link_libraries(${EXE_OR_LIB} rapidcheck)
    target_link_libraries(${EXE_OR_LIB} rapidcheck_gtest)
    set(CMAKE_CXX_STANDARD 20)
endfunction()
