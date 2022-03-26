find_package(Boost 1.71 REQUIRED COMPONENTS system thread)

message(STATUS "Boost version: ${Boost_VERSION}")

function(add_boost EXE_OR_LIB)
    target_link_libraries(${EXE_OR_LIB} Boost::system Boost::thread)
endfunction()
