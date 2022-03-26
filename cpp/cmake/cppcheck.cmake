# https://stackoverflow.com/a/48630368/8346628

find_program(CMAKE_CXX_CPPCHECK NAMES cppcheck)

if (CMAKE_CXX_CPPCHECK)
    list(
        APPEND CMAKE_CXX_CPPCHECK 
            # https://linux.die.net/man/1/cppcheck
            --quiet
            --enable=all
            --check-config
            --suppressions-list=../cppcheck/suppressions.txt
    )
    message("-- Using ccpcheck.")
else()
    message("-- Not using cppcheck.")
endif()