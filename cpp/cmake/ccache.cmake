find_program(CCACHE_PROGRAM ccache)

if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
    message("-- Using ccache.")
else()
    message("-- Not using ccache.")
endif()
