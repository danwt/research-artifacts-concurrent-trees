add_unit_test(example example.cpp LIBS Main) 
add_unit_test(without_logging without_logging.cpp LIBS Main) 
add_unit_test(rapidcheck_with_gtest_example rapidcheck_with_gtest_example.cpp LIBS Main) 

add_unit_test(concurrency_primitives concurrency_primitives.cpp LIBS Main) 
add_unit_test(concurrency_primitives_applied_to_tree concurrency_primitives_applied_to_tree.cpp LIBS Main) 