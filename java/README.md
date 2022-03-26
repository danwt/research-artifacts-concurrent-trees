# Java Implementations

## Development

Create a new IntelliJ project from this directory and ensure the Java version being used is `16`. Ensure IntelliJ is configured to build and run and run tests using `IntelliJ IDEA`:

![preferences](./preferences.png)

## Algorithms

### AvlChunked

1. MRSWCAvlIterativeFullRetryDechunked
1. MRSWCAvlIterativeFullRetryMapBased
1. MRSWCAvlRecursiveMapBased
2. SeqCAvlIterativeMapBased
2. SeqCAvlRecursiveMapBased

### Bronson

1. BronsonBrown // Brown's original version of the Bronson tree
2. BronsonBrownAlt // Brown's original alternate version of the Bronson tree
3. BronsonIterative // Bronson's original tree made iterative
4. BronsonIterativeBrown // Brown's version of the Bronson tree made iterative
5. BronsonIterativeSimpleRotates // Unrolls riteOverLeft and leftOverRite into doing two rotates
6. BronsonIterativeSimpleRotatesFixing #WIP
7. BronsonOriginal // Bronson's original version of the tree

### Brown

1. HooverBrown // The lock free external Avl due to Hoover and Brown

### Drachsler

1. DrachslerLogicalOrdering // The internal Avl due to Drachsler
