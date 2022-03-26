# research-artifacts-concurrent-trees

Source code and other artifacts for research on concurrent trees.

## Development guide

All development is intended to be done in VSCode or IntelliJ. VSCode is used for TLA+, Latex, Typescript, C++ and any scripts. IntelliJ is used for Java. Some of the work environments use VSCode [dev containers](https://code.visualstudio.com/docs/remote/containers) so a Docker daemon is required to be running in the background.

Issues should have a reference to a specific commit, if reference some code. This allows the latest commit to always contain relevant live code only.

## Subdirectories

### java

Java code implementing various sequential and concurrent trees and testing them.

Status : in working order and immediately buildable with IntelliJ. Documentation should be improved, in particular the list of algorithms.

### java_tla

Java code implementing TLC operator overrides for TLA operators used to model check trees.

Status : requires updating to use new method of TLC operator overloads.

### tla

TLA code modelling sequential and concurrent trees.

Status : requires tidying and updating models to match latest TLA knowledge.

## Additional components

There are a number of abandoned components of the project. The code is still available at various tagged commits for future reference, if the components should be reintroduced.

- [ ] A C++ implementation of various sequential AVL trees including chunked trees
- [ ] A web app for visual debugging of TLA+ traces written in Typescript, using React
