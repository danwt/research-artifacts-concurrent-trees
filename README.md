# research-artifacts-concurrent-trees

Source code and other artifacts for research on concurrent trees.

## Development guide

All development is intended to be done in VSCode or Intellij. VSCode is used for TLA+, Latex, Typescript, C++ and any scripts. Intellij is used for Java. Some of the work environments use VSCode [dev containers](https://code.visualstudio.com/docs/remote/containers) so a Docker daemon is required to be running in the background.

Issues should have a reference to a specific commit, if reference some code. This allows the latest commit to always contain relevant live code only.

## Subdirectories

### debugger

A web app that should be hosted locally and viewed in browser. The app is used to visually debug error traces.
