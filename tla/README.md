# thesis-models

Contains TLA modelling working environment for thesis.

## Notes

```bash


# tla2tools.jar is 1.8.0 downloaded from github/tlaplus/tlaplus

# Custom lib location
# ~/documents/msc-papers/thesis-tla-library/out/artifacts/CustomTLALibrary_jar/CustomTLALibrary.jar

alias tlc='java -XX:+UseParallelGC -Xmx12g -cp ~/documents/msc-papers/thesis-tla-library/out/artifacts/CustomTLALibrary_jar/CustomTLALibrary.jar:~/documents/msc-papers/thesis-models/tla2tools.jar tlc2.TLC -workers 8 -checkpoint 0 -cleanup'

alias tojson='java -jar tla2json.jar'
```
