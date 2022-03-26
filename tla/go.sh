tlc='java -XX:+UseParallelGC -Xmx12g -cp ~/documents/msc-papers/thesis-tla-library/out/artifacts/CustomTLALibrary_jar/CustomTLALibrary.jar:~/documents/msc-papers/thesis-models/tla2tools.jar tlc2.TLC -workers 8 -checkpoint 0 -coverage 9999 -cleanup';
tojson='java -jar tla2json.jar';
$tlc models/avl_chunked/traversal.tla > log.txt;
$tojson log.txt > log.json;
python3 interpret.py;