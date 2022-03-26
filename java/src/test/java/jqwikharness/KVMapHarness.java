package jqwikharness;

import util.KVMap;
import util.HashMapSeqKVMap;

public class KVMapHarness {

    KVMap impl;
    HashMapSeqKVMap oracle = new HashMapSeqKVMap();

    public KVMapHarness(KVMap impl) {
        this.impl = impl;
    }
}
