package crain;

import util.KVMap;

import java.util.Optional;

public class CrainBST extends KVMap {

    CrainContentionFriendly<Integer, Optional<Integer>> impl =
            new CrainContentionFriendly();

    public Optional<Integer> get(Integer k) {
        Optional<Integer> ret = impl.get(k);
        return ret == null ? Optional.empty() : ret;

    }

    public void insert(Integer k, Integer v) {
        // Warning: cannot truly model a KV map this way
        impl.putIfAbsent(k, Optional.of(v));
    }

    public void erase(Integer k) {
        impl.remove(k);
    }

}
