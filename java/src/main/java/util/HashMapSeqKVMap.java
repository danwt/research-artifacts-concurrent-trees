package util;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

public class HashMapSeqKVMap extends KVMap {

    public Map<Integer, Integer> impl = new HashMap<>();

    public Optional<Integer> get(Integer k) {
        if (!impl.containsKey(k)) {
            return Optional.empty();
        }
        return Optional.of(impl.get(k));
    }

    public void insert(Integer k, Integer v) {
        impl.put(k, v);
    }

    public void erase(Integer k) {
        impl.remove(k);
    }
}