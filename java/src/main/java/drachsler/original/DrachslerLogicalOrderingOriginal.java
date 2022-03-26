package drachsler.original;

/**
 * The original Drachsler implementation.
 */

import util.KVMap;

import java.util.Optional;

public class DrachslerLogicalOrderingOriginal extends KVMap {

    final int keyMin = 0;
    final int keyMax = 1000;

    LogicalOrderingAVL<Integer, Optional<Integer>> impl =
            new LogicalOrderingAVL<>(keyMin, keyMax);

    public Optional<Integer> get(Integer k) {
        return impl.getOrDefault(k, Optional.empty());
    }

    public void insert(Integer k, Integer v) {
        impl.put(k, Optional.of(v));
    }

    public void erase(Integer k) {
        impl.remove(k);
    }

    @Override
    public boolean desiredPropertiesHold() {
        return impl.invariantsHold();
    }
}
