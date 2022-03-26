package drachsler.modified.tisdall;

/**
 * The original Drachsler implementation.
 */

import util.KVMap;

import java.util.Optional;

public class DrachslerLogicalOrderingPluscal extends KVMap {

    final int keyMin = 0;
    final int keyMax = 1000;

    LogicalOrderingAVLPluscal impl =
            new LogicalOrderingAVLPluscal(keyMin, keyMax);

    public Optional<Integer> get(Integer k) {
        boolean doesContain = impl.get(k);
        return !doesContain ? Optional.empty() : Optional.of(k);
    }

    public void insert(Integer k, Integer v) {
        impl.insert(k);
    }

    public void erase(Integer k) {
        impl.remove(k);
    }

    @Override
    public boolean desiredPropertiesHold() {
        return impl.invariantsHold();
    }
}
