package brown;

/**
 * The original Drachsler implementation.
 */

import util.KVMap;

import java.util.Optional;

/**
 * TODO: I'm not yet sure of the exact technical guarantees the tree is supposed to offer
 * or how to correctly check its balance (it has complex sentinels).
 */
public class HooverBrown extends KVMap {

    /**
     * "When d = 0, each put() or remove() fixes any violation it created before
     * returning to the caller."
     */
    final int dParam = 0;

    LockFreeRelaxedAVLMap<Integer, Optional<Integer>> impl =
            new LockFreeRelaxedAVLMap<>(dParam);

    public Optional<Integer> get(Integer k) {
        Optional<Integer> found = impl.get(k);
        if (found == null) {
            return Optional.empty();
        }
        return found;
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
