package bronson.modified.brown;

import util.KVMap;

import java.util.Optional;

/**
 * Trevor Brown's Java implementation.
 */
public class BronsonBrown extends KVMap {
    SnapTreeMapBrown<Integer, Optional<Integer>> impl =
            new SnapTreeMapBrown();

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
