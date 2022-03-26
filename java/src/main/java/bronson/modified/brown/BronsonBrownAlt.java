package bronson.modified.brown;

import util.KVMap;

import java.util.Optional;

/**
 * Trevor Brown's Java implementation.
 */
public class BronsonBrownAlt extends KVMap {
    OptTreeMapBrown<Integer, Optional<Integer>> impl =
            new OptTreeMapBrown<>();

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
