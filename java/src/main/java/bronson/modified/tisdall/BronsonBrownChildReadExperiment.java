package bronson.modified.tisdall;

import util.KVMap;

import java.util.Optional;

/**
 * Trevor Brown's Java implementation.
 */
public class BronsonBrownChildReadExperiment extends KVMap {
    SnapTreeMapBrownChildReadExperiment<Integer, Optional<Integer>> impl =
            new SnapTreeMapBrownChildReadExperiment<>();

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
