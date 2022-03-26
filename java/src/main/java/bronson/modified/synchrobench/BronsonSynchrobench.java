package bronson.modified.synchrobench;

import bronson.modified.brown.SnapTreeMapBrown;
import util.KVMap;

import java.util.Optional;

/**
 * The SnapTreeMap used in Synchrobench
 */
public class BronsonSynchrobench extends KVMap {
    SnapTreeMapSynchrobench<Integer, Optional<Integer>> impl =
            new SnapTreeMapSynchrobench<>();

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
