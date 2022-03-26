package bronson.original;

import util.KVMap;

import java.util.Optional;

/**
 * The original Bronson implementation.
 * Note that the SnapTreeMap actually has some added methods for checking balance.
 */
public class BronsonOriginal extends KVMap {
    /**
     * NOTE:
     * We cannot do separate operations {contains, get} in a concurrent setting
     * but we also cannot use an Integer default. Therefore we wrap the values
     * in the implementation in an optional (but they will always be present).
     */
    SnapTreeMap<Integer, Optional<Integer>> impl =
            new SnapTreeMap<>();

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
