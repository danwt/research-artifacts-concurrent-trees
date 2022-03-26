package bronson.modified.tisdall;

import util.KVMap;

import java.util.Optional;

/**
 * Full retry iterative - without any changes to balance algorithms.
 */
public class BronsonIterative extends KVMap {

    SnapTreeMapIterative impl = new SnapTreeMapIterative();

    public Optional<Integer> get(Integer k) {
        Integer res = impl.get(k);
        if (res == null) {
            return Optional.empty();
        } else {
            return Optional.of(res);
        }
    }

    public void insert(Integer k, Integer v) {
        impl.update(k, v);
    }

    public void erase(Integer k) {
        impl.update(k, null);
    }

    @Override
    public boolean desiredPropertiesHold() {
        return impl.invariantsHold();
    }
}
