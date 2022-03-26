package bronson.modified.tisdall;

import util.KVMap;

import java.util.Optional;

/**
 * Full retry iterative - includes both the partial fixes due to Trevor Brown
 * as well as removal of separate double rotate functions.
 */
public class BronsonIterativeSimpleRotatesFixing extends KVMap {

    SnapTreeMapIterativeSimpleRotatesFixing impl = new SnapTreeMapIterativeSimpleRotatesFixing();

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
