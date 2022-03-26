package bronson.modified.tisdall;

import util.KVMap;

import java.util.Optional;

/**
 * Full retry iterative - with partial fixes due to Trevor Brown.
 */
public class BronsonIterativeBrown extends KVMap {

    SnapTreeMapIterativeBrown impl = new SnapTreeMapIterativeBrown();

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
