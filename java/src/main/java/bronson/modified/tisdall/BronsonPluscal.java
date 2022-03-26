package bronson.modified.tisdall;

import util.KVMap;

import java.util.Optional;

/**
 * Aims to replicate the original bronson algorithm as closely as possible
 * and with easy translation to Pluscal.
 */
public class BronsonPluscal extends KVMap {

    SnapTreeMapPluscal impl = new SnapTreeMapPluscal();

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
