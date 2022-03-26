package util;

import java.util.Optional;

public abstract class KVMap {
    abstract public Optional<Integer> get(Integer k);
    abstract public void insert(Integer k, Integer v);
    abstract public void erase(Integer k);
    public boolean desiredPropertiesHold(){
        return true;
    };
}
