package jqwikharness;

import lombok.AllArgsConstructor;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.stateful.Action;

@AllArgsConstructor
public class KVMapActionGenerator {

    private int keyMin = 1;
    private int keyMax = 40;

    public Arbitrary<Action<KVMapHarness>> get() {
        return Arbitraries.integers().between(keyMin, keyMax).map(GetAction::new);
    }

    public Arbitrary<Action<KVMapHarness>> insert() {
        return Arbitraries.integers().between(keyMin, keyMax).map(InsertAction::new);
    }

    public Arbitrary<Action<KVMapHarness>> erase() {
        return Arbitraries.integers().between(keyMin, keyMax).map(EraseAction::new);
    }

    public Arbitrary<Action<KVMapHarness>> checkProperties() {
        return Arbitraries.create(CheckPropertiesAction::new);
    }
}
