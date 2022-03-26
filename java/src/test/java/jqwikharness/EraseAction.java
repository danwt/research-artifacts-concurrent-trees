package jqwikharness;

import net.jqwik.api.stateful.Action;

public class EraseAction implements Action<KVMapHarness> {

    private final Integer k;

    EraseAction(Integer k) {
        this.k = k;
    }

    @Override
    public KVMapHarness run(KVMapHarness harness) {
        harness.impl.erase(k);
        harness.oracle.erase(k);
        return harness;
    }

    @Override
    public String toString() {
        return String.format("erase(%s)", k);
    }
}
