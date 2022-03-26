package jqwikharness;

import net.jqwik.api.stateful.Action;

public class InsertAction implements Action<KVMapHarness> {

    private final Integer k;

    InsertAction(Integer k) {
        this.k = k;
    }

    @Override
    public KVMapHarness run(KVMapHarness harness) {
        harness.impl.insert(k, k);
        harness.oracle.insert(k, k);
        return harness;
    }

    @Override
    public String toString() {
        return String.format("insert(%s, %s)", k, k);
    }
}
