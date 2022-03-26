package jqwikharness;

import net.jqwik.api.stateful.Action;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class GetAction implements Action<KVMapHarness> {

    private final Integer k;

    GetAction(Integer k) {
        this.k = k;
    }

    @Override
    public KVMapHarness run(KVMapHarness harness) {
        Optional<Integer> implRes = harness.impl.get(k);
        Optional<Integer> oracleRes = harness.oracle.get(k);
        assertEquals(oracleRes, implRes);
        return harness;
    }

    @Override
    public String toString() {
        return String.format("get(%s)", k);
    }
}
