package jqwikharness;

import net.jqwik.api.stateful.Action;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class CheckPropertiesAction implements Action<KVMapHarness> {

    public CheckPropertiesAction(){}

    @Override
    public KVMapHarness run(KVMapHarness harness) {
        assertTrue(harness.impl.desiredPropertiesHold());
        return harness;
    }

    @Override
    public String toString() {
        return String.format("checkProperties");
    }
}
