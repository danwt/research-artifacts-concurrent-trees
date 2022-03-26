package installationsmoke;

import org.jetbrains.kotlinx.lincheck.LinChecker;
import org.jetbrains.kotlinx.lincheck.annotations.Operation;
import org.jetbrains.kotlinx.lincheck.annotations.Param;
import org.jetbrains.kotlinx.lincheck.paramgen.IntGen;
import org.jetbrains.kotlinx.lincheck.strategy.stress.StressCTest;
import org.jetbrains.kotlinx.lincheck.verifier.VerifierState;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.util.HashMap;

/**
 * Confirm LinCheck is installed and runs.
 */
@StressCTest(minimizeFailedScenario = false)
@Param(name = "key", gen = IntGen.class, conf = "1:5")
@Param(name = "value", gen = IntGen.class, conf = "1:5")
public class LinCheck extends VerifierState {

    private final HashMap<Integer, Integer> map = new HashMap<>();

    @Operation
        public Integer put(@Param(name = "key") int key, @Param(name = "value") int value) {
        return map.put(key, value);
    }

    @Operation
    public Integer get(@Param(name = "key") int key) {
        return map.get(key);
    }

    @Test
    @Disabled
    public void test() {
        /*
        This test is supposed to fail!
        */
        LinChecker.check(LinCheck.class);
    }

    @Override
    protected Object extractState() {
        return map;
    }
}
