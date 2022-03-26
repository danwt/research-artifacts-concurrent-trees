package driven;

import drachsler.modified.tisdall.DrachslerLogicalOrderingPluscal;
import org.jetbrains.kotlinx.lincheck.LinChecker;
import org.jetbrains.kotlinx.lincheck.Options;
import org.jetbrains.kotlinx.lincheck.annotations.Operation;
import org.jetbrains.kotlinx.lincheck.annotations.Param;
import org.jetbrains.kotlinx.lincheck.annotations.Validate;
import org.jetbrains.kotlinx.lincheck.paramgen.IntGen;
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.ModelCheckingOptions;
import org.jetbrains.kotlinx.lincheck.strategy.stress.StressOptions;
import org.jetbrains.kotlinx.lincheck.verifier.VerifierState;
import org.junit.jupiter.api.Test;
import util.KVMap;

import java.util.ArrayList;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertTrue;

@Param(name = "k", gen = IntGen.class, conf = "1:10")
public class LinCheckMRMWKVMap extends VerifierState {

    private final KVMap impl = new DrachslerLogicalOrderingPluscal();

    @Test
    public void stressTest() {
        StressOptions opts = new StressOptions();
        opts.iterations(100000);
        opts.threads(3);
        opts.invocationsPerIteration(10);
        opts.actorsPerThread(4);
        LinChecker.check(LinCheckMRMWKVMap.class, opts);
    }

    @Test
    public void modelChecking() {
        Options opts = new ModelCheckingOptions();
        opts.iterations(2028);
        opts.actorsPerThread(2);
        opts.threads(2);
        LinChecker.check(LinCheckMRMWKVMap.class, opts);
    }

    @Operation
    public Optional<Integer> get(@Param(name = "k") int k) {
        Optional<Integer> ret = impl.get(k);
        return ret;
    }

    @Operation
    public void insert(@Param(name = "k") int k) {
        impl.insert(k, k);
    }

    @Operation
    public void erase(@Param(name = "k") int k) {
        impl.erase(k);
    }

    @Validate
    public void checkProperties() {
        boolean hold = impl.desiredPropertiesHold();
        assertTrue(hold);
    }

    @Override
    protected Object extractState() {
        ArrayList<Boolean> ret = new ArrayList<>();

        for (int i = 1; i <= 10; i++) {
            ret.add(impl.get(i).isPresent());
        }

        return ret;
    }
}
