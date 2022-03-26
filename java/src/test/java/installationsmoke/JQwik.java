package installationsmoke;

import net.jqwik.api.*;
import net.jqwik.api.constraints.*;

import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Confirm JQwik is installed and runs.
 */
class JQwik {

    public class MyCalculator {
        public int sum(int... addends) {
            return Arrays.stream(addends).sum();
        }
    }

    @Property
    boolean sumsOfSmallPositivesAreAlwaysPositive(@ForAll @Size(min = 1, max = 10) @IntRange(min = 1, max = 1000) int[] addends) {
        int result = new MyCalculator().sum(addends);
        return result > 0;
    }

    @Property
    void addingZeroToAnyNumberResultsInNumber(@ForAll int aNumber) {
        int result = new MyCalculator().sum(aNumber, 0);
        assertEquals(result,aNumber);
    }
}
