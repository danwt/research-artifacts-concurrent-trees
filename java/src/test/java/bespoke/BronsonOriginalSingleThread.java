package bespoke;

import bronson.original.BronsonOriginal;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Replicate the single thread imbalance error in the original Bronson implementation.
 */
public class BronsonOriginalSingleThread {

    /**
     * This test executes the operation sequence that JQwik found
     * in the original Bronson code that violates balance.
     *
     * It should fail.
     */
    @Test
    void singleThreadImbalance() {

        BronsonOriginal impl =
                new BronsonOriginal();

        impl.insert((Integer) 3, (Integer) 3);
        impl.insert((Integer) 1, (Integer) 1);
        impl.insert((Integer) 10, (Integer) 10);
        impl.insert((Integer) 6, (Integer) 6);
        impl.insert((Integer) 8, (Integer) 8);
        impl.insert((Integer) 40, (Integer) 40);
        impl.insert((Integer) 4, (Integer) 4);
        impl.insert((Integer) 2, (Integer) 2);
        impl.insert((Integer) 7, (Integer) 7);
        impl.insert((Integer) 39, (Integer) 39);
        impl.insert((Integer) 5, (Integer) 5);
        impl.erase((Integer) 39);
        assertTrue(impl.desiredPropertiesHold());
        impl.insert((Integer) 9, (Integer) 9);
        assertTrue(impl.desiredPropertiesHold());
    }
}
