package bespoke;

import bronson.modified.brown.BronsonBrown;
import bronson.modified.brown.BronsonBrownAlt;
import bronson.modified.tisdall.BronsonIterativeSimpleRotates;
import bronson.modified.tisdall.BronsonPluscal;
import bronson.modified.tisdall.SnapTreeMapIterativeSimpleRotates;
import bronson.modified.synchrobench.BronsonSynchrobench;
import bronson.original.BronsonOriginal;
import lombok.AllArgsConstructor;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import util.KVMap;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Replicate the imbalance violations found on two threads, present in
 * both the original Bronson algorithm as well as in the Java version due to Trevor Brown.
 *
 * Replicate the linearizability violation found on two threads
 */
public class BronsonTwoThread {

    String writePath(String name) {
        return "java_bronsonDebug" + name + ".json";
    }

    List<Integer> startKeys = new ArrayList<>();

    BronsonTwoThread() {
        startKeys.add(5);
        startKeys.add(4);
        startKeys.add(8);
        startKeys.add(3);
        startKeys.add(7);
        startKeys.add(10);
        startKeys.add(6);
        startKeys.add(9);
    }

    @Test
    @Disabled
    /**
     * Used to verify that indeed the correct start state is being used.
     */
    void checkStartState() {
        SnapTreeMapIterativeSimpleRotates map = new SnapTreeMapIterativeSimpleRotates();

        startKeys.forEach(it -> map.update(it, it));

//        JsonGraph.writeJson(DebugUtil.edgeList(map.rootHolder), writePath("0"));
    }

    @AllArgsConstructor
    public class Eraser implements Runnable {

        private KVMap kvmap;
        private int key;

        public void run() {
            kvmap.erase(key);
        }
    }

    @Test
    void bronsonSynchrobench() {
        // Fails
        testImbalance(BronsonSynchrobench::new);
    }

    @Test
    void bronsonIterativeSimpleRotates() {
        // Known to fail
        testImbalance(BronsonIterativeSimpleRotates::new);
    }

    @Test
    void bronsonBrownAlt() {
        // Known to fail
        testImbalance(BronsonBrownAlt::new);
    }

    @Test
    void bronsonBrown() {
        // Known to fail
        testImbalance(BronsonBrown::new);
    }

    @Test
    void bronsonPluscal() {
        // Known to fail
        testImbalance(BronsonPluscal::new);
    }

    @Test
    void bronsonOriginal() {
        // Known to fail
        testImbalance(BronsonOriginal::new);
    }

    void testImbalance(Supplier<KVMap> sup) {

        final int numRuns = 100000;
        for (int i = 0; i < numRuns; i++) {
            KVMap map = sup.get();
            startKeys.forEach(it -> map.insert(it, it));
            assertTrue(map.desiredPropertiesHold());
            Thread t0 = new Thread(new Eraser(map, 4));
            Thread t1 = new Thread(new Eraser(map, 9));
            t0.start();
            t1.start();
            try {
                t0.join();
            } catch (Exception e) {
                fail("Could not join t0");
            }
            try {
                t1.join();
            } catch (Exception e) {
                fail("Could not join t1");
            }
            assertTrue(map.desiredPropertiesHold(), String.valueOf(i));
        }
    }

    void testLinearizability(Supplier<KVMap> sup) {
        /*
        I can't remember what I used this for.
         */
        final int numRuns = 10000000;
        for (int i = 0; i < numRuns; i++) {
            KVMap map = sup.get();
            startKeys.forEach(it -> map.insert(it, it));
            Thread t0 = new Thread(new Eraser(map, 6));
            Thread t1 = new Thread(new Eraser(map, 7));
            t1.start();
            t0.start();
            try {
                t0.join();
            } catch (Exception e) {
                fail("Could not join t0");
            }
            try {
                t1.join();
            } catch (Exception e) {
                fail("Could not join t1");
            }
            assertTrue(map.get(6).isEmpty(), String.valueOf(i));
            assertTrue(map.get(7).isEmpty(), String.valueOf(i));
        }
    }


}
