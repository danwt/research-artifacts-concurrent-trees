package driven;

import chunked.*;
import bronson.modified.brown.BronsonBrown;
import bronson.modified.tisdall.*;
import bronson.original.BronsonOriginal;
import brown.HooverBrown;
import drachsler.modified.tisdall.DrachslerLogicalOrderingPluscal;
import drachsler.original.DrachslerLogicalOrderingOriginal;
import jqwikharness.KVMapActionGenerator;
import jqwikharness.KVMapHarness;
import net.jqwik.api.*;
import net.jqwik.api.stateful.ActionSequence;
import util.KVMap;

public class JQwikSequentialKVMap {

    final int keyMin = 1;
    final int keyMax = 40;

    KVMapActionGenerator actionGenerator = new KVMapActionGenerator(keyMin, keyMax);

    /**
     * ---------------------------------------------------------
     * Hoover and Brown AVL
     */

    @Property
    void checkHooverBrown(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new HooverBrown(), actions);
    }

    /**
     * ---------------------------------------------------------
     * Drachsler AVL
     */

    @Property
    void checkDrachslerLogicalOrdering(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new DrachslerLogicalOrderingOriginal(), actions);
    }

    @Property
    void checkDrachslerLogicalOrderingPluscal(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new DrachslerLogicalOrderingPluscal(), actions);
    }

    /**
     * ---------------------------------------------------------
     * Bronson AVL
     */

    @Property
    void checkBronsonIterativeSimpleRotatesFixing(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonIterativeSimpleRotatesFixing(), actions);
    }

    @Property
    void checkBronsonIterativeSimpleRotates(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonIterativeSimpleRotates(), actions);
    }

    @Property
    void checkBronsonIterativeBrown(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonIterativeBrown(), actions);
    }

    @Property
    void checkBronsonBrown(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonBrown(), actions);
    }

    @Property
    @Disabled
        // Will fail as original is faulty for a single thread
    void checkBronsonIterative(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonIterative(), actions);
    }

    @Property
    @Disabled
        // Will fail as original is faulty for a single thread
    void checkBronsonPluscal(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonPluscal(), actions);
    }

    @Property
    @Disabled
        // Will fail as original is faulty for a single thread
    void checkBronsonOriginal(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new BronsonOriginal(), actions);
    }

    /**
     * ---------------------------------------------------------
     * Chunked AVL
     */

    @Property
    void checkSeqRecursiveMapBased(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new SeqCAvlRecursiveMapBased(), actions);
    }

    @Property
    void checkSeqIterativeMapBased(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new SeqCAvlIterativeMapBased(), actions);
    }

    @Property
    void checkMRSWIterativeFullRetryMapBased(@ForAll("sequences") ActionSequence<KVMapHarness> actions) {
        runTest(new MRSWCAvlIterativeFullRetryMapBased(), actions);
    }

    void runTest(KVMap impl, ActionSequence<KVMapHarness> actions) {
        actions.run(new KVMapHarness(impl));
    }

    @Provide
    Arbitrary<ActionSequence<KVMapHarness>> sequences() {
        return Arbitraries.sequences(Arbitraries.oneOf(
                actionGenerator.get(),
                actionGenerator.insert(),
                actionGenerator.erase(),
                actionGenerator.checkProperties())
        );
    }

}
