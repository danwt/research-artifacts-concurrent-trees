package tlc2.overrides;

import org.junit.Test;
import tlc2.overrides.StandardAvlTreeGeneration.Node;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class StandardAvlTreeGenerationTest {

    @Test
    public void interestingAvlTreeSetSizesAreReasonable() {
        List<Node> trees;

        trees = StandardAvlTreeGeneration.generateAllInterestingAvlTrees(2, 5, 4, 4);
        assertTrue(1 < trees.size());

        trees = StandardAvlTreeGeneration.generateAllInterestingAvlTrees(1, 5, 3, 5);
        assertTrue(5 < trees.size());

        trees = StandardAvlTreeGeneration.generateAllInterestingAvlTrees(1, 5, 3, 5);
        assertTrue(5 < trees.size());

        trees = StandardAvlTreeGeneration.generateAllInterestingAvlTrees(2, 5, 2, 5);
        assertTrue(trees.size() < 5);
    }

    @Test
    public void generateAvlsForKeyRangeIsDeterministic() {

        final int NUM_TESTS = 1000;

        Set<Integer> sizesSeen = new HashSet<>();
        for (int i = 0; i < NUM_TESTS; i++) {
            List<Node> nodes = StandardAvlTreeGeneration.generateAvlsForKeyRange(1, 6);
            sizesSeen.add(nodes.size());
        }

        assertEquals(1, sizesSeen.size());

    }

    @Test
    /**
     * Note this test depends on generateAvlsForKeyRangeIsDeterministic to hold.
     */
    public void isInterestingIsDeterministic() {

        final int NUM_TESTS = 1000;

        Set<Integer> sizesSeen = new HashSet<>();
        for (int i = 0; i < NUM_TESTS; i++) {
            List<Node> nodes = StandardAvlTreeGeneration.generateAvlsForKeyRange(1, 6);
            nodes.removeIf(it -> !StandardAvlTreeGeneration.isInteresting(it));
            sizesSeen.add(nodes.size());
        }

        assertEquals(1, sizesSeen.size());

    }

    @Test
    /**
     * Note this test depends on generateAvlsForKeyRangeIsDeterministic to hold.
     */
    public void retainUpToIsomorphismIsDeterministic() {

        final int NUM_TESTS = 1000;

        Set<Integer> sizesSeen = new HashSet<>();
        for (int i = 0; i < NUM_TESTS; i++) {
            List<Node> nodes = StandardAvlTreeGeneration.generateAvlsForKeyRange(2, 6);
            nodes = StandardAvlTreeGeneration.retainUpToIsomorphism(new ArrayList<>(nodes));
            sizesSeen.add(nodes.size());
        }

        assertEquals(1, sizesSeen.size());

    }

    @Test
    public void generateAllInterestingAvlTreesIsDeterministic() {

        final int NUM_TESTS = 1000;

        Set<Integer> sizesSeen = new HashSet<>();
        List<Integer> sizesSeenArr = new ArrayList<Integer>();
        for (int i = 0; i < NUM_TESTS; i++) {
            List<Node> nodes = StandardAvlTreeGeneration.generateAllInterestingAvlTrees(2,5,4,4);
            sizesSeenArr.add(nodes.size());
            sizesSeen.add(nodes.size());
        }

        assertEquals(1, sizesSeen.size());

    }
}