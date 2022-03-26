package tlc2.overrides;

import tlc2.value.impl.*;
import util.UniqueString;

import java.util.*;

/**
 * Contains methods for TLA+ to interact with pure Java tree generation functionality.
 */
public class TreeGeneration {

    /**
     * Intermediate representation of a tree
     * Used in intermediate state of converting a Node rooted tree
     * to a TLC value.
     */
    static class TreeRepr {

        // Map keys are 'addresses' in the TLA+ model
        // The address is actually equal to the key.
        Map<Integer, Integer> key = new HashMap<>();
        Map<Integer, Integer> val = new HashMap<>();
        Map<Integer, Integer> left = new HashMap<>();
        Map<Integer, Integer> rite = new HashMap<>();
        Map<Integer, Integer> height = new HashMap<>();
        Map<Integer, Integer> parent = new HashMap<>();

        // The set of reachable KEYS, not addresses
        Set<Integer> reachable = new HashSet<>();

        private void traverse(StandardAvlTreeGeneration.Node n) {

            if (n == null) {
                return;
            }

            reachable.add(n.k);
            key.put(n.k, n.k);
            val.put(n.k, n.k);

            if (n.left != null) {
                left.put(n.k, n.left.k);
                parent.put(n.left.k, n.k);
            }
            if (n.rite != null) {
                rite.put(n.k, n.rite.k);
                parent.put(n.rite.k, n.k);
            }

            height.put(n.k, StandardAvlTreeGeneration.height(n));
            traverse(n.left);
            traverse(n.rite);
        }

        TreeRepr(StandardAvlTreeGeneration.Node root) {

            traverse(root);

            /*
            We assume a RootHolder with address 0, whose
            right child is always the true logical root.
            */
            if (root != null) {
                rite.put(0, root.k);
                parent.put(root.k, 0);
            }
        }

        Value toRecord() {

            /*

            A starter state will be destructured like so

              key := starter_state.key;
              val := starter_state.val;
              left := starter_state.left;
              rite := starter_state.rite;
              height := starter_state.height;
              parent := starter_state.parent;
              reachable := starter_state.reachable;

            */

            UniqueString[] names = new UniqueString[]{
                    UniqueString.uniqueStringOf("key"),
                    UniqueString.uniqueStringOf("val"),
                    UniqueString.uniqueStringOf("left"),
                    UniqueString.uniqueStringOf("rite"),
                    UniqueString.uniqueStringOf("height"),
                    UniqueString.uniqueStringOf("parent"),
                    UniqueString.uniqueStringOf("reachable")
            };

            Value[] values = new Value[]{
                    toFunction(key),
                    toFunction(val),
                    toFunction(left),
                    toFunction(rite),
                    toFunction(height),
                    toFunction(parent),
                    toSet(reachable)
            };

            return new RecordValue(names, values, false);

        }

        static Value toFunction(Map<Integer, Integer> map) {

            Value[] domain = new Value[map.size()];
            Value[] values = new Value[map.size()];
            int i = 0;
            for (Map.Entry<Integer, Integer> entry : map.entrySet()) {
                domain[i] = IntValue.gen(entry.getKey());
                values[i] = IntValue.gen(entry.getValue());
                i++;
            }
            return new FcnRcdValue(domain, values, false);
        }

        static Value toSet(Set<Integer> set) {

            List<Value> vals = new ArrayList<>();
            for (Integer v : set) {
                vals.add(IntValue.gen(v));
            }

            return new SetEnumValue(new ValueVec(vals), false);
        }

    }

    static Value treesToValue(Set<StandardAvlTreeGeneration.Node> trees) {
        Value[] valArr = new Value[trees.size()];
        int i = 0;
        for (StandardAvlTreeGeneration.Node root : trees) {
            valArr[i] = new TreeRepr(root).toRecord();
            i++;
        }
        // TODO: not 100% sure what second arg actually means (used several times)
        return new SetEnumValue(valArr, false);
    }

    private static List<StandardAvlTreeGeneration.Node> getInitial(Value minKeyV, Value maxKeyV,
                                                                   Value minSizeV,
                                                                   Value maxSizeV) {

        Integer minKey = ((IntValue) minKeyV).val;
        Integer maxKey = ((IntValue) maxKeyV).val;
        Integer minSize = ((IntValue) minSizeV).val;
        Integer maxSize = ((IntValue) maxSizeV).val;

        if (maxKey < minKey || maxSize < minSize) {
            throw new IllegalArgumentException("Invalid minKey, maxKey or minSize, maxSize " +
                    "arguments passed to setOfInterestingAvlTrees");
        }

        return StandardAvlTreeGeneration.generateAllInterestingAvlTrees(minKey,
                maxKey, minSize, maxSize);

    }

    /**
     * TODO: I have no idea if using a static like this is a thread safe approach.
     */
    private static Value setOfInterestingAvlTreesCachedRet = null;

    @TLAPlusOperator(identifier = "SetOfInterestingAvlTrees", module = "TreeGeneration")
    public static Value setOfInterestingAvlTrees(Value minKeyV, Value maxKeyV, Value minSizeV,
                                                 Value maxSizeV) {
        if (setOfInterestingAvlTreesCachedRet == null) {

            System.out.println("SetOfInterestingAvlTrees called - building response.");

            List<StandardAvlTreeGeneration.Node> trees = getInitial(minKeyV, maxKeyV, minSizeV,
                    maxSizeV);

            Set<StandardAvlTreeGeneration.Node> keep = new HashSet<>(trees);

            setOfInterestingAvlTreesCachedRet = treesToValue(keep);
        }

        return setOfInterestingAvlTreesCachedRet;
    }

    @TLAPlusOperator(identifier = "InterestingAvlTree", module = "TreeGeneration")
    public static Value interestingAvlTree(Value minKeyV, Value maxKeyV, Value minSizeV,
                                           Value maxSizeV, Value itemIndex) {
        if (setOfInterestingAvlTreesCachedRet == null) {

            System.out.println("InterestingAvlTree called - building response.");

            List<StandardAvlTreeGeneration.Node> trees = getInitial(minKeyV, maxKeyV, minSizeV,
                    maxSizeV);

            Integer ix = ((IntValue) itemIndex).val;

            Set<StandardAvlTreeGeneration.Node> keep =
                    new HashSet<>();
            keep.add(trees.get(ix));
            setOfInterestingAvlTreesCachedRet = treesToValue(keep);
        }

        return setOfInterestingAvlTreesCachedRet;
    }

}
