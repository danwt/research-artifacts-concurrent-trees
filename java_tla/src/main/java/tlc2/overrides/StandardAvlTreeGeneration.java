package tlc2.overrides;

import java.util.*;

/**
 * Contains methods to generate different kinds of AVL tree.
 * Currently supports these kinds of AVL trees:
 * 1. Standard AVL
 */
public class StandardAvlTreeGeneration {

    public static class Node {
        public Integer k;
        public Node left;
        public Node rite;
    }

    static Integer height(Node n) {
        if (n == null) {
            return 0;
        }
        return Math.max(height(n.left), height(n.rite)) + 1;
    }

    static Integer balanceFactor(Node n) {
        if (n == null) {
            return 0;
        }
        Integer lh = height(n.left);
        Integer rh = height(n.rite);
        return rh - lh;
    }

    static boolean balanced(Node n) {
        if (n == null) {
            return true;
        }
        return Math.abs(balanceFactor(n)) < 2;
    }

    /**
     * @return the set of trees formed by connecting the root key to each combination of children
     * in leftSet and riteSet. Only includes balanced trees.
     */
    static Set<Node> connectSets(Integer rootKey, List<Node> leftSet, List<Node> riteSet) {
        Set<Node> ret = new HashSet<Node>();
        for (Node left : leftSet) {
            for (Node rite : riteSet) {
                Node n = new Node();
                n.k = rootKey;
                n.left = left;
                n.rite = rite;

                // Filter out unbalanced nodes
                if (balanced(n)) {
                    ret.add(n);
                }
            }
        }
        return ret;
    }

    /**
     * Generate all standard avl trees with key values in range [low,high)
     *
     * @return
     */
    static List<Node> generateAvlsForKeyRange(Integer low, Integer high) {
        List<Node> ret = new ArrayList<>();
        ret.add(null); // We always want the empty tree
        for (int i = low; i < high; i++) {
            List<Node> leftSet = generateAvlsForKeyRange(low, i);
            List<Node> riteSet = generateAvlsForKeyRange(i + 1, high);
            ret.addAll(connectSets(i, leftSet, riteSet));
        }
        return ret;
    }

    static void inOrderVisitor(List<Integer> arr, Node curr) {

        if (curr == null) {
            return;
        }

        inOrderVisitor(arr, curr.left);
        arr.add(curr.k);
        inOrderVisitor(arr, curr.rite);
    }

    static List<Integer> inOrder(Node root) {
        List<Integer> ret = new ArrayList<>();
        inOrderVisitor(ret, root);
        return ret;
    }

    /**
     * Only keep interesting roots
     * A root is interesting if:
     * - It is not left heavy AND
     * - Its in-order traversal does not have any two adjacent elements with
     * difference more than the maximum specified gap.
     */
    static boolean isInteresting(Node root) {

        if (balanceFactor(root) < 0) {
            return false;
        }

        List<Integer> inOrder = inOrder(root);

        final int MAXIMUM_GAP = 1;
        for (int i = 0; i < inOrder.size() - 1; i++) {
            if (MAXIMUM_GAP < inOrder.get(i + 1) - inOrder.get(i)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Determines if two trees are isomorphic
     * Note: not the usual definition of isomorphic
     * We define two trees to be isomorphic if
     * - They have the same physical structure AND
     * - All <node, mirror node> pairs have the same difference in key values
     */
    static boolean areIsomorphic(Node a, Node b, Integer keyDifference) {
        if (a == null && b == null) {
            return true;
        }
        if (a == null || b == null) {
            return false;
        }
        if (b.k - a.k != keyDifference) {
            return false;
        }
        return areIsomorphic(a.left, b.left, keyDifference) &&
                areIsomorphic(a.rite, b.rite, keyDifference);
    }

    /**
     * N^2 check a list of trees and retain only those which are
     * isomorphic to no other.
     */
    static List<Node> retainUpToIsomorphism(List<Node> trees) {

        List<Node> ret = new ArrayList<>();

        /*
        In order to be deterministic, sort trees by root key descending.
         */
        trees.sort((a, b) -> {
            if (a == null || b == null) {
                return 0;
            }
            return a.k - b.k;
        });

        for (int i = 0; i + 1 < trees.size(); i++) {

            boolean isomorphicToNone = true;
            Node a = trees.get(i);

            for (int j = i + 1; j < trees.size(); j++) {
                Node b = trees.get(j);
                if (a != null && b != null) {
                    boolean areIso = areIsomorphic(a, b, b.k - a.k);
                    isomorphicToNone = isomorphicToNone && !areIso;
                }
            }

            if (isomorphicToNone) {
                ret.add(a);
            }
        }

        return ret;
    }

    /**
     * @param minKey  the minimum key value that any tree in the set can have
     * @param maxKey  the maximum key value that any tree in the set can have (inclusive)
     * @param minSize the minimum number of nodes that any tree in the set can have
     * @param maxSize the maximum number of nodes that any tree in the set can have (inclusive)
     * @return a set of 'interesting' trees matching the criteria
     */
    static List<Node> generateAllInterestingAvlTrees(Integer minKey, Integer maxKey,
                                                     Integer minSize,
                                                     Integer maxSize) {

        List<Node> ret = generateAvlsForKeyRange(minKey, maxKey + 1);

        ret.removeIf(it -> !isInteresting(it));

        ret = retainUpToIsomorphism(new ArrayList<>(ret));

        ret.removeIf(it -> {
            Integer sz = inOrder(it).size();
            return sz < minSize || maxSize < sz;
        });

        if (ret.isEmpty()) {
            throw new IllegalArgumentException("Set of generated AVL trees is empty, this will " +
                    "cause TLC to deadlock");
        }

        /**
         * TODO: This is a massive hack to get some determinism
         * Note that I should definitely fix the tests to not be misleading
         * about determinisim (right now determinisim from most methods is only up to
         * return set size, not order).
         */
        class ListComparator<T extends Comparable<T>> implements Comparator<List<T>> {

            @Override
            public int compare(List<T> o1, List<T> o2) {
                for (int i = 0; i < Math.min(o1.size(), o2.size()); i++) {
                    int c = o1.get(i).compareTo(o2.get(i));
                    if (c != 0) {
                        return c;
                    }
                }
                return Integer.compare(o1.size(), o2.size());
            }

        }

        class Comp implements Comparator<Node> {
            ListComparator<Integer> impl = new ListComparator<>();

            @Override
            public int compare(Node a, Node b) {
                List<Integer> o1 = inOrder(a);
                List<Integer> o2 = inOrder(b);
                for (int i = 0; i < Math.min(o1.size(), o2.size()); i++) {
                    int c = o1.get(i).compareTo(o2.get(i));
                    if (c != 0) {
                        return c;
                    }
                }
                o1.clear();
                o2.clear();
                depths(o1,a,0);
                depths(o2,b,0);
                for (int i = 0; i < Math.min(o1.size(), o2.size()); i++) {
                    int c = o1.get(i).compareTo(o2.get(i));
                    if (c != 0) {
                        return c;
                    }
                }
                return Integer.compare(o1.size(),o2.size());
            }

            private void depths(List<Integer> fill, Node node, Integer depth){
                if(node==null){
                    return;
                }
                depths(fill,node.left,depth+1);
                fill.add(depth);
                depths(fill,node.rite,depth+1);
            }
        }

        Collections.sort(ret, new Comp());
        return ret;

    }

}