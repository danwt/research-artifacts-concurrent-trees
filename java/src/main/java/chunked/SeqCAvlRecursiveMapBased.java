package chunked;

import lombok.NoArgsConstructor;
import util.JsonGraph;
import util.KVMap;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;

public class SeqCAvlRecursiveMapBased extends KVMap {

    @NoArgsConstructor
    private class Node {
        Integer k;
        Optional<Integer> v = Optional.empty();

        Node left;
        Node rite;
        Node parent;

        int height = 1;

        Chunk chunk;

        Node(Integer k, Node left, Node rite, int height) {
            this.k = k;
            this.left = left;
            this.rite = rite;
            this.height = height;
        }

        boolean isLeaf() {
            return v.isPresent();
        }

        boolean isChunkRoot() {
            return chunk != null;
        }
    }

    @NoArgsConstructor
    private class Chunk {

        Map<Integer, Node> leftWing = new TreeMap<>();
        Map<Integer, Node> riteWing = new TreeMap<>();
        int id;
        Node root;

        Chunk(int id) {
            this.id = id;
        }

        int size() {
            return leftWing.size() + riteWing.size();
        }

        static void erase(Map<Integer, Node> chunkMap, Integer k) {
            chunkMap.remove(k);
        }

        Node insertLeft(Integer k, Integer v, Node parent) {
            Node node = new Node();
            leftWing.put(k, node);
            writeNode(node, k, v, parent);
            return node;
        }

        Node insertRite(Integer k, Integer v, Node parent) {
            Node node = new Node();
            riteWing.put(k, node);
            writeNode(node, k, v, parent);
            return node;
        }

        void shiftLeft(Integer minKeyToKeep) {
            shift(riteWing, leftWing, (Integer k) -> k < minKeyToKeep);
        }

        void shiftRite(Integer minKeyToMove) {
            shift(leftWing, riteWing, (Integer k) -> minKeyToMove <= k);
        }

        static void writeNode(Node node, Integer k, Integer v, Node parent) {
            node.k = k;
            node.v = Optional.of(v);
            node.parent = parent;

            if (node.parent == null) {
                return;
            }

            if (node.parent.left != null && node.parent.left.k.equals(k)) {
                node.parent.left = node;
                return;
            }

            assert node.parent.rite != null;

            node.parent.rite = node;
        }

        void shift(Map<Integer, Node> from, Map<Integer, Node> to,
                   Function<Integer, Boolean> pred) {
            assert (root != null);

            Set<Integer> toRemove = new HashSet<>();

            from.forEach((k, n) -> {
                if (pred.apply(n.k)) {
                    Node node = new Node();
                    to.put(n.k, node);
                    writeNode(node, n.k, n.v.get(), n.parent);
                    toRemove.add(n.k);
                }
            });

            toRemove.forEach(it -> from.remove(it));
        }
    }

    static final int MAX_CHUNK_SIZE = 8;

    int nextChunkId = 0;

    // Use nonsense values for key and height, they will never be seen.
    volatile Node rootHolder = new Node(-42, null, null, -42);

    List<Chunk> chunks = new ArrayList<>();
    List<Node> innerNodes = new ArrayList<>();

    private static boolean isLeftChildOf(Node parent, Node child) {
        return parent.left == child;
    }

    private static int leftHeight(Node node) {
        if (node.left != null) {
            return node.left.height;
        }
        return 0;
    }

    private static int riteHeight(Node node) {
        if (node.rite != null) {
            return node.rite.height;
        }
        return 0;
    }

    /**
     * @param node
     * @return RiteHeight - LeftHeight
     */
    private static int balanceFactor(Node node) {
        return riteHeight(node) - leftHeight(node);
    }

    /**
     * @param node
     * @return abs(RiteHeight - LeftHeight) < 2
     */
    private static boolean isBalanced(Node node) {
        return Math.abs(balanceFactor(node)) < 2;
    }

    private static void adjustNodeHeight(Node node) {
        node.height = Math.max(leftHeight(node), riteHeight(node)) + 1;
    }

    private Node createNonLeaf(Integer k, Node left, Node rite) {
        Node ret = new Node(k, left, rite, 2);
        innerNodes.add(ret);
        left.parent = ret;
        rite.parent = ret;
        return ret;
    }

    private Chunk createNextChunk() {
        Chunk ret = new Chunk(nextChunkId++);
        chunks.add(ret);
        return ret;
    }

    private void destroyChunk(Chunk chunk) {
        chunks.removeIf(it -> it.id == chunk.id);
    }

    private void destroyNonLeaf(Node node) {
        innerNodes.removeIf(it -> it == node);
    }

    private void splitLeftWingIntoNewChunk(Node node) {

        Chunk c = node.chunk;
        Chunk newChunk = createNextChunk();

        node.chunk.leftWing.forEach((k, n) -> {
            if (n.k < node.left.k) {
                newChunk.insertLeft(n.k, n.v.get(), n.parent);
            } else {
                newChunk.insertRite(n.k, n.v.get(), n.parent);
            }
        });

        newChunk.root = node.left;
        newChunk.root.chunk = newChunk;

        c.root.chunk = null;
        c.root = node.rite;
        c.root.chunk = c;

        c.leftWing.clear();
        c.shiftLeft(node.rite.k);

    }

    Optional<Integer> getImpl(Integer k, Node curr) {
        if (curr == null) {
            return Optional.empty();
        }
        if (curr.isLeaf() && curr.k.equals(k)) {
            return curr.v;
        }
        if (k < curr.k) {
            return getImpl(k, curr.left);
        }
        return getImpl(k, curr.rite);
    }

    public Optional<Integer> get(Integer k) {
        return getImpl(k, rootHolder.rite);
    }

    private Node rotateLeft(Node pivot) {

        assert (!pivot.rite.isLeaf());

        if (pivot.isChunkRoot()) {
            pivot.chunk.shiftLeft(pivot.rite.k);
            pivot.chunk.root = pivot.rite;
            pivot.rite.chunk = pivot.chunk;
            pivot.chunk = null;
        } else if (pivot.rite.isChunkRoot()) {
            splitLeftWingIntoNewChunk(pivot.rite);
        }

        Node newPivot = pivot.rite;
        newPivot.parent = pivot.parent;
        pivot.rite = newPivot.left;
        newPivot.left.parent = pivot;
        newPivot.left = pivot;
        pivot.parent = newPivot;

        adjustNodeHeight(newPivot.left);
        adjustNodeHeight(newPivot);

        return newPivot;
    }

    private Node rotateRite(Node pivot) {

        assert (!pivot.left.isLeaf());

        if (pivot.isChunkRoot()) {
            pivot.chunk.shiftRite(pivot.left.k);
            pivot.chunk.root = pivot.left;
            pivot.left.chunk = pivot.chunk;
            pivot.chunk = null;
        } else if (pivot.left.isChunkRoot()) {
            splitLeftWingIntoNewChunk(pivot.left);
        }

        Node newPivot = pivot.left;
        newPivot.parent = pivot.parent;
        pivot.left = newPivot.rite;
        newPivot.rite.parent = pivot;
        newPivot.rite = pivot;
        pivot.parent = newPivot;

        adjustNodeHeight(newPivot.rite);
        adjustNodeHeight(newPivot);

        return newPivot;
    }

    private Node rotate(Node pivot) {
        Integer bal = balanceFactor(pivot);
        if (bal < -1) {
            if (0 < balanceFactor(pivot.left)) {
                pivot.left = rotateLeft(pivot.left);
            }
            pivot = rotateRite(pivot);
        } else if (1 < bal) {
            if (balanceFactor(pivot.rite) < 0) {
                pivot.rite = rotateRite(pivot.rite);
            }
            pivot = rotateLeft(pivot);
        }
        return pivot;
    }

    private void rebalance(Node curr) {
        while (curr.parent != null) {

            adjustNodeHeight(curr);

            Node parent = curr.parent;

            if (isBalanced(curr)) {
                curr = parent;
                continue;
            }

            if (isLeftChildOf(parent, curr)) {
                parent.left = rotate(parent.left);
            } else {
                parent.rite = rotate(parent.rite);
            }

            curr = parent;
        }
    }

    void insertImpl(Integer k, Integer v, Node curr, Chunk c) {

        if (curr.isChunkRoot()) {
            c = curr.chunk;
            if (c.size() == MAX_CHUNK_SIZE) {
                splitLeftWingIntoNewChunk(curr);
                c = null;
            }
        }

        if (!curr.isLeaf()) {
            if (k < curr.k) {
                insertImpl(k, v, curr.left, c);
                return;
            }
            insertImpl(k, v, curr.rite, c);
            return;
        }

        if (k.equals(curr.k)) {
            curr.v = Optional.of(v);
            return;
        }

        assert c != null;

        Node inserted;

        if (k < c.root.k) {
            inserted = c.insertLeft(k, v, null);
        } else {
            inserted = c.insertRite(k, v, null);
        }

        Node parent = curr.parent;

        boolean currIsLeftChild = isLeftChildOf(parent, curr);

        Node newLeafParent;

        if (k < curr.k) {
            newLeafParent = createNonLeaf(curr.k, inserted, curr);
        } else {
            newLeafParent = createNonLeaf(k, curr, inserted);
        }

        if (currIsLeftChild) {
            parent.left = newLeafParent;
        } else {
            parent.rite = newLeafParent;
        }

        newLeafParent.parent = parent;

        if (curr.isChunkRoot()) {
            newLeafParent.chunk = c;
            c.root = newLeafParent;
            curr.chunk = null;
            newLeafParent.chunk.shiftLeft(k);
        }

        rebalance(newLeafParent.parent);
        return;
    }

    public void insert(Integer k, Integer v) {

        if (rootHolder.rite == null) {
            Chunk chunk = createNextChunk();
            rootHolder.rite = chunk.insertRite(k, v, null);
            rootHolder.rite.parent = rootHolder;
            rootHolder.rite.chunk = chunk;
            chunk.root = rootHolder.rite;
            return;
        }

        insertImpl(k, v, rootHolder.rite, null);

    }

    private void bindParentToNewChild(Node parent, Node oldChild, Node replacementChild) {
        if (isLeftChildOf(parent, oldChild)) {
            parent.left = replacementChild;
            parent.left.parent = parent;
            return;
        }
        parent.rite = replacementChild;
        parent.rite.parent = parent;
    }

    private void doErase(Integer k, Node curr, Node nonLeafWithKeyK, Chunk c) {
        Node parent = curr.parent;
        if (curr.isChunkRoot()) {
            destroyChunk(c);
            if (parent == rootHolder) {
                rootHolder.rite = null;
                return;
            }
        } else {
            if (k < c.root.k) {
                c.erase(c.leftWing, k);
            } else {
                c.erase(c.riteWing, k);
            }
        }

        Node parentParent = parent.parent;

        if (nonLeafWithKeyK == null) {
            if (parent.isChunkRoot()) {
                c.root = parent.rite;
                c.root.chunk = c;
                c.shiftLeft(c.root.k);
            }
            bindParentToNewChild(parentParent, parent, parent.rite);
        } else if (nonLeafWithKeyK == parent) {
            if (parent.isChunkRoot()) {
                c.shiftRite(parent.left.k);
                c.root = parent.left;
                c.root.chunk = c;
            }
            bindParentToNewChild(parentParent, parent, parent.left);
        } else {
            if (parent.isChunkRoot()) {
                c.root = parent.rite;
                c.root.chunk = c;
                c.shiftLeft(c.root.k);
            }
            nonLeafWithKeyK.k = parent.k;
            if (parentParent == nonLeafWithKeyK) {
                parentParent.rite = parent.rite;
            } else {
                parentParent.left = parent.rite;
            }
            parent.rite.parent = parentParent;
        }

        destroyNonLeaf(parent);

        rebalance(parentParent);

    }

    void eraseImpl(Integer k, Node curr, Node nonLeafWithKeyK, Chunk c) {
        if (curr == null) {
            return;
        }
        if (curr.isChunkRoot()) {
            c = curr.chunk;
        }
        if (curr.k.equals(k)) {
            if (curr.isLeaf()) {
                doErase(k, curr, nonLeafWithKeyK, c);
                return;
            }
            nonLeafWithKeyK = curr;

        }
        if (k < curr.k) {
            eraseImpl(k, curr.left, nonLeafWithKeyK, c);
            return;
        }
        eraseImpl(k, curr.rite, nonLeafWithKeyK, c);
    }

    public void erase(Integer k) {
        eraseImpl(k, rootHolder.rite, null, null);
    }

    /*
    ~~~~~~~~~~~~~~~~
    Duplicate code for checking invariants
     */

    static class Recursive<F> {
        F fun;
        boolean good = true;
    }

    boolean parentsAreConnected() {

        Recursive<Consumer<Node>> f =
                new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return;
            }
            f.fun.accept(node.left);
            f.fun.accept(node.rite);
            if(node.rite != null && node.rite.parent != node){
                f.good = false;
            }
            if(node.left != null && node.left.parent != node){
                f.good = false;
            }
        };

        f.fun.accept(rootHolder.rite);

        return f.good;
    }

    boolean heightsFieldsAreCorrect() {

        Recursive<Function<Node, Integer>> f =
                new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return 0;
            }
            int lh = f.fun.apply(node.left);
            int rh = f.fun.apply(node.rite);
            int h = Math.max(lh, rh) + 1;
            if (node.height != h) {
                f.good = false;
            }
            return h;
        };

        f.fun.apply(rootHolder.rite);

        return f.good;
    }

    public boolean trueBalance() {

        Recursive<Function<Node, Integer>> f =
                new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return 0;
            }
            int lh = f.fun.apply(node.left);
            int rh = f.fun.apply(node.rite);
            if (1 < Math.abs(rh - lh)) {
                f.good = false;
            }
            return Math.max(lh, rh) + 1;
        };

        f.fun.apply(rootHolder.rite);

        return f.good;
    }

    @Override
    public boolean desiredPropertiesHold() {
        boolean good = true;
        good = good && trueBalance();
        good = good && heightsFieldsAreCorrect();
        good = good && parentsAreConnected();
        if (!good) {
            dumpGraph();
        }
        return good;
    }

    public void dumpGraph() {

        Map<Node, JsonGraph.Node> nodes = new HashMap<>();

        List<JsonGraph.Edge> edges = new ArrayList<>();

        Consumer<Node> insert = node -> {
            nodes.put(node, new JsonGraph.Node(node.hashCode(), node.k.toString(),
                    node.v.isPresent() ? node.v.get().toString() : "None", node.isChunkRoot(), node.isLeaf(), node.height));
        };

        Recursive<Consumer<Node>> f =
                new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return;
            }

            if (!nodes.containsKey(node)) {
                insert.accept(node);
            }

            if (node.left != null && !nodes.containsKey(node.left)) {
                insert.accept(node.left);
            }

            if (node.rite != null && !nodes.containsKey(node.rite)) {
                insert.accept(node.rite);
            }

            if (node.parent != null) {
                JsonGraph.Node self = nodes.get(node);
                JsonGraph.Node parent = nodes.get(node.parent);
                edges.add(new JsonGraph.Edge(self, parent, "parent"));
            }

            if (node.left != null) {
                JsonGraph.Node self = nodes.get(node);
                JsonGraph.Node left = nodes.get(node.left);
                edges.add(new JsonGraph.Edge(self, left, "left"));
            }

            if (node.rite != null) {
                JsonGraph.Node self = nodes.get(node);
                JsonGraph.Node rite = nodes.get(node.rite);
                edges.add(new JsonGraph.Edge(self, rite, "rite"));
            }

            f.fun.accept(node.left);
            f.fun.accept(node.rite);
        };

        f.fun.accept(rootHolder);

        JsonGraph.writeJson(edges, "/Users/danwt/documents/msc-papers/thesis-scratch-space/dump/seqcavlrecursivemapbasedcppcopy.json");
    }

}
