package drachsler.modified.tisdall;

import lombok.AllArgsConstructor;

import java.util.Optional;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.Consumer;
import java.util.function.Function;

public class LogicalOrderingAVLPluscal {

    private Node root;

    Integer compareSpecial(Integer key, Integer other) {
        if (key < other) {
            return -1;
        }
        if (key == other) {
            return 0;
        }
        return 1;
    }

    /**
     * Constructor, initialize the tree and the logical ordering layouts.
     * The logical ordering is initialized by creating two nodes, where their
     * keys are the minimal and maximal values.
     * The tree layout is initialized by setting the root to point to the node
     * with the maximal value.
     *
     * @param min The minimal value
     * @param max The maximal value
     */
    public LogicalOrderingAVLPluscal(Integer min, Integer max) {
        Node parent = new Node(min);
        root = new Node(max, null, parent, parent, parent);
        root.parent = parent;
        parent.rite = root;
        parent.succ = root;
    }


    public boolean get(Integer key) {
        Node node = root;
        Node child = new Node(42); // use any non-null value
        Integer nodeKey;
        int dirNodeKeyToKey = -1;
        while (dirNodeKeyToKey != 0 && child != null) {
            if (0 < dirNodeKeyToKey) {
                child = node.rite;
            } else {
                child = node.left;
            }
            if (child != null) {
                node = child;
                nodeKey = node.key;
                dirNodeKeyToKey = compareSpecial(key, nodeKey);
            }
        }
        while (0 < dirNodeKeyToKey) {
            node = node.succ;
            nodeKey = node.key;
            dirNodeKeyToKey = compareSpecial(key, nodeKey);
        }
        while (dirNodeKeyToKey < 0) {
            node = node.pred;
            nodeKey = node.key;
            dirNodeKeyToKey = compareSpecial(key, nodeKey);
        }
        return dirNodeKeyToKey == 0 && node.notLogicallyRemoved;
    }


    public void insert(Integer key) {
        Node node = null;
        Integer nodeKey = null;
        int dirNodeKeyToKey = -1;
        while (true) {
            node = root;
            Node child = new Node(42); // use any non-null value
            dirNodeKeyToKey = -1;
            while (dirNodeKeyToKey != 0 && child != null) {
                if (0 < dirNodeKeyToKey) {
                    child = node.rite;
                } else {
                    child = node.left;
                }
                if (child != null) {
                    node = child;
                    nodeKey = node.key;
                    dirNodeKeyToKey = compareSpecial(key, nodeKey);
                }
            }
            Node pred = 0 < dirNodeKeyToKey ? node : node.pred;
            pred.lockSuccLock();
            if (pred.notLogicallyRemoved) {
                Integer predKey = pred.key;
                int dirPredKeyToKey = pred == node ? dirNodeKeyToKey : compareSpecial(key, predKey);
                if (0 < dirPredKeyToKey) {
                    Node succ = pred.succ;
                    Integer succKey = succ.key;
                    int dirSuccKeyToKey = succ == node ? dirNodeKeyToKey : compareSpecial(key, succKey);
                    if (dirSuccKeyToKey < 0) {
                        Node parent = node == pred || node == succ ? node : pred;

                        parent.lockTreeLock();
                        while (!(
                                (parent == pred && parent.rite == null)
                                        ||
                                        (parent != pred && parent.left == null)
                        )) {
                            parent.unlockTreeLock();
                            if (parent == pred) {
                                parent = succ;
                            } else {
                                parent = pred;
                            }
                            parent.lockTreeLock();
                        }

                        Node newNode = new Node(key, null, pred, succ, parent);
                        succ.pred = newNode;
                        pred.succ = newNode;
                        pred.unlockSuccLock();
                        if (parent == pred) {
                            parent.rite = newNode;
                            parent.riteHeight = 1;
                        } else {
                            parent.left = newNode;
                            parent.leftHeight = 1;
                        }
                        if (parent != root) {
                            Node grandParent = eventuallyLockAndReturnParent(parent);
                            if (grandParent == root) {
                                grandParent.unlockTreeLock();
                                unlockTreeLockIfNotNull(parent);
                            } else {
                                rebalance(grandParent, parent, grandParent.left == parent);
                            }
                        } else {
                            parent.unlockTreeLock();
                        }
                        return;
                    }
                    if (dirSuccKeyToKey == 0) {
                        pred.unlockSuccLock();
                        return;
                    }
                }
            }
            pred.unlockSuccLock();
        }
    }

    private Node eventuallyLockAndReturnParent(Node node) {
        Node parent = node.parent;
        parent.lockTreeLock();
        while (node.parent != parent || parent.logicallyRemoved()) {
            parent.unlockTreeLock();
            parent = node.parent;
            parent.lockTreeLock();
        }
        return parent;
    }

    public void remove(Integer key) {
        Node pred = null;
        Node node = null;
        Integer nodeKey = null;
        int dirNodeKeyToKey = 0;
        while (true) {
            node = root;
            Node child = new Node(42);// Use any non-null value
            dirNodeKeyToKey = -1;
            while (dirNodeKeyToKey != 0 && child != null) {
                if (0 < dirNodeKeyToKey) {
                    child = node.rite;
                } else {
                    child = node.left;
                }
                if (child != null) {
                    node = child;
                    nodeKey = node.key;
                    dirNodeKeyToKey = compareSpecial(key, nodeKey);
                }
            }
            pred = 0 < dirNodeKeyToKey ? node : node.pred;
            pred.lockSuccLock();
            if (pred.notLogicallyRemoved) {
                Integer predKey = pred.key;
                int dirPredKeyToKey = pred == node ? dirNodeKeyToKey : compareSpecial(key, predKey);
                if (0 < dirPredKeyToKey) {
                    Node succ = pred.succ;
                    Integer succKey = succ.key;
                    int dirSuccKeyToKey = succ == node ? dirNodeKeyToKey : compareSpecial(key, succKey);
                    if (dirSuccKeyToKey < 0) {
                        pred.unlockSuccLock();
                        return;
                    }
                    if (dirSuccKeyToKey == 0) {
                        unlinkFoundNode(pred, succ);
                        return;
                    }
                }
            }
            pred.unlockSuccLock();
        }
    }

    private void unlinkFoundNode(Node pred, Node node) {
        node.lockSuccLock();
        Node succ = null;
        boolean done = false;
        while (!done) {
            node.lockTreeLock();
            Node rite = node.rite;
            Node left = node.left;
            if (rite != null && left != null) {
                succ = lockSuccessorAndItsChildAndReturnSuccessorOrNullIfFailed(node);
                done = succ != null;
            } else if ((rite == null || rite.tryLockTreeLock()) && (left == null || left.tryLockTreeLock())) {
                done = true;
            } else {
                node.unlockTreeLock();
            }
        }
        Node nodeParent = eventuallyLockAndReturnParent(node);
        node.notLogicallyRemoved = false;
        Node literalSucc = node.succ;
        literalSucc.pred = pred;
        pred.succ = literalSucc;
        node.unlockSuccLock();
        pred.unlockSuccLock();
        if (succ == null) {
            Node rite = node.rite;
            Node child = rite == null ? node.left : rite;
            boolean nodeIsLeft = nodeParent.left == node;
            bindParentAndNewChild(nodeParent, node, child);
            node.unlockTreeLock();
            if (nodeParent == root) {
                nodeParent.unlockTreeLock();
                unlockTreeLockIfNotNull(child);
            } else {
                rebalance(nodeParent, child, nodeIsLeft);
            }
            return;
        }
        Node oldParent = succ.parent;
        Node oldRite = succ.rite;
        bindParentAndNewChild(oldParent, succ, oldRite);

        succ.leftHeight = node.leftHeight;
        succ.riteHeight = node.riteHeight;
        Node left = node.left;
        Node rite = node.rite;
        succ.parent = nodeParent;
        succ.left = left;
        succ.rite = rite;
        left.parent = succ;
        if (rite != null) {
            rite.parent = succ;
        }
        if (nodeParent.left == node) {
            nodeParent.left = succ;
        } else {
            nodeParent.rite = succ;
        }
        boolean nodeIsOldParent = node == oldParent;
        boolean isImbalanced = balanceFactorIsImbalanced(succ.leftHeightMinusRiteHeight());
        if (nodeIsOldParent) {
            oldParent = succ;
        } else {
            succ.unlockTreeLock();
        }
        node.unlockTreeLock();
        nodeParent.unlockTreeLock();
        boolean childIsLeft = !nodeIsOldParent;
        if (oldParent == root) {
            oldParent.unlockTreeLock();
            unlockTreeLockIfNotNull(oldRite);
        } else {
            rebalance(oldParent, oldRite, childIsLeft);
        }
        if (isImbalanced) {
            succ.lockTreeLock();
            int bf = succ.leftHeightMinusRiteHeight();
            if (succ.notLogicallyRemoved && succ != root && balanceFactorIsImbalanced(bf)) {
                rebalance(succ, null, bf < 2);
            } else {
                succ.unlockTreeLock();
            }
        }
    }

    private Node lockSuccessorAndItsChildAndReturnSuccessorOrNullIfFailed(Node node) {
        Node succ = node.succ;

        Node parent = succ.parent;
        if (parent != node) {
            if (!parent.tryLockTreeLock()) {
                node.unlockTreeLock();
                return null;
            } else if (parent != succ.parent || parent.logicallyRemoved()) {
                parent.unlockTreeLock();
                node.unlockTreeLock();
                return null;
            }
        }
        if (!succ.tryLockTreeLock()) {
            node.unlockTreeLock();
            if (parent != node) {
                parent.unlockTreeLock();
            }
            return null;
        }
        Node succRiteChild = succ.rite; // there is no left child to
        // the succ, perhaps there is a rite one, which we need to lock.
        if (succRiteChild != null && !succRiteChild.tryLockTreeLock()) {
            node.unlockTreeLock();
            succ.unlockTreeLock();
            if (parent != node) {
                parent.unlockTreeLock();
            }
            return null;
        }
        return succ;
    }

    @AllArgsConstructor
    class RebalanceRegionRet {
        boolean childIsLeft;
        int bf;
        Node child;
        Node node;
        Node parent;
    }

    private Optional<RebalanceRegionRet> rebalanceRegion(
            boolean childIsLeft, int bf, Node child, Node node, Node parent
    ) {

        if ((childIsLeft && bf <= -2) || (!childIsLeft && 2 <= bf)) {
            unlockTreeLockIfNotNull(child);
            child = childIsLeft ? node.rite : node.left;
            if (child.tryLockTreeLock()) {
                childIsLeft = !childIsLeft;
            } else {
                unlockTreeLockIfNotNull(parent);
                node.unlockTreeLock();
                child = eventuallyAquireTreeLocksOfNodeAndHeavyChildAndReturnChildOrNoOpIfNodeLogicallyRemoved(node);
                if (!node.treeLock.isHeldByCurrentThread()) {
                    return Optional.empty();
                }
                childIsLeft = node.left == child;
                bf = node.leftHeightMinusRiteHeight();
                return Optional.of(new RebalanceRegionRet(childIsLeft, bf, child, node, null));
            }
        }

        if (childIsLeft && child.leftHeightMinusRiteHeight() < 0 && child.rite.tryLockTreeLock()) {
            Node grandChild = child.rite;
            if (node.left == child) {
                node.left = grandChild;
            } else {
                node.rite = grandChild;
            }
            rotateLeft(grandChild, child, node);
            child.unlockTreeLock();
            child = grandChild;
        } else if (!childIsLeft && 0 < child.leftHeightMinusRiteHeight() && child.left.tryLockTreeLock()) {
            Node grandChild = child.left;
            if (node.left == child) {
                node.left = grandChild;
            } else {
                node.rite = grandChild;
            }
            rotateRite(grandChild, child, node);
            child.unlockTreeLock();
            child = grandChild;
        } else if ((childIsLeft && child.leftHeightMinusRiteHeight() < 0) || (!childIsLeft && 0 < child.leftHeightMinusRiteHeight())) {
            child.unlockTreeLock();
            unlockTreeLockIfNotNull(parent);
            node.unlockTreeLock();
            child = eventuallyAquireTreeLocksOfNodeAndHeavyChildAndReturnChildOrNoOpIfNodeLogicallyRemoved(node);
            if (!node.treeLock.isHeldByCurrentThread()) {
                return Optional.empty();
            }
            childIsLeft = node.left == child;
            bf = node.leftHeightMinusRiteHeight();
            return Optional.of(new RebalanceRegionRet(childIsLeft, bf, child, node, null));
        }
        if (parent == null) {
            parent = eventuallyLockAndReturnParent(node);
        }
        if (parent.left == node) {
            parent.left = child;
        } else {
            parent.rite = child;
        }
        if (childIsLeft) {
            rotateRite(child, node, parent);
        } else {
            rotateLeft(child, node, parent);
        }
        bf = node.leftHeightMinusRiteHeight();
        if (balanceFactorIsImbalanced(bf)) {
            parent.unlockTreeLock();
            parent = child;
            child = null;
            childIsLeft = bf < 2; // enforce locking child
        } else {
            Node temp = child;
            child = node;
            node = temp;
            childIsLeft = node.left == child;
            bf = node.leftHeightMinusRiteHeight();
        }
        return Optional.of(new RebalanceRegionRet(childIsLeft, bf, child, node, parent));
    }

    private void rebalance(Node node, Node child, boolean childIsLeft) {
        Node parent = null;
        try {
            while (node != root) {
                boolean heightWasNotChanged = updateHeightFieldInParentAndReturnIfUnchanged(child, node, childIsLeft);
                int bf = node.leftHeightMinusRiteHeight();
                if (heightWasNotChanged && !balanceFactorIsImbalanced(bf)) {
                    return;
                }
                while (balanceFactorIsImbalanced(bf)) {
                    Optional<RebalanceRegionRet> res = rebalanceRegion(childIsLeft, bf, child, node, parent);
                    if (res.isEmpty()) {
                        return;
                    }
                    childIsLeft = res.get().childIsLeft;
                    bf = res.get().bf;
                    child = res.get().child;
                    node = res.get().node;
                    parent = res.get().parent;
                }
                unlockTreeLockIfNotNull(child);
                child = node;
                node = parent != null && parent.treeLock.isHeldByCurrentThread() ? parent :
                        eventuallyLockAndReturnParent(node);
                childIsLeft = node.left == child;
                parent = null;
            }
        } finally {
            if (child != null && child.treeLock.isHeldByCurrentThread()) {
                child.unlockTreeLock();
            }
            if (node.treeLock.isHeldByCurrentThread()) {
                node.unlockTreeLock();
            }
            if (parent != null && parent.treeLock.isHeldByCurrentThread()) {
                parent.unlockTreeLock();
            }
        }
    }


    private Node eventuallyAquireTreeLocksOfNodeAndHeavyChildAndReturnChildOrNoOpIfNodeLogicallyRemoved(Node node) {
        while (true) {
            node.lockTreeLock();
            if (node.logicallyRemoved()) {
                node.unlockTreeLock();
                return null;
            }
            Node child = balanceFactorIsImbalanced(node.leftHeightMinusRiteHeight()) ? node.left : node.rite;
            if (child == null) {
                return null;
            }
            if (child.tryLockTreeLock()) {
                return child;
            }
            node.unlockTreeLock();
        }
    }

    private void rotateRite(Node child, Node node, Node parent) {
        child.parent = parent;
        node.parent = child;
        Node grandChild = child.rite;
        node.left = grandChild;
        if (grandChild != null) {
            grandChild.parent = node;
        }
        child.rite = node;
        node.leftHeight = child.riteHeight;
        child.riteHeight = calculateHeightFromChildren(node);
    }

    private void rotateLeft(Node child, Node node, Node parent) {
        child.parent = parent;
        node.parent = child;
        Node grandChild = child.left;
        node.rite = grandChild;
        if (grandChild != null) {
            grandChild.parent = node;
        }
        child.left = node;
        node.riteHeight = child.leftHeight;
        child.leftHeight = calculateHeightFromChildren(node);
    }

    private boolean updateHeightFieldInParentAndReturnIfUnchanged(Node node, Node parent, boolean nodeIsLeftChild) {
        int newHeight = node == null ? 0 : calculateHeightFromChildren(node);
        int oldHeight = nodeIsLeftChild ? parent.leftHeight : parent.riteHeight;
        if (newHeight == oldHeight) {
            return true;
        }
        if (nodeIsLeftChild) {
            parent.leftHeight = newHeight;
        } else {
            parent.riteHeight = newHeight;
        }
        return false;
    }

    private void bindParentAndNewChild(Node parent, Node oldChild, Node newChild) {
        if (newChild != null) {
            newChild.parent = parent;
        }
        if (parent.left == oldChild) {
            parent.left = newChild;
        } else {
            parent.rite = newChild;
        }
    }

    private int calculateHeightFromChildren(Node node) {
        return Math.max(node.leftHeight, node.riteHeight) + 1;
    }

    private boolean balanceFactorIsImbalanced(int bf) {
        return 2 <= Math.abs(bf);
    }

    private void unlockTreeLockIfNotNull(Node node) {
        if (node != null) {
            node.unlockTreeLock();
        }
    }

    class Node {

        public Integer key;

        public volatile boolean notLogicallyRemoved;

        public volatile Node pred;


        public volatile Node succ;

        /**
         * The lock that protects the node's {@code succ} field and the {@code pred} field of the
         * node pointed by {@code succ}.
         */
        public Lock succLock;

        public volatile Node parent;

        public volatile Node left;

        public volatile Node rite;


        public int leftHeight;


        public int riteHeight;

        /**
         * The lock that protects the node's tree fields, that is, {@code parent, left, rite,
         * leftHeight, riteHeight}.
         */
        public ReentrantLock treeLock;


        public Node(Integer key, Object item, Node pred, Node succ, Node parent) {
            this.key = key;
            notLogicallyRemoved = true;

            this.pred = pred;
            this.succ = succ;
            succLock = new ReentrantLock();

            this.parent = parent;
            rite = null;
            left = null;
            leftHeight = 0;
            riteHeight = 0;
            treeLock = new ReentrantLock();
        }


        public Node(Integer key) {
            this(key, null, null, null, null);
        }

        public void lockTreeLock() {
            treeLock.lock();
        }

        public boolean tryLockTreeLock() {
            return treeLock.tryLock();
        }

        public void unlockTreeLock() {
            treeLock.unlock();
        }

        public int leftHeightMinusRiteHeight() {
            return leftHeight - riteHeight;
        }

        public void lockSuccLock() {
            succLock.lock();
        }

        public void unlockSuccLock() {
            succLock.unlock();
        }

        public boolean logicallyRemoved() {
            return !this.notLogicallyRemoved;
        }

        public boolean treeLockIsHeld() {
            return this.treeLock.isLocked();
        }

    }

    /*
    --------------------------------------------
    BEGIN modifications to original source code
     */

    class Recursive<F> {
        F fun;
        boolean good = true;
    }

    boolean trueBalance() {
        Recursive<Function<Node, Integer>> f = new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return 0;
            }
            int lh = f.fun.apply(node.left);
            int rh = f.fun.apply(node.rite);
            if (1 < Math.abs(lh - rh)) {
                f.good = false;
            }
            return Math.max(lh, rh) + 1;
        };

        f.fun.apply(root.left);

        return f.good;
    }

    boolean noTreeLockIsHeld() {

        Recursive<Consumer<Node>> f = new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return;
            }
            f.fun.accept(node.left);
            f.fun.accept(node.rite);
            if (node.treeLockIsHeld()) {
                f.good = false;
            }
        };

        f.fun.accept(root.left);

        return f.good;
    }

    public boolean invariantsHold() {
        boolean good = true;
        good = good && trueBalance();
        good = good && noTreeLockIsHeld();
        return good;
    }
}
