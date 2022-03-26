package bronson.modified.tisdall;

public class SnapTreeMapIterative {

    public final transient Node rootHolder = new Node(null, 1, null, null, 0L, null, null);

    public boolean invariantsHold() {
        return DebugUtil.invariantsHold(rootHolder);
    }

    private static final int UnlinkActionRequired = -1;
    private static final int RebalanceActionRequired = -2;
    private static final int NoRepairActionRequired = -3;

    static final Object RetrySymbol = new Object();

    static final long UnlinkedVer = 2;

    static long beginChange(long ver) {
        return ver | 1;
    }

    static long EndChange(long ver) {
        return (ver | 3) + 1;
    }

    static boolean IsUnlinked(long ver) {
        return (ver & 2) != 0;
    }

    static boolean IsShrinkingOrUnlinked(long ver) {
        return (ver & 3) != 0L;
    }

    static boolean BalanceFactorIsBalanced(int bal) {
        return -1 <= bal && bal <= 1;
    }

    static boolean BalanceFactorIsImBalanced(int bal) {
        return !BalanceFactorIsBalanced(bal);
    }

    static boolean IsLogicallyDeleted(Node node) {
        return node.val == null;
    }

    static int MaxPlusOne(int a, int b) {
        return Math.max(a, b) + 1;
    }

    private static int NullSafeHeight(final Node node) {
        return node == null ? 0 : node.height;
    }

    public Integer get(final Integer k) {
        while (true) {
            final Object vo = getImpl(k, rootHolder);
            if (vo != RetrySymbol) {
                return (Integer) vo;
            }
        }
    }

    private Object getImpl(final Comparable<Integer> k, Node node) {
        long nVer = 0L;
        char dirToC = 'R';
        while (true) {
            final Node child = node.Child(dirToC);

            if (child == null) {
                if (node.ver != nVer) {
                    return RetrySymbol;
                }
                return null;
            }
            final int childCmp = k.compareTo(child.key);

            if (childCmp == 0) {
                return child.val;
            }

            final long childVer = child.ver;
            if (IsShrinkingOrUnlinked(childVer)) {
                child.WaitUntilShrinkCompleted(childVer);

                if (node.ver != nVer) {
                    return RetrySymbol;
                }

            } else if (child != node.Child(dirToC)) {

                if (node.ver != nVer) {
                    return RetrySymbol;
                }

            } else {
                if (node.ver != nVer) {
                    return RetrySymbol;
                }

                node = child;
                dirToC = (childCmp < 0 ? 'L' : 'R');
                nVer = childVer;
            }
        }
    }

    public Object update(final Integer k,
                         final Integer newValue) {
        while (true) {
            Node node = rootHolder.rite;
            if (node == null) {
                if (newValue == null) {
                    return null;
                }
                synchronized (rootHolder) {
                    if (rootHolder.rite == null) {
                        rootHolder.rite = new Node(k, 1, newValue, rootHolder, 0L, null,
                                null);
                        rootHolder.height = 2;
                        return null;
                    }
                }
            } else {
                long nVer = node.ver;
                if (IsShrinkingOrUnlinked(nVer)) {
                    node.WaitUntilShrinkCompleted(nVer);
                } else if (node == rootHolder.rite) {
                    Object vo = updateImpl(k, k, newValue, rootHolder, node, nVer);
                    if (vo != RetrySymbol) {
                        return vo;
                    }
                }
            }
        }
    }

    private Object updateImpl(final Integer key, final Comparable<Integer> k,
                              final Integer newValue, Node parent, Node node, long nVer) {
        while (true) {
            final int cmp = k.compareTo(node.key);
            if (cmp == 0) {
                return attemptNodeUpdate(newValue, parent, node);
            }
            final char dirToC = cmp < 0 ? 'L' : 'R';
            final Node child = node.Child(dirToC);
            if (node.ver != nVer) {
                return RetrySymbol;
            }
            if (child == null) {
                if (newValue == null) {
                    return null;
                }
                final boolean success;
                final Node damaged;
                synchronized (node) {
                    if (node.ver != nVer) {
                        return RetrySymbol;
                    }
                    if (node.Child(dirToC) != null) {
                        success = false;
                        damaged = null;
                    } else {
                        node.setChild(dirToC, new Node(key, 1, newValue, node, 0L,
                                null, null));
                        success = true;
                        damaged =
                                fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(node);
                    }
                }
                if (success) {
                    fixHeightAndRebalance(damaged);
                    return null;
                }
            } else {
                final long childVer = child.ver;
                if (IsShrinkingOrUnlinked(childVer)) {
                    child.WaitUntilShrinkCompleted(childVer);
                } else if (child == node.Child(dirToC)) {
                    if (node.ver != nVer) {
                        return RetrySymbol;
                    }
                    parent = node;
                    node = child;
                    nVer = childVer;
                }
            }
        }
    }

    private Object attemptNodeUpdate(final Integer newValue,
                                     final Node parent,
                                     final Node node) {

        if (newValue == null && IsLogicallyDeleted(node)) {
            return null;
        }

        if (newValue == null && (node.left == null || node.rite == null)) {
            final Object prev;
            final Node damaged;
            synchronized (parent) {
                if (IsUnlinked(parent.ver) || node.parent != parent) {
                    return RetrySymbol;
                }
                synchronized (node) {
                    prev = node.val;
                    if (prev == null) {
                        return null;
                    }
                    if (!attemptUnlink_argsLocked(parent, node)) {
                        return RetrySymbol;
                    }
                }
                damaged =
                        fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(parent);
            }
            fixHeightAndRebalance(damaged);
            return prev;
        }

        synchronized (node) {
            if (IsUnlinked(node.ver)) {
                return RetrySymbol;
            }

            if (newValue == null && (node.left == null || node.rite == null)) {
                return RetrySymbol;
            }

            final Object prev = node.val;
            node.val = newValue;
            return prev;
        }
    }

    private int requiredRepairActionOrReplacementHeight(final Node node) {

        final Node nL = node.left;
        final Node nR = node.rite;

        if ((nL == null || nR == null) && IsLogicallyDeleted(node)) {
            return UnlinkActionRequired;
        }

        final int hN = node.height;
        final int hL0 = NullSafeHeight(nL);
        final int hR0 = NullSafeHeight(nR);

        final int hNRepl = MaxPlusOne(hL0, hR0);

        final int bal = hL0 - hR0;

        if (BalanceFactorIsImBalanced(bal)) {
            return RebalanceActionRequired;
        }

        return hN != hNRepl ? hNRepl : NoRepairActionRequired;
    }

    private void fixHeightAndRebalance(Node node) {
        while (node != null && node.parent != null) {
            final int actionOrHeight = requiredRepairActionOrReplacementHeight(node);
            if (actionOrHeight == NoRepairActionRequired || IsUnlinked(node.ver)) {
                return;
            }
            if (actionOrHeight != UnlinkActionRequired && actionOrHeight != RebalanceActionRequired) {
                synchronized (node) {
                    node = fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(node);
                }
            } else {
                final Node nP = node.parent;
                synchronized (nP) {
                    if (!IsUnlinked(nP.ver) && node.parent == nP) {
                        synchronized (node) {
                            final Node nL = node.left;
                            final Node nR = node.rite;
                            if ((nL == null || nR == null) && IsLogicallyDeleted(node)) {
                                if (attemptUnlink_argsLocked(nP, node)) {
                                    node = fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(nP);
                                }
                            } else {
                                final int hN = node.height;
                                final int hL0 = NullSafeHeight(nL);
                                final int hR0 = NullSafeHeight(nR);
                                final int hNRepl = MaxPlusOne(hL0, hR0);
                                if (hL0 + 1 < hR0) { // rite heavy
                                    synchronized (nR) {
                                        node = rebalanceToLeft_argsLocked(nP, node, nR, hL0);
                                    }
                                } else if (hL0 > 1 + hR0) { // left heavy
                                    synchronized (nL) {
                                        node = rebalanceToRite_argsLocked(nP, node, nL, hR0);
                                    }
                                } else if (hNRepl != hN) {
                                    node.height = hNRepl;
                                    node = fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(nP);
                                } else {
                                    node = null;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private boolean attemptUnlink_argsLocked(final Node parent, final Node node) {

        final Node parentL = parent.left;
        final Node parentR = parent.rite;

        if (parentL != node && parentR != node) {
            return false;
        }

        final Node left = node.left;
        final Node rite = node.rite;

        if (left != null && rite != null) {
            return false;
        }

        final Node splice = left != null ? left : rite;

        if (parentL == node) {
            parent.left = splice;
        } else {
            parent.rite = splice;
        }
        if (splice != null) {
            splice.parent = parent;
        }

        node.ver = UnlinkedVer;
        node.val = null;

        return true;
    }

    private Node fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(final Node node) {
        final int c = requiredRepairActionOrReplacementHeight(node);
        switch (c) {
            case RebalanceActionRequired:
                return node;
            case UnlinkActionRequired:
                return node;
            case NoRepairActionRequired:
                return null;
            default:
                node.height = c;
                return node.parent;
        }
    }

    private Node rebalanceToRite_argsLocked(final Node nP,
                                            final Node n,
                                            final Node nL,
                                            final int hR0) {
        final int hL = nL.height;
        if (hL <= 1 + hR0) { // Left heavy enough to be worth balancing?
            return n;
        }
        final Node nLR = nL.rite;
        final int hLL0 = NullSafeHeight(nL.left);
        final int hLR0 = NullSafeHeight(nLR);
        if (hLL0 >= hLR0) { // Left is not rite heavy
            return rotateRite_argsLocked(nP, n, nL, hR0, hLL0, nLR, hLR0);
        }
        synchronized (nLR) {
            final int hLR = nLR.height;
            if (hLL0 >= hLR) { // Left is not rite heavy
                return rotateRite_argsLocked(nP, n, nL, hR0, hLL0, nLR, hLR);
            }
            // Left is rite heavy
            final int hLRL = NullSafeHeight(nLR.left);
            if (
                    BalanceFactorIsBalanced(hLL0 - hLRL) // Left is balanced
                            // Begin original extra check, deleted by Trevor
                            && !(
                            (hLL0 == 0 || hLRL == 0) &&
                                    IsLogicallyDeleted(nL)
                    )
                // End ----------
            ) {
                return rotateLeftThenRite_argsLocked(nP, n, nL, hR0, hLL0, nLR, hLRL);
            }
            // More care needed to properly rebalance left child, delegate the work
            return rebalanceToLeft_argsLocked(n, nL, nLR, hLL0);
        }
    }

    private Node rebalanceToLeft_argsLocked(final Node nP,
                                            final Node n,
                                            final Node nR,
                                            final int hL0) {
        final int hR = nR.height;
        if (hL0 + 1 >= hR) { // Rite heavy enough to be worth balancing?
            return n;
        }
        final Node nRL = nR.left;
        final int hRL0 = NullSafeHeight(nRL);
        final int hRR0 = NullSafeHeight(nR.rite);
        if (hRL0 <= hRR0) { // Rite is not left heavy
            return rotateLeft_argsLocked(nP, n, hL0, nR, nRL, hRL0, hRR0);
        }
        synchronized (nRL) {
            final int hRL = nRL.height;
            if (hRL <= hRR0) { // Rite is not left heavy
                return rotateLeft_argsLocked(nP, n, hL0, nR, nRL, hRL, hRR0);
            }
            // Rite is left heavy
            final int hRLR = NullSafeHeight(nRL.rite);
            if (
                    BalanceFactorIsBalanced(hRR0 - hRLR) // Rite is balanced
                            // Begin original extra check, deleted by Trevor
                            && !(
                            (hRR0 == 0 || hRLR == 0) &&
                                    IsLogicallyDeleted(nR)
                    )
                // End ----------
            ) {
                return rotateRiteThenLeft_argsLocked(nP, n, hL0, nR, nRL, hRR0, hRLR);
            }
            // More care needed to properly rebalance rite child, delegate the work
            return rebalanceToRite_argsLocked(n, nR, nRL, hRR0);
        }
    }

    private Node rotateRite_argsLocked(final Node nP,
                                       final Node n,
                                       final Node nL,
                                       final int hR,
                                       final int hLL,
                                       final Node nLR,
                                       final int hLR) {
        final long nVer = n.ver;

        final Node nPL = nP.left;

        n.ver = beginChange(nVer);

        n.left = nLR;
        if (nLR != null) {
            nLR.parent = n;
        }

        nL.rite = n;
        n.parent = nL;

        if (nPL == n) {
            nP.left = nL;
        } else {
            nP.rite = nL;
        }
        nL.parent = nP;

        final int hNRepl = MaxPlusOne(hLR, hR);
        n.height = hNRepl;
        nL.height = MaxPlusOne(hLL, hNRepl);

        n.ver = EndChange(nVer);

        final int balN = hLR - hR;
        if (BalanceFactorIsImBalanced(balN)) {
            return n;
        }
        // Begin original extra check, deleted by Trevor
        if ((nLR == null || hR == 0) && IsLogicallyDeleted(n)) {
            return n;
        }
        if (hLL == 0 && IsLogicallyDeleted(nL)) {
            return nL;
        }
        // End -------------
        final int balL = hLL - hNRepl;
        if (BalanceFactorIsImBalanced(balL)) {
            return nL;
        }
        return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(nP);
    }

    private Node rotateLeft_argsLocked(final Node nP,
                                       final Node n,
                                       final int hL,
                                       final Node nR,
                                       final Node nRL,
                                       final int hRL,
                                       final int hRR) {
        final long nVer = n.ver;

        final Node nPL = nP.left;

        n.ver = beginChange(nVer);

        n.rite = nRL;
        if (nRL != null) {
            nRL.parent = n;
        }

        nR.left = n;
        n.parent = nR;

        if (nPL == n) {
            nP.left = nR;
        } else {
            nP.rite = nR;
        }
        nR.parent = nP;

        final int hNRepl = MaxPlusOne(hL, hRL);
        n.height = hNRepl;
        nR.height = MaxPlusOne(hNRepl, hRR);

        n.ver = EndChange(nVer);

        final int balN = hRL - hL;
        if (BalanceFactorIsImBalanced(balN)) {
            return n;
        }
        // Begin original extra check, deleted by Trevor
        if ((nRL == null || hL == 0) && IsLogicallyDeleted(n)) {
            return n;
        }
        if (hRR == 0 && IsLogicallyDeleted(nR)) {
            return nR;
        }
        // End -------------
        final int balR = hRR - hNRepl;
        if (BalanceFactorIsImBalanced(balR)) {
            return nR;
        }
        return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(nP);
    }

    private Node rotateLeftThenRite_argsLocked(final Node nP,
                                               final Node n,
                                               final Node nL,
                                               final int hR,
                                               final int hLL,
                                               final Node nLR,
                                               final int hLRL) {
        final long nVer = n.ver;
        final long nLVer = nL.ver;

        final Node nPL = nP.left;
        final Node nLRL = nLR.left;
        final Node nLRR = nLR.rite;
        final int hLRR = NullSafeHeight(nLRR);

        n.ver = beginChange(nVer);
        nL.ver = beginChange(nLVer);

        n.left = nLRR;
        if (nLRR != null) {
            nLRR.parent = n;
        }

        nL.rite = nLRL;
        if (nLRL != null) {
            nLRL.parent = nL;
        }

        nLR.left = nL;
        nL.parent = nLR;
        nLR.rite = n;
        n.parent = nLR;

        if (nPL == n) {
            nP.left = nLR;
        } else {
            nP.rite = nLR;
        }
        nLR.parent = nP;

        final int hNRepl = MaxPlusOne(hLRR, hR);
        n.height = hNRepl;
        final int hLRepl = MaxPlusOne(hLL, hLRL);
        nL.height = hLRepl;
        nLR.height = MaxPlusOne(hLRepl, hNRepl);

        n.ver = EndChange(nVer);
        nL.ver = EndChange(nLVer);

        // Begin original extra check, deleted by Trevor
        if ((nLRR == null || hR == 0) && IsLogicallyDeleted(n)) {
            return n;
        }
        // End -------------

        final int balN = hLRR - hR;
        if (BalanceFactorIsImBalanced(balN)) {
            return n;
        }

        final int balLR = hLRepl - hNRepl;
        if (BalanceFactorIsImBalanced(balLR)) {
            return nLR;
        }

        return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(nP);
    }

    private Node rotateRiteThenLeft_argsLocked(final Node nP,
                                               final Node n,
                                               final int hL,
                                               final Node nR,
                                               final Node nRL,
                                               final int hRR,
                                               final int hRLR) {
        final long nVer = n.ver;
        final long nRVer = nR.ver;

        final Node nPL = nP.left;
        final Node nRLL = nRL.left;
        final Node nRLR = nRL.rite;
        final int hRLL = NullSafeHeight(nRLL);

        n.ver = beginChange(nVer);
        nR.ver = beginChange(nRVer);

        n.rite = nRLL;
        if (nRLL != null) {
            nRLL.parent = n;
        }

        nR.left = nRLR;
        if (nRLR != null) {
            nRLR.parent = nR;
        }

        nRL.rite = nR;
        nR.parent = nRL;
        nRL.left = n;
        n.parent = nRL;

        if (nPL == n) {
            nP.left = nRL;
        } else {
            nP.rite = nRL;
        }
        nRL.parent = nP;

        final int hNRepl = MaxPlusOne(hL, hRLL);
        n.height = hNRepl;
        final int hRRepl = MaxPlusOne(hRLR, hRR);
        nR.height = hRRepl;
        nRL.height = MaxPlusOne(hNRepl, hRRepl);

        n.ver = EndChange(nVer);
        nR.ver = EndChange(nRVer);

        // Begin original extra check, deleted by Trevor
        if ((nRLL == null || hL == 0) && IsLogicallyDeleted(n)) {
            return n;
        }
        // End -------------

        final int balN = hRLL - hL;
        if (BalanceFactorIsImBalanced(balN)) {
            return n;
        }

        final int balRL = hRRepl - hNRepl;
        if (BalanceFactorIsImBalanced(balRL)) {
            return nRL;
        }

        return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(nP);
    }

}
