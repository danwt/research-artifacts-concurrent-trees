package bronson.modified.tisdall;

public class SnapTreeMapIterativeSimpleRotatesFixing {

    public transient Node rootHolder = new Node(null, 1, null, null, 0L, null, null);

    public boolean invariantsHold() {
        return DebugUtil.invariantsHold(rootHolder);
    }

    private static int UnlinkActionRequired = -1;
    private static int RebalanceActionRequired = -2;
    private static int NoRepairActionRequired = -3;

    static Object RetrySymbol = new Object();

    static long UnlinkedVer = 2;

    static long BeginChange(long ver) {
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

    private static int NullSafeHeight(Node node) {
        return node == null ? 0 : node.height;
    }

    public Integer get(Integer G_k) {

        Object G_vo;

        while (true) {
            G_vo = getImpl(G_k, rootHolder);
            if (G_vo != RetrySymbol) {
                return (Integer) G_vo;
            }
        }
    }

    private Object getImpl(Integer GI_k, Node GI_node) {

        long GI_nVer = 0L;
        char GI_dirToC = 'R';

        Node GI_child;
        int GI_childKRead;
        long GI_childVer;

        while (true) {
            GI_child = GI_node.Child(GI_dirToC);

            if (GI_child == null) {
                if (GI_node.ver != GI_nVer) {
                    return RetrySymbol;
                }
                return null;
            }
            GI_childKRead = GI_k.compareTo(GI_child.key);

            if (GI_childKRead == 0) {
                return GI_child.val;
            }

            GI_childVer = GI_child.ver;
            if (IsShrinkingOrUnlinked(GI_childVer)) {
                GI_child.WaitUntilShrinkCompleted(GI_childVer);

                if (GI_node.ver != GI_nVer) {
                    return RetrySymbol;
                }

            } else if (GI_child != GI_node.Child(GI_dirToC)) {

                if (GI_node.ver != GI_nVer) {
                    return RetrySymbol;
                }

            } else {
                if (GI_node.ver != GI_nVer) {
                    return RetrySymbol;
                }

                GI_node = GI_child;
                GI_dirToC = (GI_childKRead < 0 ? 'L' : 'R');
                GI_nVer = GI_childVer;
            }
        }
    }

    public Object update(Integer U_k,
                         Integer U_newValue) {

        Node U_node;
        long U_nVer;
        Object U_vo;

        while (true) {
            U_node = rootHolder.rite;
            if (U_node == null) {
                if (U_newValue == null) {
                    return null;
                }
                synchronized (rootHolder) {
                    if (rootHolder.rite == null) {
                        rootHolder.rite = new Node(U_k, 1, U_newValue, rootHolder, 0L, null,
                                null);
                        rootHolder.height = 2;
                        return null;
                    }
                }
            } else {
                U_nVer = U_node.ver;
                if (IsShrinkingOrUnlinked(U_nVer)) {
                    U_node.WaitUntilShrinkCompleted(U_nVer);
                } else if (U_node == rootHolder.rite) {
                    U_vo = updateImpl(U_k, U_newValue, rootHolder, U_node, U_nVer);
                    if (U_vo != RetrySymbol) {
                        return U_vo;
                    }
                }
            }
        }
    }

    private Object updateImpl(Integer UI_k,
                              Integer UI_newValue, Node UI_parent, Node UI_node, long UI_nVer) {

        int UI_nodeKRead;
        char UI_dirToC;
        Node UI_child;
        boolean UI_success;
        Node UI_damaged;
        long UI_childVer;

        while (true) {
            UI_nodeKRead = UI_k.compareTo(UI_node.key);
            if (UI_nodeKRead == 0) {
                return attemptNodeUpdate(UI_newValue, UI_parent, UI_node);
            }
            UI_dirToC = UI_nodeKRead < 0 ? 'L' : 'R';
            UI_child = UI_node.Child(UI_dirToC);
            if (UI_node.ver != UI_nVer) {
                return RetrySymbol;
            }
            if (UI_child == null) {
                if (UI_newValue == null) {
                    return null;
                }
                synchronized (UI_node) {
                    if (UI_node.ver != UI_nVer) {
                        return RetrySymbol;
                    }
                    if (UI_node.Child(UI_dirToC) != null) {
                        UI_success = false;
                        UI_damaged = null;
                    } else {
                        UI_node.setChild(UI_dirToC, new Node(UI_k, 1, UI_newValue, UI_node, 0L,
                                null, null));
                        UI_success = true;
                        UI_damaged =
                                fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(UI_node);
                    }
                }
                if (UI_success) {
                    fixHeightAndRebalance(UI_damaged);
                    return null;
                }
            } else {
                UI_childVer = UI_child.ver;
                if (IsShrinkingOrUnlinked(UI_childVer)) {
                    UI_child.WaitUntilShrinkCompleted(UI_childVer);
                } else if (UI_child == UI_node.Child(UI_dirToC)) {
                    if (UI_node.ver != UI_nVer) {
                        return RetrySymbol;
                    }
                    UI_parent = UI_node;
                    UI_node = UI_child;
                    UI_nVer = UI_childVer;
                }
            }
        }
    }

    private Object attemptNodeUpdate(Integer ANU_newValue,
                                     Node ANU_parent,
                                     Node ANU_node) {

        Object ANU_prev;
        Node ANU_damaged;

        if (ANU_newValue == null && IsLogicallyDeleted(ANU_node)) {
            return null;
        }

        if (ANU_newValue == null && (ANU_node.left == null || ANU_node.rite == null)) {
            synchronized (ANU_parent) {
                if (IsUnlinked(ANU_parent.ver) || ANU_node.parent != ANU_parent) {
                    return RetrySymbol;
                }
                synchronized (ANU_node) {
                    ANU_prev = ANU_node.val;
                    if (ANU_prev == null) {
                        return null;
                    }
                    if (!attemptUnlink_argsLocked(ANU_parent, ANU_node)) {
                        return RetrySymbol;
                    }
                }
                ANU_damaged =
                        fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ANU_parent);
            }
            fixHeightAndRebalance(ANU_damaged);
            return ANU_prev;
        }

        synchronized (ANU_node) {
            if (IsUnlinked(ANU_node.ver)) {
                return RetrySymbol;
            }

            if (ANU_newValue == null && (ANU_node.left == null || ANU_node.rite == null)) {
                return RetrySymbol;
            }

            ANU_prev = ANU_node.val;
            ANU_node.val = ANU_newValue;
            return ANU_prev;
        }
    }

    private int requiredRepairActionOrReplacementHeight(Node RAOH_node) {

        Node RAOH_nL;
        Node RAOH_nR;
        int RAOH_hN;
        int RAOH_hL0 = 0;
        int RAOH_hR0 = 0;
        int RAOH_hNRepl;

        RAOH_nL = RAOH_node.left;
        RAOH_nR = RAOH_node.rite;

        if ((RAOH_nL == null || RAOH_nR == null) && IsLogicallyDeleted(RAOH_node)) {
            return UnlinkActionRequired;
        }

        RAOH_hN = RAOH_node.height;

        RAOH_hL0 = NullSafeHeight(RAOH_nL);
        RAOH_hR0 = NullSafeHeight(RAOH_nR);

        RAOH_hNRepl = MaxPlusOne(RAOH_hL0, RAOH_hR0);

        if (BalanceFactorIsImBalanced(RAOH_hL0 - RAOH_hR0)) {
            return RebalanceActionRequired;
        }

        return RAOH_hN != RAOH_hNRepl ? RAOH_hNRepl : NoRepairActionRequired;
    }

    private void fixHeightAndRebalance(Node FHR_node) {

        int FHR_actionOrHeight;
        Node FHR_nP;
        Node FHR_nL;
        Node FHR_nR;
        int FHR_hN;
        int FHR_hL0;
        int FHR_hR0;
        int FHR_hNRepl;

        while (FHR_node != null) {
            if (FHR_node.parent == null) {
                return;
            }
            FHR_actionOrHeight = requiredRepairActionOrReplacementHeight(FHR_node);
            if (FHR_actionOrHeight == NoRepairActionRequired || IsUnlinked(FHR_node.ver)) {
                return;
            }
            if (FHR_actionOrHeight != UnlinkActionRequired && FHR_actionOrHeight != RebalanceActionRequired) {
                synchronized (FHR_node) {
                    FHR_node =
                            fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_node);
                }
            } else {
                FHR_nP = FHR_node.parent;
                synchronized (FHR_nP) {
                    if (!IsUnlinked(FHR_nP.ver) && FHR_node.parent == FHR_nP) {
                        synchronized (FHR_node) {
                            FHR_nL = FHR_node.left;
                            FHR_nR = FHR_node.rite;
                            if ((FHR_nL == null || FHR_nR == null) && IsLogicallyDeleted(FHR_node)) {
                                if (attemptUnlink_argsLocked(FHR_nP, FHR_node)) {
                                    FHR_node =
                                            fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_nP);
                                }
                            } else {
                                FHR_hN = FHR_node.height;
                                FHR_hL0 = NullSafeHeight(FHR_nL);
                                FHR_hR0 = NullSafeHeight(FHR_nR);
                                FHR_hNRepl = MaxPlusOne(FHR_hL0, FHR_hR0);
                                if (FHR_hL0 + 1 < FHR_hR0) { // rite heavy
                                    synchronized (FHR_nR) {
                                        FHR_node = rebalanceToLeft_argsLocked(FHR_nP, FHR_node,
                                                FHR_nR, FHR_hL0);
                                    }
                                } else if (FHR_hL0 > 1 + FHR_hR0) { // left heavy
                                    synchronized (FHR_nL) {
                                        FHR_node = rebalanceToRite_argsLocked(FHR_nP, FHR_node,
                                                FHR_nL, FHR_hR0);
                                    }
                                } else if (FHR_hNRepl != FHR_hN) {
                                    FHR_node.height = FHR_hNRepl;
                                    FHR_node =
                                            fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_nP);
                                } else {
                                    FHR_node = null;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private boolean attemptUnlink_argsLocked(Node AUL_parent, Node AUL_node) {

        Node AUL_parentL;
        Node AUL_parentR;
        Node AUL_left;
        Node AUL_rite;
        Node AUL_splice;

        AUL_parentL = AUL_parent.left;
        AUL_parentR = AUL_parent.rite;

        if (AUL_parentL != AUL_node && AUL_parentR != AUL_node) {
            return false;
        }

        AUL_left = AUL_node.left;
        AUL_rite = AUL_node.rite;

        if (AUL_left != null && AUL_rite != null) {
            return false;
        }

        AUL_splice = AUL_left != null ? AUL_left : AUL_rite;

        if (AUL_parentL == AUL_node) {
            AUL_parent.left = AUL_splice;
        } else {
            AUL_parent.rite = AUL_splice;
        }
        if (AUL_splice != null) {
            AUL_splice.parent = AUL_parent;
        }

        AUL_node.ver = UnlinkedVer;
        AUL_node.val = null;

        return true;
    }

    private Node fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(Node S_node) {

        int S_c;

        S_c = requiredRepairActionOrReplacementHeight(S_node);
        if (S_c == RebalanceActionRequired) {
            return S_node;
        }
        if (S_c == UnlinkActionRequired) {
            return S_node;
        }
        if (S_c == NoRepairActionRequired) {
            return null;
        }
        S_node.height = S_c;
        return S_node.parent;
    }

    private Node rebalanceToRite_argsLocked(Node REBR_nP,
                                            Node REBR_n,
                                            Node REBR_nL,
                                            int REBR_hR0) {

        int REBR_hL;
        Node REBR_nLR;
        int REBR_hLL0;
        int REBR_hLR0;
        int REBR_hLR;
        int REBR_hLRL;
        Node REBR_nLRL;
        Node REBR_nLRR;
        int REBR_hLRR;
        Node REBR_maybeDamaged;

        REBR_hL = REBR_nL.height;
        if (REBR_hL <= 1 + REBR_hR0) { // Left heavy enough to be worth balancing?
            return REBR_n;
        }
        REBR_nLR = REBR_nL.rite;
        REBR_hLL0 = NullSafeHeight(REBR_nL.left);
        REBR_hLR0 = NullSafeHeight(REBR_nLR);
        if (REBR_hLL0 >= REBR_hLR0) { // Left is not rite heavy
            return rotateRite_argsLocked(REBR_nP, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR,
                    REBR_hLR0);
        }
        synchronized (REBR_nLR) {
            REBR_hLR = REBR_nLR.height;
            if (REBR_hLL0 >= REBR_hLR) { // Left is not rite heavy
                return rotateRite_argsLocked(REBR_nP, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0,
                        REBR_nLR, REBR_hLR);
            }
            // Left is rite heavy
            REBR_hLRL = NullSafeHeight(REBR_nLR.left);
            if (BalanceFactorIsBalanced(REBR_hLL0 - REBR_hLRL)) {
                // Left will be balanced after double rotate

                REBR_nLRL = REBR_nLR.left;
                REBR_nLRR = REBR_nLR.rite;
                REBR_hLRR = NullSafeHeight(REBR_nLRR);
                rotateLeft_argsLocked(REBR_n, REBR_nL, REBR_hLL0, REBR_nLR, REBR_nLRL, REBR_hLRL,
                        REBR_hLRR);
                REBR_maybeDamaged = rotateRite_argsLocked(REBR_nP, REBR_n, REBR_nLR, REBR_hR0,
                        REBR_hL, REBR_nLRR, REBR_hLRR);
                if (REBR_maybeDamaged != REBR_n) {
                    REBR_maybeDamaged = REBR_nLR;
                }
                return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(REBR_maybeDamaged);
            }
            // More care needed to properly rebalance left child, delegate the work
            return rebalanceToLeft_argsLocked(REBR_n, REBR_nL, REBR_nLR, REBR_hLL0);
        }
    }

    private Node rebalanceToLeft_argsLocked(Node REBL_nP,
                                            Node REBL_n,
                                            Node REBL_nR,
                                            int REBL_hL0) {
        int REBL_hR;
        Node REBL_nRL;
        int REBL_hRL0;
        int REBL_hRR0;
        int REBL_hRL;
        int REBL_hRLR;
        Node REBL_nRLL;
        Node REBL_nRLR;
        int REBL_hRLL;
        Node REBL_maybeDamaged;

        REBL_hR = REBL_nR.height;
        if (REBL_hL0 + 1 >= REBL_hR) { // Rite heavy enough to be worth balancing?
            return REBL_n;
        }
        REBL_nRL = REBL_nR.left;
        REBL_hRL0 = NullSafeHeight(REBL_nRL);
        REBL_hRR0 = NullSafeHeight(REBL_nR.rite);
        if (REBL_hRL0 <= REBL_hRR0) { // Rite is not left heavy
            return rotateLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRL0,
                    REBL_hRR0);
        }
        synchronized (REBL_nRL) {
            REBL_hRL = REBL_nRL.height;
            if (REBL_hRL <= REBL_hRR0) { // Rite is not left heavy
                return rotateLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nR, REBL_nRL,
                        REBL_hRL, REBL_hRR0);
            }
            // Rite is left heavy
            REBL_hRLR = NullSafeHeight(REBL_nRL.rite);
            if (BalanceFactorIsBalanced(REBL_hRR0 - REBL_hRLR)) {
                // Rite will be balanced after double rotate

                REBL_nRLL = REBL_nRL.left;
                REBL_nRLR = REBL_nRL.rite;
                REBL_hRLL = NullSafeHeight(REBL_nRLL);
                rotateRite_argsLocked(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0, REBL_hRLL, REBL_nRLR,
                        REBL_hRLR);
                REBL_maybeDamaged = rotateLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nRL,
                        REBL_nRLL, REBL_hRLL, REBL_hR);
                if (REBL_maybeDamaged != REBL_n) {
                    REBL_maybeDamaged = REBL_nRL;
                }
                return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(REBL_maybeDamaged);
            }
            // More care needed to properly rebalance rite child, delegate the work
            return rebalanceToRite_argsLocked(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0);
        }
    }

    private Node rotateRite_argsLocked(Node ROTR_nP,
                                       Node ROTR_n,
                                       Node ROTR_nL,
                                       int ROTR_hR,
                                       int ROTR_hLL,
                                       Node ROTR_nLR,
                                       int ROTR_hLR) {
        long ROTR_nVer;
        Node ROTR_nPL;
        int ROTR_hNRepl;

        ROTR_nVer = ROTR_n.ver;

        ROTR_nPL = ROTR_nP.left;

        ROTR_n.ver = BeginChange(ROTR_nVer);

        ROTR_n.left = ROTR_nLR;
        if (ROTR_nLR != null) {
            ROTR_nLR.parent = ROTR_n;
        }

        ROTR_nL.rite = ROTR_n;
        ROTR_n.parent = ROTR_nL;

        if (ROTR_nPL == ROTR_n) {
            ROTR_nP.left = ROTR_nL;
        } else {
            ROTR_nP.rite = ROTR_nL;
        }
        ROTR_nL.parent = ROTR_nP;

        ROTR_hNRepl = MaxPlusOne(ROTR_hLR, ROTR_hR);
        ROTR_n.height = ROTR_hNRepl;
        ROTR_nL.height = MaxPlusOne(ROTR_hLL, ROTR_hNRepl);

        ROTR_n.ver = EndChange(ROTR_nVer);

        if (BalanceFactorIsImBalanced(ROTR_hLR - ROTR_hR)) {
            return ROTR_n;
        }
        if (BalanceFactorIsImBalanced(ROTR_hLL - ROTR_hNRepl)) {
            return ROTR_nL;
        }
        return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ROTR_nP);
    }

    private Node rotateLeft_argsLocked(Node ROTL_nP,
                                       Node ROTL_n,
                                       int ROTL_hL,
                                       Node ROTL_nR,
                                       Node ROTL_nRL,
                                       int ROTL_hRL,
                                       int ROTL_hRR) {

        long ROTL_nVer;
        Node ROTL_nPL;
        int ROTL_hNRepl;

        ROTL_nVer = ROTL_n.ver;

        ROTL_nPL = ROTL_nP.left;

        ROTL_n.ver = BeginChange(ROTL_nVer);

        ROTL_n.rite = ROTL_nRL;
        if (ROTL_nRL != null) {
            ROTL_nRL.parent = ROTL_n;
        }

        ROTL_nR.left = ROTL_n;
        ROTL_n.parent = ROTL_nR;

        if (ROTL_nPL == ROTL_n) {
            ROTL_nP.left = ROTL_nR;
        } else {
            ROTL_nP.rite = ROTL_nR;
        }
        ROTL_nR.parent = ROTL_nP;

        ROTL_hNRepl = MaxPlusOne(ROTL_hL, ROTL_hRL);
        ROTL_n.height = ROTL_hNRepl;
        ROTL_nR.height = MaxPlusOne(ROTL_hNRepl, ROTL_hRR);

        ROTL_n.ver = EndChange(ROTL_nVer);

        if (BalanceFactorIsImBalanced(ROTL_hRL - ROTL_hL)) {
            return ROTL_n;
        }
        if (BalanceFactorIsImBalanced(ROTL_hRR - ROTL_hNRepl)) {
            return ROTL_nR;
        }
        return fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ROTL_nP);
    }

}
