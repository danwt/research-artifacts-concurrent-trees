/*
 * Copyright (c) 2009 Stanford University, unless otherwise specified.
 * All rights reserved.
 *
 * This software was developed by the Pervasive Parallelism Laboratory of
 * Stanford University, California, USA.
 *
 * Permission to use, copy, modify, and distribute this software in source
 * or binary form for any purpose with or without fee is hereby granted,
 * provided that the following conditions are met:
 *
 *    1. Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *
 *    3. Neither the name of Stanford University nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

package bronson.modified.tisdall;

public class SnapTreeMapPluscal {

    private transient volatile Node rootHolder = new Node(null,
            1,
            null,
            null,
            0L,
            null,
            null);

    public boolean invariantsHold() {
        return DebugUtil.invariantsHold(rootHolder);
    }

    private final static int UnlinkRequired = -1;
    private final static int RebalanceActionRequired = -2;
    private final static int NoRebalanceActionRequired = -3;

    static long UnlinkedSymbol = 2;

    static Object RetrySymbol = new Object();

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

    static int MaxPlusOne(int a, int b) {
        return Math.max(a, b) + 1;
    }

    private static int NullSafeHeight(Node node) {
        return node == null ? 0 : node.height;
    }

    private static char AppropriateDirection(Integer routerKey, Integer soughtKey) {
        return routerKey <= soughtKey ? 'R' : 'L';
    }

    public Integer get(Integer G_k) {

        Node G_rite;
        long G_ver;
        Object G_vo;
        Integer G_riteKRead;

        while (true) {
            G_rite = rootHolder.rite;
            if (G_rite == null) {
                return null;
            } else {
                G_riteKRead = G_rite.key;
                if (G_riteKRead == G_k) {
                    return (Integer) G_rite.val;
                }
                G_ver = G_rite.ver;
                if (IsShrinkingOrUnlinked(G_ver)) {
                    G_rite.WaitUntilShrinkCompleted(G_ver);
                } else if (G_rite == rootHolder.rite) {
                    G_vo = attemptGet(G_k, G_rite, AppropriateDirection(G_riteKRead, G_k), G_ver);
                    if (G_vo != RetrySymbol) {
                        return (Integer) G_vo;
                    }
                }
            }
        }
    }

    private Object attemptGet(Integer AG_k,
                              Node AG_node,
                              char AG_dirToC,
                              long AG_nodeVer) {
        Node AG_child;
        long AG_childVer;
        Object AG_vo;
        Integer AG_childKRead;

        while (true) {
            AG_child = AG_node.Child(AG_dirToC);

            if (AG_child == null) {
                if (AG_node.ver != AG_nodeVer) {
                    return RetrySymbol;
                }
                return null;
            } else {
                AG_childKRead = AG_child.key;
                if (AG_childKRead == AG_k) {
                    return AG_child.val;
                }
                AG_childVer = AG_child.ver;
                if (IsShrinkingOrUnlinked(AG_childVer)) {
                    AG_child.WaitUntilShrinkCompleted(AG_childVer);
                    if (AG_node.ver != AG_nodeVer) {
                        return RetrySymbol;
                    }
                } else if (AG_child != AG_node.Child(AG_dirToC)) {
                    if (AG_node.ver != AG_nodeVer) {
                        return RetrySymbol;
                    }
                } else {
                    if (AG_node.ver != AG_nodeVer) {
                        return RetrySymbol;
                    }
                    AG_vo = attemptGet(AG_k, AG_child, AppropriateDirection(AG_childKRead, AG_k),
                            AG_childVer);
                    if (AG_vo != RetrySymbol) {
                        return AG_vo;
                    }
                }
            }
        }
    }

    public Object update(Integer U_k,
                         Integer U_newValue) {

        Node U_holder = rootHolder;
        Node U_rite;
        long U_ver;
        Object U_vo;

        while (true) {
            U_rite = U_holder.rite;
            if (U_rite == null) {
                if(U_newValue == null){
                    return null;
                }
                synchronized (U_holder) {
                    if (U_holder.rite == null) {
                        U_holder.rite = new Node(U_k, 1, U_newValue, U_holder, 0L,
                                null, null);
                        U_holder.height = 2;
                        return null;
                    }
                }
            } else {
                U_ver = U_rite.ver;
                if (IsShrinkingOrUnlinked(U_ver)) {
                    U_rite.WaitUntilShrinkCompleted(U_ver);
                } else if (U_rite == U_holder.rite) {
                    U_vo = attemptUpdate(U_k, U_newValue, U_holder,
                            U_rite, U_ver);
                    if (U_vo != RetrySymbol) {
                        return U_vo;
                    }
                }
            }
        }
    }

    @SuppressWarnings("unchecked")
    private Object attemptUpdate(Integer AU_k,
                                 Integer AU_newValue,
                                 Node AU_parent,
                                 Node AU_node,
                                 long AU_nodeVer) {

        char AU_dirToC;
        Node AU_child;
        boolean AU_success;
        Node AU_damaged;
        Object AU_vo;
        long AU_childVer;
        Integer AU_nodeKRead;

        AU_nodeKRead = AU_node.key;
        if (AU_nodeKRead == AU_k) {
            return attemptNodeUpdate(AU_newValue, AU_parent, AU_node);
        }

        AU_dirToC = AppropriateDirection(AU_nodeKRead, AU_k);

        while (true) {
            AU_child = AU_dirToC == 'L' ? AU_node.left : AU_node.rite;
            if (AU_node.ver != AU_nodeVer) {
                return RetrySymbol;
            }
            if (AU_child == null) {
                if (AU_newValue == null) {
                    return null;
                } else {
                    synchronized (AU_node) {
                        if (AU_node.ver != AU_nodeVer) {
                            return RetrySymbol;
                        }
                        if (AU_node.Child(AU_dirToC) != null) {
                            AU_success = false;
                            AU_damaged = null;
                        } else {
                            AU_node.setChild(AU_dirToC, new Node(AU_k, 1, AU_newValue
                                    , AU_node, 0L,
                                    null, null));
                            AU_success = true;
                            AU_damaged = fixHeight_nl(AU_node);
                        }
                    }
                    if (AU_success) {
                        fixHeightAndRebalance(AU_damaged);
                        return null;
                    }
                }
            } else {
                AU_childVer = AU_child.ver;
                if (IsShrinkingOrUnlinked(AU_childVer)) {
                    AU_child.WaitUntilShrinkCompleted(AU_childVer);
                } else {
                    if (AU_node.ver != AU_nodeVer) {
                        return RetrySymbol;
                    }
                    AU_vo = attemptUpdate(AU_k, AU_newValue, AU_node, AU_child
                            , AU_childVer);
                    if (AU_vo != RetrySymbol) {
                        return AU_vo;
                    }
                }
            }
        }
    }

    private Object attemptNodeUpdate(
            Object ANU_newValue,
            Node ANU_parent,
            Node ANU_node) {

        Object ANU_prev;
        Node ANU_damaged;

        if (ANU_newValue == null) {
            if (ANU_node.val == null) {
                return null;
            }
        }

        if (ANU_newValue == null && (ANU_node.left == null || ANU_node.rite == null)) {
            synchronized (ANU_parent) {
                if (IsUnlinked(ANU_parent.ver) || ANU_node.parent != ANU_parent) {
                    return RetrySymbol;
                }
                synchronized (ANU_node) {
                    ANU_prev = ANU_node.val;
                    if (ANU_prev == null) {
                        return ANU_prev;
                    }
                    if (!attemptUnlink_nl(ANU_parent, ANU_node)) {
                        return RetrySymbol;
                    }
                }
                ANU_damaged = fixHeight_nl(ANU_parent);
            }
            fixHeightAndRebalance(ANU_damaged);
            return ANU_prev;
        } else {
            synchronized (ANU_node) {
                if (IsUnlinked(ANU_node.ver)) {
                    return RetrySymbol;
                }
                ANU_prev = ANU_node.val;
                if (ANU_newValue == null && (ANU_node.left == null || ANU_node.rite == null)) {
                    return RetrySymbol;
                }
                ANU_node.val = ANU_newValue;
                return ANU_prev;
            }
        }
    }

    private boolean attemptUnlink_nl(Node AUL_parent, Node AUL_node) {

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

        AUL_node.ver = UnlinkedSymbol;
        AUL_node.val = null;

        return true;
    }

    private int nodeCondition(Node NC_node) {

        Node NC_nL;
        Node NC_nR;
        int NC_hN;
        int NC_hL0;
        int NC_hR0;
        int NC_hNRepl;
        int NC_bal;

        NC_nL = NC_node.left;
        NC_nR = NC_node.rite;

        if ((NC_nL == null || NC_nR == null) && NC_node.val == null) {
            return UnlinkRequired;
        }

        NC_hN = NC_node.height;
        NC_hL0 = NullSafeHeight(NC_nL);
        NC_hR0 = NullSafeHeight(NC_nR);

        NC_hNRepl = MaxPlusOne(NC_hL0, NC_hR0);
        NC_bal = NC_hL0 - NC_hR0;

        if (NC_bal < -1 || NC_bal > 1) {
            return RebalanceActionRequired;
        }

        return NC_hN != NC_hNRepl ? NC_hNRepl : NoRebalanceActionRequired;
    }

    private void fixHeightAndRebalance(Node FHR_node) {

        int FHR_condition;
        Node FHR_nParent;

        while (FHR_node != null) {
            if (FHR_node.parent == null) {
                return;
            }
            FHR_condition = nodeCondition(FHR_node);
            if (FHR_condition == NoRebalanceActionRequired || IsUnlinked(FHR_node.ver)) {
                return;
            }
            if (FHR_condition != UnlinkRequired && FHR_condition != RebalanceActionRequired) {
                synchronized (FHR_node) {
                    FHR_node = fixHeight_nl(FHR_node);
                }
            } else {
                FHR_nParent = FHR_node.parent;
                synchronized (FHR_nParent) {
                    if (!IsUnlinked(FHR_nParent.ver) && FHR_node.parent == FHR_nParent) {
                        synchronized (FHR_node) {
                            FHR_node = rebalance_nl(FHR_nParent, FHR_node);
                        }
                    }
                }
            }
        }
    }

    private Node fixHeight_nl(Node FH_node) {

        int FH_c;

        FH_c = nodeCondition(FH_node);

        if (FH_c == RebalanceActionRequired) {
            return FH_node;
        }
        if (FH_c == UnlinkRequired) {
            return FH_node;
        }
        if (FH_c == NoRebalanceActionRequired) {
            return null;
        }
        FH_node.height = FH_c;
        return FH_node.parent;
    }

    private Node rebalance_nl(Node REB_nParent, Node REB_n) {
        Node REB_nL;
        Node REB_nR;
        int REB_hN;
        int REB_hL0;
        int REB_hR0;
        int REB_hNRepl;
        int REB_bal;

        REB_nL = REB_n.left;
        REB_nR = REB_n.rite;

        if ((REB_nL == null || REB_nR == null) && REB_n.val == null) {
            if (attemptUnlink_nl(REB_nParent, REB_n)) {
                return fixHeight_nl(REB_nParent);
            } else {
                return REB_n;
            }
        }

        REB_hN = REB_n.height;
        REB_hL0 = NullSafeHeight(REB_nL);
        REB_hR0 = NullSafeHeight(REB_nR);
        REB_hNRepl = MaxPlusOne(REB_hL0, REB_hR0);
        REB_bal = REB_hL0 - REB_hR0;

        if (REB_bal > 1) {
            return rebalanceToRite_nl(REB_nParent, REB_n, REB_nL, REB_hR0);
        } else if (REB_bal < -1) {
            return rebalanceToLeft_nl(REB_nParent, REB_n, REB_nR, REB_hL0);
        } else if (REB_hNRepl != REB_hN) {
            REB_n.height = REB_hNRepl;
            return fixHeight_nl(REB_nParent);
        } else {
            return null;
        }
    }

    private Node rebalanceToRite_nl(Node REBR_nParent,
                                    Node REBR_n,
                                    Node REBR_nL,
                                    int REBR_hR0) {

        int REBR_hL;
        Node REBR_nLR;
        int REBR_hLL0;
        int REBR_hLR0;
        int REBR_hLR;
        int REBR_hLRL;
        int REBR_bal;

        synchronized (REBR_nL) {
            REBR_hL = REBR_nL.height;
            if (REBR_hL - REBR_hR0 <= 1) {
                return REBR_n;
            } else {
                REBR_nLR = REBR_nL.rite;
                REBR_hLL0 = NullSafeHeight(REBR_nL.left);
                REBR_hLR0 = NullSafeHeight(REBR_nLR);
                if (REBR_hLL0 >= REBR_hLR0) {
                    return rotateRite_nl(REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0,
                            REBR_nLR, REBR_hLR0);
                } else {
                    synchronized (REBR_nLR) {
                        REBR_hLR = REBR_nLR.height;
                        if (REBR_hLL0 >= REBR_hLR) {
                            return rotateRite_nl(REBR_nParent, REBR_n, REBR_nL, REBR_hR0,
                                    REBR_hLL0, REBR_nLR,
                                    REBR_hLR);
                        } else {
                            REBR_hLRL = NullSafeHeight(REBR_nLR.left);
                            REBR_bal = REBR_hLL0 - REBR_hLRL;
                            if (REBR_bal >= -1 && REBR_bal <= 1 && !((REBR_hLL0 == 0 || REBR_hLRL == 0) && REBR_nL.val == null)) {
                                return rotateRiteOverLeft_nl(REBR_nParent, REBR_n, REBR_nL,
                                        REBR_hR0, REBR_hLL0,
                                        REBR_nLR, REBR_hLRL);
                            }
                        }
                    }
                    return rebalanceToLeft_nl(REBR_n, REBR_nL, REBR_nLR, REBR_hLL0);
                }
            }
        }
    }

    private Node rebalanceToLeft_nl(Node REBL_nParent,
                                    Node REBL_n,
                                    Node REBL_nR,
                                    int REBL_hL0) {

        int REBL_hR;
        Node REBL_nRL;
        int REBL_hRL0;
        int REBL_hRR0;
        int REBL_hRL;
        int REBL_hRLR;
        int REBL_bal;

        synchronized (REBL_nR) {
            REBL_hR = REBL_nR.height;
            if (REBL_hL0 - REBL_hR >= -1) {
                return REBL_n;
            } else {
                REBL_nRL = REBL_nR.left;
                REBL_hRL0 = NullSafeHeight(REBL_nRL);
                REBL_hRR0 = NullSafeHeight(REBL_nR.rite);
                if (REBL_hRR0 >= REBL_hRL0) {
                    return rotateLeft_nl(REBL_nParent, REBL_n, REBL_hL0, REBL_nR, REBL_nRL,
                            REBL_hRL0, REBL_hRR0);
                } else {
                    synchronized (REBL_nRL) {
                        REBL_hRL = REBL_nRL.height;
                        if (REBL_hRR0 >= REBL_hRL) {
                            return rotateLeft_nl(REBL_nParent, REBL_n, REBL_hL0, REBL_nR,
                                    REBL_nRL, REBL_hRL,
                                    REBL_hRR0);
                        } else {
                            REBL_hRLR = NullSafeHeight(REBL_nRL.rite);
                            REBL_bal = REBL_hRR0 - REBL_hRLR;
                            if (REBL_bal >= -1 && REBL_bal <= 1 && !((REBL_hRR0 == 0 || REBL_hRLR == 0) && REBL_nR.val == null)) {
                                return rotateLeftOverRite_nl(REBL_nParent, REBL_n, REBL_hL0,
                                        REBL_nR, REBL_nRL,
                                        REBL_hRR0, REBL_hRLR);
                            }
                        }
                    }
                    return rebalanceToRite_nl(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0);
                }
            }
        }
    }

    private Node rotateRite_nl(Node ROTR_nParent,
                               Node ROTR_n,
                               Node ROTR_nL,
                               int ROTR_hR,
                               int ROTR_hLL,
                               Node ROTR_nLR,
                               int ROTR_hLR) {

        long ROTR_nodeVer;
        Node ROTR_nPL;
        int ROTR_hNRepl;
        int ROTR_balN;
        int ROTR_balL;

        ROTR_nodeVer = ROTR_n.ver;

        ROTR_nPL = ROTR_nParent.left;

        ROTR_n.ver = BeginChange(ROTR_nodeVer);

        ROTR_n.left = ROTR_nLR;
        if (ROTR_nLR != null) {
            ROTR_nLR.parent = ROTR_n;
        }

        ROTR_nL.rite = ROTR_n;
        ROTR_n.parent = ROTR_nL;

        if (ROTR_nPL == ROTR_n) {
            ROTR_nParent.left = ROTR_nL;
        } else {
            ROTR_nParent.rite = ROTR_nL;
        }
        ROTR_nL.parent = ROTR_nParent;

        ROTR_hNRepl = MaxPlusOne(ROTR_hLR, ROTR_hR);
        ROTR_n.height = ROTR_hNRepl;
        ROTR_nL.height = MaxPlusOne(ROTR_hLL, ROTR_hNRepl);

        ROTR_n.ver = EndChange(ROTR_nodeVer);

        ROTR_balN = ROTR_hLR - ROTR_hR;
        if (ROTR_balN < -1 || ROTR_balN > 1) {

            return ROTR_n;
        }

        if ((ROTR_nLR == null || ROTR_hR == 0) && ROTR_n.val == null) {

            return ROTR_n;
        }

        ROTR_balL = ROTR_hLL - ROTR_hNRepl;
        if (ROTR_balL < -1 || ROTR_balL > 1) {
            return ROTR_nL;
        }

        if (ROTR_hLL == 0 && ROTR_nL.val == null) {
            return ROTR_nL;
        }

        return fixHeight_nl(ROTR_nParent);
    }

    private Node rotateLeft_nl(Node ROTL_nParent,
                               Node ROTL_n,
                               int ROTL_hL,
                               Node ROTL_nR,
                               Node ROTL_nRL,
                               int ROTL_hRL,
                               int ROTL_hRR) {

        long ROTL_nodeVer;
        Node ROTL_nPL;
        int ROTL_hNRepl;
        int ROTL_balN;
        int ROTL_balR;

        ROTL_nodeVer = ROTL_n.ver;

        ROTL_nPL = ROTL_nParent.left;

        ROTL_n.ver = BeginChange(ROTL_nodeVer);

        ROTL_n.rite = ROTL_nRL;
        if (ROTL_nRL != null) {
            ROTL_nRL.parent = ROTL_n;
        }

        ROTL_nR.left = ROTL_n;
        ROTL_n.parent = ROTL_nR;

        if (ROTL_nPL == ROTL_n) {
            ROTL_nParent.left = ROTL_nR;
        } else {
            ROTL_nParent.rite = ROTL_nR;
        }
        ROTL_nR.parent = ROTL_nParent;

        ROTL_hNRepl = MaxPlusOne(ROTL_hL, ROTL_hRL);
        ROTL_n.height = ROTL_hNRepl;
        ROTL_nR.height = MaxPlusOne(ROTL_hNRepl, ROTL_hRR);

        ROTL_n.ver = EndChange(ROTL_nodeVer);

        ROTL_balN = ROTL_hRL - ROTL_hL;
        if (ROTL_balN < -1 || ROTL_balN > 1) {
            return ROTL_n;
        }

        if ((ROTL_nRL == null || ROTL_hL == 0) && ROTL_n.val == null) {
            return ROTL_n;
        }

        ROTL_balR = ROTL_hRR - ROTL_hNRepl;
        if (ROTL_balR < -1 || ROTL_balR > 1) {
            return ROTL_nR;
        }

        if (ROTL_hRR == 0 && ROTL_nR.val == null) {
            return ROTL_nR;
        }

        return fixHeight_nl(ROTL_nParent);
    }

    private Node rotateRiteOverLeft_nl(Node ROTROL_nParent,
                                       Node ROTROL_n,
                                       Node ROTROL_nL,
                                       int ROTROL_hR,
                                       int ROTROL_hLL,
                                       Node ROTROL_nLR,
                                       int ROTROL_hLRL) {
        long ROTROL_nodeOVL;
        long ROTROL_leftOVL;
        Node ROTROL_nPL;
        Node ROTROL_nLRL;
        Node ROTROL_nLRR;
        int ROTROL_hLRR;
        int ROTROL_hNRepl;
        int ROTROL_hLRepl;
        int ROTROL_balN;
        int ROTROL_balLR;

        ROTROL_nodeOVL = ROTROL_n.ver;
        ROTROL_leftOVL = ROTROL_nL.ver;

        ROTROL_nPL = ROTROL_nParent.left;
        ROTROL_nLRL = ROTROL_nLR.left;
        ROTROL_nLRR = ROTROL_nLR.rite;
        ROTROL_hLRR = NullSafeHeight(ROTROL_nLRR);

        ROTROL_n.ver = BeginChange(ROTROL_nodeOVL);
        ROTROL_nL.ver = BeginChange(ROTROL_leftOVL);

        ROTROL_n.left = ROTROL_nLRR;
        if (ROTROL_nLRR != null) {
            ROTROL_nLRR.parent = ROTROL_n;
        }

        ROTROL_nL.rite = ROTROL_nLRL;
        if (ROTROL_nLRL != null) {
            ROTROL_nLRL.parent = ROTROL_nL;
        }

        ROTROL_nLR.left = ROTROL_nL;
        ROTROL_nL.parent = ROTROL_nLR;
        ROTROL_nLR.rite = ROTROL_n;
        ROTROL_n.parent = ROTROL_nLR;

        if (ROTROL_nPL == ROTROL_n) {
            ROTROL_nParent.left = ROTROL_nLR;
        } else {
            ROTROL_nParent.rite = ROTROL_nLR;
        }
        ROTROL_nLR.parent = ROTROL_nParent;

        ROTROL_hNRepl = MaxPlusOne(ROTROL_hLRR, ROTROL_hR);
        ROTROL_n.height = ROTROL_hNRepl;
        ROTROL_hLRepl = MaxPlusOne(ROTROL_hLL, ROTROL_hLRL);
        ROTROL_nL.height = ROTROL_hLRepl;
        ROTROL_nLR.height = MaxPlusOne(ROTROL_hLRepl, ROTROL_hNRepl);

        ROTROL_n.ver = EndChange(ROTROL_nodeOVL);
        ROTROL_nL.ver = EndChange(ROTROL_leftOVL);

        ROTROL_balN = ROTROL_hLRR - ROTROL_hR;
        if (ROTROL_balN < -1 || ROTROL_balN > 1) {
            return ROTROL_n;
        }

        if ((ROTROL_nLRR == null || ROTROL_hR == 0) && ROTROL_n.val == null) {
            return ROTROL_n;
        }

        ROTROL_balLR = ROTROL_hLRepl - ROTROL_hNRepl;
        if (ROTROL_balLR < -1 || ROTROL_balLR > 1) {
            return ROTROL_nLR;
        }

        return fixHeight_nl(ROTROL_nParent);
    }

    private Node rotateLeftOverRite_nl(Node ROTLOR_nParent,
                                       Node ROTLOR_n,
                                       int ROTLOR_hL,
                                       Node ROTLOR_nR,
                                       Node ROTLOR_nRL,
                                       int ROTLOR_hRR,
                                       int ROTLOR_hRLR) {
        long ROTLOR_nodeOVL;
        long ROTLOR_rightOVL;
        Node ROTLOR_nPL;
        Node ROTLOR_nRLL;
        Node ROTLOR_nRLR;
        int ROTLOR_hRLL;
        int ROTLOR_hNRepl;
        int ROTLOR_hRRepl;
        int ROTLOR_balN;
        int ROTLOR_balRL;

        ROTLOR_nodeOVL = ROTLOR_n.ver;
        ROTLOR_rightOVL = ROTLOR_nR.ver;

        ROTLOR_nPL = ROTLOR_nParent.left;
        ROTLOR_nRLL = ROTLOR_nRL.left;
        ROTLOR_nRLR = ROTLOR_nRL.rite;
        ROTLOR_hRLL = NullSafeHeight(ROTLOR_nRLL);

        ROTLOR_n.ver = BeginChange(ROTLOR_nodeOVL);
        ROTLOR_nR.ver = BeginChange(ROTLOR_rightOVL);

        ROTLOR_n.rite = ROTLOR_nRLL;
        if (ROTLOR_nRLL != null) {
            ROTLOR_nRLL.parent = ROTLOR_n;
        }

        ROTLOR_nR.left = ROTLOR_nRLR;
        if (ROTLOR_nRLR != null) {
            ROTLOR_nRLR.parent = ROTLOR_nR;
        }

        ROTLOR_nRL.rite = ROTLOR_nR;
        ROTLOR_nR.parent = ROTLOR_nRL;
        ROTLOR_nRL.left = ROTLOR_n;
        ROTLOR_n.parent = ROTLOR_nRL;

        if (ROTLOR_nPL == ROTLOR_n) {
            ROTLOR_nParent.left = ROTLOR_nRL;
        } else {
            ROTLOR_nParent.rite = ROTLOR_nRL;
        }
        ROTLOR_nRL.parent = ROTLOR_nParent;

        ROTLOR_hNRepl = MaxPlusOne(ROTLOR_hL, ROTLOR_hRLL);
        ROTLOR_n.height = ROTLOR_hNRepl;
        ROTLOR_hRRepl = MaxPlusOne(ROTLOR_hRLR, ROTLOR_hRR);
        ROTLOR_nR.height = ROTLOR_hRRepl;
        ROTLOR_nRL.height = MaxPlusOne(ROTLOR_hNRepl, ROTLOR_hRRepl);

        ROTLOR_n.ver = EndChange(ROTLOR_nodeOVL);
        ROTLOR_nR.ver = EndChange(ROTLOR_rightOVL);

        ROTLOR_balN = ROTLOR_hRLL - ROTLOR_hL;
        if (ROTLOR_balN < -1 || ROTLOR_balN > 1) {
            return ROTLOR_n;
        }
        if ((ROTLOR_nRLL == null || ROTLOR_hL == 0) && ROTLOR_n.val == null) {
            return ROTLOR_n;
        }
        ROTLOR_balRL = ROTLOR_hRRepl - ROTLOR_hNRepl;
        if (ROTLOR_balRL < -1 || ROTLOR_balRL > 1) {
            return ROTLOR_nRL;
        }
        return fixHeight_nl(ROTLOR_nParent);
    }

}
