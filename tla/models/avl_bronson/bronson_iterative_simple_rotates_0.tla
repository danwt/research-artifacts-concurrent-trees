------------------- MODULE bronson_iterative_simple_rotates_0 -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Linearizability, TreeGeneration, TreeStructure 

CONSTANT NullModelValue
CONSTANT Readers \* Always contains 1
CONSTANT Writers

TreeGenSizeMin == 8
TreeGenSizeMax == 8
TreeGenKeyMin ==  1
TreeGenKeyMax == 10
OperationKeyMin == 1
OperationKeyMax == 11
NodeAddressSet == 1..14
CallStackBound == 8
VersionNumberBound == 6

Range(f) == { f[x] : x \in DOMAIN f }

Procs == 
    Writers 
    \* \cup Readers

KeySetToOperateOn == OperationKeyMin..OperationKeyMax

RootHolder == 0
AddressSetWithoutRootHolder == NodeAddressSet
AddressSetWithRootHolder ==  AddressSetWithoutRootHolder \cup {RootHolder}

IntegerShift == 100
Null == IntegerShift + 1
ShrinkingSymbol == IntegerShift + 2
UnlinkedSymbol == IntegerShift + 3
RetrySymbol == IntegerShift + 4
DirectionLeftSymbol == IntegerShift + 5
RiteSymbol == IntegerShift + 6
NoRepairActionRequired == IntegerShift + 7
UnlinkActionRequired == IntegerShift + 8
RebalanceActionRequired == IntegerShift + 9
FalseInt == IntegerShift + 10
TrueInt == IntegerShift + 11
IntBoolAsBool(x) == x = TrueInt
IsIntBool(x) == x = TrueInt \/ x = FalseInt

VersionNumberInitValue == 0

(* --algorithm algo {

variables

    (* Non-algorithm variables *)

    event_sequence = <<>>;
    operation_succeeded = [p \in Procs |-> Null];
    reachable_at_start;

    (* Algorithm variables *)

    ver           = [e \in AddressSetWithRootHolder    |-> VersionNumberInitValue];  
    key           = [e \in AddressSetWithRootHolder    |-> Null]; 
    val           = [e \in AddressSetWithRootHolder    |-> Null]; 
    height        = [e \in AddressSetWithRootHolder    |-> Null]; 
    parent        = [e \in AddressSetWithRootHolder    |-> Null];
    left          = [e \in AddressSetWithRootHolder    |-> Null];
    rite          = [e \in AddressSetWithRootHolder    |-> Null];
    locked        = [e \in AddressSetWithRootHolder    |-> NullModelValue]; 

    ret = [e \in Procs |-> Null]; 

define {

    (* Algorithm operators *)

    NullSafeHeight(e) == IF e = Null THEN 0 ELSE height[e] 
    IsLogicallyDeleted(e) == key[e] # Null /\ val[e] = Null
    
    IsShrinking(x) == x = ShrinkingSymbol
    IsUnlinked(x) == x = UnlinkedSymbol
    IsShrinkingOrUnlinked(x) == IsShrinking(x) \/ IsUnlinked(x)
    NotShrinkingOrUnlinked(x) == ~IsShrinkingOrUnlinked(x)
    BeginChange(x) == ShrinkingSymbol
    EndChange(x) == x + 1

    AppropriateDirection(router_key, sought_key) == IF sought_key < router_key 
                                                    THEN DirectionLeftSymbol
                                                    ELSE RiteSymbol

    Child(Maddr, direction_symbol) == IF direction_symbol = DirectionLeftSymbol 
                                     THEN left[Maddr] 
                                     ELSE rite[Maddr]

    MaxPlusOne(x, y) == IF y < x 
                        THEN x + 1 
                        ELSE y + 1

    BalanceFactorIsBalanced(x) == (0-2 < x) /\ (x < 2)
    BalanceFactorIsImbalanced(x) == ~BalanceFactorIsBalanced(x)

    IsUnusedAddr(e) == key[e] = Null 

    UnusedAddress == CHOOSE e \in AddressSetWithoutRootHolder : IsUnusedAddr(e)

}

macro invoke(Moperation_name, Marg){
    event_sequence := event_sequence \o <<<<"invoke", self, Moperation_name, Marg>>>>;
}

macro respond(Msucceeded_int_bool){
    assert IsIntBool(Msucceeded_int_bool);
    event_sequence := event_sequence \o <<<<"respond", self, IntBoolAsBool(Msucceeded_int_bool) >>>>;
}

(*
Get succeeds if the key was present (and not marked deleted)
Erase succeeds if the key was present and update removes it
Insert succeeds if the key was not present and update inserts it
*)
macro operation_succeed(){
    assert operation_succeeded[self] = Null;
    operation_succeeded[self] := TrueInt;
}

macro operation_fail(){
    assert operation_succeeded[self] = Null;
    operation_succeeded[self] := FalseInt;
}

(*
Must always be called from inside a strongly fair label
*)
macro lock(Maddr){
    await locked[Maddr] = NullModelValue \/ locked[Maddr] = self;
    locked[Maddr] := self;
}

macro unlock(Maddr){
    locked[Maddr] := NullModelValue;
}

macro nullify_ret(){
    ret[self] := Null;
}

macro retry(){
    ret[self] := RetrySymbol;
}

macro await_not_shrinking(Me){
    await ~IsShrinking(Me);
}

macro write_new_leaf(Maddr, Mdir, Mkey, Mval,  Mparent){
    key[Maddr] := Mkey;
    val[Maddr] := Mval;
    parent[Maddr] := Mparent;
    height[Maddr] := 1;
    if(Mdir = DirectionLeftSymbol){
        left[Maddr] := Null || left[Mparent] := Maddr;
        rite[Maddr] := Null;
    }else{
        left[Maddr] := Null;
        rite[Maddr] := Null || rite[Mparent] := Maddr;
    };
    ver[Maddr] := VersionNumberInitValue ;
}

macro write_new_leaf_under_RootHolder(Maddr, Mkey, Mval){
    key[Maddr] := Mkey;
    val[Maddr] := Mval;
    parent[Maddr] := RootHolder;
    height[Maddr] := 1 || height[RootHolder] := 2;
    left[Maddr] := Null;
    rite[RootHolder] := Maddr || rite[Maddr] := Null;
    ver[Maddr] := VersionNumberInitValue ;
}

procedure get(G_k)
{
g0:
    while (TRUE) {
        call getImpl(G_k, RootHolder);
g1:
        if (ret[self] # RetrySymbol) {
            if(ret[self] # Null){
                operation_succeed();
            }else{
                operation_fail();
            };
            return;
        }
    }
}

procedure getImpl(GI_k, GI_node)
variables
    GI_nVer = VersionNumberInitValue;
    GI_dirToC = RiteSymbol;
    GI_child;
    GI_kRead;
    GI_childVer;
{
gi0:
    while (TRUE) {

        GI_child := Child(GI_node, GI_dirToC);

        if (GI_child = Null) {
            if (ver[GI_node] # GI_nVer) {
gi1:
                retry();
                return;
            };
gi2:
            nullify_ret();
            return;
        };
gi3:

        GI_kRead := key[GI_child];

        if (GI_kRead = GI_k) {
gi4:
            ret[self] := val[GI_child];
            return;
        };
gi5:

        GI_childVer := ver[GI_child];

        if (IsShrinkingOrUnlinked(GI_childVer)) {
gi6:

            await_not_shrinking(ver[GI_child]);

            if(ver[GI_node] # GI_nVer){
gi7:
                retry();
                return;
            };

        } else if (GI_child # Child(GI_node, GI_dirToC)) {

            if (ver[GI_node] # GI_nVer) {
gi8:
                retry();
                return;
            };

        } else {
            if (ver[GI_node] # GI_nVer) {
gi9:
                retry();
                return;
            };
gi10:
            GI_node := GI_child;
            GI_dirToC := AppropriateDirection(GI_kRead, GI_k);
            GI_nVer := GI_childVer;
        }
    }
}

procedure update(U_k, U_newValue)
    variables
        U_node;
        U_nVer;
{
u0:
    while (TRUE) {
        U_node := rite[RootHolder];
        if (U_node = Null) {
            if (U_newValue = Null) {
u1:
                operation_fail(); \* Unsuccessful erase
                nullify_ret();
                return;
            };
uLock0RH:+
            lock(RootHolder);
u2MaybeInsertUnderRH:
                if (rite[RootHolder] = Null) {
                    write_new_leaf_under_RootHolder(UnusedAddress, U_k, U_newValue);
u3FinishInsertUnderRH:
                    unlock(RootHolder);
                    operation_succeed(); \* Successful insert
                    nullify_ret();
                    return;
                };
u4UnlockRH:
            unlock(RootHolder);
        } else {
            U_nVer := ver[U_node];
            if (IsShrinkingOrUnlinked(U_nVer)) {
                await_not_shrinking(ver[U_node]);
            } else if (U_node = rite[RootHolder]) {
u5CallUpdateImpl:
                call updateImpl(U_k, U_newValue, RootHolder, U_node, U_nVer);
u6CheckIfDone:
                if (ret[self] # RetrySymbol) {
                    return;
                }
            }
        }
    }
}

procedure updateImpl(UI_k, UI_newValue,  UI_parent,  UI_node,  UI_nVer)
    variables
        UI_kRead;
        UI_success = FALSE;
        UI_damaged;
        UI_childVer;
        UI_child;
{
ui0ReadK:
    while (TRUE) {
        UI_kRead := key[UI_node];
        if (UI_kRead = UI_k) {
ui1:
            call attemptNodeUpdate(UI_newValue, UI_parent, UI_node);
            return;
        };
ui2ReadChild:
        UI_child := Child(UI_node, AppropriateDirection(UI_kRead, UI_k));
        if (ver[UI_node] # UI_nVer) {
ui3Retry:
            retry();
            return;
        };
ui4:
        if (UI_child = Null) {
            if (UI_newValue = Null) {
ui5AlreadyErased:
                nullify_ret();
                operation_fail(); \* Erase fail
                return;
            };
uiLock0Node:+
            lock(UI_node);
ui6:
                if (ver[UI_node] # UI_nVer) {
ui7Retry:
                    retry();
                    unlock(UI_node);
                    return;
                };
ui8:
                if (Child(UI_node, AppropriateDirection(UI_kRead, UI_k)) # Null) {
                    UI_damaged := Null;
                } else {
ui9WriteNewLeaf:
                    write_new_leaf(
                        UnusedAddress, 
                        AppropriateDirection(UI_kRead, UI_k),
                        UI_k,
                        UI_newValue,
                        UI_node
                    );

                    UI_success := TRUE;
                    call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(UI_node);
ui10:
                    UI_damaged := ret[self];
                };
ui11:
            unlock(UI_node);
            if (UI_success) {
ui12RebalAfterInsert:
                call fixHeightAndRebalance(UI_damaged);
ui13:
                nullify_ret();
                operation_succeed();
                return;
            };
        } else {
            UI_childVer := ver[UI_child];
            if (IsShrinkingOrUnlinked(UI_childVer)) {
ui14WaitNotShrink:
                await_not_shrinking(ver[UI_child]);
            } else if (UI_child = Child(UI_node, AppropriateDirection(UI_kRead, UI_k))) {
                if (ver[UI_node] # UI_nVer) {
ui15Retry:
                    retry();
                    return;
                };
ui16Traverse:
                UI_parent := UI_node;
                UI_node := UI_child;
                UI_nVer := UI_childVer;
            }
        }
    }
}

procedure attemptNodeUpdate(ANU_newValue,
                            ANU_parent,
                            ANU_node)
    variables
        ANU_prev;
{
anu0CheckAlreadyLogicallyErased:
    if (ANU_newValue = Null /\ IsLogicallyDeleted(ANU_node)) {
        nullify_ret();
        operation_fail(); \* Fail erase
        return;
    };
anu1:
    if (ANU_newValue = Null /\ (left[ANU_node] = Null \/ rite[ANU_node] = Null)) {
anuLock0Parent:+
        lock(ANU_parent);
anu2:
            if (IsUnlinked(ver[ANU_parent]) \/ parent[ANU_node] # ANU_parent) {
anu3Retry:
                unlock(ANU_parent);
                retry();
                return;
            };
anuLock1Node:+
            lock(ANU_node);
                ANU_prev := val[ANU_node];
                if (ANU_prev = Null) {
anu4EraseIsTooLate:
                    nullify_ret();
                    unlock(ANU_node);
anu5:
                    unlock(ANU_parent);
                    operation_fail(); \* Fail erase
                    return;
                };
anu6:
                call attemptUnlink_argsLocked(ANU_parent, ANU_node);
anu7:
                if (ret[self] = FalseInt) {
anu8Retry:
                    retry();
                    unlock(ANU_node);
anu9:
                    unlock(ANU_parent);
                    return;
                };
anu10UnlinkSucceeded:
            unlock(ANU_node);
            call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ANU_parent);
anu11:
        unlock(ANU_parent);
        call fixHeightAndRebalance(ret[self]);
anu12:
        ret[self] := ANU_prev;
        operation_succeed();
        return;
    };

anuLock2Node:+
    lock(ANU_node);
        if (IsUnlinked(ver[ANU_node])) {
anu13Retry:
            retry();
            unlock(ANU_node);
            return;
        };

anu14:
        if (ANU_newValue = Null /\ (left[ANU_node] = Null \/  rite[ANU_node] = Null)) {
anu15Retry:
            retry();
            unlock(ANU_node);
            return;
        };

anu16WriteVal:
        ANU_prev := val[ANU_node];

        (* -- START of bookkeeping section (not part of algorithm) -- *)
        if(ANU_newValue = Null){
            if(ANU_prev = Null){
                operation_fail();  \* Erase fail
            }else{
                operation_succeed(); \* Erase succeed
            }
        }else{
            if(ANU_prev = Null){
                operation_succeed(); \* Insert succeed
            }else{
                operation_fail();  \* Insert fail
            }
        };
        (* -- END of bookkeeping section (not part of algorithm) -- *)

        val[ANU_node] := ANU_newValue;
        ret[self] := ANU_prev;
anu17:
        ANU_prev := val[ANU_node];
    unlock(ANU_node);
anu18:
    return;
}

procedure requiredRepairActionOrReplacementHeight(RAOH_node)
    variables 
        RAOH_nL;
        RAOH_nR;
        RAOH_hN;
        RAOH_hL0;
        RAOH_hR0;
        RAOH_hNRepl;
{
raoh0ReadLandR:

    RAOH_nL := left[RAOH_node];
    RAOH_nR := rite[RAOH_node];

    if ((RAOH_nL = Null \/  RAOH_nR = Null) /\ IsLogicallyDeleted(RAOH_node)) {
raoh1ShouldUnlink:
        ret[self] := UnlinkActionRequired;
        return;
    };
raoh2ReadHeights:

    RAOH_hN := height[RAOH_node];
    RAOH_hL0 := NullSafeHeight(RAOH_nL);
    RAOH_hR0 := NullSafeHeight(RAOH_nR);

    RAOH_hNRepl := MaxPlusOne(RAOH_hL0, RAOH_hR0);

    if (BalanceFactorIsImbalanced(RAOH_hL0 - RAOH_hR0)) {
raoh3ShouldRebalance:
        ret[self] := RebalanceActionRequired;
        return;
    };
raoh4:

    if(RAOH_hN # RAOH_hNRepl){
raoh5ShouldUpdateHeight:
        ret[self] := RAOH_hNRepl;
    }else{
raoh6ShouldDoNothing:
        ret[self] := NoRepairActionRequired;
    };
raoh7:
    return;
}

procedure fixHeightAndRebalance(FHR_node)
    variables
        FHR_actionOrHeight;
        FHR_nP;
        FHR_nL;
        FHR_nR;
        FHR_hN;
        FHR_hL0;
        FHR_hR0;
        FHR_hNRepl;
{
fhr0:
    while (FHR_node # Null) {
        if(parent[FHR_node] = Null){
            return;
        };
fhr1GetRAOH:
        call requiredRepairActionOrReplacementHeight(FHR_node);
fhr2:
        FHR_actionOrHeight := ret[self]; 
        if (FHR_actionOrHeight = NoRepairActionRequired \/  IsUnlinked(ver[FHR_node])) {
fhr3NoMoreWork:
            return;
        };
fhr4:
        if (FHR_actionOrHeight # UnlinkActionRequired /\ FHR_actionOrHeight # RebalanceActionRequired) {
fhrLock0Node:+
            lock(FHR_node);
fhr5:
                call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_node);
fhr6:
            unlock(FHR_node);
            FHR_node := ret[self];
        } else {
            FHR_nP := parent[FHR_node];
fhrLock1nP:+
            lock(FHR_nP);
fhr7:
                if (~IsUnlinked(ver[FHR_nP]) /\ parent[FHR_node] = FHR_nP) {
fhrLock2Node:+
                    lock(FHR_node);
fhr8ReadLandRMaybeHeights:
                        FHR_nL := left[FHR_node];
                        FHR_nR := rite[FHR_node];
                        if ((FHR_nL = Null \/  FHR_nR = Null) /\ IsLogicallyDeleted(FHR_node)) {
fhr9:
                            call attemptUnlink_argsLocked(FHR_nP, FHR_node);
fhr10:
                            if (ret[self] = TrueInt) {
fhr11UnlinkSucceeded:
                                call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_nP);
                            }else{
                                ret[self] := FHR_node;
                            }
                        } else {
                              FHR_hN := height[FHR_node];
                              FHR_hL0 := NullSafeHeight(FHR_nL);
                              FHR_hR0 := NullSafeHeight(FHR_nR);
                              FHR_hNRepl := MaxPlusOne(FHR_hL0, FHR_hR0);
                            if (FHR_hL0 + 1 < FHR_hR0) { \* rite heavy
fhrLock3nR:+
                                lock(FHR_nR);
                                    call rebalanceToLeft_argsLocked(FHR_nP, FHR_node, FHR_nR, FHR_hL0);
fhr12:
                                unlock(FHR_nR);
                            } else if (FHR_hL0 > 1 + FHR_hR0) { \* left heavy
fhrLock4nL:+
                                lock(FHR_nL);
                                    call rebalanceToRite_argsLocked(FHR_nP, FHR_node, FHR_nL, FHR_hR0);
fhr13:
                                unlock(FHR_nL);
                            } else if (FHR_hNRepl # FHR_hN) {
fhr14WriteReplHeight:
                                height[FHR_node] := FHR_hNRepl;
                                call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_nP);
                            } else {
                                \* NOTE: This lets us set FHR_node to ret[self] after we unlock.
                                ret[self] := Null; 
                            };
                        };
fhr15:
                    unlock(FHR_node);
                    FHR_node := ret[self];
                };
fhr16:
            unlock(FHR_nP);
        }
    };
    return;
}

procedure attemptUnlink_argsLocked(AUL_parent, AUL_node) 
    variables
        AUL_parentL;
        AUL_parentR;
        AUL_left;
        AUL_rite;
        AUL_splice;
{
aul0ReadParentLandR:
    AUL_parentL := left[AUL_parent];
    AUL_parentR := rite[AUL_parent];

    if (AUL_parentL # AUL_node /\ AUL_parentR # AUL_node) {
aul1ParentNotParent:
        ret[self] := FalseInt;
        return;
    };
aul2ReadLandR:

    AUL_left := left[AUL_node];
    AUL_rite := rite[AUL_node];

    if (AUL_left # Null /\ AUL_rite # Null) {
aul3CantUnlink:
        ret[self] := FalseInt;
        return;
    };
aul4SpliceOut:

    AUL_splice := IF AUL_left # Null THEN AUL_left ELSE AUL_rite;

    if (AUL_parentL = AUL_node) {
        left[AUL_parent] := AUL_splice;
    } else {
        rite[AUL_parent] := AUL_splice;
    };
    if (AUL_splice # Null) {
        parent[AUL_splice] := AUL_parent;
    };

    ver[AUL_node] := UnlinkedSymbol;
    val[AUL_node] := Null;

    ret[self] := TrueInt;
aul5:
    return;
}

procedure fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(S_node)
variables
    S_t;
{
s0:
    call requiredRepairActionOrReplacementHeight(S_node);
s1:
    S_t := ret[self];
    if(S_t = RebalanceActionRequired){
        ret[self] := S_node;
    } else if(S_t = UnlinkActionRequired){
        ret[self] := S_node;
    } else if(S_t = NoRepairActionRequired){
        nullify_ret();
    } else{
        height[S_node] := S_t;
        ret[self] := parent[S_node];
    };
s2:
    return;
}

procedure rebalanceToRite_argsLocked(REBR_nP,
                                     REBR_n,
                                     REBR_nL,
                                     REBR_hR0)
    variables
        REBR_hL;
        REBR_nLR;
        REBR_hLL0;
        REBR_hLR0;
        REBR_hLR;
        REBR_hLRL;
        REBR_nLRL;
        REBR_nLRR;
        REBR_hLRR;
{
rebr0:
    REBR_hL := height[REBR_nL];
    if (REBR_hL <= 1 + REBR_hR0) { \* Left heavy enough to be worth balancing?
rebr1NoNeed:
        ret[self] := REBR_n;
        return;
    };
rebr2:
    REBR_nLR := rite[REBR_nL];
    REBR_hLL0 := NullSafeHeight(left[REBR_nL]);
    REBR_hLR0 := NullSafeHeight(REBR_nLR);
    if (REBR_hLL0 >= REBR_hLR0) { \* Left is not rite heavy
rebr3:
        call rotateRite_argsLocked(REBR_nP, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR, REBR_hLR0);
        return;
    };
rebrLock0nLR:+
    lock(REBR_nLR);
        REBR_hLR := height[REBR_nLR];
        if (REBR_hLL0 >= REBR_hLR) { \* Left is not rite heavy
rebr4:
            call rotateRite_argsLocked(REBR_nP, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR, REBR_hLR);
rebr5:
            unlock(REBR_nLR);
            return;
        };
rebr6:
        \* Left is rite heavy
        REBR_hLRL := NullSafeHeight(left[REBR_nLR]);
        if (
                BalanceFactorIsBalanced(REBR_hLL0 - REBR_hLRL) \* Left is balanced
        ) {
rebr7:
            \* Left will be balanced after double rotate
            REBR_nLRL := left[REBR_nLR];
            REBR_nLRR := rite[REBR_nLR];
            REBR_hLRR := NullSafeHeight(REBR_nLRR);
            call rotateLeft_argsLocked(REBR_n, REBR_nL, REBR_hLL0, REBR_nLR, REBR_nLRL, REBR_hLRL, REBR_hLRR);
rebr8:
            call rotateRite_argsLocked(REBR_nP, REBR_n, REBR_nLR, REBR_hR0, REBR_hL, REBR_nLRR, REBR_hLRR);
rebr9:
            if (ret[self] # REBR_n) {
                ret[self] := REBR_nLR;
            };
            call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ret[self]);
rebr10:
            unlock(REBR_nLR);
            return;
        };
        \* More care needed to properly rebalance left child, delegate the work
rebr11:
        call rebalanceToLeft_argsLocked(REBR_n, REBR_nL, REBR_nLR, REBR_hLL0);
rebr12:
    unlock(REBR_nLR);
    return;
}

procedure rebalanceToLeft_argsLocked(REBL_nP,
                                     REBL_n,
                                     REBL_nR,
                                     REBL_hL0)
    variables
        REBL_hR; 
        REBL_nRL; 
        REBL_hRL0; 
        REBL_hRR0; 
        REBL_hRL; 
        REBL_hRLR; 
        REBL_nRLL;
        REBL_nRLR;
        REBL_hRLL;
{
rebl0:
    REBL_hR := height[REBL_nR];
    if (REBL_hL0 + 1 >= REBL_hR) { \* Rite heavy enough to be worth balancing?
rebl1NoNeed:
        ret[self] := REBL_n;
        return;
    };
rebl2:
    REBL_nRL := left[REBL_nR];
    REBL_hRL0 := NullSafeHeight(REBL_nRL);
    REBL_hRR0 := NullSafeHeight(rite[REBL_nR]);
    if (REBL_hRL0 <= REBL_hRR0) { \* Rite is not left heavy
rebl3:
        call rotateLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRL0, REBL_hRR0);
        return;
    };
reblLock0nRL:+
    lock(REBL_nRL);
        REBL_hRL := height[REBL_nRL];
        if (REBL_hRL <= REBL_hRR0) { \* Rite is not left heavy
rebl4:
            call rotateLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRL, REBL_hRR0);
rebl5:
            unlock(REBL_nRL);
            return;
        };
rebl6:
        \* Rite is left heavy
        REBL_hRLR := NullSafeHeight(rite[REBL_nRL]);
        if (
                BalanceFactorIsBalanced(REBL_hRR0 - REBL_hRLR) \* Rite is balanced
        ) {
rebl7:
            \* Rite will be balanced after double rotate
            REBL_nRLL := left[REBL_nRL];
            REBL_nRLR := rite[REBL_nRL];
            REBL_hRLL := NullSafeHeight(REBL_nRLL);
            call rotateRite_argsLocked(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0, REBL_hRLL, REBL_nRLR, REBL_hRLR);
rebl8:
            call rotateLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nRL, REBL_nRLL, REBL_hRLL, REBL_hR);
rebl9:
            if (ret[self] # REBL_n) {
                ret[self] := REBL_nRL;
            };
            call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ret[self]);
rebl10:
            unlock(REBL_nRL);
            return;
        };
        \* More care needed to properly rebalance rite child, delegate the work
rebl11:
        call rebalanceToRite_argsLocked(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0);
rebl12:
    unlock(REBL_nRL);
    return;
}

procedure rotateRite_argsLocked(ROTR_nP,
                                ROTR_n,
                                ROTR_nL,
                                ROTR_hR,
                                ROTR_hLL,
                                ROTR_nLR,
                                ROTR_hLR)
    variables
        ROTR_nVer;
        ROTR_nPL;
        ROTR_hNRepl;
{
rotr0:
    ROTR_nVer := ver[ROTR_n];
rotr1:
    ROTR_nPL := left[ROTR_nP];
rotr2BeginChange:
    ver[ROTR_n] := BeginChange(ROTR_nVer);
rotr3MutnandnLR:

    left[ROTR_n] := ROTR_nLR;
    if (ROTR_nLR # Null) {
        parent[ROTR_nLR] := ROTR_n;
    };

rotr4MutnLandn:
    rite[ROTR_nL] := ROTR_n;
    parent[ROTR_n] := ROTR_nL;

rotr5MutnP:
    if (ROTR_nPL = ROTR_n) {
        left[ROTR_nP] := ROTR_nL;
    } else {
        rite[ROTR_nP] := ROTR_nL;
    };
rotr6MutnL:
    parent[ROTR_nL] := ROTR_nP;
rotr7Mutn:

    ROTR_hNRepl := MaxPlusOne(ROTR_hLR, ROTR_hR);
    height[ROTR_n] := ROTR_hNRepl;

rotr8MutnL:

    height[ROTR_nL] := MaxPlusOne(ROTR_hLL, ROTR_hNRepl);
rotr9EndChange:
    ver[ROTR_n] := EndChange(ROTR_nVer);

    if (BalanceFactorIsImbalanced(ROTR_hLR - ROTR_hR)) {
rotr6:
        ret[self] := ROTR_n;
        return;
    };
rotr7:
    if (BalanceFactorIsImbalanced(ROTR_hLL - ROTR_hNRepl)) {
rotr8:
        ret[self] := ROTR_nL;
        return;
    };
rotr9:
    call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ROTR_nP);
    return;
}

procedure rotateLeft_argsLocked(ROTL_nP,
                                ROTL_n,
                                ROTL_hL,
                                ROTL_nR,
                                ROTL_nRL,
                                ROTL_hRL,
                                ROTL_hRR)
    variables
        ROTL_nVer;
        ROTL_nPL;
        ROTL_hNRepl;
{
rotl0:
    ROTL_nVer := ver[ROTL_n];
rotl1:
    ROTL_nPL := left[ROTL_nP];
rotl2BeginChange:
    ver[ROTL_n] := BeginChange(ROTL_nVer);
rotl3MutnandnLR:

    rite[ROTL_n]:= ROTL_nRL;
    if (ROTL_nRL # Null) {
        parent[ROTL_nRL] := ROTL_n;
    };

rotl4MutnRandn:
    left[ROTL_nR] := ROTL_n;
    parent[ROTL_n] := ROTL_nR;

rotl5MutnP:
    if (ROTL_nPL = ROTL_n) {
        left[ROTL_nP] := ROTL_nR;
    } else {
        rite[ROTL_nP] := ROTL_nR;
    };
rotl6MutnR:
    parent[ROTL_nR] := ROTL_nP;
rotl7Mutn:

    ROTL_hNRepl := MaxPlusOne(ROTL_hL, ROTL_hRL);
    height[ROTL_n] := ROTL_hNRepl;

rotl7MutnR:

    height[ROTL_nR] := MaxPlusOne(ROTL_hNRepl, ROTL_hRR);
rotl5EndChange:
    ver[ROTL_n] := EndChange(ROTL_nVer);

    if (BalanceFactorIsImbalanced(ROTL_hRL - ROTL_hL )) {
rotl6:
        ret[self] := ROTL_n;
        return;
    };
rotl7:
    if (BalanceFactorIsImbalanced(ROTL_hRR - ROTL_hNRepl)) {
rotl8:
        ret[self] := ROTL_nR;
        return;
    };
rotl9:
    call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ROTL_nP);
    return;
}

(*
End procedures
---------------
*)


(*
---------------
Begin processes
*)

fair process (initializer = "initializer")
{
init0:
    \* with (starter_state \in InterestingAvlTree(TreeGenKeyMin, TreeGenKeyMax, TreeGenSizeMin, TreeGenSizeMax, 10)){
    with (starter_state \in SetOfInterestingAvlTrees(TreeGenKeyMin, TreeGenKeyMax, TreeGenSizeMin, TreeGenSizeMax)){
        key := starter_state.key @@ key;
        val := starter_state.val @@ val;
        left := starter_state.left @@ left;
        rite := starter_state.rite @@ rite;
        height := starter_state.height @@ height;
        parent := starter_state.parent @@ parent;
        reachable_at_start := starter_state.reachable;
    }
}

\* fair process (reader \in Readers)
\* {
\* readInv:
    \* await pc["initializer"] = "Done";
    \* with (e \in KeySetToOperateOn){
        \* invoke("get", e);
        \* call get(e);
    \* };
\* readResp:
    \* respond(operation_succeeded[self]);
\* }

fair process (writer \in Writers )
{
writeInv:
    await pc["initializer"] = "Done";
    with (e \in KeySetToOperateOn){
        \* either{
            \* invoke("insert", e);
            \* call update(e, e);
        \* } 
        \* or {
            invoke("erase", e);
            call update(e, Null);
        \* };
    };
writeResp:
    respond(operation_succeeded[self]);
}

fair process (verifier = "verifier")
{
verif0:
    \* await \A p \in Readers  : pc[p] = "Done";
    await \A p \in Writers  : pc[p] = "Done";
    assert IsLinearizable(event_sequence, reachable_at_start);
}

} *)


\* BEGIN TRANSLATION (chksum(pcal) = "cc90ae3c" /\ chksum(tla) = "6775548a")
\* END TRANSLATION 

VersionNumbersAreBounded == \A x \in Range(ver) : x <= VersionNumberBound \/ IsShrinkingOrUnlinked(x)

CallStackSizesAreBounded == \A p \in Procs : Len(stack[p]) < CallStackBound

SanityChecks == CallStackSizesAreBounded /\ VersionNumbersAreBounded

QuiescenceGuarantees == 

                    LET 

                        IsQuiescent(p) == pc[p] \in 
                            {
                                "WriteInv",
                                "WriteResp",
                                "Done"
                            }

                            
                    IN  (\A p \in Writers: IsQuiescent(p)) => 
                        (
                        \* /\ IsCycleFree(Null, left, rite, RootHolder)
                        /\ IsBalanced(Null, left, rite, RootHolder)
                        )

AllInvariants == /\ SanityChecks
                 /\ QuiescenceGuarantees

=============================================================================
\* Modification History
\* Last modified Tue Jun 15 18:25:43 BST 2021 by dan
\* Created Thu Apr 01 09:35:51 BST 2021 by dan
