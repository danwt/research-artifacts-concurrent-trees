------------------- MODULE bronson_iterative_brown_child_read_optimization_0 -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Linearizability, TreeGeneration, TreeStructure 

CONSTANT NullModelValue
CONSTANT Readers \* Always contains 1
CONSTANT Writers

TreeGenSizeMin == 7
TreeGenSizeMax == 7
TreeGenKeyMin ==  2
TreeGenKeyMax == 9
OperationKeyMin == 1
OperationKeyMax == 10
NodeAddressSet == 1..14
CallStackLimit == 6
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
    num_write_operations = [p \in Writers |-> 0];
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
uLock0:+
            lock(RootHolder);
u2:
                if (rite[RootHolder] = Null) {
                    write_new_leaf_under_RootHolder(UnusedAddress, U_k, U_newValue);
u3:
                    unlock(RootHolder);
                    operation_succeed(); \* Successful insert
                    nullify_ret();
                    return;
                };
u4:
            unlock(RootHolder);
        } else {
            U_nVer := ver[U_node];
            if (IsShrinkingOrUnlinked(U_nVer)) {
                await_not_shrinking(ver[U_node]);
            } else if (U_node = rite[RootHolder]) {
u5:
                call updateImpl(U_k, U_newValue, RootHolder, U_node, U_nVer);
u6:
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
ui0:
    while (TRUE) {
        UI_kRead := key[UI_node];
        if (UI_kRead = UI_k) {
uiT0:
            call attemptNodeUpdate(UI_newValue, UI_parent, UI_node);
            return;
        };
ui1:
        UI_child := Child(UI_node, AppropriateDirection(UI_kRead, UI_k));
        if (ver[UI_node] # UI_nVer) {
ui2:
            retry();
            return;
        };
ui3:
        if (UI_child = Null) {
            if (UI_newValue = Null) {
ui4:
                nullify_ret();
                operation_fail(); \* Erase fail
                return;
            };
uiLock0:+
            lock(UI_node);
ui7:
                if (ver[UI_node] # UI_nVer) {
ui8:
                    retry();
                    unlock(UI_node);
                    return;
                };
ui9:
                if (Child(UI_node, AppropriateDirection(UI_kRead, UI_k)) # Null) {
                    UI_damaged := Null;
                } else {
ui10:
                    write_new_leaf(
                        UnusedAddress, 
                        AppropriateDirection(UI_kRead, UI_k),
                        UI_k,
                        UI_newValue,
                        UI_node
                    );

                    UI_success := TRUE;
                    call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(UI_node);
ui11:
                    UI_damaged := ret[self];
                };
ui12:
            unlock(UI_node);
            if (UI_success) {
ui13:
                call fixHeightAndRebalance(UI_damaged);
ui14:
                nullify_ret();
                operation_succeed();
                return;
            };
        } else {
            UI_childVer := ver[UI_child];

            if (ver[UI_node] # UI_nVer) {
ui16:
                retry();
                return;
            };
ui17:
            UI_parent := UI_node;
            UI_node := UI_child;
            UI_nVer := UI_childVer;
        }
    }
}

procedure attemptNodeUpdate(ANU_newValue,
                            ANU_parent,
                            ANU_node)
    variables
        ANU_prev;
{
anu0:
    if (ANU_newValue = Null /\ IsLogicallyDeleted(ANU_node)) {
        nullify_ret();
        operation_fail(); \* Fail erase
        return;
    };
anu1:
    if (ANU_newValue = Null /\ (left[ANU_node] = Null \/ rite[ANU_node] = Null)) {
anuLock0:+
        lock(ANU_parent);
anu2:
            if (IsUnlinked(ver[ANU_parent]) \/ parent[ANU_node] # ANU_parent) {
anu3:
                unlock(ANU_parent);
                retry();
                return;
            };
anuLock1:+
            lock(ANU_node);
                ANU_prev := val[ANU_node];
                if (ANU_prev = Null) {
anu4:
                    nullify_ret();
                    unlock(ANU_node);
anu5:
                    unlock(ANU_parent);
                    operation_fail();
                    return;
                };
anu6:
                call attemptUnlink_argsLocked(ANU_parent, ANU_node);
anu7:
                if (ret[self] = FalseInt) {
anu8:
                    retry();
                    unlock(ANU_node);
anu9:
                    unlock(ANU_parent);
                    return;
                };
anu10:
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

anuLock2:+
    lock(ANU_node);
        if (IsUnlinked(ver[ANU_node])) {
anu13:
            retry();
            unlock(ANU_node);
            return;
        };

anu14:
        if (ANU_newValue = Null /\ (left[ANU_node] = Null \/  rite[ANU_node] = Null)) {
anu15:
            retry();
            unlock(ANU_node);
            return;
        };

anu16:
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

procedure requiredRepairActionOrReplacementHeight(RRORH_node)
    variables 
        RRORH_nL;
        RRORH_nR;
        RRORH_hN;
        RRORH_hL0;
        RRORH_hR0;
        RRORH_hNRepl;
{
rrorh0:

    RRORH_nL := left[RRORH_node];
    RRORH_nR := rite[RRORH_node];

    if ((RRORH_nL = Null \/  RRORH_nR = Null) /\ IsLogicallyDeleted(RRORH_node)) {
rrorh1:
        ret[self] := UnlinkActionRequired;
        return;
    };
rrorh2:

    RRORH_hN := height[RRORH_node];
    RRORH_hL0 := NullSafeHeight(RRORH_nL);
    RRORH_hR0 := NullSafeHeight(RRORH_nR);

    RRORH_hNRepl := MaxPlusOne(RRORH_hL0, RRORH_hR0);

    if (BalanceFactorIsImbalanced(RRORH_hL0 - RRORH_hR0)) {
rrorh3:
        ret[self] := RebalanceActionRequired;
        return;
    };
rrorh4:

    if(RRORH_hN # RRORH_hNRepl){
        ret[self] := RRORH_hNRepl;
    }else{
        ret[self] := NoRepairActionRequired;
    };
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
fhr1:
        call requiredRepairActionOrReplacementHeight(FHR_node);
fhr2:
        FHR_actionOrHeight := ret[self]; 
        if (FHR_actionOrHeight = NoRepairActionRequired \/  IsUnlinked(ver[FHR_node])) {
fhr3:
            return;
        };
fhr4:
        if (FHR_actionOrHeight # UnlinkActionRequired /\ FHR_actionOrHeight # RebalanceActionRequired) {
fhrLock0:+
            lock(FHR_node);
                call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_node);
fhr5:
            unlock(FHR_node);
            FHR_node := ret[self];
        } else {
            FHR_nP := parent[FHR_node];
fhrLock1:+
            lock(FHR_nP);
                if (~IsUnlinked(ver[FHR_nP]) /\ parent[FHR_node] = FHR_nP) {
fhrLock2:+
                    lock(FHR_node);
                        FHR_nL := left[FHR_node];
                        FHR_nR := rite[FHR_node];
                        if ((FHR_nL = Null \/  FHR_nR = Null) /\ IsLogicallyDeleted(FHR_node)) {
fhr6:
                            call attemptUnlink_argsLocked(FHR_nP, FHR_node);
fhr7:
                            if (ret[self] = TrueInt) {
fhr8:
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
fhrLock3:+
                                lock(FHR_nR);
                                    call rebalanceToLeft_argsLocked(FHR_nP, FHR_node, FHR_nR, FHR_hL0);
fhr9:
                                unlock(FHR_nR);
                            } else if (FHR_hL0 > 1 + FHR_hR0) { \* left heavy
fhrLock4:+
                                lock(FHR_nL);
                                    call rebalanceToRite_argsLocked(FHR_nP, FHR_node, FHR_nL, FHR_hR0);
fhr10:
                                unlock(FHR_nL);
                            } else if (FHR_hNRepl # FHR_hN) {
fhr11:
                                height[FHR_node] := FHR_hNRepl;
                                call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(FHR_nP);
                            } else {
                                \* NOTE: This lets us set FHR_node to ret[self] after we unlock.
                                ret[self] := Null; 
                            };
                        };
fhr12:
                    unlock(FHR_node);
                    FHR_node := ret[self];
                };
fhr13:
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
aul0:
    AUL_parentL := left[AUL_parent];
    AUL_parentR := rite[AUL_parent];

    if (AUL_parentL # AUL_node /\ AUL_parentR # AUL_node) {
aul1:
        ret[self] := FalseInt;
        return;
    };
aul2:

    AUL_left := left[AUL_node];
    AUL_rite := rite[AUL_node];

    if (AUL_left # Null /\ AUL_rite # Null) {
aul3:
        ret[self] := FalseInt;
        return;
    };
aul4:

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
{
rebr0:
    REBR_hL := height[REBR_nL];
    if (REBR_hL <= 1 + REBR_hR0) { \* Left heavy enough to be worth balancing?
rebr1:
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
rebrLock0:+
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
            call rotateLeftThenRite_argsLocked(REBR_nP, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR, REBR_hLRL);
rebr8:
            unlock(REBR_nLR);
            return;
        };
        \* More care needed to properly rebalance left child, delegate the work
rebr9:
        call rebalanceToLeft_argsLocked(REBR_n, REBR_nL, REBR_nLR, REBR_hLL0);
rebr10:
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
{
rebl0:
    REBL_hR := height[REBL_nR];
    if (REBL_hL0 + 1 >= REBL_hR) { \* Rite heavy enough to be worth balancing?
rebl1:
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
reblLock0:+
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
            call rotateRiteThenLeft_argsLocked(REBL_nP, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRR0, REBL_hRLR);
rebl8:
            unlock(REBL_nRL);
            return;
        };
        \* More care needed to properly rebalance rite child, delegate the work
rebl9:
        call rebalanceToRite_argsLocked(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0);
rebl10:
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
rotr2:
    ver[ROTR_n] := BeginChange(ROTR_nVer);

    left[ROTR_n] := ROTR_nLR;
    if (ROTR_nLR # Null) {
        parent[ROTR_nLR] := ROTR_n;
    };

    rite[ROTR_nL] := ROTR_n;
rotr3:
    parent[ROTR_n] := ROTR_nL;

rotr4:
    if (ROTR_nPL = ROTR_n) {
        left[ROTR_nP] := ROTR_nL;
    } else {
        rite[ROTR_nP] := ROTR_nL;
    };
    parent[ROTR_nL] := ROTR_nP;

    ROTR_hNRepl := MaxPlusOne(ROTR_hLR, ROTR_hR);
    height[ROTR_n] := ROTR_hNRepl;
rotr5:
    height[ROTR_nL] := MaxPlusOne(ROTR_hLL, ROTR_hNRepl);

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
rotl2:

    ver[ROTL_n] := BeginChange(ROTL_nVer);

    rite[ROTL_n]:= ROTL_nRL;
    if (ROTL_nRL # Null) {
        parent[ROTL_nRL] := ROTL_n;
    };

    left[ROTL_nR] := ROTL_n;
rotl3:
    parent[ROTL_n] := ROTL_nR;

rotl4:
    if (ROTL_nPL = ROTL_n) {
        left[ROTL_nP] := ROTL_nR;
    } else {
        rite[ROTL_nP] := ROTL_nR;
    };
    parent[ROTL_nR] := ROTL_nP;

    ROTL_hNRepl := MaxPlusOne(ROTL_hL, ROTL_hRL);
    height[ROTL_n] := ROTL_hNRepl;
rotl5:
    height[ROTL_nR] := MaxPlusOne(ROTL_hNRepl, ROTL_hRR);

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

procedure rotateLeftThenRite_argsLocked(ROTLTR_nP,
                                        ROTLTR_n,
                                        ROTLTR_nL,
                                        ROTLTR_hR,
                                        ROTLTR_hLL,
                                        ROTLTR_nLR,
                                        ROTLTR_hLRL)
    variables
        ROTLTR_nVer;
        ROTLTR_nLVer;
        ROTLTR_nPL;
        ROTLTR_nLRL;
        ROTLTR_nLRR;
        ROTLTR_hLRR;
        ROTLTR_hNRepl;
        ROTLTR_hLRepl;
{
rotltr0:
    ROTLTR_nVer := ver[ROTLTR_n];
    ROTLTR_nLVer := ver[ROTLTR_nL];
    ROTLTR_nPL := left[ROTLTR_nP];
    ROTLTR_nLRL := left[ROTLTR_nLR];
    ROTLTR_nLRR := rite[ROTLTR_nLR];
    ROTLTR_hLRR := NullSafeHeight(ROTLTR_nLRR);

rotltr1:
    ver[ROTLTR_n] := BeginChange(ROTLTR_nVer);
rotltr2:
    ver[ROTLTR_nL] := BeginChange(ROTLTR_nLVer);

    left[ROTLTR_n] := ROTLTR_nLRR;
    if (ROTLTR_nLRR # Null) {
rotltr3:
        parent[ROTLTR_nLRR] := ROTLTR_n;
    };

rotltr4:
    rite[ROTLTR_nL] := ROTLTR_nLRL;
    if (ROTLTR_nLRL # Null) {
rotltr5:
        parent[ROTLTR_nLRL] := ROTLTR_nL;
    };

rotltr6:
    left[ROTLTR_nLR] := ROTLTR_nL;
rotltr7:
    parent[ROTLTR_nL] := ROTLTR_nLR;
rotltr8:
    rite[ROTLTR_nLR] := ROTLTR_n;
rotltr9:
    parent[ROTLTR_n] := ROTLTR_nLR;

    if (ROTLTR_nPL = ROTLTR_n) {
rotltr10:
        left[ROTLTR_nP] := ROTLTR_nLR;
    } else {
rotltr11:
        rite[ROTLTR_nP] := ROTLTR_nLR;
    };
rotltr12:
    parent[ROTLTR_nLR] := ROTLTR_nP;

    ROTLTR_hNRepl := MaxPlusOne(ROTLTR_hLRR, ROTLTR_hR);
rotltr13:
    height[ROTLTR_n] := ROTLTR_hNRepl;
    ROTLTR_hLRepl := MaxPlusOne(ROTLTR_hLL, ROTLTR_hLRL);
rotltr14:
    height[ROTLTR_nL] := ROTLTR_hLRepl;
rotltr15:
    height[ROTLTR_nLR] := MaxPlusOne(ROTLTR_hLRepl, ROTLTR_hNRepl);

rotltr16:
    ver[ROTLTR_n] := EndChange(ROTLTR_nVer);
rotltr17:
    ver[ROTLTR_nL] := EndChange(ROTLTR_nLVer);

    if (BalanceFactorIsImbalanced(ROTLTR_hLRR - ROTLTR_hR)) {
rotltr18:
        ret[self] := ROTLTR_n;
        return;
    };
rotltr19:
    if (BalanceFactorIsImbalanced(ROTLTR_hLRepl - ROTLTR_hNRepl)) {
rotltr20:
        ret[self] := ROTLTR_nLR;
        return;
    };

rotltr21:
    call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ROTLTR_nP);
    return;
}

procedure rotateRiteThenLeft_argsLocked(ROTRTL_nP,
                                        ROTRTL_n,
                                        ROTRTL_hL,
                                        ROTRTL_nR,
                                        ROTRTL_nRL,
                                        ROTRTL_hRR,
                                        ROTRTL_hRLR)
    variables
        ROTRTL_nVer; 
        ROTRTL_nRVer; 
        ROTRTL_nPL; 
        ROTRTL_nRLL; 
        ROTRTL_nRLR; 
        ROTRTL_hRLL; 
        ROTRTL_hNRepl; 
        ROTRTL_hRRepl; 
{
rotrtl0:
    ROTRTL_nVer := ver[ROTRTL_n];
    ROTRTL_nRVer := ver[ROTRTL_nR];
    ROTRTL_nPL := left[ROTRTL_nP];
    ROTRTL_nRLL := left[ROTRTL_nRL];
    ROTRTL_nRLR := rite[ROTRTL_nRL];
    ROTRTL_hRLL := NullSafeHeight(ROTRTL_nRLL);

rotrtl1:
    ver[ROTRTL_n] := BeginChange(ROTRTL_nVer);
rotrtl2:
    ver[ROTRTL_nR] := BeginChange(ROTRTL_nRVer);

    rite[ROTRTL_n]:= ROTRTL_nRLL;
    if (ROTRTL_nRLL # Null) {
rotrtl3:
        parent[ROTRTL_nRLL] := ROTRTL_n;
    };

rotrtl4:
    left[ROTRTL_nR] := ROTRTL_nRLR;
    if (ROTRTL_nRLR # Null) {
rotrtl5:
        parent[ROTRTL_nRLR] := ROTRTL_nR;
    };

rotrtl6:
    rite[ROTRTL_nRL] := ROTRTL_nR;
rotrtl7:
    parent[ROTRTL_nR] := ROTRTL_nRL;
rotrtl8:
    left[ROTRTL_nRL] := ROTRTL_n;
rotrtl9:
    parent[ROTRTL_n] := ROTRTL_nRL;

    if (ROTRTL_nPL = ROTRTL_n) {
rotrtl10:
        left[ROTRTL_nP] := ROTRTL_nRL;
    } else {
rotrtl11:
        rite[ROTRTL_nP] := ROTRTL_nRL;
    };
rotrtl12:
    parent[ROTRTL_nRL] := ROTRTL_nP;

    ROTRTL_hNRepl := MaxPlusOne(ROTRTL_hL, ROTRTL_hRLL);
rotrtl13:
    height[ROTRTL_n] := ROTRTL_hNRepl;
    ROTRTL_hRRepl := MaxPlusOne(ROTRTL_hRLR, ROTRTL_hRR);
rotrtl14:
    height[ROTRTL_nR] := ROTRTL_hRRepl;
rotrtl15:
    height[ROTRTL_nRL] := MaxPlusOne(ROTRTL_hNRepl, ROTRTL_hRRepl);

rotrtl16:
    ver[ROTRTL_n] := EndChange(ROTRTL_nVer);
rotrtl17:
    ver[ROTRTL_nR] := EndChange(ROTRTL_nRVer);

    if (BalanceFactorIsImbalanced(ROTRTL_hRLL - ROTRTL_hL)) {
rotrtl18:
        ret[self] := ROTRTL_n;
        return;
    };
rotrtl19:
    if (BalanceFactorIsImbalanced(ROTRTL_hRRepl - ROTRTL_hNRepl)) {
rotrtl20:
        ret[self] := ROTRTL_nRL;
        return;
    };

rotrtl21:
    call fixHeightAndGetParentOrGetNodeToRebalanceOrUnlinkOrNullIfNothingToDo_argsLocked(ROTRTL_nP);
    return;
}

fair process (initializer = "initializer")
{
init0:
    with (starter_state \in SetOfInterestingAvlTrees(TreeGenKeyMin, TreeGenKeyMax, TreeGenSizeMin, TreeGenSizeMax)){
    \* with (starter_state \in InterestingAvlTree(TreeGenKeyMin, TreeGenKeyMax, TreeGenSizeMin, TreeGenSizeMax, 10)){
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
\*     await pc["initializer"] = "Done";
\*     with (e \in KeySetToOperateOn){
\*         invoke("get", e);
\*         call get(e);
\*     };
\* readResp:
\*     respond(operation_succeeded[self]);
\* }

fair process (writer \in Writers )
{
writeInv:
    await pc["initializer"] = "Done";
    with (e \in KeySetToOperateOn){
        either{
            invoke("insert", e);
            call update(e, e);
        }
        or {
            invoke("erase", e);
            call update(e, Null);
        };
        \* or {
            \* invoke("get", e);
            \* call get(e);
        \* }; 
    };
writeResp:
    respond(operation_succeeded[self]);
}

fair process (verifier = "verifier")
{
verif:
    \* await \A p \in Readers  : pc[p] = "Done";
    await \A p \in Writers  : pc[p] = "Done";
    assert IsLinearizable(event_sequence, reachable_at_start);
}

} *)


\* BEGIN TRANSLATION (chksum(pcal) = "4287e1b9" /\ chksum(tla) = "2b947106")
\* END TRANSLATION 

VersionNumbersAreBounded == \A x \in Range(ver) : x <= VersionNumberBound \/ IsShrinkingOrUnlinked(x)

CallStackSizesAreBounded == \A p \in Procs : Len(stack[p]) < CallStackLimit

SanityChecks == CallStackSizesAreBounded /\ VersionNumbersAreBounded

QuiescenceGuarantees == 

                    LET 

                        IsQuiescent(p) == pc[p] \in 
                            {
                                "writeResp",
                                "Done"
                            }

                            
                    IN  (\A p \in Writers: IsQuiescent(p)) => 
                        (
                        /\ IsCycleFree(Null, left, rite, RootHolder)
                        \* /\ IsBalanced(Null, left, rite, RootHolder)
                        )

AllInvariants == /\ SanityChecks
                 /\ QuiescenceGuarantees

=============================================================================
\* Modification History
\* Last modified Mon Jun 07 10:14:20 BST 2021 by dan
\* Created Thu Apr 01 09:35:51 BST 2021 by dan
