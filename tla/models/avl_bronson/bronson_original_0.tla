------------------- MODULE bronson_original_0 -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Linearizability, TreeGeneration, TreeStructure 

CONSTANT NullModelValue
CONSTANT Readers \* Always contains 1
CONSTANT Writers

TreeGenSizeMin == 0
TreeGenSizeMax == 8
TreeGenKeyMin ==  2
TreeGenKeyMax == 10
OperationKeyMin == 1
OperationKeyMax == 11
NodeAddressSet == 1..14
CallStackBound == 24
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
    variables
        G_rite;
        G_ver;
        G_vo;
        G_riteKRead;
{
g0:
    while (TRUE) {
        G_rite := rite[RootHolder];
        if (G_rite = Null) {
g1:
            nullify_ret();

            operation_fail(); \* Element absent
            return;
        } else {
            G_riteKRead := key[G_rite];
            if (G_riteKRead = G_k) {
g2:
                ret[self] := val[G_rite];

                if(ret[self] = Null){
                    operation_fail(); \* Element absent
                }else{
                    operation_succeed(); \* Element present
                };

                return;
            };
g3:
            G_ver := ver[G_rite];
            if (IsShrinkingOrUnlinked(G_ver)) {
                await_not_shrinking(ver[G_rite]);
            } else if (G_rite = rite[RootHolder]) {
                call attemptGet(G_k, G_rite, AppropriateDirection(G_riteKRead, G_k), G_ver);
g4:
                G_vo := ret[self];
                if (G_vo # RetrySymbol) {
g5:
                    ret[self] := G_vo;

                    if(ret[self] = Null){
                        operation_fail(); \* Element absent
                    }else{
                        operation_succeed(); \* Element present
                    };

                    return;
                }
            }
        }
    }
}

procedure attemptGet(AG_k,
           AG_node,
           AG_dirToC,
           AG_nodeVer)
    variables
        AG_child;
        AG_childVer;
        AG_vo;
        AG_childKRead;
{
ag0:
    while (TRUE) {
        AG_child := Child(AG_node, AG_dirToC);

        if (AG_child = Null) {
            if (ver[AG_node] # AG_nodeVer) {
ag1:
                retry();
                return;
            };
ag2:
            nullify_ret();
            return;
        } else {
            AG_childKRead := key[AG_child];
            if (AG_childKRead = AG_k) {
ag3:
                ret[self] := val[AG_child];
                return;
            };
ag4:
            AG_childVer := ver[AG_child];
            if (IsShrinkingOrUnlinked(AG_childVer)) {
                await_not_shrinking(ver[AG_child]);
                if (ver[AG_node] # AG_nodeVer) {
ag5:
                    retry();
                    return;
                }
            } else if (AG_child # Child(AG_node, AG_dirToC)) {
                if (ver[AG_node] # AG_nodeVer) {
ag6:
                    retry();
                    return;
                }
            } else {
                if (ver[AG_node] # AG_nodeVer) {
ag7:
                    retry();
                    return;
                };
ag8:
                call attemptGet(AG_k, AG_child, AppropriateDirection(AG_childKRead, AG_k), AG_childVer);
ag9:
                AG_vo := ret[self];
                if (AG_vo # RetrySymbol) {
ag10:
                    return;
                }
            }
        }
    }
}

procedure update(U_k,
                 U_newValue)
    variables
        U_rite;
        U_ver;
        U_vo;
{
u0:
    while (TRUE) {
        U_rite := rite[RootHolder];
        if (U_rite = Null) {
            if(U_newValue = Null){
u1:
                operation_fail(); \* Erase - element absent
                return;
            };
uLock0:+
            lock(RootHolder);
u2:
                if (rite[RootHolder] = Null) {

                    write_new_leaf_under_RootHolder(UnusedAddress, U_k, U_newValue);
                    
                    nullify_ret();

                    unlock(RootHolder);

                    operation_succeed(); \* Insert succeeded
                    return;
                }; 
u3:
            unlock(RootHolder);
        } else {
            U_ver := ver[U_rite];
            if (IsShrinkingOrUnlinked(U_ver)) {
                await_not_shrinking(ver[U_rite]);
            } else if (U_rite = rite[RootHolder]) {
                call attemptUpdate(U_k, U_newValue, RootHolder, U_rite, U_ver);
u4:
                U_vo := ret[self];
                if (U_vo # RetrySymbol) {
u5:
                    return;
                }
            }
        }
    }
}

procedure attemptUpdate(AU_k,
                        AU_newValue,
                        AU_parent,
                        AU_node,
                        AU_nodeVer)
    variables
        AU_dirToC;
        AU_child;
        AU_success;
        AU_damaged;
        AU_vo;
        AU_childVer;
        AU_nodeKRead;
{
au0: 
    AU_nodeKRead := key[AU_node];
    if (AU_nodeKRead = AU_k) {
au1: 
        call attemptNodeUpdate(AU_newValue, AU_parent, AU_node);
auT3: 
        return;
    };
au2: 

    AU_dirToC := AppropriateDirection(AU_nodeKRead, AU_k);
au3: 

    while (TRUE) {
        AU_child := Child(AU_node, AU_dirToC);
        if (ver[AU_node] # AU_nodeVer) {
au4: 
            retry();
            return;
        };
au5: 
        if (AU_child = Null) {
            if (AU_newValue = Null) {
au6: 
                nullify_ret();
                operation_fail(); \* Erase - element absent
                return;
            } else {
auLock0:+
                lock(AU_node);
au7:
                    if (ver[AU_node] # AU_nodeVer) {
au8: 
                        retry();
                        unlock(AU_node);
                        return;
                    };
au9: 
                    if (Child(AU_node, AU_dirToC) # Null) {
                        AU_success := FALSE;
                        AU_damaged := Null;
                    } else {

                         write_new_leaf(
                            UnusedAddress, 
                            AppropriateDirection(AU_nodeKRead, AU_k),
                            AU_k,
                            AU_newValue,
                            AU_node
                            );
                        
                        AU_success := TRUE;
                        call fixHeight_nl(AU_node);
auT1:
                        AU_damaged := ret[self];
                    };
auT2:
                unlock(AU_node);
                if (AU_success) {
au10: 
                    call fixHeightAndRebalance(AU_damaged);
au11: 
                    nullify_ret();

                    operation_succeed(); \* Insert succeeded

                    return;
                }
            }
        } else {
            AU_childVer := ver[AU_child];
            if (IsShrinkingOrUnlinked(AU_childVer)) {
                await_not_shrinking(ver[AU_child]);
            } else {
                if (ver[AU_node] # AU_nodeVer) {
au12: 
                    retry();
                    return;
                };
au13: 
                call attemptUpdate(AU_k, AU_newValue, AU_node, AU_child , AU_childVer);
au14: 
                AU_vo := ret[self];
                if (AU_vo # RetrySymbol) {
au15: 
                    return;
                }
            }
        }
    }
}

procedure attemptNodeUpdate(ANU_newValue,
                            ANU_parent,
                            ANU_node)
    variables
        ANU_prev;
        ANU_damaged;
{
anu0:
    if (ANU_newValue = Null) {
        if (val[ANU_node] = Null) {
            nullify_ret();
            operation_fail(); \* Erase - element absent
            return;
        }
    };

anu1:
    if (ANU_newValue = Null /\ (left[ANU_node] = Null \/ rite[ANU_node] = Null)) {
anuLock0:+
        lock(ANU_parent);
anu2:
            if (IsUnlinked(ver[ANU_parent]) \/ parent[ANU_node] # ANU_parent) {
anu3:
                retry();
                unlock(ANU_parent);
                return;
            };
anuLock1:+
            lock(ANU_node);
anu4:
                ANU_prev := val[ANU_node];
                if (ANU_prev = Null) {
anu5:
                    ret[self] := ANU_prev;
                    unlock(ANU_node);
anu6:
                    unlock(ANU_parent);

                    operation_fail(); \* Erase - element absent
                    return;
                };
anu7:
                call attemptUnlink_nl(ANU_parent, ANU_node);
anuT0:
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
anu11:
            call fixHeight_nl(ANU_parent);
anu12:
            ANU_damaged := ret[self];
        unlock(ANU_parent);
anu13:
        call fixHeightAndRebalance(ANU_damaged);
anu14:
        ret[self] := ANU_prev;
        operation_succeed();
        return;
    } else {
anuLock2:+
        lock(ANU_node);
anu15:
            if (IsUnlinked(ver[ANU_node])) {
anu16:
                retry();
                unlock(ANU_node);
                return;
            };
anu17:
            ANU_prev := val[ANU_node];
            if (ANU_newValue = Null /\ (left[ANU_node] = Null \/ rite[ANU_node] = Null)) {
anu18:
                retry();
                unlock(ANU_node);
                return;
            };
anu19:

            (* -- START of bookkeeping section (not part of Bronson) -- *)
            if(ANU_newValue = Null){
                \* Erase
                if(val[ANU_node] = Null){
                    operation_fail(); 
                }else{
                    operation_succeed(); 
                }
            }else{
                \* Insert
                if(val[ANU_node] = Null){
                    operation_succeed();  \* If it's null, then the element was absent
                }else{
                    (*
                    NOTE: Since we are inserting a <key,value> pair and the key is present then
                    we declare failure. Note that this is only OK because we model a Set ADT
                    not a Map ADT.
                    *)
                    operation_fail();  
                }
            };
            (* -- END of bookkeeping section (not part of Bronson) -- *)

            val[ANU_node] := ANU_newValue;
            ret[self] := ANU_prev;
        unlock(ANU_node);
        return;
    }
}

procedure attemptUnlink_nl(AUL_parent, 
                           AUL_node)
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

aul5:
    ret[self] := TrueInt;
    return;
}

procedure nodeCondition(NC_node)
    variables
        NC_nL;
        NC_nR;
        NC_hN;
        NC_hL0;
        NC_hR0;
        NC_hNRepl;
        NC_bal;
{
nc0:

    NC_nL := left[NC_node];
    NC_nR := rite[NC_node];

    if ((NC_nL = Null \/ NC_nR = Null) /\ val[NC_node] = Null) {
nc1:
        ret[self] := UnlinkActionRequired;
        return;
    };
nc2:

    NC_hN := height[NC_node];
    NC_hL0 := NullSafeHeight(NC_nL);
    NC_hR0 := NullSafeHeight(NC_nR);

    NC_hNRepl := MaxPlusOne(NC_hL0, NC_hR0);
    NC_bal := NC_hL0 - NC_hR0;

    if (NC_bal <0-1 \/ NC_bal > 1) {
nc3:
        ret[self] := RebalanceActionRequired;
        return;
    };
nc4:

    ret[self] := IF NC_hN # NC_hNRepl THEN NC_hNRepl ELSE NoRepairActionRequired;
    return;
}

procedure fixHeightAndRebalance(FHR_node)
    variables
        FHR_condition;
        FHR_nParent;
{
fhr0:
    while (FHR_node # Null) {
        if (parent[FHR_node] = Null) {
fhr1:
            return;
        };
fhr2:
        call nodeCondition(FHR_node);
fhrT1:
        FHR_condition := ret[self];
        if (FHR_condition = NoRepairActionRequired \/ IsUnlinked(ver[FHR_node])) {
fhr3:
            return;
        };
fhr4:
        if (FHR_condition # UnlinkActionRequired /\ FHR_condition # RebalanceActionRequired) {
fhrLock0:+
            lock(FHR_node);
fhr5:
                call fixHeight_nl(FHR_node);
fhrT0:
            unlock(FHR_node);
            FHR_node := ret[self];
        } else {
            FHR_nParent := parent[FHR_node];
fhrLock1:+
            lock(FHR_nParent);
fhr6:
                if (~IsUnlinked(ver[FHR_nParent]) /\ parent[FHR_node] = FHR_nParent) {
fhrLock2:+
                    lock(FHR_node);
fhr7:
                        call rebalance_nl(FHR_nParent, FHR_node);
fhr8:
                    unlock(FHR_node);
                    FHR_node := ret[self];
                };
fhr9:
            unlock(FHR_nParent);
        }
    };
fhr10:
    return;
}

procedure fixHeight_nl(FH_node)
    variables
        FH_c;
{
fh0:
    call nodeCondition(FH_node);
fhT0:
    FH_c := ret[self];

    if (FH_c = RebalanceActionRequired) {
fh1:
        ret[self] := FH_node;
        return;
    };
fh2:
    if (FH_c = UnlinkActionRequired) {
fh3:
        ret[self] := FH_node;
        return;
    };
fh4:
    if (FH_c = NoRepairActionRequired) {
fh5:
        nullify_ret();
        return;
    };
fh6:
    height[FH_node] := FH_c;
    ret[self] := parent[FH_node];
    return;
}

procedure rebalance_nl(REB_nParent,
                       REB_n)
    variables
        REB_nL;
        REB_nR;
        REB_hN;
        REB_hL0;
        REB_hR0;
        REB_hNRepl;
        REB_bal;
{
reb0:

    REB_nL := left[REB_n];
    REB_nR := rite[REB_n];

    if ((REB_nL = Null \/ REB_nR = Null) /\ val[REB_n] = Null) {
        call attemptUnlink_nl(REB_nParent, REB_n);
rebT0:
        if (ret[self] = TrueInt) {
reb1:
            call fixHeight_nl(REB_nParent);
            return;
        } else {
reb2:
            ret[self] := REB_n;
            return;
        }
    };
reb3:

    REB_hN := height[REB_n];
    REB_hL0 := NullSafeHeight(REB_nL);
    REB_hR0 := NullSafeHeight(REB_nR);
    REB_hNRepl := MaxPlusOne(REB_hL0, REB_hR0);
    REB_bal := REB_hL0 - REB_hR0;

    if (REB_bal > 1) {
reb4:
        call rebalanceToRite_nl(REB_nParent, REB_n, REB_nL, REB_hR0);
reb5:
        return;
    } else if (REB_bal <0-1) {
reb6:
        call rebalanceToLeft_nl(REB_nParent, REB_n, REB_nR, REB_hL0);
reb7:
        return;
    } else if (REB_hNRepl # REB_hN) {
reb8:
        height[REB_n] := REB_hNRepl;
        call fixHeight_nl(REB_nParent);
reb9:
        return;
    } else {
reb10:
        nullify_ret();
        return;
    }
}

procedure rebalanceToRite_nl(REBR_nParent,
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
        REBR_bal;
{
rebr0Lock0:+
    lock(REBR_nL);
rebr1:
        REBR_hL := height[REBR_nL];
        if (REBR_hL - REBR_hR0 <= 1) {
rebr2:
            ret[self] := REBR_n;
            unlock(REBR_nL);
            return;
        } else {
            REBR_nLR := rite[REBR_nL];
            REBR_hLL0 := NullSafeHeight(left[REBR_nL]);
            REBR_hLR0 := NullSafeHeight(REBR_nLR);
            if (REBR_hLL0 >=  REBR_hLR0) {
rebr3:
                call rotateRite_nl(REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR, REBR_hLR0);
rebr4:
                unlock(REBR_nL);
                return;
            } else {
rebrLock1:+
                lock(REBR_nLR);
rebr5:
                    REBR_hLR := height[REBR_nLR];
                    if (REBR_hLL0 >=  REBR_hLR) {
rebr6:
                        call rotateRite_nl(REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR, REBR_hLR);
rebr7:
                        unlock(REBR_nLR);
rebr8:
                        unlock(REBR_nL);
                        return;
                    } else {
                        REBR_hLRL := NullSafeHeight(left[REBR_nLR]);
                        REBR_bal := REBR_hLL0 - REBR_hLRL;
                        if (REBR_bal >= 0-1 /\ REBR_bal <= 1 /\ ~((REBR_hLL0 = 0 \/ REBR_hLRL = 0) /\ val[REBR_nL] = Null)) {
rebr9:
                            call rotateRiteOverLeft_nl(REBR_nParent, REBR_n, REBR_nL, REBR_hR0, REBR_hLL0, REBR_nLR, REBR_hLRL);
rebr10:
                            unlock(REBR_nLR);
rebr11:
                            unlock(REBR_nL);
                            return;
                        }
                    };
rebr12:
                unlock(REBR_nLR);
rebr13:
                call rebalanceToLeft_nl(REBR_n, REBR_nL, REBR_nLR, REBR_hLL0);
rebr14:
                return;
            }
        };
rebr15:
    unlock(REBR_nL);
}

procedure rebalanceToLeft_nl(REBL_nParent,
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
        REBL_bal;
{
rebl0Lock0:+
    lock(REBL_nR);
rebl1:
        REBL_hR := height[REBL_nR];
        if (REBL_hL0 - REBL_hR >= 0-1) {
rebl2:
            ret[self] := REBL_n;
            unlock(REBL_nR);
            return;
        } else {
            REBL_nRL := left[REBL_nR];
            REBL_hRL0 := NullSafeHeight(REBL_nRL);
            REBL_hRR0 := NullSafeHeight(rite[REBL_nR]);
            if (REBL_hRR0 >=  REBL_hRL0) {
rebl3:
                call rotateLeft_nl(REBL_nParent, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRL0, REBL_hRR0);
rebl4:
                unlock(REBL_nR);
                return;
            } else {
reblLock1:+
                lock(REBL_nRL);
rebl5:
                    REBL_hRL := height[REBL_nRL];
                    if (REBL_hRR0 >=  REBL_hRL) {
rebl6:
                        call rotateLeft_nl(REBL_nParent, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRL, REBL_hRR0);
rebl7:
                        unlock(REBL_nR);
rebl8:
                        unlock(REBL_nRL);
                        return;
                    } else {
                        REBL_hRLR := NullSafeHeight(rite[REBL_nRL]);
                        REBL_bal := REBL_hRR0 - REBL_hRLR;
                        if (REBL_bal >= 0-1 /\ REBL_bal <= 1 /\ ~((REBL_hRR0 = 0 \/ REBL_hRLR = 0) /\ val[REBL_nR] = Null)) {
rebl9:
                            call rotateLeftOverRite_nl(REBL_nParent, REBL_n, REBL_hL0, REBL_nR, REBL_nRL, REBL_hRR0, REBL_hRLR);
rebl10:
                            unlock(REBL_nR);
rebl11:
                            unlock(REBL_nRL);
                            return;
                        }
                    };
rebl12:
                unlock(REBL_nRL);
rebl13:
                call rebalanceToRite_nl(REBL_n, REBL_nR, REBL_nRL, REBL_hRR0);
rebl14:
                return;
            }
        };
rebl15:
    unlock(REBL_nR);
}

procedure rotateRite_nl(ROTR_nParent,
                        ROTR_n,
                        ROTR_nL,
                        ROTR_hR,
                        ROTR_hLL,
                        ROTR_nLR,
                        ROTR_hLR)
    variables
        ROTR_nodeVer;
        ROTR_nPL;
        ROTR_hNRepl;
        ROTR_balN;
        ROTR_balL;
{
rotr0:

    ROTR_nodeVer := ver[ROTR_n];

    ROTR_nPL := left[ROTR_nParent];

    ver[ROTR_n] := BeginChange(ROTR_nodeVer);
rotrT0:

    left[ROTR_n] := ROTR_nLR;
    if (ROTR_nLR # Null) {
        parent[ROTR_nLR] := ROTR_n;
    };

rotr1:
    rite[ROTR_nL] := ROTR_n;
    parent[ROTR_n] := ROTR_nL;
rotr2:

    if (ROTR_nPL = ROTR_n) {
        left[ROTR_nParent] := ROTR_nL;
    } else {
        rite[ROTR_nParent] := ROTR_nL;
    };
rotr3:
    parent[ROTR_nL] := ROTR_nParent;

    ROTR_hNRepl := MaxPlusOne(ROTR_hLR, ROTR_hR);
    height[ROTR_n] := ROTR_hNRepl;
rotr4:
    height[ROTR_nL] := MaxPlusOne(ROTR_hLL, ROTR_hNRepl);

    ver[ROTR_n] := EndChange(ROTR_nodeVer);

    ROTR_balN := ROTR_hLR - ROTR_hR;
    if (ROTR_balN <0-1 \/ ROTR_balN > 1) {
rotr5:

        ret[self] := ROTR_n;
        return;
    };

rotr6:
    if ((ROTR_nLR = Null \/ ROTR_hR = 0) /\ val[ROTR_n] = Null) {
rotr7:

        ret[self] := ROTR_n;
        return;
    };
rotr8:

    ROTR_balL := ROTR_hLL - ROTR_hNRepl;
    if (ROTR_balL <0-1 \/ ROTR_balL > 1) {
rotr9:
        ret[self] := ROTR_nL;
        return;
    };
rotr10:

    if (ROTR_hLL = 0 /\ val[ROTR_nL] = Null) {
rotr11:
        ret[self] := ROTR_nL;
        return;
    };
rotr12:

    call fixHeight_nl(ROTR_nParent);
    return;
}

procedure rotateLeft_nl(ROTL_nParent,
                        ROTL_n,
                        ROTL_hL,
                        ROTL_nR,
                        ROTL_nRL,
                        ROTL_hRL,
                        ROTL_hRR)
    variables
        ROTL_nodeVer;
        ROTL_nPL;
        ROTL_hNRepl;
        ROTL_balN;
        ROTL_balR;
{
rotl0:
    ROTL_nodeVer := ver[ROTL_n];

    ROTL_nPL := left[ROTL_nParent];

    ver[ROTL_n] := BeginChange(ROTL_nodeVer);
rotlT0:

    rite[ROTL_n] := ROTL_nRL;
    if (ROTL_nRL # Null) {
        parent[ROTL_nRL] := ROTL_n;
    };

rotl1:
    left[ROTL_nR] := ROTL_n;
    parent[ROTL_n] := ROTL_nR;
rotl2:

    if (ROTL_nPL = ROTL_n) {
        left[ROTL_nParent] := ROTL_nR;
    } else {
        rite[ROTL_nParent] := ROTL_nR;
    };
rotl3:
    parent[ROTL_nR] := ROTL_nParent;

    ROTL_hNRepl := MaxPlusOne(ROTL_hL, ROTL_hRL);
    height[ROTL_n] := ROTL_hNRepl;
rotl4:
    height[ROTL_nR] := MaxPlusOne(ROTL_hNRepl, ROTL_hRR);

    ver[ROTL_n] := EndChange(ROTL_nodeVer);

    ROTL_balN := ROTL_hRL - ROTL_hL;
    if (ROTL_balN <0-1 \/ ROTL_balN > 1) {
rotl5:
        ret[self] := ROTL_n;
        return;
    };

rotl6:
    if ((ROTL_nRL = Null \/ ROTL_hL = 0) /\ val[ROTL_n] = Null) {
rotl7:
        ret[self] := ROTL_n;
        return;
    };
rotl8:

    ROTL_balR := ROTL_hRR - ROTL_hNRepl;
    if (ROTL_balR <0-1 \/ ROTL_balR > 1) {
rotl9:
        ret[self] := ROTL_nR;
        return;
    };
rotl10:

    if (ROTL_hRR = 0 /\ val[ROTL_nR] = Null) {
rotl11:
        ret[self] := ROTL_nR;
        return;
    };
rotl12:

    call fixHeight_nl(ROTL_nParent);
    return;
}

procedure rotateRiteOverLeft_nl(ROTROL_nParent,
                                ROTROL_n,
                                ROTROL_nL,
                                ROTROL_hR,
                                ROTROL_hLL,
                                ROTROL_nLR,
                                ROTROL_hLRL)
    variables
        ROTROL_nodeOVL;
        ROTROL_leftOVL;
        ROTROL_nPL;
        ROTROL_nLRL;
        ROTROL_nLRR;
        ROTROL_hLRR;
        ROTROL_hNRepl;
        ROTROL_hLRepl;
        ROTROL_balN;
        ROTROL_balLR;
{
rotrol0:

    ROTROL_nodeOVL := ver[ROTROL_n];
    ROTROL_leftOVL := ver[ROTROL_nL];

    ROTROL_nPL := left[ROTROL_nParent];
    ROTROL_nLRL := left[ROTROL_nLR];
    ROTROL_nLRR := rite[ROTROL_nLR];
    ROTROL_hLRR := NullSafeHeight(ROTROL_nLRR);

    ver[ROTROL_n] := BeginChange(ROTROL_nodeOVL);
rotrol1:
    ver[ROTROL_nL] := BeginChange(ROTROL_leftOVL);
rotrolT0:

    left[ROTROL_n] := ROTROL_nLRR;
    if (ROTROL_nLRR # Null) {
        parent[ROTROL_nLRR] := ROTROL_n;
    };

rotrol2:
    rite[ROTROL_nL] := ROTROL_nLRL;
    if (ROTROL_nLRL # Null) {
        parent[ROTROL_nLRL] := ROTROL_nL;
    };

    left[ROTROL_nLR] := ROTROL_nL;
rotrol3:
    parent[ROTROL_nL] := ROTROL_nLR;
    rite[ROTROL_nLR] := ROTROL_n;
rotrol4:
    parent[ROTROL_n] := ROTROL_nLR;

    if (ROTROL_nPL = ROTROL_n) {
        left[ROTROL_nParent] := ROTROL_nLR;
    } else {
        rite[ROTROL_nParent] := ROTROL_nLR;
    };
rotrol5:
    parent[ROTROL_nLR] := ROTROL_nParent;

    ROTROL_hNRepl := MaxPlusOne(ROTROL_hLRR, ROTROL_hR);
    height[ROTROL_n] := ROTROL_hNRepl;
    ROTROL_hLRepl := MaxPlusOne(ROTROL_hLL, ROTROL_hLRL);
rotrol6:
    height[ROTROL_nL] := ROTROL_hLRepl;
rotrol7:
    height[ROTROL_nLR] := MaxPlusOne(ROTROL_hLRepl, ROTROL_hNRepl);

    ver[ROTROL_n] := EndChange(ROTROL_nodeOVL);
rotrol8:
    ver[ROTROL_nL] := EndChange(ROTROL_leftOVL);

    ROTROL_balN := ROTROL_hLRR - ROTROL_hR;
    if (ROTROL_balN <0-1 \/ ROTROL_balN > 1) {
rotrol9:
        ret[self] := ROTROL_n;
        return;
    };
rotrol10:

    if ((ROTROL_nLRR = Null \/ ROTROL_hR = 0) /\ val[ROTROL_n] = Null) {
rotrol11:
        ret[self] := ROTROL_n;
        return;
    };
rotrol12:

    ROTROL_balLR := ROTROL_hLRepl - ROTROL_hNRepl;
    if (ROTROL_balLR <0-1 \/ ROTROL_balLR > 1) {
rotrol13:
        ret[self] := ROTROL_nLR;
        return;
    };
rotrol14:

    call fixHeight_nl(ROTROL_nParent);
    return;
}

procedure rotateLeftOverRite_nl(ROTLOR_nParent,
                                ROTLOR_n,
                                ROTLOR_hL,
                                ROTLOR_nR,
                                ROTLOR_nRL,
                                ROTLOR_hRR,
                                ROTLOR_hRLR)
    variables
        ROTLOR_nodeOVL;
        ROTLOR_rightOVL;
        ROTLOR_nPL;
        ROTLOR_nRLL;
        ROTLOR_nRLR;
        ROTLOR_hRLL;
        ROTLOR_hNRepl;
        ROTLOR_hRRepl;
        ROTLOR_balN;
        ROTLOR_balRL;
{
rotlor0:

    ROTLOR_nodeOVL := ver[ROTLOR_n];
    ROTLOR_rightOVL := ver[ROTLOR_nR];

    ROTLOR_nPL := left[ROTLOR_nParent];
    ROTLOR_nRLL := left[ROTLOR_nRL];
    ROTLOR_nRLR := rite[ROTLOR_nRL];
    ROTLOR_hRLL := NullSafeHeight(ROTLOR_nRLL);

    ver[ROTLOR_n] := BeginChange(ROTLOR_nodeOVL);
rotlor1:
    ver[ROTLOR_nR] := BeginChange(ROTLOR_rightOVL);
rotlorT0:

    rite[ROTLOR_n] := ROTLOR_nRLL;
    if (ROTLOR_nRLL # Null) {
        parent[ROTLOR_nRLL] := ROTLOR_n;
    };

rotlor2:
    left[ROTLOR_nR] := ROTLOR_nRLR;
    if (ROTLOR_nRLR # Null) {
        parent[ROTLOR_nRLR] := ROTLOR_nR;
    };

    rite[ROTLOR_nRL] := ROTLOR_nR;
rotlor3:
    parent[ROTLOR_nR] := ROTLOR_nRL;
    left[ROTLOR_nRL] := ROTLOR_n;
rotlor4:
    parent[ROTLOR_n] := ROTLOR_nRL;

    if (ROTLOR_nPL = ROTLOR_n) {
        left[ROTLOR_nParent] := ROTLOR_nRL;
    } else {
        rite[ROTLOR_nParent] := ROTLOR_nRL;
    };
rotlor5:
    parent[ROTLOR_nRL] := ROTLOR_nParent;

    ROTLOR_hNRepl := MaxPlusOne(ROTLOR_hL, ROTLOR_hRLL);
    height[ROTLOR_n] := ROTLOR_hNRepl;
    ROTLOR_hRRepl := MaxPlusOne(ROTLOR_hRLR, ROTLOR_hRR);
rotlor6:
    height[ROTLOR_nR] := ROTLOR_hRRepl;
rotlor7:
    height[ROTLOR_nRL] := MaxPlusOne(ROTLOR_hNRepl, ROTLOR_hRRepl);

    ver[ROTLOR_n] := EndChange(ROTLOR_nodeOVL);
rotlor8:
    ver[ROTLOR_nR] := EndChange(ROTLOR_rightOVL);

    ROTLOR_balN := ROTLOR_hRLL - ROTLOR_hL;
    if (ROTLOR_balN <0-1 \/ ROTLOR_balN > 1) {
rotlor9:
        ret[self] := ROTLOR_n;
        return;
    };
rotlor10:
    if ((ROTLOR_nRLL = Null \/ ROTLOR_hL = 0) /\ val[ROTLOR_n] = Null) {
rotlor11:
        ret[self] := ROTLOR_n;
        return;
    };
rotlor12:
    ROTLOR_balRL := ROTLOR_hRRepl - ROTLOR_hNRepl;
    if (ROTLOR_balRL <0-1 \/ ROTLOR_balRL > 1) {
rotlor13:
        ret[self] := ROTLOR_nRL;
        return;
    };
rotlor14:
    call fixHeight_nl(ROTLOR_nParent);
    return;
}

fair process (initializer = "initializer")
{
init0:
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


\* BEGIN TRANSLATION (chksum(pcal) = "e5ad1470" /\ chksum(tla) = "cef24d2")
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
                        /\ IsCycleFree(Null, left, rite, RootHolder)
                        /\ IsBalanced(Null, left, rite, RootHolder)
                        )

AllInvariants == /\ SanityChecks
                 /\ QuiescenceGuarantees

=============================================================================
\* Modification History
\* Last modified Mon May 10 13:41:06 BST 2021 by dan
\* Created Thu Apr 01 09:35:51 BST 2021 by dan
