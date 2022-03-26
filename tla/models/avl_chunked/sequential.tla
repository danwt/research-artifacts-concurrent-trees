------------------- MODULE sequential -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Linearizability, TreeGeneration
CONSTANT Readers, Writers, NullModelValue

Procs == Readers \cup Writers \* Actually ony one writer

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
Range(f) == { f[x] : x \in DOMAIN f }
SeqToSet(f) == Range(f)

MaxKey == 5
ChunkMaxSize == 2
NumWriteOperations == 2

KeySetToOperateOn == 1..MaxKey

LeafNodeAddressSet == (MaxKey+1)..35
InnerNodeAddressSet == KeySetToOperateOn
AddressSetWithoutRootHolder == InnerNodeAddressSet \cup LeafNodeAddressSet 

RootHolder == 0
AddressSetWithRootHolder ==  AddressSetWithoutRootHolder \cup {RootHolder}

ChunkAddressSet == LeafNodeAddressSet \* Worst case: each leaf has its own chunk.

IntegerShift == 100
Null == IntegerShift + 1
ShrinkingSymbol == IntegerShift + 2
UnlinkedSymbol == IntegerShift + 3
RetrySymbol == IntegerShift + 4
DirectionLeftSymbol == IntegerShift + 5
DirectionRiteSymbol == IntegerShift + 6
NoRepairActionRequired == IntegerShift + 7
UnlinkActionRequired == IntegerShift + 8
RebalanceActionRequired == IntegerShift + 9
FalseInt == IntegerShift + 10
TrueInt == IntegerShift + 11
IntBoolAsBool(x) == x = TrueInt

VersionNumberInitValue == 0

(* --algorithm algo {

variables

    (* Algorithm variables *)
    
    \* NOTE: not including root holder for some of these screws up debugging
    ovl           = [e \in AddressSetWithRootHolder    |-> 0];  
    is_leaf       = [e \in AddressSetWithRootHolder    |-> FALSE]; 
    chunk_of_node = [e \in AddressSetWithRootHolder    |-> Null]; 
    key           = [e \in AddressSetWithRootHolder    |-> Null]; 
    val           = [e \in AddressSetWithRootHolder    |-> Null]; 
    height        = [e \in AddressSetWithRootHolder    |-> Null]; 
    parent        = [e \in AddressSetWithRootHolder    |-> Null];
    left          = [e \in AddressSetWithRootHolder    |-> Null];
    rite          = [e \in AddressSetWithRootHolder    |-> Null];
    locked        = [e \in AddressSetWithRootHolder    |-> NullModelValue]; 

    root_of_chunk = [e \in ChunkAddressSet |-> Null];
    left_wing     = [e \in ChunkAddressSet |-> {}];
    rite_wing     = [e \in ChunkAddressSet |-> {}];

    ret = [e \in Procs |-> Null]; 

    (* Non-algorithm variables *)

    event_sequence = <<>>;
    operation_succeeded = [p \in Procs |-> Null];
    num_write_operations = 0;

define {

    NullSafeHeight(e) == IF e = Null THEN 0 ELSE height[e]
    LeftHeight(e) == NullSafeHeight(left[e])
    RiteHeight(e) == NullSafeHeight(rite[e])
    IsLeftChild(p, c) == left[p] = c 
    IsRiteChild(p, c) == rite[p] = c 
    ChunkLeftSize(e) == Cardinality(left_wing[e])
    ChunkRiteSize(e) == Cardinality(rite_wing[e])
    ChunkSize(e) == ChunkLeftSize(e) + ChunkRiteSize(e)
    ChunkNotFull(e) == ChunkSize(e) < ChunkMaxSize
    ChunkIsFull(e) == ChunkSize(e) = ChunkMaxSize
    IsChunkRoot(e) == chunk_of_node[e] # Null
    IsLeaf(e) == is_leaf[e]

    IsShrinking(x) == x = ShrinkingSymbol
    IsUnlinked(x) == x = UnlinkedSymbol
    IsShrinkingOrUnlinked(x) == IsShrinking(x) \/ IsUnlinked(x)
    NotShrinkingOrUnlinked(x) == ~IsShrinkingOrUnlinked(x)
    BeginChange(x) == ShrinkingSymbol
    EndChange(x) == x + 1
    
    AppropriateDirection(router_key, sought_key) == IF sought_key < router_key 
                                                    THEN DirectionLeftSymbol
                                                    ELSE DirectionRiteSymbol

    Child(addr, direction_symbol) == IF direction_symbol = DirectionLeftSymbol 
                                     THEN left[addr] 
                                     ELSE rite[addr]

    MaxPlusOne(x, y) == IF y < x 
                        THEN x + 1 
                        ELSE y + 1

    BalanceFactor(e) == RiteHeight(e) - LeftHeight(e)
    BalanceFactorIsBalanced(x) == (0-2 < x) /\ (x < 2)
    BalanceFactorIsImbalanced(x) == ~BalanceFactorIsBalanced(x)
    IsBalanced(e) == BalanceFactorIsBalanced(BalanceFactor(e))

    IsUnusedNodeAddr(e) == key[e] = Null
    UnusedInnerNodeAddr == CHOOSE e \in InnerNodeAddressSet : IsUnusedNodeAddr(e)
    UnusedLeafNodeAddr == CHOOSE e \in LeafNodeAddressSet : IsUnusedNodeAddr(e)

    IsUnusedChunkAddr(e) == root_of_chunk[e] = Null \* DENK: Is this Ok?
    UnusedChunkAddr == CHOOSE e \in ChunkAddressSet : IsUnusedChunkAddr(e)

}

(*
---------------
Begin bookkeeping macros
*)

macro invoke(operation_name, arg){
    event_sequence := event_sequence \o <<<<"invoke", self, operation_name, arg>>>>;
}

macro respond(succeeded_int_bool){
    event_sequence := event_sequence \o <<<<"respond", self, IntBoolAsBool(succeeded_int_bool) >>>>;
}

(*
Get succeeds if the key was present (and not marked deleted)
Erase succeeds if the key was present and update removes it
Insert succeeds if the key was not present and update inserts it
*)
macro operation_succeed(){
    operation_succeeded[self] := TrueInt;
}

macro operation_fail(){
    operation_succeeded[self] := FalseInt;
}

(*
Precondition: left child and right child both have height 1
*)
macro write_non_leaf(Maddress, Mk, Mleft_child, Mrite_child){
    key[Maddress] := Mk;
    height[Maddress] := 2;
    left[Maddress] := Mleft_child;
    rite[Maddress] := Mrite_child;
    parent[Mleft_child] := Maddress || parent[Mrite_child] := Maddress;
}

macro adjust_node_height(Mnode){
    height[Mnode] := MaxPlusOne(LeftHeight(Mnode), RiteHeight(Mnode)) + 1;
}

macro write_node(Mnode, Mk, Mv, Mparent){

    assert IsUnusedNodeAddr(Mnode);
    is_leaf[Mnode] := TRUE;
    height[Mnode] := 1;
    key[Mnode] := Mk;
    val[Mnode] := Mv;
    parent[Mnode] := Mparent;

    if(Mparent # Null){
        if(left[Mparent] # Null){
            if(key[left[Mparent]] = Mk){
                left[Mparent] := Mnode;
            }
        }else{
            rite[Mparent] := Mnode;
        }
    }
}

macro chunk_insert_left(Mleaf_addr, Mchunk_addr, Mk, Mv, Mparent)
{
    left_wing[Mchunk_addr] := left_wing[Mchunk_addr] \cup {Mleaf_addr};
    write_node(Mleaf_addr, Mk, Mv, Mparent);
}

macro chunk_insert_rite(Mleaf_addr, Mchunk_addr, Mk, Mv, Mparent)
{
    rite_wing[Mchunk_addr] := rite_wing[Mchunk_addr] \cup {Mleaf_addr};
    write_node(Mleaf_addr, Mk, Mv, Mparent);
}

macro chunk_erase(Mchunk_addr, MdirectionSymbolForWing, Mk)
{
    if(MdirectionSymbolForWing = DirectionLeftSymbol){
        left_wing[Mchunk_addr] := left_wing[Mchunk_addr] \ {e \in left_wing[Mchunk_addr] : key[e] = Mk};
    }else{
        rite_wing[Mchunk_addr] := rite_wing[Mchunk_addr] \ {e \in rite_wing[Mchunk_addr] : key[e] = Mk};
    }
}


macro bind_parent_to_new_child(Mparent, Mold_child, Mreplacement_child)
{
    if(IsLeftChild(Mparent, Mold_child)){
        left[Mparent] := Mreplacement_child;
        parent[left[Mparent]] := Mparent;
    }else{
        rite[Mparent] := Mreplacement_child;
        parent[rite[Mparent]] := Mparent;
    }
}

macro destroy_chunk(Mchunk_addr){
    skip;
}

macro destroy_non_leaf(Mnode){
    skip;
}

procedure chunk_shift_left(CSL_chunkAddr, CSL_minKeyToKeep)
(*
Thought: Using a loop like this is obviously unfortunate.
There is also the matter of cleaning up the old adddresses
*)
(*
NOTE:
I think there is a subtlety here. We're using UnusedLeafNodeAddr directly in the macro parameter
which I think means that it will get evaluated many times. This might be fine since CHOOSE
is deterministic and everything happens in the same action?
*)
    variables
        CSL_shift_seq;
        CSL_i;
{
csl0:
    CSL_shift_seq := SetToSeq({e \in rite_wing[CSL_chunkAddr] : key[e] < CSL_minKeyToKeep});
    CSL_i := 1;
csl1:
    while(CSL_i <= Len(CSL_shift_seq)){
        chunk_insert_left(
            UnusedLeafNodeAddr,
            CSL_chunkAddr,
            key[CSL_shift_seq[CSL_i]],
            val[CSL_shift_seq[CSL_i]],
            parent[CSL_shift_seq[CSL_i]]
        );
csl2:
        CSL_i := CSL_i + 1;
    };
    rite_wing[CSL_chunkAddr] := rite_wing[CSL_chunkAddr] \ SeqToSet(CSL_shift_seq); \* Could recompute
    \* parent := [e \in SeqToSet(CSL_shift_seq) |-> Null ] @@ parent; \* NOTE: this is NOT justified in concurrent ver
    return;
}

procedure chunk_shift_rite(CSR_chunkAddr, CSR_minKeyToMove)
    variables
        CSR_shift_seq;
        CSR_i;
{
csr0:
    CSR_shift_seq := SetToSeq({e \in left_wing[CSR_chunkAddr] : CSR_minKeyToMove <= key[e]});
    CSR_i := 1;
csr1:
    while(CSR_i <= Len(CSR_shift_seq)){
        chunk_insert_rite(
            UnusedLeafNodeAddr,
            CSR_chunkAddr,
            key[CSR_shift_seq[CSR_i]],
            val[CSR_shift_seq[CSR_i]],
            parent[CSR_shift_seq[CSR_i]]
        );
csr2:
        CSR_i := CSR_i + 1;
    };
    left_wing[CSR_chunkAddr] := left_wing[CSR_chunkAddr] \ SeqToSet(CSR_shift_seq); \* Could recompute
    \* parent := [e \in SeqToSet(CSR_shift_seq) |-> Null ] @@ parent; \* NOTE: this is NOT justified in concurrent ver
    return;
}

procedure get_impl(G_k, G_curr)
{
gi0:
    if(G_curr = Null){
        operation_fail();
        return;
    };

gi1:
    if(IsLeaf(G_curr) /\ key[G_curr] = G_k){
        operation_succeed();
        return;
    };

gi2:
    if(G_k < key[G_curr]){
        call get_impl(G_k, left[G_curr]);
        return;
    }else{
        call get_impl(G_k, rite[G_curr]);
        return;
    };
}

(*
Returns: nothing meaningful
*)
procedure get(G_k)
{
g0:
    call get_impl(G_k, rite[RootHolder]);
    return;
}

(*
Returns: nothing meaningful
*)
procedure rotate_left(RL_pivot, RL_directionFromParent)
    variables
        RL_new_pivot;
{
rl0:

   if(IsChunkRoot(RL_pivot)){
       call chunk_shift_left(chunk_of_node[RL_pivot], key[rite[RL_pivot]]);
rl1:
       root_of_chunk[chunk_of_node[RL_pivot]] := rite[RL_pivot];
       chunk_of_node[rite[RL_pivot]] := chunk_of_node[RL_pivot];
rl2:
       chunk_of_node[RL_pivot] := Null;
   } else if (IsChunkRoot(rite[RL_pivot])){
       call split_left_wing_into_new_chunk(rite[RL_pivot]);
   };
rl3:

    RL_new_pivot := rite[RL_pivot];
    parent[RL_new_pivot] := parent[RL_pivot];
    rite[RL_pivot] := left[RL_new_pivot];
rl4:
    parent[left[RL_new_pivot]] := RL_pivot;
    left[RL_new_pivot] := RL_pivot;
rl5:
    parent[RL_pivot] := RL_new_pivot;

    if(RL_directionFromParent = DirectionLeftSymbol){
        left[parent[RL_new_pivot]] := RL_new_pivot;
    } else {
        rite[parent[RL_new_pivot]] := RL_new_pivot;
    };

    adjust_node_height(left[RL_pivot]);
rl6:
    adjust_node_height(RL_pivot);

    return;
}

(*
Returns: nothing meaningful
*)
procedure rotate_rite(RR_pivot, RR_directionFromParent)
    variables
        RR_new_pivot;
{
rr0:

   if(IsChunkRoot(RR_pivot)){
       call chunk_shift_rite(chunk_of_node[RR_pivot], key[left[RR_pivot]]);
rr1:
       root_of_chunk[chunk_of_node[RR_pivot]] := left[RR_pivot];
       chunk_of_node[left[RR_pivot]] := chunk_of_node[RR_pivot];
rr2:
       chunk_of_node[RR_pivot] := Null;
   } else if (IsChunkRoot(left[RR_pivot])){
       call split_left_wing_into_new_chunk(left[RR_pivot]);
   };
rr3:

    RR_new_pivot := left[RR_pivot];
    parent[RR_new_pivot] := parent[RR_pivot];
    left[RR_pivot] := rite[RR_new_pivot];
rr4:
    parent[rite[RR_new_pivot]] := RR_pivot;
    rite[RR_new_pivot] := RR_pivot;
rr5:
    parent[RR_pivot] := RR_new_pivot;

    if(RR_directionFromParent = DirectionRiteSymbol){
        rite[parent[RR_new_pivot]] := RR_new_pivot;
    } else {
        left[parent[RR_new_pivot]] := RR_new_pivot;
    };

    adjust_node_height(rite[RR_pivot]);
rr6:
    adjust_node_height(RR_pivot);

    return;
}

(*
Returns: nothing meaningful
*)
procedure rotate(R_pivot, R_directionFromParent)
{
r0:
    if(BalanceFactor(R_pivot) < 0-1 ){
        if (0 < BalanceFactor(left[R_pivot])){
            call rotate_left(left[R_pivot], DirectionLeftSymbol);
        };
r1:
        call rotate_rite(R_pivot, R_directionFromParent);
    }else if(1 < BalanceFactor(R_pivot)){
        if (BalanceFactor(rite[R_pivot]) < 0){
            call rotate_rite(rite[R_pivot], DirectionRiteSymbol);
        };
r2:
        call rotate_left(R_pivot, R_directionFromParent);
    };
r3:
    return;
}


(*
Returns: nothing meaningful
*)
procedure rebalance(REB_curr)
    variables
        REB_parent;
{
reb0:
    while(parent[REB_curr] # Null){
        adjust_node_height(REB_curr);
        REB_parent := parent[REB_curr];
        if(~IsBalanced(REB_curr)){
            if(IsLeftChild(REB_parent, REB_curr)){
                call rotate(left[REB_parent], DirectionLeftSymbol);
            }else{
                call rotate(rite[REB_parent], DirectionRiteSymbol);
            }
        };
reb1:
        REB_curr := REB_parent;
    };
    return;
}

(*
Returns: nothing meaningful
*)
procedure split_left_wing_into_new_chunk(SLWINC_node)
    variables
        SLWINC_c;
        SLWINC_new_chunk;
        SLWINC_left_wing;
        SLWINC_i;
{
slwinc0:
    SLWINC_c := chunk_of_node[SLWINC_node];
    SLWINC_new_chunk := UnusedChunkAddr;
    SLWINC_left_wing := SetToSeq(left_wing[chunk_of_node[SLWINC_node]]);
    SLWINC_i := 1;

slwinc1:
    while(SLWINC_i <= Len(SLWINC_left_wing)){
slwinc2:
        if(key[SLWINC_left_wing[SLWINC_i]] < key[left[SLWINC_node]]){
            chunk_insert_left(
                UnusedLeafNodeAddr,
                SLWINC_new_chunk, 
                key[SLWINC_left_wing[SLWINC_i]],
                val[SLWINC_left_wing[SLWINC_i]],
                parent[SLWINC_left_wing[SLWINC_i]]
            );
        }else{
            chunk_insert_rite(
                UnusedLeafNodeAddr,
                SLWINC_new_chunk, 
                key[SLWINC_left_wing[SLWINC_i]],
                val[SLWINC_left_wing[SLWINC_i]],
                parent[SLWINC_left_wing[SLWINC_i]]
            );
        };
slwinc3:
        SLWINC_i := SLWINC_i + 1;
    };

    root_of_chunk[SLWINC_new_chunk] := left[SLWINC_node];
    chunk_of_node[root_of_chunk[SLWINC_new_chunk]] := SLWINC_new_chunk;

slwinc4:
    chunk_of_node[root_of_chunk[SLWINC_c]] := Null;
    root_of_chunk[SLWINC_c] := rite[SLWINC_node];
slwinc5:
    chunk_of_node[root_of_chunk[SLWINC_c]] := SLWINC_c;

    left_wing[SLWINC_c] := {}; \* TODO: do this properly
    call chunk_shift_left(SLWINC_c, key[rite[SLWINC_node]]);

    return;
}

(*
Returns: nothing meaningful
*)
procedure insert_impl(II_k, II_v, II_curr, II_c)
    variables
        II_inserted;
        II_parent;
        II_new_leaf_parent;
        II_curr_was_left_child;
{
ii0:
    if(IsChunkRoot(II_curr)){
        II_c := chunk_of_node[II_curr];

        if(ChunkIsFull(II_c)){
            call split_left_wing_into_new_chunk(II_curr);
ii1:
            II_c := Null;
        }
    };

ii2:
    if(~IsLeaf(II_curr)){
        if(II_k < key[II_curr]){
            call insert_impl(II_k, II_v, left[II_curr], II_c);
            return;
        };
ii3:
        call insert_impl(II_k, II_v, rite[II_curr], II_c);
        return;
    };

ii4:
    if(key[II_curr] = II_k){
        val[II_curr] := II_v;
        (*
        NOTE: we declare the operation to fail because we only model
        a situtation where the key is always equal to the value. Since the key is
        present, we fail.
        *)
        operation_fail();
        return;
    };

ii5:
    II_inserted := UnusedLeafNodeAddr;

    if(II_k < key[root_of_chunk[II_c]]){
ii6:
        chunk_insert_left(II_inserted, II_c, II_k, II_v, Null);
    }else{
ii7:
        chunk_insert_rite(II_inserted, II_c, II_k, II_v, Null);
    };
ii8:

    II_parent := parent[II_curr];

    II_curr_was_left_child := IsLeftChild(II_parent, II_curr);
    
    II_new_leaf_parent := UnusedInnerNodeAddr;

    if(II_k < key[II_curr]){
        write_non_leaf(II_new_leaf_parent, key[II_curr], II_inserted, II_curr);
    }else{
        write_non_leaf(II_new_leaf_parent, II_k, II_curr, II_inserted);
    };

    if(II_curr_was_left_child){
ii9:
        left[II_parent] := II_new_leaf_parent;
    }else{
ii10:
        rite[II_parent] := II_new_leaf_parent;
    };

ii11:
    parent[II_new_leaf_parent] := II_parent;

    if(IsChunkRoot(II_curr)){
        chunk_of_node[II_new_leaf_parent] := II_c;
        root_of_chunk[II_c] := II_new_leaf_parent;
ii12:
        chunk_of_node[II_curr] := Null;
        call chunk_shift_left(chunk_of_node[II_new_leaf_parent], II_k);
    };
    
ii13:
    call rebalance(parent[II_new_leaf_parent]);
ii14:
    operation_succeed();
    return;
}

(*
Returns: nothing meaningful
*)
procedure insert(I_k, I_v)
    variables
        I_chunk;
        I_inserted;
{
i0:
    if(rite[RootHolder] = Null){
        I_chunk := UnusedChunkAddr;
        I_inserted := UnusedLeafNodeAddr;
i1:
        chunk_insert_rite(I_inserted, I_chunk, I_k, I_v, Null);
i2:
        rite[RootHolder] := I_inserted;
        parent[rite[RootHolder]] := RootHolder;
        chunk_of_node[rite[RootHolder]] := I_chunk;
        root_of_chunk[I_chunk] := rite[RootHolder];
        operation_succeed();
        return;
    };

i3:
    call insert_impl(I_k, I_v, rite[RootHolder], Null);
    return;
}

(*
Returns: nothing meaningful
src: erase_impl
*)
procedure do_erase(DE_k, DE_curr, DE_non_leaf_with_key_k, DE_c)
    variables
        DE_parent;
        DE_parent_parent;
{
de0:
    DE_parent := parent[DE_curr];

    if(IsChunkRoot(DE_curr)){

        destroy_chunk(DE_c);

        if(DE_parent = RootHolder){
            rite[RootHolder] := Null;
de1:
            operation_succeed();
            return;
        };

    }else{

        if(DE_k < key[root_of_chunk[DE_c]]){
            chunk_erase(DE_c, DirectionLeftSymbol, DE_k);
        }else{
            chunk_erase(DE_c, DirectionRiteSymbol, DE_k);
        }

    };

de2:

    DE_parent_parent := parent[DE_parent];

    if(DE_non_leaf_with_key_k = Null){

        if(IsChunkRoot(DE_parent)){
            root_of_chunk[DE_c] := rite[DE_parent];
            chunk_of_node[root_of_chunk[DE_c]] := DE_c;
            call chunk_shift_left(DE_c, key[root_of_chunk[DE_c]]);
        };
de3:

        bind_parent_to_new_child(DE_parent_parent, DE_parent, rite[DE_parent]);

    }else if(DE_non_leaf_with_key_k = DE_parent){

        if(IsChunkRoot(DE_parent)){
            call chunk_shift_rite(DE_c, key[left[DE_parent]]);
de4:
            root_of_chunk[DE_c] := left[DE_parent];
            chunk_of_node[root_of_chunk[DE_c]] := DE_c;
        };

de5:
        bind_parent_to_new_child(DE_parent_parent, DE_parent, left[DE_parent]);

    }else{

        if(IsChunkRoot(DE_parent)){
            root_of_chunk[DE_c] := rite[DE_parent];
            chunk_of_node[root_of_chunk[DE_c]] := DE_c;
            call chunk_shift_left(DE_c, key[root_of_chunk[DE_c]]);
        };
de6:

        key[DE_non_leaf_with_key_k] := key[DE_parent];

        if(DE_parent_parent = DE_non_leaf_with_key_k){
            rite[DE_parent_parent] := rite[DE_parent];
        }else{
            left[DE_parent_parent] := rite[DE_parent];
        };

        parent[rite[DE_parent]] := DE_parent_parent;

    };
de7:

    destroy_non_leaf(DE_parent);

    operation_succeed(); \* 'Cheat' a bit with ordering (makes no difference)
    call rebalance(DE_parent_parent);
    return;
    
}



(*
Returns: nothing meaningful
src: erase_impl
*)
procedure erase_impl(E_k, E_curr, E_non_leaf_with_key_k, E_c)
    variables
{
e0:
    if(E_curr # Null){
        if(IsChunkRoot(E_curr)){
            E_c := chunk_of_node[E_curr];
        };

        if(key[E_curr] = E_k){
            if(IsLeaf(E_curr)){
e1:
                call do_erase(E_k, E_curr, E_non_leaf_with_key_k, E_c);
                return;
            };
e2:
            E_non_leaf_with_key_k := E_curr;
        };

e3:
        if(E_k < key[E_curr]){
            call erase_impl(E_k, left[E_curr], E_non_leaf_with_key_k, E_c);
        }else{
            call erase_impl(E_k, rite[E_curr], E_non_leaf_with_key_k, E_c);
        }
    }else{
        operation_fail();
    };
e4:
    return;
}

fair process (reader \in Readers )
{
reader0:
    \* with (e \in KeySetToOperateOn){
        \* ret[self] := Null;
        \* operation_succeed[self] := Null;
        \* invoke("get", e);
        \* call get(e);
    \* };
\* reader1:
    \* respond(operation_succeed[self]);
    skip;
}

fair process (writer \in Writers )
{
writer0:
    while(num_write_operations < NumWriteOperations){
        num_write_operations := num_write_operations + 1;
        with (e \in KeySetToOperateOn){
            ret[self] := Null;
            operation_succeeded[self] := Null;
            either{
                invoke("insert", e);
                call insert(e, e);
            } 
            or {
                invoke("erase", e);
                \* skip wrapper
                call erase_impl(e, rite[RootHolder], Null, Null);
            }
            or {
                invoke("get", e);
                call get(e);
            }
        };
writer1:
        respond(operation_succeeded[self]);
    }
}

fair process (verifier = "verifier")
{
verif0:
    await \A p \in Procs  : pc[p] = "Done";
    assert IsLinearizable(event_sequence, {}); \* Reachable at start is empty
}


} *)


\* BEGIN TRANSLATION (chksum(pcal) = "3d995e94" /\ chksum(tla) = "cb61478d")
\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Apr 12 16:36:20 BST 2021 by dan
\* Created Tue Feb 02 11:29:57 GMT 2021 by dan
