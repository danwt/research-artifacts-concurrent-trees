------------------- MODULE mrsw_iterative_full_retry_map_based -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Linearizability, TreeGeneration, TreeStructure, Reals

CONSTANT NullModelValue
CONSTANT Readers \* Always contains 1
CONSTANT Writers \* Always 1 for MRSW

Procs == 
    Writers 
    \cup Readers

MaxKey == 4
ChunkMaxSize == 4
NumWriteOperations == MaxKey
KeySetToOperateOn == 1..MaxKey
LeafNodeAddressSet == 10..20
InnerNodeAddressSet == KeySetToOperateOn
CallStackLimit == 12
VersionNumberBound == 10

IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
Range(f) == { f[x] : x \in DOMAIN f }
SeqToSet(f) == Range(f)

ChunkAddressSet == LeafNodeAddressSet \* Worst case: each leaf has its own chunk.

RootHolder == 0
AddressSetWithoutRootHolder == InnerNodeAddressSet \cup LeafNodeAddressSet 
AddressSetWithRootHolder ==  AddressSetWithoutRootHolder \cup {RootHolder}

IntegerShift == 100
null ==                        IntegerShift + 1
ShrinkingSymbol ==             IntegerShift + 2
RetrySymbol ==                 IntegerShift + 4
FullRetrySymbol ==             IntegerShift + 5
DirectionLeftSymbol ==         IntegerShift + 6
DirectionRiteSymbol ==         IntegerShift + 7
NoRepairActionRequired ==      IntegerShift + 8
UnlinkActionRequired ==        IntegerShift + 9
RebalanceActionRequired ==     IntegerShift + 10
FalseInt ==                    IntegerShift + 11
TrueInt ==                     IntegerShift + 12
IntBoolAsBool(x) == x = TrueInt
IsIntBool(x) == x = TrueInt \/ x = FalseInt

(* --algorithm algo {

variables

    (* Non-algorithm variables *)

    event_sequence = <<>>;
    operation_succeeded = [p \in Procs |-> null];
    num_write_operations = 0;

    (* Algorithm variables *)
    
    ver           = [e \in AddressSetWithRootHolder    |-> 0];  
    is_leaf       = [e \in AddressSetWithRootHolder    |-> FALSE]; 
    chunk_of_node = [e \in AddressSetWithRootHolder    |-> null]; 
    key           = [e \in AddressSetWithRootHolder    |-> null]; 
    height        = [e \in AddressSetWithRootHolder    |-> null]; 
    parent        = [e \in AddressSetWithRootHolder    |-> null];
    left          = [e \in AddressSetWithRootHolder    |-> null];
    rite          = [e \in AddressSetWithRootHolder    |-> null];

    root_of_chunk = [e \in ChunkAddressSet |-> null];
    left_wing     = [e \in ChunkAddressSet |-> {}];
    rite_wing     = [e \in ChunkAddressSet |-> {}];

    rotate_ret = null;

define {

    (* Algorithm operators *)

    NullSafeHeight(e) == IF e = null THEN 0 ELSE height[e]
    LeftHeight(e) == NullSafeHeight(left[e])
    RiteHeight(e) == NullSafeHeight(rite[e])
    IsLeftChild(p, c) == left[p] = c 
    IsRiteChild(p, c) == rite[p] = c 
    ChunkLeftSize(e) == Cardinality(left_wing[e])
    ChunkRiteSize(e) == Cardinality(rite_wing[e])
    ChunkSize(e) == ChunkLeftSize(e) + ChunkRiteSize(e)
    ChunkIsFull(e) == ChunkMaxSize <= ChunkSize(e)
    IsChunkRoot(e) == chunk_of_node[e] #null 
    IsLeaf(e) == is_leaf[e]

    IsShrinking(x) == x = ShrinkingSymbol
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
    BalanceFactorIsBalanced(x) == (-2 < x) /\ (x < 2)
    NodeIsBalanced(e) == BalanceFactorIsBalanced(BalanceFactor(e))

    IsUnusedNodeAddr(e) == key[e] =null 
    UnusedInnerNodeAddr == CHOOSE e \in InnerNodeAddressSet : IsUnusedNodeAddr(e)
    UnusedLeafNodeAddr == CHOOSE e \in LeafNodeAddressSet : IsUnusedNodeAddr(e)

    IsUnusedChunkAddr(e) == root_of_chunk[e] =null 
    UnusedChunkAddr == CHOOSE e \in ChunkAddressSet : IsUnusedChunkAddr(e)

}

macro invoke(operation_name, arg){
    event_sequence := event_sequence \o <<<<"invoke", self, operation_name, arg>>>>;
}

macro respond(succeeded_int_bool){
    assert IsIntBool(succeeded_int_bool);
    event_sequence := event_sequence \o <<<<"respond", self, IntBoolAsBool(succeeded_int_bool) >>>>;
}

(*
Get succeeds if the key was present
Erase succeeds if the key was present and update removes it
Insert succeeds if the key was not present and update inserts it
*)
macro operation_succeed(){
    assert operation_succeeded[self] = null;
    operation_succeeded[self] := TrueInt;
}

macro operation_fail(){
    assert operation_succeeded[self] = null;
    operation_succeeded[self] := FalseInt;
}

(*
Precondition: left child and right child both have height 1
*)
macro new_non_leaf(m_address, m_k, m_left_child, m_rite_child){
    key[m_address] := m_k;
    height[m_address] := 2;
    left[m_address] := m_left_child;
    rite[m_address] := m_rite_child;
}

macro update_node_height_based_on_child_heights(m_node){
    height[m_node] := MaxPlusOne(LeftHeight(m_node), RiteHeight(m_node)) + 1;
}

macro write_data_to_node_and_link_parent(m_node, m_k, m_parent){

    assert IsUnusedNodeAddr(m_node);
    is_leaf[m_node] := TRUE;
    height[m_node] := 1;
    key[m_node] := m_k;
    parent[m_node] := m_parent;

    if(m_parent # null){
        if(left[m_parent] # null){
            if(key[left[m_parent]] = m_k){
                left[m_parent] := m_node;
            }
        }else{
            rite[m_parent] := m_node;
        }
    }
}

macro chunk_insert_left(m_leaf_addr, m_chunk_addr, m_k, m_parent)
{
    left_wing[m_chunk_addr] := left_wing[m_chunk_addr] \cup {m_leaf_addr};
    write_data_to_node_and_link_parent(m_leaf_addr, m_k, m_parent);
}

macro chunk_insert_rite(m_leaf_addr, m_chunk_addr, m_k, m_parent)
{
    rite_wing[m_chunk_addr] := rite_wing[m_chunk_addr] \cup {m_leaf_addr};
    write_data_to_node_and_link_parent(m_leaf_addr, m_k, m_parent);
}

macro chunk_erase(m_chunk_addr, m_directionSymbolForWing, m_k)
{
    if(m_directionSymbolForWing = DirectionLeftSymbol){
        left_wing[m_chunk_addr] := left_wing[m_chunk_addr] \ {e \in left_wing[m_chunk_addr] : key[e] = m_k};
    }else{
        rite_wing[m_chunk_addr] := rite_wing[m_chunk_addr] \ {e \in rite_wing[m_chunk_addr] : key[e] = m_k};
    }
}

macro bind_parent_to_new_child(m_parent, m_old_child, m_replacement_child)
{
    if(IsLeftChild(m_parent, m_old_child)){
        left[m_parent] := m_replacement_child;
        parent[left[m_parent]] := m_parent;
    }else{
        rite[m_parent] := m_replacement_child;
        parent[rite[m_parent]] := m_parent;
    }
}

procedure chunk_shift_left(CSL_chunkAddr, CSL_minKeyToKeep)
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
            parent[CSL_shift_seq[CSL_i]]
        );
csl2:
        CSL_i := CSL_i + 1;
    };
    rite_wing[CSL_chunkAddr] := rite_wing[CSL_chunkAddr] \ SeqToSet(CSL_shift_seq);
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
            parent[CSR_shift_seq[CSR_i]]
        );
csr2:
        CSR_i := CSR_i + 1;
    };
    left_wing[CSR_chunkAddr] := left_wing[CSR_chunkAddr] \ SeqToSet(CSR_shift_seq); 
    return;
}

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
        if(key[SLWINC_left_wing[SLWINC_i]] < key[left[SLWINC_node]]){
            chunk_insert_left(
                UnusedLeafNodeAddr,
                SLWINC_new_chunk, 
                key[SLWINC_left_wing[SLWINC_i]],
                parent[SLWINC_left_wing[SLWINC_i]]
            );
        }else{
            chunk_insert_rite(
                UnusedLeafNodeAddr,
                SLWINC_new_chunk, 
                key[SLWINC_left_wing[SLWINC_i]],
                parent[SLWINC_left_wing[SLWINC_i]]
            );
        };
        SLWINC_i := SLWINC_i + 1;
    };

    root_of_chunk[SLWINC_new_chunk] := left[SLWINC_node];
    chunk_of_node[root_of_chunk[SLWINC_new_chunk]] := SLWINC_new_chunk;

slwinc2:
    chunk_of_node[root_of_chunk[SLWINC_c]] := null;
    root_of_chunk[SLWINC_c] := rite[SLWINC_node];
slwinc3:
    chunk_of_node[root_of_chunk[SLWINC_c]] := SLWINC_c;

    left_wing[SLWINC_c] := {};
    call chunk_shift_left(SLWINC_c, key[rite[SLWINC_node]]);

    return;
}

procedure get(G_k)
    variables
        G_curr;
        G_currOvl;
        G_dirToC;
        G_child;
        G_childKey;
        G_childOvl;
{
g0:
    G_curr := RootHolder;
    G_currOvl := 0;
    G_dirToC := DirectionRiteSymbol;

g1:
    while(TRUE){
        G_child := Child(G_curr, G_dirToC);
gt0:
        if(ver[G_curr] # G_currOvl){
            G_curr := RootHolder;
            G_currOvl := 0;
            G_dirToC := DirectionRiteSymbol;
        }else if(G_child = null){
            operation_fail();
            return;
        }else{
            G_childKey := key[G_child];
            if(G_childKey = G_k /\ IsLeaf(G_child)){
                operation_succeed();
g2:
                return;
            };
g3:
            G_childOvl := ver[G_child];
gt1:
            if(G_child = Child(G_curr, DirectionRiteSymbol)){
gt2:
                if(ver[G_curr] = G_currOvl){
gt3:
                    if(~IsShrinking(G_childOvl)){
                        G_curr := G_child;
                        G_currOvl := G_childOvl;
                        G_dirToC := AppropriateDirection(G_childKey, G_k);
                    }
                }
            }
        }
    }
}

procedure rotate_left(RL_pivot)
    variables
        RL_new_pivot;
        RL_child_of_new_pivot;
{
rl0:
   if(IsChunkRoot(RL_pivot)){
       call chunk_shift_left(chunk_of_node[RL_pivot], key[rite[RL_pivot]]);
rl1:
       root_of_chunk[chunk_of_node[RL_pivot]] := rite[RL_pivot];
       chunk_of_node[rite[RL_pivot]] := chunk_of_node[RL_pivot];
rl2:
       chunk_of_node[RL_pivot] := null;
   } else if (IsChunkRoot(rite[RL_pivot])){
       call split_left_wing_into_new_chunk(rite[RL_pivot]);
   };

rl3:
    RL_new_pivot := rite[RL_pivot];
rlt0:
    parent[RL_new_pivot] := parent[RL_pivot];
rlt1:
    rite[RL_pivot] := left[RL_new_pivot];
rl4:
    parent[left[RL_new_pivot]] := RL_pivot;
rlt2:
    left[RL_new_pivot] := RL_pivot;
rl5:
    parent[RL_pivot] := RL_new_pivot;

    update_node_height_based_on_child_heights(left[RL_new_pivot]);
rl6:
    update_node_height_based_on_child_heights(RL_new_pivot);

    rotate_ret := RL_new_pivot;
    return;
}

procedure rotate_rite(RR_pivot)
    variables
        RR_new_pivot;
        RR_child_of_new_pivot;
{
rr0:
   if(IsChunkRoot(RR_pivot)){
       call chunk_shift_rite(chunk_of_node[RR_pivot], key[left[RR_pivot]]);
rr1:
       root_of_chunk[chunk_of_node[RR_pivot]] := left[RR_pivot];
       chunk_of_node[left[RR_pivot]] := chunk_of_node[RR_pivot];
rr2:
       chunk_of_node[RR_pivot] := null;
   } else if (IsChunkRoot(left[RR_pivot])){
       call split_left_wing_into_new_chunk(left[RR_pivot]);
   };

rr3:
    RR_new_pivot := left[RR_pivot];
rrt0:
    parent[RR_new_pivot] := parent[RR_pivot];
rrt1:
    left[RR_pivot] := rite[RR_new_pivot];
rr4:
    parent[rite[RR_new_pivot]] := RR_pivot;
rrt2:
    rite[RR_new_pivot] := RR_pivot;
rr5:
    parent[RR_pivot] := RR_new_pivot;

    update_node_height_based_on_child_heights(rite[RR_new_pivot]);
rr6:
    update_node_height_based_on_child_heights(RR_new_pivot);

    rotate_ret := RR_new_pivot;
    return;
}

procedure rotate(R_pivot)
    variables
        R_bal;
        R_shrinking;
        R_ver;
{
r0:
    R_bal := BalanceFactor(R_pivot);
    if(R_bal < -1){
        if (0 < BalanceFactor(left[R_pivot])){
            R_shrinking := left[R_pivot];
            R_ver := ver[R_shrinking];
rt0:
            ver[R_shrinking] := BeginChange(R_ver);
rt1:
            call rotate_left(R_shrinking);
r1:
            left[R_pivot] := rotate_ret || rotate_ret := null;
rt2:
            ver[R_shrinking] := EndChange(R_ver);
        };
r2:
        call rotate_rite(R_pivot);
        return;
    };
r3:
    if (BalanceFactor(rite[R_pivot]) < 0){
        R_shrinking := rite[R_pivot];
        R_ver := ver[R_shrinking];
rt3:
        ver[R_shrinking] := BeginChange(R_ver);
rt4:
        call rotate_rite(R_shrinking);
r4:
        rite[R_pivot] := rotate_ret || rotate_ret := null;
rt5:
        ver[R_shrinking] := EndChange(R_ver);
    };
r5:
    call rotate_left(R_pivot);
    return;
}


procedure rebalance(REB_curr)
    variables
        REB_parent;
        REB_shrinking;
        REB_ver;
{
reb0:
    while(parent[REB_curr] # null){
        update_node_height_based_on_child_heights(REB_curr);
rebt0:
        REB_parent := parent[REB_curr];
        if(~NodeIsBalanced(REB_curr)){
            if(IsLeftChild(REB_parent, REB_curr)){
                if(~NodeIsBalanced(left[REB_parent])){
                    REB_shrinking := left[REB_parent];
                    REB_ver := ver[REB_shrinking];
rebt1:
                    ver[REB_shrinking] := BeginChange(REB_ver);
rebt2:
                    call rotate(REB_shrinking);
reb1:
                    left[REB_parent] := rotate_ret || rotate_ret := null;
rebt3:
                    ver[REB_shrinking] := EndChange(REB_ver);
                }
            }else if(IsRiteChild(REB_parent, REB_curr)){
                if(~NodeIsBalanced(rite[REB_parent])){
                    REB_shrinking := rite[REB_parent];
                    REB_ver := ver[REB_shrinking];
rebt4:
                    ver[REB_shrinking] := BeginChange(REB_ver);
rebt5:
                    call rotate(REB_shrinking);
reb2:
                    rite[REB_parent] := rotate_ret || rotate_ret := null;
rebt6:
                    ver[REB_shrinking] := EndChange(REB_ver);
                }
            }
        };
reb3:
        REB_curr := REB_parent;
    };
    return;
}

procedure insert(I_k)
    variables
        I_chunk;
        I_inserted;
        I_curr;        
        I_c;
        I_parent;
        I_curr_is_left_child;
        I_new_leaf_parent;
{
i0:
    if(rite[RootHolder] = null){
        I_chunk := UnusedChunkAddr;
        I_inserted := UnusedLeafNodeAddr;
        chunk_insert_rite(I_inserted, I_chunk, I_k, null);
i1:
        rite[RootHolder] := I_inserted;
        parent[rite[RootHolder]] := RootHolder;
        chunk_of_node[rite[RootHolder]] := I_chunk;
        root_of_chunk[I_chunk] := rite[RootHolder];
        operation_succeed();
        return;
    };

i2:
    I_curr := rite[RootHolder];
    I_c := null;

i3:
    while(TRUE){
        if(IsChunkRoot(I_curr)){
            I_c := chunk_of_node[I_curr];

            if(ChunkIsFull(I_c)){
                call split_left_wing_into_new_chunk(I_curr);
i4:
                I_c := null;
            }
        };

i5:
        if(~IsLeaf(I_curr)){
            if(I_k < key[I_curr]){
                I_curr := left[I_curr];
            }else{
                I_curr := rite[I_curr];
            }
        }else{

            if(key[I_curr] = I_k){
                operation_fail();
                return;
            };

i6:
            I_inserted := UnusedLeafNodeAddr;

            if(I_k < key[root_of_chunk[I_c]]){
                chunk_insert_left(I_inserted, I_c, I_k, null);
            }else{
                chunk_insert_rite(I_inserted, I_c, I_k, null);
            };

            I_parent := parent[I_curr];

            I_curr_is_left_child := IsLeftChild(I_parent, I_curr);
            
            I_new_leaf_parent := UnusedInnerNodeAddr;

            if(I_k < key[I_curr]){
i7:
                new_non_leaf(I_new_leaf_parent, key[I_curr], I_inserted, I_curr);
            }else{
i8:
                new_non_leaf(I_new_leaf_parent, I_k, I_curr, I_inserted);
            };
i9:
            parent[I_inserted] := I_new_leaf_parent;
i10:
            parent[I_curr] := I_new_leaf_parent;

            if(I_curr_is_left_child){
                left[I_parent] := I_new_leaf_parent;
            }else{
                rite[I_parent] := I_new_leaf_parent;
            };
i11:

            parent[I_new_leaf_parent] := I_parent;

            if(IsChunkRoot(I_curr)){
                chunk_of_node[I_new_leaf_parent] := I_c;
                root_of_chunk[I_c] := I_new_leaf_parent;
i12:
                chunk_of_node[I_curr] := null;
                call chunk_shift_left(chunk_of_node[I_new_leaf_parent], I_k);
            };
            
i13:
            call rebalance(parent[I_new_leaf_parent]);
i14:
            operation_succeed();
            return;
        }
    }
}

procedure do_erase(DE_k, DE_curr, DE_non_leaf_with_key_k, DE_c)
    variables
        DE_parent;
        DE_parent_parent;
{
de0:
    DE_parent := parent[DE_curr];

    if(IsChunkRoot(DE_curr)){

        if(DE_parent = RootHolder){
            rite[RootHolder] := null;
            operation_succeed();
de1:
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

    if(DE_non_leaf_with_key_k = null){

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

det0:
        if(DE_parent_parent = DE_non_leaf_with_key_k){
            rite[DE_parent_parent] := rite[DE_parent];
        }else{
            left[DE_parent_parent] := rite[DE_parent];
        };

        parent[rite[DE_parent]] := DE_parent_parent;

    };

de7:
    operation_succeed();
    call rebalance(DE_parent_parent);
    return;
    
}

procedure erase(E_k, E_curr, E_non_leaf_with_key_k, E_c)
{
e0:
    while(TRUE){
        if(E_curr = null){
            operation_fail();
            return;
        };
e1:
        if(IsChunkRoot(E_curr)){
            E_c := chunk_of_node[E_curr];
        };
        if(key[E_curr] = E_k){
            if(IsLeaf(E_curr)){
e2:
                call do_erase(E_k, E_curr, E_non_leaf_with_key_k, E_c);
                return;
            };
e3:
            E_non_leaf_with_key_k := E_curr;
        };
e4:
        if(E_k < key[E_curr]){
            E_curr := left[E_curr];
        }else{
            E_curr := rite[E_curr];
        };
    }
}

(*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
'Meta' aspects of the model are below this line.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
*)

fair process (reader \in Readers)
{
readInv:
    with (e \in KeySetToOperateOn){
        invoke("get", e);
        call get(e);
    };
readResp:
    respond(operation_succeeded[self]);
}

fair process (writer \in Writers )
{
writeInv:
    while(num_write_operations < NumWriteOperations){
        num_write_operations := num_write_operations + 1;
        with (e \in KeySetToOperateOn){
            operation_succeeded[self] := null;
            either{
                invoke("insert", e);
                call insert(e);
            } 
            or {
                invoke("erase", e);
                call erase(e, rite[RootHolder], null, null);
            }
        };
writeResp:
        respond(operation_succeeded[self]);
    }
}

fair process (verifier = "verifier")
{
verif:
    await \A p \in Readers  : pc[p] = "Done";
    await \A p \in Writers  : pc[p] = "Done";
    assert IsLinearizable(event_sequence, {}); \* Nothing is reachable at the start
}

} *)


\* BEGIN TRANSLATION (chksum(pcal) = "8beb7653" /\ chksum(tla) = "20b69330")
\* END TRANSLATION 

VersionNumbersAreBounded == \A x \in Range(ver) : x <= VersionNumberBound \/ IsShrinking(x)

CallStackSizesAreBounded == \A p \in Procs : Len(stack[p]) < CallStackLimit

QuiescenceGuarantees == 

                    LET 

                        IsQuiescent(p) == pc[p] = "Done"

                            
                    IN  (\A p \in Writers: IsQuiescent(p)) => 
                        (
                        /\ IsCycleFree(null, left, rite, RootHolder)
                        /\ IsBalanced(null, left, rite, RootHolder)
                        )

AllInvariants == 
    /\ QuiescenceGuarantees
    /\ TRUE

=============================================================================
\* Modification History
\* Last modified Mon Jun 07 10:07:52 BST 2021 by dan
\* Created Tue Feb 02 11:29:57 GMT 2021 by dan
