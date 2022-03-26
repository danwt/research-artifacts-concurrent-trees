------------------- MODULE TreeStructureTest -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, TreeStructure, TreeGeneration, Linearizability

CONSTANT NullModelValue

TreeGenSizeMin == 2
TreeGenSizeMax == 5
TreeGenKeyMin == 2
TreeGenKeyMax == 5

RootHolder == 0
NodeAddressSet == 1..15
AddressSetWithoutRootHolder == NodeAddressSet
AddressSetWithRootHolder ==  AddressSetWithoutRootHolder \cup {RootHolder}

IntegerShift == 100
Null == IntegerShift + 1


(* --algorithm algo {

variables

    height        = [e \in AddressSetWithRootHolder    |-> Null]; 
    left          = [e \in AddressSetWithRootHolder    |-> Null];
    rite          = [e \in AddressSetWithRootHolder    |-> Null];


macro create_cycle(){
    \* Should be found by IsCycleFree
    rite[rite[RootHolder]] := RootHolder;
}

macro create_unreachable_cycle(){
    \* Should not be found by IsCycleFree
    rite[13] := 12 || rite[12] := 13;
}

fair process (initializer = "initializer")
{
init0:
    with (starter_state \in SetOfInterestingAvlTrees(TreeGenKeyMin, TreeGenKeyMax, TreeGenSizeMin, TreeGenSizeMax)){
        left := starter_state.left @@ left;
        rite := starter_state.rite @@ rite;
        height := starter_state.height @@ height;
    };
}

fair process (proc \in {"p0"})
{
main0:
    await pc["initializer"] = "Done";

    \* create_cycle();
    create_unreachable_cycle();
    
main1:
    assert IsCycleFree(Null, left, rite, RootHolder); \* If create_cycle executed, should provide a trace.
    assert IsBalanced(Null, left, rite, RootHolder);
}

} *)


\* BEGIN TRANSLATION (chksum(pcal) = "f69ed3ab" /\ chksum(tla) = "454f9ad2")
\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Thu Apr 15 14:52:22 BST 2021 by dan
\* Created Thu Apr 01 09:35:51 BST 2021 by dan
