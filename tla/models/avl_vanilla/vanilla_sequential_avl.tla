------------------- MODULE vanilla_sequential_avl -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences

CONSTANTS KeyMax, \* values for key/value pairs (positive integer)
          Procs, \* processes, use 1 for now, e.g {p1} (model value)
          Null \* (model value)

Keys == 1..KeyMax
Min(S) == CHOOSE i \in S : \A j \in S : i <= j
Max(S) == CHOOSE i \in S : \A j \in S : j <= i
Abs(x) == Max({x, 0 - x})

\* Joins two edge sets, if there is an edge a->b in R and b->c in S then it will return a->c
R**S == LET T == {rs \in R \times S : rs[1][2] = rs[2][1]}
        IN {<<x[1][1],x[2][2]>> : x \in T}
        
NodesOf(R) == { r[1] : r \in R } \union { r[2] : r \in R }

\* Transitive closure, taken from Lamport's hyperbook, S 9.6.2
LamportRelationTC(R) ==
    \* Takes a set of relations {<<s,t>>}
    LET RECURSIVE STC(_)
        (*
        This is: edges u 2 edges u 3 edges u 4 edges ...
        By starting with n+1 then we include (full length) cycles
        *)
        STC(n) == IF n=1 THEN R
                         ELSE STC(n-1) \union STC(n-1)**R
    IN IF R={} THEN {} ELSE STC(Cardinality(NodesOf(R))+1)

  
Relation(f) == {<<x, f[x]>> : x \in DOMAIN f }

Range(f) == { f[x] : x \in DOMAIN f }

(* --algorithm algo {

\* TODO: right now all the labels are just in the minimally necessary places

variables

    (* parent = [e \in Keys |-> Null]; \* TODO: use parent ptr version *)
    left = [e \in Keys |-> Null]; 
    right = [e \in Keys |-> Null];
    height = [e \in Keys |-> Null];
    root = Null; \* Hold the key of root -> just makes code easier
    t_stack = [e \in Procs |-> <<>>]; \* use stack for now (just for first iteration, see todo above)

    ret = [e \in Procs |-> Null]; \* 'return' values
    ret_expect = [e \in Procs |-> Null];
    should_be_present = {}; \* Keys that should be in the tree 
    
define {
    Height(e) == IF e = Null THEN 0 ELSE height[e]
    LeftHeight(e) == Height(left[e])
    RightHeight(e) == Height(right[e])
    BalanceFactor(e) == RightHeight(e) - LeftHeight(e)
    IsBalanced(e) == Abs(BalanceFactor(e)) < 2
    IsLeftChild(p, c) == left[p] = c
    IsRightChild(p, c) == right[p] = c
    PeekStack(proc) == Head(t_stack[proc])
    StackIsEmpty(proc) == Len(t_stack[proc]) = 0

    EdgesWithNonNullDest(f) == { r \in Relation(f): r[2] # Null }

    TypeInvariant == /\ Null \notin DOMAIN left
                     /\ Null \notin DOMAIN right
                     /\ Null \notin DOMAIN height
                     (* TODO: a useful invariant would be to check that there is only at most one path from any node to any other node *)
                     /\ EdgesWithNonNullDest(left) \cap EdgesWithNonNullDest(right) = {}

    OutgoingEdges == EdgesWithNonNullDest(left) \cup EdgesWithNonNullDest(right)
    TransitiveClosure == LamportRelationTC(OutgoingEdges)

    Reachable == {root} \cup {r[2] : r \in TransitiveClosure} \* NOTE: there are many alternative ways to consider this
    NoCycles == ~ \E r \in TransitiveClosure : r[1] = r[2]
    IsRoot(e) == \A c \in Reachable \ {e} : <<e, c>> \in TransitiveClosure
    RootIsTheUniqueRoot == \/ Reachable = {Null}
                           \/ \A e \in Reachable : (e = root) = IsRoot(e)

    Balanced ==
        LET WithNull(f) == f @@ Null :> Null
        IN
            LET RECURSIVE TrueHeight(_) 
                TrueHeight(e) == IF e = Null THEN 0
                                             ELSE Max({TrueHeight(WithNull(left)[e]), TrueHeight(WithNull(right)[e])}) + 1
        \* DENK: maybe it's better to not make these helpers depend on each other too much
        IN \A e \in Reachable : Abs(TrueHeight(WithNull(right)[e]) - TrueHeight(WithNull(left)[e])) < 2

}

macro debuggable_invariant_check(){
    assert ret[self] = ret_expect[self];
    assert \/ 
             /\ should_be_present = {} 
             /\ Reachable = {Null}
           \/ Reachable = should_be_present;
    assert NoCycles;
    assert RootIsTheUniqueRoot;
    assert Balanced;
}

macro free_node(k){
    left[k] := Null;
    right[k] := Null;
    height[k] := Null;
}

macro adjust_node_height(k){
    height[k] := Max({LeftHeight(k), RightHeight(k)}) + 1;
}

macro clear_stack(){
    t_stack[self] := <<>>;
}

macro push_stack(k){
    t_stack[self] := <<k>> \o t_stack[self];
}
    
macro pop_stack(){
    t_stack[self] := Tail(t_stack[self]);
}

procedure get(k)
    variable curr;
{
g1:
    if(root = Null){
        return;
    };
g2:
    curr := root;
g3:
    while(curr # k){
        if(k < curr){
            if(left[curr] # Null){
                curr := left[curr];
            }else{
                return;
            }
        } else if (right[curr] # Null){
            curr := right[curr];
        } else {
            return;
        }
    };
g4:
    ret[self] := curr;
    return;
}

(*
For rotation functions:

parent: key or Null -> Null means the new pivot should be root, then child_is_left is ignored
child_is_left: bool or Null -> left/right, or root in case of Null
*)

procedure rotate_left(parent, child_is_left, k)
    variables 
        new_pivot;
{
rotl1: 
    new_pivot := right[k];
    right[k] := left[new_pivot];
    left[new_pivot] := k;
rotl2:
    if(parent = Null){
        root := new_pivot;
    }else{
rotl3:
        if(child_is_left){
            left[parent] := new_pivot;
        }else{
rotl4:
            right[parent] := new_pivot;
        }
    };
rotl5:
    adjust_node_height(k);
rotl6:
    adjust_node_height(new_pivot);
    return;
}

procedure rotate_right(parent, child_is_left, k)
    variables 
        new_pivot;
{
rotr1: 
    new_pivot := left[k];
    left[k] := right[new_pivot];
    right[new_pivot] := k;
rotr2:
    if(parent = Null){
        root := new_pivot;
    }else{
rotr3:
        if(child_is_left){
            left[parent] := new_pivot;
        }else{
rotr4:
            right[parent] := new_pivot;
        }
    };
rotr5:
    adjust_node_height(k);
rotr6:
    adjust_node_height(new_pivot);
    return;
}

procedure rotate(parent, child_is_left, k)
    variables 
        bal;
{
rot1:
    bal := BalanceFactor(k);
    if(bal < 0 - 1){ \* If left heavy
        if(0 < BalanceFactor(left[k])){
            call rotate_left(k, TRUE, left[k]); \* If left is right heavy
        };
rot2:
        call rotate_right(parent, child_is_left, k);
    }else if(1 < bal){ \* If right heavy
        if(BalanceFactor(right[k]) < 0){
            call rotate_right(k, FALSE, right[k]); \* If right is left heavy
        };
rot4:
        call rotate_left(parent, child_is_left, k);
    };
rot5    :
    return;
}

procedure rebalance()
    variables  
        curr;
        parent;
{
reb1:
    while(~StackIsEmpty(self)){

        curr := PeekStack(self);
        pop_stack();
reb2:
        adjust_node_height(curr);

        if(~IsBalanced(curr)){
            if(StackIsEmpty(self)){
                call rotate(Null, Null, root);
                return;
            };
reb3:
            parent := PeekStack(self);

            if(IsLeftChild(parent, curr)){
                call rotate(parent, TRUE, curr);
            }else{
                assert IsRightChild(parent, curr);
                call rotate(parent, FALSE, curr);
            }
        }
    };
    
    return;
}

procedure insert(k)
    variables
        curr;
{
i1:
    if(root = Null){
        root := k;
        height[k] := 1;
        return;
    };
i2:
    clear_stack();
i3:
    curr := root;
i4:
    while(curr # k){
        push_stack(curr);
        if(k < curr){
            if(left[curr] # Null){
                curr := left[curr];
            }else{
                \* Insert
                left[curr] := k;
                height[k] := 1;
i5:
                call rebalance();
                return;
            }
        } else if (right[curr] # Null){
            curr := right[curr];
        } else {
            \* Insert
            right[curr] := k;
            height[k] := 1;
i6:
            call rebalance();
            return;
        }
    };
    
    return;
}

procedure erase(k)
    variables
        curr;
        parent;
        ghost_parent;
{
e1:
    if(root = Null){
        return;
    };
e2:
    clear_stack();
e3:
    curr := root;
e4: 
    while(curr # k){
        push_stack(curr);
        if(k < curr){
            if(left[curr] # Null){
                curr := left[curr];
            }else{
                return;
            }
        } else if (right[curr] # Null){
            curr := right[curr];
        } else {
            return;
        }
    };
e5:
    \* Swap with left successor (left for now, can change it)

    if(left[curr] = Null){ \* No successor, simply remove
        if(StackIsEmpty(self)){
            \* Item to be deleted is root
            root := right[root];
            free_node(k);
            return;
        };
e6:
        parent := PeekStack(self);
        if(IsLeftChild(parent, curr)){
            left[parent] := right[curr];
        }else{
            assert IsRightChild(parent, curr);
            right[parent] := right[curr];
        };
e7:
        free_node(k);
        call rebalance();
        return;
    };
e8:
    \* There is a successor, find it

    (* 
    We will need to save the parent of k if it exists (ghost parent).
    Note: an alternative would be to use a clever TLA operator to find the ghost parent later,
    but that may lead to us using assumptions which (for now) are too strong.
    *)

    ghost_parent := IF StackIsEmpty(self) THEN Null ELSE PeekStack(self);

e10: \* TODO: maybe this label isn't necessary but it's hard to be sure

    push_stack(curr);
    curr := left[curr];
e11:
    while(right[curr] # Null){
        push_stack(curr);
        curr := right[curr];
    };
e12:

    (* 
    Now set the successors parent to point to the successors left and
    let successor replace the role of k
    *)
    parent := PeekStack(self);

    if(IsLeftChild(parent, curr)){
        \* 'Special' case
        right[curr] := right[k];
    }else{
        assert IsRightChild(parent, curr);
        right[parent] := left[curr] || right[curr] := right[k];
        left[curr] := left[k];
    };

e13:
    (*
    Now: we have to make whatever pointed to k before, point to the successsor
    In an implementation this is not necessary as we will have been mutating objects
    *)
    if(ghost_parent = Null){
        root := curr;
    }else if(IsLeftChild(ghost_parent, k)){
        left[ghost_parent] := curr;
    }else{
        assert IsRightChild(ghost_parent, k);
        right[ghost_parent] := curr;
    };

e14:
    free_node(k);

    (* HACK: we have changed the pointers but there is still a value of k in the
    traversal stack, where we want the successor. We can replace this with curr using TLA.
    Note: this doesn't weaken our model of the implementation as the implementation will have mutated the Node object.
    *)

    t_stack[self][CHOOSE i \in 1..Len(t_stack[self]): t_stack[self][i] = k] := curr;

    call rebalance();
    return;
}

fair process (proc \in Procs ) 
(* 
Thought: For now we just go for the most naive approach with respect to assertions 
For example we check invariants with assert Invariant at the end of the while loop, however what is commonly done is to define invariants underneath the translation.
*)
{
main1:
    while(TRUE){
        ret_expect[self] := Null;
        ret[self] := Null;
main2:
        with (e \in Keys){
            either{
                if(e \in should_be_present){
                    ret_expect[self] := e;
                };
                call get(e);
            } or {
                should_be_present := should_be_present \cup {e};
                call insert(e);
            } or {
                should_be_present := should_be_present \ {e};
                call erase(e);
            };
        };
main3:
        debuggable_invariant_check();
    };
}

} *)

\* BEGIN TRANSLATION (chksum(pcal) = "b192180f" /\ chksum(tla) = "7352af4a")
\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Feb 05 08:53:43 GMT 2021 by dan
\* Created Tue Feb 02 11:29:57 GMT 2021 by dan
