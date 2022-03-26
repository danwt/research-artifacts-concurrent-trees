------------------- MODULE traversal -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Reals

(*

This is a model of a logical 'flow' in the MRSW Cavl tree.

The MRSW CAvl tree uses optimistic version number locks to ensure
that concurrent traversals are not thrown off course by concurrent
rotations.

This TLA+ model attempts to extract the relevant tricky logic from
the algorithm. Instead of modelling a tree, here we just model
a linked list with 4 elements.

The shape of the list is 

HEAD -> one -> two -> three -> END

the address of HEAD is fixed, and END is just a sentinel.

The traverser process will search for one of three keys, 1,2,3 and
will start from HEAD. A concurrent process will rearrange the list.
It will either swap nodes one and two, or swap nodes two and three.

*)

End == 666
Shrinking == 42
Null == 777

(* --algorithm algo {

variables
    key = [e \in 0..3 |-> e];
    ver = [e \in 0..3 |-> 0];
    next = [e \in 0..3 |-> IF e = 3 THEN End ELSE e + 1];

define {

    MyOperator == FALSE
    One == next[0]
    Two == next[One]
    Three == next[Two]

    Max(S) == CHOOSE i \in S : \A j \in S : j <= i
    MaxVer == Max({ver[e] : e \in DOMAIN ver})
    NotMaxVerExceeded == MaxVer < 4
}

procedure walk(k)
variables
    curr = 0;
    curr_ver = 0;
    child = Null;
    child_key = Null;
    child_ver = Null;
{
WalkIterStart:
    while (TRUE) {
ReadChild:
        child := next[curr];
CheckCurrVer:
        if (ver[curr] # curr_ver) {
Reset:
            curr := 0;
            curr_ver := 0;
            child := Null;
            child_key := Null;
            child_ver := Null;
        } else if (child = End) {
ReachedEnd:
            (*
            This is the failure condition.
            If the end is reached, the algorithm is wrong. This is because
            we only search for a key we know is present.
            *)
            assert FALSE;
        } else {
ReadChildKey:
            child_key := key[child];
CompareChildKey:
            if(child_key = k){
FoundCorrectKey:
                return;
            };
ReadChildVer:
            child_ver := ver[child];
CheckIfChildIsNotShrinkingAndStillChild:
            if(child = next[curr] /\ child_ver # Shrinking){
CheckCurrVerAgain:
                if(curr_ver = ver[curr]){
GoToChild:
                    curr := child;
                    curr_ver := child_ver;
                }
            }
        }
    }
}

process (order \in {"order"}){
OrderBegin:
    with (to_find \in 1..3){
        call walk(to_find);
    }
}

process (chaos \in {"chaos"})
variables
    one = Null;
    two = Null;
    three = Null;
    cached_ver = Null;
{
ChaosBegin:
    while(NotMaxVerExceeded){
        (*
        The chaotic process 'sees' the whole list because it represents
        a concurrent writer who can be anywhere.
        *) 
        one := One; \* Address of first (after HEAD) element in list
        two := Two; \* ..
        three := Three; \* ..
        either{
            skip;
        }or{
            \* Shrink 1
Shrink1:
            ver[one] := Shrinking || cached_ver := ver[one];
Swap1And2Part1:
            next[two] := one;
Swap1And2Part2:
            next[0] := two;
Swap1And2Part3:
            next[one] := three;
Incr1Ver:
            ver[one] := cached_ver + 1;
        }or{
            \* Shrink 2
Shrink2:
            ver[two] := Shrinking || cached_ver := ver[two];
Swap2And3Part1:
            next[three] := two;
Swap2And3Part2:
            next[one] := three;
Swap2And3Part3:
            next[two] := End ;
Incr2Ver:
            ver[two] := cached_ver + 1;
        }
    }
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "378f6350" /\ chksum(tla) = "ede4bceb")
\* END TRANSLATION 


\* Check the list maintains its shape (check that I didn't make a mistake writing the swaps)
Inv == 
    \* /\ next[Three] = End
    /\ TRUE
    /\ TRUE

=============================================================================
\* Modification History
\* Last modified Tue Apr 06 12:14:29 BST 2021 by dan
\* Created Tue Feb 02 11:29:57 GMT 2021 by dan
