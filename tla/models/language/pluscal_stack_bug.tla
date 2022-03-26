------------------- MODULE pluscal_stack_bug -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences
CONSTANT Procs

(*
I suspect there is a bug in the pluscal translation, it caused me a headache. This tries to replicate the problem.
https://github.com/tlaplus/tlaplus/issues/606
*)

(* --algorithm algo {

procedure fun0(){
fun00:
    skip;
    return;
}
    
procedure fun1(fun1_arg){
fun10:
    if(fun1_arg = 1){
        call fun0();
        return;
    };
fun11:
    assert fun1_arg = 0;
fun12:
    call fun1(1);
fun13:
    assert fun1_arg = 0;

    return;
}

procedure fun2(fun2_arg){
fun20:
    if(fun2_arg = 1){
        call fun0();
fun2AdditionalLabel:
        return;
    };
fun21:
    assert fun2_arg = 0;
fun22:
    call fun2(1);
fun23:
    assert fun2_arg = 0;

    return;
}

procedure fun3(fun3_arg){
fun30:
    if(fun3_arg = 1){
fun3AdditionalLabel:
        call fun0();
        return;
    };
fun31:
    assert fun3_arg = 0;
fun32:
    call fun3(1);
fun33:
    assert fun3_arg = 0;

    return;
}

process (proc \in Procs){
main0:

    \* Fails!
    \* call fun1(0);

    \* Fails!
    call fun3(0);

    \* Succeeds
    \* call fun2(0);
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "83c6ddab" /\ chksum(tla) = "c7a5862d")
\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Fri May 07 18:27:24 BST 2021 by dan
\* Created Tue Feb 02 11:29:57 GMT 2021 by dan
