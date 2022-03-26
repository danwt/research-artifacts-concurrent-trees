------------------- MODULE hello_world -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences
CONSTANT Procs

MyNum == 42

(* --algorithm algo {

variables
    values = {};

define {

    MyOperator == FALSE

}
    
procedure work(){
work0:
    skip;
work1:
    return;
}

process (proc \in Procs){
main0:
    call work();
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "eb27b70b" /\ chksum(tla) = "674ef643")
\* END TRANSLATION 

Invariant == 1 < 2


=============================================================================
\* Modification History
\* Last modified Tue Apr 06 12:14:29 BST 2021 by dan
\* Created Tue Feb 02 11:29:57 GMT 2021 by dan
