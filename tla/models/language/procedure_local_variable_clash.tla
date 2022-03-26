------------------- MODULE procedure_local_variable_clash -------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences
CONSTANTS Procs

(*
NOTE: there is definitely some bizzare behavior to do with name clashes but I can't remember exactly what.
So this model maybe reveals something but I'm not sure what.

*)

(* --algorithm algo {

variables
    
procedure proc0()
    variables
        shared;
{
p10:
    shared := 0;
p11:
    assert shared = 0;
    return;
}

    
procedure proc1()
    variables
        shared;
{
p20:
    shared := 1;
p21:
    assert shared = 1;
    return;
}


process (proc \in Procs){
main0:
    while(TRUE){
        either{
            call proc0();
        } or {
            call proc1();
        }
    }
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "92dead2e" /\ chksum(tla) = "e07744e4")
\* END TRANSLATION 


=============================================================================
\* Modification History
\* Created Sat Mar 13 20:25:42 GMT 2021 by dan
