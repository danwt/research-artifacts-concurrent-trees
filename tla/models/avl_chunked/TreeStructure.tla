------------------- MODULE TreeStructure -------------------

LOCAL INSTANCE Naturals 
LOCAL INSTANCE FiniteSets 
LOCAL INSTANCE TLC 
LOCAL INSTANCE Sequences


IsCycleFree(Null, left, rite, RootHolder) == 

    LET
        (*
        Takes pairs <<x,y>> and <<y,z>> to <<x,z>>    
        *)
        Closure(R, S) == 
        \* R**S ==
            LET
                T == {rs \in R \times S : rs[1][2] = rs[2][1]}
            IN {<<x[1][1], x[2][2]>> : x \in T}

        NodesOf(R) == { r[1] : r \in R } \union { r[2] : r \in R }

        (*
        Transitive closure, taken from Lamport's hyperbook, S 9.6.2

        Takes a set of relations. A set whose elements are of the from <<a, b>>
        meaning a |-> b.
        *)
        TransitiveClosure(R) ==

            LET 
                    
                RECURSIVE STC(_)
                (*
                (1 edge) u (2 edges) u (3 edges) u ...
                *)
                STC(n) == IF n=1 
                            THEN R
                            \* ELSE STC(n-1) \union STC(n-1)**R
                            ELSE STC(n-1) \union Closure(STC(n-1), R)

            \* By starting with n+1 then we include (full length) cycles
            IN IF R={} THEN {} ELSE STC(Cardinality(NodesOf(R))+1)
    

        FullTransitiveClosure == 
        
            LET 

                NonNullRelations(R) == { r \in R: r[2] # Null }
                
                Relations(f) == {<<x, f[x]>> : x \in DOMAIN f }
                
            IN TransitiveClosure(
                NonNullRelations(Relations(left)) \cup NonNullRelations(Relations(rite))
            )

        TransitiveClosureFromRootHolder == 
            \* TODO: Does this compute FullTransitiveClosure twice? Probably.
            {r \in FullTransitiveClosure : <<RootHolder, r[1]>> \in FullTransitiveClosure}

    IN \A r \in TransitiveClosureFromRootHolder : r[1] # r[2] \* There is no cycle


IsBalanced(Null, left, rite, RootHolder) == 
    (*
    This is horribly inefficient and should only be used for small graphs.
    Graphs with loops with likely cause an infinite recursion and a stack overflow exception.
    *)
    LET 

        MaxPlusOne(x, y) == IF y < x 
                            THEN x + 1 
                            ELSE y + 1
                            
        \* Avl balance
        Balanced(x, y) == ( y < x + 2 ) /\ ( x < y + 2 )

        \* Keep types the same to enable comparison
        ImbalancedSymbol == 777

        RECURSIVE TrueHeight(_)
        TrueHeight(e) == 
            IF e = Null 
                THEN 0 
                ELSE MaxPlusOne(TrueHeight(left[e]), TrueHeight(rite[e]))

        RECURSIVE TrueBalanced(_)
        TrueBalanced(e) ==
            IF e = Null
                THEN 0
                ELSE (
                    IF 
                        (
                        TrueBalanced(left[e]) = ImbalancedSymbol
                        \/
                        TrueBalanced(rite[e]) = ImbalancedSymbol
                        )
                    THEN ImbalancedSymbol
                    ELSE
                        (
                            IF
                            (
                                ~Balanced(TrueBalanced(left[e]), TrueBalanced(rite[e]))
                            )
                            THEN ImbalancedSymbol
                            ELSE TrueHeight(e)
                        )
                )

    IN TrueBalanced(rite[RootHolder]) # ImbalancedSymbol


=============================================================================
\* Modification History
