def list_Length : List (List (List Nat)) → Nat
| [] => 0
| head :: tail =>
  list_Length tail + 1

#eval list_Length [[[1,2],[1,3,2],[1,6,7,8,9]]]
#eval 1

abbrev c := [0,0,0,0,0,0,0,0]

abbrev out := [0,0,0,0,0,0,0,0]

abbrev outd := [0,0,0,0]

abbrev l := [0,1,2,3,4,5,6,7]

#eval c[2]

-- def counts : (A : List (List Nat)) → List Nat :=
--   (A.map (·.map (c[·] = c[·] + 1) )).map (out[·] = out[·] + 1)

-- def pairCounts : (A : List (List (List Nat))) → List Nat :=
--   A.map( (c[·[l.map(·)]][·[l.map(·+1)]]) = (c[·[l.map(·)]][·[l.map(·+1)]]) + 1 )

-- def countCounts : (A : List (List Nat)) → List Nat :=
--   l.map(out[(pairCounts A)[·][l.map(· + 1)]] )


--/--I am unsure how to tell it to return nothing if i is in L-/
-- def compl : (A : List Nat) → Nat :=
--   l.map (if !(list.mem · A) then i)
