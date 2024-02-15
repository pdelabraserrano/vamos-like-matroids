-- sum of a list
def sum : List Nat → Nat
  | [] => 0
  | head :: tail =>
    head + sum tail

#eval sum []
#eval sum [1, 7, 12]

-- max of a list
def max : List Nat → Nat
  | [] => 0
  | head :: tail =>
    let m := max tail
    if m > head then
      m
    else
      head

#eval max [12, 20, 200]

--length of a list
def length : List Nat → Nat
| [] => 0
| head :: tail =>
  length tail + 1


#eval length [1, 7, 3, 4, 5]
#eval length [1, 2, 3, 4, 5]
#eval length [123423, 25, 1334, 190, 35, 1, 0]

-- add 1 to every entry in a list
def addOne : List Nat → List Nat
  | [] => []
  | head :: tail =>
    (head + 1) :: addOne (tail)


example : 3 :: [] = [3] := rfl

#eval addOne [1, 7, 2] -- [2, 8, 3]

-- take every second entry from a list
def RemoveEveryOtherItem : List Nat → List Nat
  | [] => []
  | [x] => []
  | (x :: y :: z) => y :: RemoveEveryOtherItem z


#eval RemoveEveryOtherItem [1, 7, 3, 4, 5]

-- filter the even-valued entries (only) from a list
def removeOdds : List Nat → List Nat
  | [] => []
  | head :: tail =>
  let o := head % 2
  if o == 1 then removeOdds tail
  else head :: removeOdds tail

#eval removeOdds [1, 7, 3, 4, 5]
#eval removeOdds [123423, 25, 1334, 190, 35]

--check equality of two lists
def same : List Nat → List Nat → Bool
  | [], [] => true
  | [], h2 :: t2 => false
  | h1 :: t1, [] => false
  | h1 :: t1, h2 :: t2 => h1 - h2 = 0 && same t1 t2


#eval same [1, 2, 3] [1, 2, 3]

-- check if two ordered lists of the same length differ by at most one entry
-- This function is not complete. We need to figure out how to give each list one "free pass" (two total)
partial def NearlySameAux : List Nat → List Nat → (Bool × Bool)
  | [], [] => (true, false)
  | [], [h2] => (true, true)
  | [], h2 :: m2 :: t2 => (false, true)
  | [h1], [] => (true, true)
  | h1 :: m1 :: t1, [] => (false, true)
  | h1 :: t1, h2 :: t2 =>
    if h1 = h2 then
      NearlySameAux t1 t2
    else
      let (b, freePassUsed) :=
        if h1 < h2 then
          NearlySameAux t1 (h2 :: t2)
        else
          NearlySameAux (h1 :: t1) t2
      if freePassUsed == true then
        (false, true)
      else
        (b, true)

#eval NearlySameAux [] [] -- true
#eval NearlySameAux [] [1] -- true
#eval NearlySameAux [] [1, 2] -- true
#eval NearlySameAux [1, 2, 3] [1, 2, 3] -- true
#eval NearlySameAux [1, 2, 5] [1, 5] -- false
#eval NearlySameAux  [1, 5] [1, 2, 5] -- false

#eval NearlySameAux [1, 2, 5, 7, 9] [1, 2, 3, 5, 9] -- true
#eval NearlySameAux [1, 2, 5, 7, 9] [1, 2, 3, 7, 10] -- false

#eval NearlySameAux [1, 2, 3] [1, 4] -- can return whatever is convenient -- we don't care about the output on lists of different lengths
#eval NearlySameAux [1, 2, 3] [3, 2, 1] -- can return whatever is convenient -- we don't care about the output on non-ordered lists


-- insert a number in a list immediately before the first entry bigger than it
--intersperse two lists
--concatenate two lists
