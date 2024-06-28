-- practice: sum of a list
def sum : List Nat → Nat
  | [] => 0
  | head :: tail =>
    head + sum tail

#eval sum [] -- returns 0
#eval sum [1, 7, 12] -- returns 20

-- practice: max of a list
def max : List Nat → Nat
  | [] => 0
  | head :: tail =>
    let m := max tail
    if m > head then
      m
    else
      head

#eval max [12, 20, 200] -- returns 200

-- practice: length of a list
def length : List Nat → Nat
| [] => 0
| head :: tail =>
  length tail + 1


#eval length [1, 7, 3, 4, 5] -- returns 5
#eval length [1, 2, 3, 4, 5] -- returns 5
#eval length [123423, 25, 1334, 190, 35, 1, 0] -- returns 7


def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- practice: add 1 to every entry in a list
def addOne : List Nat → List Nat
  | [] => []
  | head :: tail =>
    (head + 1) :: addOne (tail)


example : 3 :: [] = [3] := rfl

#eval addOne [1, 7, 2] -- returns [2, 8, 3]

-- practice : take every second entry from a list
def RemoveEveryOtherItem : List Nat → List Nat
  | [] => []
  | [x] => []
  | (x :: y :: z) => y :: RemoveEveryOtherItem z


#eval RemoveEveryOtherItem [1, 7, 3, 4, 5] -- returns [7,4]

-- practice: filter the even-valued entries (only) from a list
def removeOdds : List Nat → List Nat
  | [] => []
  | head :: tail =>
  let o := head % 2
  if o == 1 then removeOdds tail
  else head :: removeOdds tail

#eval removeOdds [1, 7, 3, 4, 5] -- returns [4]
#eval removeOdds [123423, 25, 1334, 190, 35] -- returns [1334, 190]

--practice: check equality of two lists
def same : List Nat → List Nat → Bool
  | [], [] => true
  | [], h2 :: t2 => false
  | h1 :: t1, [] => false
  | h1 :: t1, h2 :: t2 => h1 - h2 = 0 && same t1 t2


#eval same [1, 2, 3] [1, 2, 3] -- returns true




def determineSame : List Nat → List Nat → Bool
  | [], [] => true
  | [], a2 :: l2 => false
  | a1 :: l1, [] => false
  | a1 :: l1, a2 :: l2 =>
   a1-a2=0 && determineSame l1 l2

#eval determineSame [1, 7, 3, 4, 5] [1, 7, 3, 4, 5]
