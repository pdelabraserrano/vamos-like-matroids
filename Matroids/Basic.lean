def sum : List Nat → Nat
  | [] => 0
  | head :: tail =>
    head + sum tail

def max : List Nat → Nat
  | [] => 0
  | head :: tail =>
    let m := max tail
    if m > head then
      m
    else
      head


def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n



def additional_triangles (m: Nat) : Nat :=
  (fac (m))/(3* fac 3 * fac (m-3))


new_list = []

def addOne : List Nat → List Nat
  | [] => []
  | head :: tail =>
    (head + 1) :: addOne (tail)


example : 3 :: [] = [3] := rfl




#eval parsing [1, 2, 3, 4, 5] --[2, 4]
#eval parsing [6, 4, 11] --[6, 11]

def parsing : List Nat → List Nat
  | [] => []
  | head :: tail =>
    [] :: head :: parsing (tail)


#eval parsing [1, 2, 3, 4, 5]

def RemoveEveryOtherItem : List Nat → List Nat
| [] => []
| [x] => []
| (x :: y :: z) => y :: RemoveEveryOtherItem z


#eval RemoveEveryOtherItem [1, 7, 3, 4, 5]

def removeOdds : List Nat → List Nat
  | [] => []
  | head :: tail =>
  let o := head % 2
  if o == 1 then removeOdds tail
  else head :: removeOdds tail

#eval removeOdds [1, 7, 3, 4, 5]
#eval removeOdds [1, 2, 3, 4, 5]
#eval removeOdds [123423, 25, 1334, 190, 35]

def length : List Nat → Nat
| [] => 0
| head :: tail =>
  length tail + 1

#eval length [1, 7, 3, 4, 5]
#eval length [1, 2, 3, 4, 5]
#eval length [123423, 25, 1334, 190, 35, 1, 0]


def determineSame : List Nat → List Nat → Bool
  | [], [] => true
  | [], a2 :: l2 => false
  | a1 :: l1, [] => false
  | a1 :: l1, a2 :: l2 =>
   a1-a2=0 && determineSame l1 l2

#eval determineSame [1, 7, 3, 4, 5] [1, 7, 3, 4, 5]
