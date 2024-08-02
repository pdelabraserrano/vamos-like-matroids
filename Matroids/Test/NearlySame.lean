import Matroids.NearlySame
import Std

/-- info: (true, false, false) -/
#guard_msgs in
#eval NearlySameAux [] []

/-- info: true -/
#guard_msgs in
#eval NearlySame [] []

/-- info: (true, false, true) -/
#guard_msgs in
#eval NearlySameAux [] [1]

/-- info: true -/
#guard_msgs in
#eval NearlySame [] [1]

/-- info: (false, false, true) -/
#guard_msgs in
#eval NearlySameAux [] [1, 2]

/-- info: false -/
#guard_msgs in
#eval NearlySame [] [1, 2]

/-- info: (true, false, false) -/
#guard_msgs in
#eval NearlySameAux [1, 2, 3] [1, 2, 3]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1, 2, 3] [1, 2, 3]

/-- info: (true, true, false) -/
#guard_msgs in
#eval NearlySameAux [1, 2, 5] [1, 5]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1, 2, 5] [1, 5]

/-- info: (true, false, true) -/
#guard_msgs in
#eval NearlySameAux [1, 5] [1, 2, 5]

/-- info: true -/
#guard_msgs in
#eval NearlySame  [1, 5] [1, 2, 5]

/-- info: (true, true, true) -/
#guard_msgs in
#eval NearlySameAux [1, 2, 5, 7, 9] [1, 2, 3, 5, 9]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1, 2, 5, 7, 9] [1, 2, 3, 5, 9] -- true

/-- info: (false, true, true) -/
#guard_msgs in
#eval NearlySameAux [1, 2, 5, 7, 9] [1, 2, 3, 7, 10]

/-- info: false -/
#guard_msgs in
#eval NearlySame [1, 2, 5, 7, 9] [1, 2, 3, 7, 10] -- false


/-- info: (true, true, true) -/
#guard_msgs in
#eval NearlySameAux [1,2,3,5,7] [2,3,5,7,8]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1,2,3,5,7] [2,3,5,7,8] -- true

/-- info: (false, true, true) -/
#guard_msgs in
#eval NearlySameAux [1, 2, 3] [1, 4]

#eval NearlySame [1, 2, 3] [1, 4] -- can return whatever is convenient -- we don't care about the output on lists of different lengths

/-- info: (false, true, true) -/
#guard_msgs in
#eval NearlySameAux [1, 2, 3] [3, 2, 1]

#eval NearlySame [1, 2, 3] [3, 2, 1] -- can return whatever is convenient -- we don't care about the output on non-ordered lists
