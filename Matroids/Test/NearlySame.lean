import Matroids.NearlySame
import Std

/-- info: true -/
#guard_msgs in
#eval NearlySame [] []

/-- info: true -/
#guard_msgs in
#eval NearlySame [] [1]

/-- info: false -/
#guard_msgs in
#eval NearlySame [] [1, 2]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1, 2, 3] [1, 2, 3]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1, 2, 5] [1, 5]

/-- info: true -/
#guard_msgs in
#eval NearlySame  [1, 5] [1, 2, 5]

/-- info: true -/
#guard_msgs in
#eval NearlySame [1, 2, 5, 7, 9] [1, 2, 3, 5, 9] -- true

/-- info: false -/
#guard_msgs in
#eval NearlySame [1, 2, 5, 7, 9] [1, 2, 3, 7, 10] -- false

/-- info: true -/
#guard_msgs in
#eval NearlySame [1,2,3,5,7] [2,3,5,7,8] -- true
