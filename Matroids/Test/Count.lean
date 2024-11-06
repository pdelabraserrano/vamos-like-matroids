import Matroids.Count

#eval [0,1,3,0,2,5,1,2,3].sort

#eval countAux [0,0,1,1,2,2,2,3,4,5,5]
#eval countAux [1,1,1,1,1,3,3,3,3,5,5,7,7,8,9,9,9,9]

#eval count [0,0,1,1,2,2,2,3,4,5,5]
#eval count [0,0,1,1,2,0,2,3,4,5,5]

example : List ℤ × ℕ := ([-2, 0, 2, 3], 2)
example : ℕ × List ℤ := (2, [-2, 0, 2, 3])
example : List (ℤ × ℕ) := [(2, 3), (4, 6), (10, 24)]

#eval count ([[0, 1], [0, 1], [1, 0], [0, 1, 3,2], [0, 1, 9], [0, 1], [0,2]]) /- Note, this is not
a list of partial matroids-/
