import Matroids.Verification.Basic
import Matroids.Count

/- Lemma for count (related to Theorem 1):  If the input is an list of partial matroids
(order does matter, for both the lists and for the members) with range i < n and lenght = r, then
the output will be a list of natural numbers that counts the single ocurrences of lawful sparse
paving matroids-/

#eval count ([[0, 1], [0, 1], [1, 0], [0, 1, 3,2], [0, 1, 9], [0, 1], [0,2]]) /- Note, this is not
a list of partial matroids-/


/- Lemma for groupByValue (related to Theorem 1): If the input is an list of partial matroids
(order does matter, for both the lists and for the members) with range i < n and lenght = r, then
the output will be a list of lists of lawful sparse paving matroids -/
