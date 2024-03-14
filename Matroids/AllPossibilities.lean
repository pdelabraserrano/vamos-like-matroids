import Matroids.PartialMatroid

namespace PartialMatroid

/-- all the partial matroids which can be obtained by adding one triangle to the
partial matroid A -/
def augmentations (A : PartialMatroid) : List PartialMatroid := A.remainingOptions.map  (augment · A)

#eval D1
#eval augmentations D1

#check List.concat

def augmentationsTwo (A : PartialMatroid) : List PartialMatroid :=
  ((augmentations A).map augmentations).join

def augmentationsThree (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsTwo).join

def augmentationsFour (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsThree).join

def augmentationsFive (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsFour).join


#eval augmentationsTwo D1
#eval augmentationsThree D1
#eval augmentationsFour D1
#eval augmentationsFive D1

def augmentationsMany (n : Nat) (A : PartialMatroid) : List PartialMatroid :=
   sorry

def augmentationsFinal (A : PartialMatroid) : List PartialMatroid
   | h1::t1,[] => A.join
   | h2::t2,h3::t3 => (augmentations A).map augmentations
