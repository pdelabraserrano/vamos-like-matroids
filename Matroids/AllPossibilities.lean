import Matroids.PartialMatroid

namespace PartialMatroid

/-- all the partial matroids which can be obtained by adding one triangle to the
partial matroid A -/
def augmentations (A : PartialMatroid) : List PartialMatroid := A.remainingOptions.map  (augment · A)

#eval D1
#eval augmentations D1

def augmentationsTwo (A : PartialMatroid) : List (List PartialMatroid) :=
  (augmentations A).map augmentations

def augmentationsThree (A : PartialMatroid) : List (List (List PartialMatroid)) :=
   (augmentations A).map augmentationsTwo

def augmentationsFour (A : PartialMatroid) : List (List (List (List PartialMatroid))) :=
   (augmentations A).map augmentationsThree

def augmentationsFive (A : PartialMatroid) : List (List (List (List (List PartialMatroid)))) :=
   (augmentations A).map augmentationsFour

#eval augmentationsFive D1

#check List.concat

def augmentationsTwo' (A : PartialMatroid) : List PartialMatroid :=
  ((augmentations A).map augmentations).join


#eval augmentationsTwo' D1
