
vamos = [[0,1,2,3],[0,1,4,5],[0,1,6,7],[2,3,4,5],[2,3,6,7]]

def pairCounts (Ls) :
  counts = []
  for i in range(8): 
    counts.append ([0] * 8)
  for L in Ls :
    for i in range(len(L)): 
      for j in range (i+1, len(L)): 
        counts [L[i]][L[j]] += 1
  return counts

def countCounts (Ls) : 
  pc = pairCounts (Ls)
  out = [0]*4
  for i in range(8):
    for j in range (i+1,8):
      out [pc[i][j]] += 1
  return out

def counts (Ls) :
  c = [0] * 8
  for L in Ls : 
    for x in L :
      c [x] += 1
  out = [0] * 8
  for x in c : 
    out [x] += 1
  return out


# The 39 matroids in the list. 
matroids = [[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 6], [1, 2, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 7], [0, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 7], [1, 2, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [1, 2, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 7], [1, 2, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],    
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [0, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 5, 7], [1, 2, 5, 7], [1, 3, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [1, 3, 4, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 7], [0, 3, 5, 6], [1, 2, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 7], [1, 2, 5, 6], [1, 3, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 6], [1, 2, 5, 6], [1, 3, 4, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 3, 5, 7], [1, 2, 5, 7], [1, 3, 4, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 6], [0, 3, 5, 7], [1, 2, 4, 6], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [1, 2, 4, 6], [1, 2, 5, 7], [1, 3, 4, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [0, 3, 4, 6], [1, 3, 4, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 6], [0, 3, 4, 7], [1, 2, 4, 7], [1, 3, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 3, 4, 6], [0, 3, 5, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [1, 2, 5, 7], [1, 3, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 7], [0, 3, 4, 6], [1, 2, 4, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 3, 5, 6], [1, 2, 5, 6], [1, 3, 4, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [1, 3, 4, 6], [1, 3, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 5, 7], [1, 3, 4, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 7], [0, 3, 5, 6], [1, 2, 4, 6], [1, 2, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [0, 3, 4, 7], [1, 2, 4, 7], [1, 3, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [0, 3, 4, 6], [0, 3, 5, 7], [1, 2, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 3, 4, 6], [0, 3, 5, 7], [1, 2, 4, 6], [1, 2, 5, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 3, 4, 7], [0, 3, 5, 6], [1, 2, 5, 6], [1, 3, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 5, 7], [0, 3, 4, 6], [1, 2, 4, 6], [1, 3, 4, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 4, 6], [1, 3, 4, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [0, 3, 4, 7], [0, 3, 5, 6], [1, 2, 5, 6], [1, 3, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [0, 3, 4, 6], [0, 3, 5, 7], [1, 2, 4, 6], [1, 2, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [0, 3, 5, 6], [1, 2, 4, 7], [1, 3, 4, 6], [1, 3, 5, 7], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 6], [0, 2, 5, 7], [0, 3, 4, 7], [0, 3, 5, 6], [1, 2, 4, 7], [1, 2, 5, 6], [1, 3, 4, 6], [2, 3, 4, 5], [2, 3, 6, 7]],
[[0, 1, 2, 3], [0, 1, 4, 5], [0, 1, 6, 7], [0, 2, 4, 7], [0, 2, 5, 6], [0, 3, 4, 6], [0, 3, 5, 7], [1, 2, 4, 6], [1, 2, 5, 7], [1, 3, 4, 7], [1, 3, 5, 6], [2, 3, 4, 5], [2, 3, 6, 7]]]

print(len(matroids))

def compl (L) :
  return [i for i in range(8) if i not in L]

def inv (L) :
  return tuple (countCounts (L) + countCounts(map(compl, L)) + counts (L))

def inv_ (L) :
  return tuple (counts (L) + counts (map (compl, L))) 

def compl (L) :
  return [i for i in range(8) if i not in L]

invs = [inv (M) for M in matroids]

sinvs = sorted(invs)

for i in range (39) : 
  print (sinvs [i], (i < 38 and sinvs[i] == sinvs [i+1]))
