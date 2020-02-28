# Polynomial-Time Reductions in Isabelle/HOL
This repository sets out to formalize some classic results about NP-completeness in Isabelle/HOL. 

## Index
### Polynomial-Time Reductions
So far we only formalize some classic reductions between NP-hard problems without proving
that they can be computed in polynomial time.
- `Three_Sat_To_Set_Cover.thy`: 3CNF-SAT <= Independent Set <= Vertex Cover <= Set Cover 
- `CNF_SAT_To_Clique.thy`: CNF-SAT <= Clique
- `HC_To_UHC.thy`: Hamiltonian Cycle <= Undicrected Hamiltonian Cycle
- `VC_To_FNS.thy`: Vertex Cover <= Feedback Node Set
- `VC_To_HC.thy`: VC <= Hamiltonian Cycle

###Auxiliaries
- `VC_Set_To_VC_List.thy`: The representation of Vertex Cover using list makes the reduction from Vertex Cover to Hamiltonian Cycle easier. The rest of the repository uses the representation with sets.
- `List_Auxiliaries.thy` contains a definition of a sublist used to describe paths.
- `Graph_Auxiliaries.thy` and `Graph_Auxiliaries.thy` contain some basic lemmas used at different places.
- `Vwalk_Cycle.thy` contains a new definition of a cycle in a graph based on vwalk. The standard definition is based on awalk. 

## NREST

use https://github.com/maxhaslbeck/NREST
