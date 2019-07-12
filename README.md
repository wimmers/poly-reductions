# Polynomial-Time Reductions in Isabelle/HOL
This repository sets out to formalize some classic results about NP-completeness in Isabelle/HOL.

## Index
### Polynomial-Time Reductions
So far we only formalize some classic reductions between NP-hard problems without proving
that they can be computed in polynomial time.
- `Three_Sat_To_Set_Cover.thy`: 3CNF-SAT <= Independent Set <= Vertex Cover <= Set Cover 
