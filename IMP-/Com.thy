\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "IMP- A reduced imperative language"

theory Com  imports Main AExp begin

paragraph "Summary"
text\<open>Syntax definition for IMP-. Based on the syntax definition of IMP\<close>

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     vname com com     ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  vname com         ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)

end