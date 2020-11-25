\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "IMP- A reduced imperative language"

theory Com imports Main AExp begin

paragraph "Summary"
text\<open>Syntax definition for IMP-. Based on the syntax definition of IMP\<close>

datatype
  com = SKIP 
      | Assign vname aexp      
      | Seq    com  com         
      | If     vname com com     
      | While  vname com         

bundle com_syntax
begin
notation Assign ("_ ::= _" [1000, 61] 61) and
         Seq ("_;;/ _"  [60, 61] 60) and
         If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

bundle no_com_syntax
begin
no_notation Assign ("_ ::= _" [1000, 61] 61) and
            Seq ("_;;/ _"  [60, 61] 60) and
            If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
            While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

unbundle com_syntax

end