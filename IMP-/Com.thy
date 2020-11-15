theory Com
  imports Main AExp
begin

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     vname com com     ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  vname com         ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)

end