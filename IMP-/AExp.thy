theory AExp
  imports Main
begin

type_synonym vname = string
type_synonym val = nat
type_synonym state = "vname \<Rightarrow> val"

datatype atomExp = N val | V vname
datatype aexp =  A atomExp | Plus atomExp atomExp | Sub atomExp atomExp

fun atomVal :: "atomExp \<Rightarrow> state \<Rightarrow> val" where
"atomVal (V var) s = s var"|
"atomVal (N number) _ = number"
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (A atomExp) s = atomVal atomExp s"|
"aval (Plus a b) s = atomVal a s  + atomVal b s"|
"aval (Sub a b) s = atomVal a s - atomVal b s"

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text "how does it work?"     
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Sub (V ''x'') (N 5)) <''x'' := 7>"
value "aval (Sub (V ''x'') (N 10)) <''x'' := 7>"

end