\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>
section "Arithmetic Expressions"

text \<open>
We define non-nested arithmetic expressions on natural numbers.
The defined operations are addition and modified subtraction. Based on the AExp theory of IMP.
\<close>

theory AExp imports Main begin

type_synonym vname = string
type_synonym val = nat
type_synonym state = "vname \<Rightarrow> val"

text "Defining atomic expressions:"
datatype atomExp = N val | V vname


fun atomVal :: "atomExp \<Rightarrow> state \<Rightarrow> val" where
"atomVal (V var) s = s var"|
"atomVal (N number) _ = number"

text "Defining arithmetic operators and general form of expressions: "
datatype aexp =  A atomExp | Plus atomExp atomExp | Sub atomExp atomExp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (A atomExp) s = atomVal atomExp s"|
"aval (Plus a b) s = atomVal a s  + atomVal b s"|
"aval (Sub a b) s = atomVal a s - atomVal b s"

text "evaluation examples:"
value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text "Syntactic sugar to write states:"     
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