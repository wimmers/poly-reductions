theory IMP_Minus_Common_Funs_Nat
  imports "../../IMP-/IMP_Minus_Nat_Bijection"
begin

subsection \<open>append\<close>

text\<open>Goal of this subsection is *append_tail*, which is defined in terms
  of reverse_nat and append_acc, both of which, in turn, are defined in
  terms of -- or can be related to -- *reverse_nat_acc*.\<close>

lemma "append_acc acc xs = reverse_nat_acc acc xs"
  by(induction xs arbitrary: acc rule: append_acc.induct) simp+

(*
  append_tail xs ys
= reverse_nat       (append_acc      (reverse_nat       xs) ys)
= reverse_nat       (reverse_nat_acc (reverse_nat       xs) ys)
= reverse_nat_acc 0 (reverse_nat_acc (reverse_nat_acc 0 xs) ys)
*)

(*
-- stop -- usage of function --
*)





subsection \<open>elemof\<close>

(* Registers:
  e: e
  f: list
  a: "result"
*)
definition elemof_IMP_Minus_iteration where "elemof_IMP_Minus_iteration \<equiv>
  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''a'' ::= ((V ''fst_nat'') \<ominus> (V ''e'')) ;;
  ''b'' ::= ((V ''e'') \<ominus> (V ''fst_nat'')) ;;
  ''a'' ::= ((V ''a'') \<oplus> (V ''b'')) ;;
  IF ''a''\<noteq>0 THEN
    ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
    IMP_Minus_snd_nat ;;

    ''f'' ::= (A (V ''snd_nat''))
  ELSE (
    ''a'' ::= (A (N 1));;
    ''f'' ::= (A (N 0))
  ) ;;
  zero_variables [''b'', ''c'', ''fst_nat'', ''snd_nat'']"
(*
WHILE 0/=l DO
  if hd_nat l = e then r = 1; BREAK
  else l = tl_nat l
*)

definition elemof_IMP_Minus_iteration_time where
"elemof_IMP_Minus_iteration_time e l \<equiv>
  2 + IMP_Minus_fst_nat_time (l - 1) + 2 + 2 + 2 +
  (if e = hd_nat l then  2 + 2 + 1
  else
    2 + IMP_Minus_fst_nat_time (l - 1) + 2 + 1
) +
  zero_variables_time [''b'', ''c'', ''fst_nat'', ''snd_nat'']"

end
