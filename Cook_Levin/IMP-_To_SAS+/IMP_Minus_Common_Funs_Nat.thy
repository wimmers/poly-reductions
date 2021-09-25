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

lemma elemof_IMP_Minus_iteration_correct:
  "(elemof_IMP_Minus_iteration, s)
    \<Rightarrow>\<^bsup>elemof_IMP_Minus_iteration_time (s ''e'') (s ''f'')\<^esup>
  s(''a'' := (if (s ''e'') = hd_nat (s ''f'') then 1 else 0),
    ''b'' := 0,
    ''c'' := 0,
    ''f'' := (if (s ''e'') = hd_nat (s ''f'') then 0 else (tl_nat (s ''f''))),
    ''fst_nat'' := 0,
    ''snd_nat'' := 0)"
proof(cases "hd_nat (s ''f'') = s ''e''")
  case True
  then have 1: "fst_nat (s ''f'' - Suc 0) - s ''e'' +
        (s ''e'' -
         fst_nat (s ''f'' - Suc 0)) = 0" 
    using hd_nat_def by auto

  show ?thesis
    unfolding elemof_IMP_Minus_iteration_def
        elemof_IMP_Minus_iteration_time_def
    apply(rule Seq')+
    apply(fastforce
        intro: terminates_in_time_state_intro[OF Big_StepT.Assign]
        )
    apply(fastforce
        intro: terminates_in_time_state_intro[OF IMP_Minus_fst_nat_correct]
        )
    apply(fastforce
        intro: terminates_in_time_state_intro[OF Big_StepT.Assign]
        )+
     apply(fastforce simp: True 1
        intro: terminates_in_time_state_intro[OF Big_StepT.IfFalse]
        )
    apply(fastforce simp add: True
        intro: terminates_in_time_state_intro[OF zero_variables_correct]
        )
    done
next
  case False
  then have 1: "fst_nat (s ''f'' - Suc 0) - s ''e'' +
        (s ''e'' -
         fst_nat (s ''f'' - Suc 0)) \<noteq> 0" 
    using hd_nat_def by auto
  then have 0: "(s(''c'' := 0, ''fst_nat'' := fst_nat (s ''f'' - Suc 0), ''b'' := s ''e'' - fst_nat (s ''f'' - Suc 0),
   ''a'' := fst_nat (s ''f'' - Suc 0) - s ''e'' + (s ''e'' - fst_nat (s ''f'' - Suc 0))))
 ''a'' \<noteq> 0" by simp

  have 2: "( ''a'' ::= (V ''f'' \<ominus> N 1);;
          IMP_Minus_snd_nat;;
          ''f'' ::= A (V ''snd_nat''),
    s(''c'' := 0,
      ''fst_nat'' := fst_nat (s ''f'' - Suc 0),
      ''b'' := s ''e'' - fst_nat (s ''f'' - Suc 0),
      ''a'' := fst_nat (s ''f'' - Suc 0) - s ''e'' +
              (s ''e'' - fst_nat (s ''f'' - Suc 0))
      )    )
     \<Rightarrow>\<^bsup> 2 + IMP_Minus_fst_nat_time (s ''f'' - 1) + 2 \<^esup>
      s(''a'' := 0, ''b'' := 0, ''c'' := 0,
        ''f'' := snd_nat (s ''f'' - Suc 0),
        ''fst_nat'' := fst_nat (s ''f'' - Suc 0),
        ''snd_nat'' := snd_nat (s ''f'' - 1))"
    by (auto simp: hd_nat_def
        intro!: terminates_in_time_state_intro[OF Seq']
      intro: IMP_Minus_snd_nat_correct)

  have 3: "2 + IMP_Minus_fst_nat_time (s ''f'' - 1) + 2 + 1 =
  (if s ''e'' = hd_nat (s ''f'') then 2 + 2 + 1
    else 2 + IMP_Minus_fst_nat_time (s ''f'' - 1) + 2 + 1
  )"
    using False by simp

  show ?thesis
    unfolding elemof_IMP_Minus_iteration_def
        elemof_IMP_Minus_iteration_time_def
    apply(rule Seq')+
    apply(fastforce
        intro: terminates_in_time_state_intro[OF Big_StepT.Assign]
        )
    apply(fastforce
        intro: terminates_in_time_state_intro[OF IMP_Minus_fst_nat_correct]
        )
    apply(fastforce
        intro: terminates_in_time_state_intro[OF Big_StepT.Assign]
        )+
     apply(fastforce simp add: False 1
        intro!: terminates_in_time_state_intro[OF Big_StepT.IfTrue ,
        of "s
   (''c'' := 0, ''fst_nat'' := fst_nat (s ''f'' - Suc 0), ''b'' := s ''e'' - fst_nat (s ''f'' - Suc 0),
    ''a'' := fst_nat (s ''f'' - Suc 0) - s ''e'' + (s ''e'' - fst_nat (s ''f'' - Suc 0)))"
        "''a''"
        "''a'' ::= (V ''f'' \<ominus> N 1);; IMP_Minus_snd_nat;; ''f'' ::= A (V ''snd_nat'')"
      , OF 0 2 3[symmetric]
        ])
    using False
    apply simp
    apply(fastforce simp add: False tl_nat_def
        intro: terminates_in_time_state_intro[OF zero_variables_correct]
        )
    done
qed


definition elemof_IMP_Minus_loop where "elemof_IMP_Minus_loop \<equiv>
  (WHILE ''f'' \<noteq>0 DO elemof_IMP_Minus_iteration)"

end
