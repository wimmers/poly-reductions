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
    apply(fastforce simp add: tl_nat_def
        intro: terminates_in_time_state_intro[OF zero_variables_correct]
        )
    done
qed


definition elemof_IMP_Minus_loop where "elemof_IMP_Minus_loop \<equiv>
  (WHILE ''f'' \<noteq>0 DO elemof_IMP_Minus_iteration)"

fun elemof_IMP_Minus_loop_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "elemof_IMP_Minus_loop_time e 0 = 2"
| "elemof_IMP_Minus_loop_time e l = 1 + elemof_IMP_Minus_iteration_time e l
 + elemof_IMP_Minus_loop_time e (if e = hd_nat l then 0 else (tl_nat l))"


lemma elemof_IMP_Minus_loop_correct:
  assumes "s ''a'' = 0" "s ''b'' = 0" "s ''c'' = 0" "s ''fst_nat'' = 0" "s ''snd_nat'' = 0"
    shows
  "(elemof_IMP_Minus_loop, s)
    \<Rightarrow>\<^bsup>elemof_IMP_Minus_loop_time (s ''e'') (s ''f'')\<^esup>
  s(''a'' := elemof (s ''e'') (s ''f''),
    ''b'' := 0,
    ''c'' := 0,
    ''f'' := 0,
    ''fst_nat'' := 0,
    ''snd_nat'' := 0 )"
using assms
proof(induction "s ''e''" "s ''f''" arbitrary: s rule: elemof.induct)
  case 1
  then show ?case
  proof(cases "s ''f''")
    case 0
    then have "elemof (s ''e'') (s ''f'') = 0" by simp
    then have a1: "s =
s(''a'' := elemof (s ''e'') (s ''f''), ''b'' := 0, ''c'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0)"
      using 0 1 by auto

    from 0 have a2: "Suc (Suc 0) = elemof_IMP_Minus_loop_time (s ''e'') (s ''f'')"
      by simp

    show ?thesis
      unfolding elemof_IMP_Minus_loop_def
      using
       terminates_in_time_state_intro[OF Big_StepT.WhileFalse a2,
  of s "''f''", OF 0,
of "s(''a'' := elemof (s ''e'') (s ''f''), ''b'' := 0, ''c'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0)"
elemof_IMP_Minus_iteration, OF a1
] by simp

  next
    case (Suc nat)
    then have b1: "s ''f'' \<noteq> 0" by simp
    show ?thesis
    proof(cases "hd_nat (s ''f'') = s ''e''")
      case True
      then show ?thesis unfolding elemof_IMP_Minus_loop_def
        using Suc
          terminates_in_time_state_intro[OF Big_StepT.WhileTrue[of s], OF b1
elemof_IMP_Minus_iteration_correct Big_StepT.WhileFalse ]
        by simp
    next
      case False
      let ?s1 = "(s ( ''a'' := if s ''e'' = hd_nat (s ''f'') then 1 else 0,
                      ''b'' := 0, ''c'' := 0,
                      ''f'' := if s ''e'' = hd_nat (s ''f'') then 0 else tl_nat (s ''f''),
                      ''fst_nat'' := 0, ''snd_nat'' := 0))"

      have ih: "(WHILE ''f''\<noteq>0 DO elemof_IMP_Minus_iteration, ?s1)
        \<Rightarrow>\<^bsup> elemof_IMP_Minus_loop_time (?s1 ''e'') (?s1 ''f'') \<^esup>
  ?s1(''a'' := elemof (?s1 ''e'') (?s1 ''f''), ''b'' := 0, ''c'' := 0, ''f'' := 0,
  ''fst_nat'' := 0, ''snd_nat'' := 0)" using 1(1)[OF b1 False, of ?s1] False
        unfolding elemof_IMP_Minus_loop_def by simp

      have iht: " elemof_IMP_Minus_loop_time (s ''e'') (s ''f'') = 
 1 + elemof_IMP_Minus_iteration_time (s ''e'') (s ''f'')
 + elemof_IMP_Minus_loop_time (?s1 ''e'') (?s1 ''f'')"
        using Suc
        by simp

      from False b1 have "elemof (s ''e'') (tl_nat (s ''f'')) = elemof (s ''e'') (s ''f'')" by simp

      then have "s(
          ''a'' := if s ''e'' = hd_nat (s ''f'') then 1 else 0, ''b'' := 0, ''c'' := 0,
          ''f'' := if s ''e'' = hd_nat (s ''f'') then 0 else tl_nat (s ''f''),
    ''fst_nat'' := 0, ''snd_nat'' := 0,
    ''a'' := elemof
       ((s(''a'' := if s ''e'' = hd_nat (s ''f'') then 1 else 0, ''b'' := 0, ''c'' := 0,
           ''f'' := if s ''e'' = hd_nat (s ''f'') then 0 else tl_nat (s ''f''), ''fst_nat'' := 0, ''snd_nat'' := 0))
         ''e'')
       ((s(''a'' := if s ''e'' = hd_nat (s ''f'') then 1 else 0, ''b'' := 0, ''c'' := 0,
           ''f'' := if s ''e'' = hd_nat (s ''f'') then 0 else tl_nat (s ''f''), ''fst_nat'' := 0, ''snd_nat'' := 0))
         ''f''),
    ''b'' := 0, ''c'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0)
= s(
    ''a'' := elemof (s ''e'') (s ''f''),
    ''b'' := 0, ''c'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0)" using False by simp


      then
      show ?thesis unfolding elemof_IMP_Minus_loop_def
        using
terminates_in_time_state_intro[OF Big_StepT.WhileTrue[of s], OF b1
elemof_IMP_Minus_iteration_correct ih iht[symmetric] refl
] by blast

    qed
  qed
qed



(* Registers:
  a: e
  b: l
*)
definition elemof_IMP_Minus where "elemof_IMP_Minus \<equiv>
  ''e'' ::= (A (V ''a'')) ;;
  ''f'' ::= (A (V ''b'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''fst_nat'', ''snd_nat''] ;;
  elemof_IMP_Minus_loop ;;
  ''elemof'' ::= (A (V ''a'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat'']"

definition elemof_IMP_Minus_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "elemof_IMP_Minus_time e l = 2 + 2
 + zero_variables_time [''a'', ''b'', ''c'', ''fst_nat'', ''snd_nat'']
 + elemof_IMP_Minus_loop_time e l + 2
 + zero_variables_time [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat'']
"

lemma elemof_IMP_Minus_correct:
  "(elemof_IMP_Minus, s)
    \<Rightarrow>\<^bsup>elemof_IMP_Minus_time (s ''a'') (s ''b'')\<^esup>
  s(''a'' := 0,
    ''b'' := 0,
    ''c'' := 0,
    ''e'' := 0,
    ''f'' := 0,
    ''fst_nat'' := 0,
    ''snd_nat'' := 0,
    ''elemof'' := elemof (s ''a'') (s ''b'')
  )"
  unfolding elemof_IMP_Minus_def elemof_IMP_Minus_time_def
  apply(rule Seq')+
       apply (fastforce intro: terminates_in_time_state_intro)
      apply (fastforce intro: terminates_in_time_state_intro)
  apply (fastforce intro: zero_variables_correct)
    apply (fastforce
        intro: terminates_in_time_state_intro[OF elemof_IMP_Minus_loop_correct]
        )
   apply(fastforce intro!: terminates_in_time_state_intro[OF Big_StepT.Assign])

proof-
  let ?s1 = "(\<lambda>v. if v = ''a'' \<or> v = ''b'' \<or> v = ''c'' \<or> v = ''fst_nat'' \<or> v = ''snd_nat'' then 0 else (s(''e'' := s ''a'', ''f'' := s ''b'')) v)
     (''a'' := if s ''b'' = 0 then 0 else if hd_nat (s ''b'') = s ''a'' then 1 else elemof (s ''a'') (tl_nat (s ''b'')), ''b'' := 0, ''c'' := 0,
      ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0,
      ''elemof'' :=
        if s ''b'' = 0 then 0
        else if hd_nat (s ''b'') = s ''a'' then 1
             else elemof (s ''a'') (tl_nat (s ''b'')))"

     let ?s2 = "
 s(''e'' := s ''a'',
''a'' := if s ''b'' = 0 then 0 else
if hd_nat (s ''b'') = s ''a'' then 1 else elemof (s ''a'') (tl_nat (s ''b'')),
''b'' := 0, ''c'' := 0,
      ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0,
      ''elemof'' := elemof (s ''a'') (s ''b''))
"

     have "(\<lambda>v. if v \<in> set [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat''] then 0
      else (?s1) v) =
(\<lambda>v. if v \<in> set [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat''] then 0
      else (?s2) v)
" by auto

     also have "\<dots> =
(\<lambda>v. (s(''e'' := 0,
''a'' := 0,
''b'' := 0, ''c'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0,
''elemof'' := elemof (s ''a'') (s ''b'')))
                v)
" by auto
     also have "\<dots> =
  (s(''e'' := 0,
''a'' := 0,
''b'' := 0, ''c'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0,
''elemof'' := elemof (s ''a'') (s ''b'')))
" by blast

     ultimately have c1: "(\<lambda>v. if v \<in> set [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat''] then 0
      else (?s1) v) = 
s(''e'' := 0, ''a'' := 0, ''b'' := 0, ''c'' := 0,  ''f'' := 0, ''fst_nat'' := 0,
''snd_nat'' := 0, ''elemof'' := elemof (s ''a'') (s ''b''))"
       by simp


     have "
s(''e'' := 0, ''a'' := 0, ''b'' := 0, ''c'' := 0,  ''f'' := 0, ''fst_nat'' := 0,
''snd_nat'' := 0)
=
s(''a'' := 0, ''b'' := 0, ''c'' := 0, ''e'' := 0, ''f'' := 0, ''fst_nat'' := 0,
''snd_nat'' := 0)
"  by auto

     then have c2: "s(''e'' := 0, ''a'' := 0, ''b'' := 0, ''c'' := 0,  ''f'' := 0, ''fst_nat'' := 0,
''snd_nat'' := 0, ''elemof'' := elemof (s ''a'') (s ''b''))
=
s(''a'' := 0, ''b'' := 0, ''c'' := 0, ''e'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0, ''elemof'' := elemof (s ''a'') (s ''b''))
" by simp

     from c1 c2 have d: "(\<lambda>v. if v \<in> set [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat''] then 0
      else (?s1) v) = 
s(''a'' := 0, ''b'' := 0, ''c'' := 0, ''e'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0, ''elemof'' := elemof (s ''a'') (s ''b''))
" by simp


     show "(zero_variables [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat''],
     ?s1) \<Rightarrow>\<^bsup> zero_variables_time [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat''] \<^esup> s
    (''a'' := 0, ''b'' := 0, ''c'' := 0, ''e'' := 0, ''f'' := 0, ''fst_nat'' := 0, ''snd_nat'' := 0, ''elemof'' := elemof (s ''a'') (s ''b''))"
       using  terminates_in_state_intro[OF zero_variables_correct,
of "[''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat'']"
?s1 "s
(''a'' := 0, ''b'' := 0, ''c'' := 0, ''e'' := 0, ''f'' := 0,
''fst_nat'' := 0, ''snd_nat'' := 0,
''elemof'' := elemof (s ''a'') (s ''b''))",
OF d] .

   qed


end
