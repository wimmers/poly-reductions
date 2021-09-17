\<^marker>\<open>creator Florian Kessler\<close>

theory IMP_Minus_Nat_Bijection
  imports Multiplication "HOL-Library.Nat_Bijection" 
    "../Cook_Levin/IMP-_To_SAS+/IMP-_To_IMP--/Primitives"
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax

definition IMP_Minus_triangle where "IMP_Minus_triangle \<equiv>
  ''b'' ::= ((V ''a'') \<oplus> (N 1)) ;;
  IMP_minus_mul ;;
  ''triangle'' ::= ((V ''c'') \<then>) ;;
  ''c'' ::= (A (N 0))"

lemma IMP_Minus_triangle_correct: 
   "(IMP_Minus_triangle, s) 
      \<Rightarrow>\<^bsup>mul_time (1 + s ''a'') + 6\<^esup> 
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''triangle'' := triangle (s ''a''))"
  unfolding IMP_Minus_triangle_def triangle_def 
  by(force
      intro: terminates_in_state_intro[OF Seq[OF Seq]]
        IMP_minus_mul_correct)

definition IMP_Minus_prod_encode where "IMP_Minus_prod_encode \<equiv>
  ''prod_encode'' ::= (A (V ''a'')) ;;
  ''a'' ::= ((V ''a'') \<oplus> (V ''b'')) ;;
  IMP_Minus_triangle ;;
  ''prod_encode'' ::= ((V ''triangle'') \<oplus> (V ''prod_encode'')) ;;
  ''triangle'' ::= (A (N 0))"

definition IMP_Minus_prod_encode_time where "IMP_Minus_prod_encode_time x y \<equiv>
  mul_time (1 + x + y) + 14"

lemma IMP_Minus_prod_encode_correct: 
  "(IMP_Minus_prod_encode, s) 
      \<Rightarrow>\<^bsup>IMP_Minus_prod_encode_time (s ''a'') (s ''b'')\<^esup> 
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := prod_encode (s ''a'', s ''b''))"
  unfolding IMP_Minus_prod_encode_def prod_encode_def IMP_Minus_prod_encode_time_def
  by(force
      intro: terminates_in_state_intro[OF Seq[OF Seq]]
        IMP_Minus_triangle_correct)

fun prod_decode_aux_iterations :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "prod_decode_aux_iterations k m =
    (if m \<le> k then 0 else Suc (prod_decode_aux_iterations (Suc k) (m - Suc k)))"

declare prod_decode_aux_iterations.simps [simp del]

definition prod_decode_aux_iteration where "prod_decode_aux_iteration \<equiv>
  ''a'' ::= ((V ''a'') \<oplus> (N 1)) ;;
  ''b'' ::= ((V ''b'') \<ominus> (V ''a'')) ;;
  ''c'' ::= ((V ''b'') \<ominus> (V ''a''))"

lemma prod_decode_aux_loop_correct: 
  "s ''a'' = k \<Longrightarrow> s ''b'' = m \<Longrightarrow> s ''c'' = m - k 
  \<Longrightarrow> (WHILE ''c'' \<noteq>0 DO prod_decode_aux_iteration, s) 
      \<Rightarrow>\<^bsup>2 + 7 * prod_decode_aux_iterations (s ''a'') (s ''b'')\<^esup> 
    s(''a'' := fst (prod_decode_aux (s ''a'') (s ''b''))
         + snd (prod_decode_aux (s ''a'') (s ''b'')),
      ''b'' := fst (prod_decode_aux (s ''a'') (s ''b'')),
      ''c'' := 0)"
proof(induction k m arbitrary: s rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case
  proof(cases "m - k")
    case 0
    then show ?thesis
      using 1 terminates_in_state_intro[OF Big_StepT.WhileFalse]
      by(auto simp: fun_eq_iff prod_decode_aux.simps numeral_eq_Suc 
          prod_decode_aux_iterations.simps)
  next
    case (Suc nat)

    have first_iteration: "(prod_decode_aux_iteration, s) \<Rightarrow>\<^bsup> 6 \<^esup> 
      s(''a'' := Suc k,
        ''b'' := m - (Suc k),
        ''c'' := (m - (Suc k)) - Suc k)"
      unfolding prod_decode_aux_iteration_def
      using \<open>s ''a'' = k\<close>  \<open>s ''b'' = m\<close>
      by(auto 
          simp: numeral_eq_Suc fun_eq_iff 
          intro!: terminates_in_state_intro[OF Seq[OF Seq]])

    show ?thesis
      using terminates_in_state_intro[OF Big_StepT.WhileTrue[OF _ first_iteration "1.IH"]]
        prod_decode_aux_iterations.simps[where ?k = "s ''a''"]
        prod_decode_aux.simps[where ?k = "s ''a''"]
        \<open>s ''a'' = k\<close>  \<open>s ''b'' = m\<close> \<open>s ''c'' = m - k\<close> \<open>m - k = Suc nat\<close>
      by(auto simp: fun_eq_iff)
  qed
qed

definition IMP_Minus_fst_nat where "IMP_Minus_fst_nat \<equiv>
  ''b'' ::= (A (V ''a'')) ;; 
  ''a'' ::= (A (N 0)) ;;
  ''c'' ::= ((V ''b'') \<ominus> (V ''a'')) ;;
  WHILE ''c'' \<noteq>0 DO prod_decode_aux_iteration ;;
  ''fst_nat'' ::= (A (V ''b'')) ;;
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (N 0))"

definition IMP_Minus_fst_nat_time where "IMP_Minus_fst_nat_time x \<equiv>
  14 + 7 * prod_decode_aux_iterations 0 x"

lemma IMP_Minus_fst_nat_correct: 
  "(IMP_Minus_fst_nat, s) 
      \<Rightarrow>\<^bsup>IMP_Minus_fst_nat_time (s ''a'')\<^esup> 
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''fst_nat'' := fst_nat (s ''a''))"
  unfolding IMP_Minus_fst_nat_def fst_nat_def prod_decode_def IMP_Minus_fst_nat_time_def
  by (force intro!: 
      terminates_in_state_intro[OF Seq]
      prod_decode_aux_loop_correct)

definition IMP_Minus_snd_nat where "IMP_Minus_snd_nat \<equiv>
  ''b'' ::= (A (V ''a'')) ;; 
  ''a'' ::= (A (N 0)) ;;
  ''c'' ::= ((V ''b'') \<ominus> (V ''a'')) ;;
  WHILE ''c'' \<noteq>0 DO prod_decode_aux_iteration ;;
  ''snd_nat'' ::= ((V ''a'') \<ominus> (V ''b'')) ;;
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (N 0))"

lemma IMP_Minus_snd_nat_correct: 
  "(IMP_Minus_snd_nat, s) 
      \<Rightarrow>\<^bsup>IMP_Minus_fst_nat_time (s ''a'')\<^esup> 
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''snd_nat'' := snd_nat (s ''a''))"
  unfolding IMP_Minus_snd_nat_def snd_nat_def prod_decode_def IMP_Minus_fst_nat_time_def
  by (force intro!: 
      terminates_in_state_intro[OF Seq]
      prod_decode_aux_loop_correct)

definition nth_nat_iteration where "nth_nat_iteration \<equiv>
  ''a'' ::= ((V ''a'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  ''a'' ::= (A (V ''snd_nat'')) ;;
  ''snd_nat'' ::= (A (N 0)) ;;
  ''nth_nat'' ::= ((V ''nth_nat'') \<ominus> (N 1))"

fun nth_nat_loop_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_nat_loop_time 0 x = 2" |
"nth_nat_loop_time (Suc n) x = 9 + IMP_Minus_fst_nat_time (x - 1) 
  + nth_nat_loop_time n (tl_nat x)"

fun drop_n_nat :: "nat \<Rightarrow> nat\<Rightarrow> nat" where 
"drop_n_nat 0 x = x "|
"drop_n_nat (Suc n) x = drop_n_nat n (tl_nat x)"

lemma nth_nat_is_hd_of_drop_n_nat:
  "nth_nat n x = fst_nat (drop_n_nat n x - Suc 0)"
  by (induction n arbitrary: x)
    (auto simp: hd_nat_def)

lemma nth_nat_loop_correct:
  "s ''nth_nat'' = k
  \<Longrightarrow> (WHILE ''nth_nat'' \<noteq>0 DO nth_nat_iteration, s) 
      \<Rightarrow>\<^bsup>nth_nat_loop_time (s ''nth_nat'') (s ''a'') \<^esup>
      s(''a'' := drop_n_nat k (s ''a''),
        ''b'' := (if k > 0 then 0 else s ''b''),
        ''c'' := (if k > 0 then 0 else s ''c''),
        ''snd_nat'' := (if k > 0 then 0 else s ''snd_nat''),
        ''nth_nat'' := 0)"
proof(induction k arbitrary: s)
  case 0
  then show ?case
    by(auto simp: numeral_eq_Suc fun_eq_iff 
        intro!: terminates_in_state_intro[OF Big_StepT.WhileFalse])
next
  case (Suc k)

  have first_iteration: "(nth_nat_iteration, s)
    \<Rightarrow>\<^bsup> 8 + IMP_Minus_fst_nat_time ((s ''a'') - 1) \<^esup>
      s(''a'' := tl_nat (s ''a''),
        ''b'' := 0,
        ''c'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := k)"
    unfolding nth_nat_iteration_def tl_nat_def
    using \<open>s ''nth_nat'' = Suc k\<close>
    by(force intro!: terminates_in_state_intro[OF Seq]
        IMP_Minus_snd_nat_correct)

  show ?case
    using \<open>s ''nth_nat'' = Suc k\<close>
    by (force intro!: terminates_in_state_intro
          [OF Big_StepT.WhileTrue[OF _ first_iteration Suc.IH]])
qed


definition nth_nat_IMP_Minus where "nth_nat_IMP_Minus \<equiv>
  ''nth_nat'' ::= (A (V ''a'')) ;;
  ''a'' ::= (A (V ''b'')) ;;
  WHILE ''nth_nat'' \<noteq>0 DO nth_nat_iteration ;;
  ''snd_nat'' ::= (A (N 0)) ;;
  ''a'' ::= ((V ''a'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''nth_nat'' ::= (A (V ''fst_nat'')) ;;
  ''fst_nat'' ::= (A (N 0))"

definition nth_nat_IMP_Minus_time where "nth_nat_IMP_Minus_time n x \<equiv>
  12 + nth_nat_loop_time n x + IMP_Minus_fst_nat_time ((drop_n_nat n x) - 1)"

lemma nth_nat_IMP_Minus_correct:
  "(nth_nat_IMP_Minus, s) \<Rightarrow>\<^bsup>nth_nat_IMP_Minus_time (s ''a'') (s ''b'') \<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0,
      ''nth_nat'' := nth_nat (s ''a'') (s ''b''))"
  apply(cases "s ''a'' = 0")
  unfolding nth_nat_IMP_Minus_def nth_nat_IMP_Minus_time_def tl_nat_def 
  by (fastforce simp: hd_nat_def nth_nat_is_hd_of_drop_n_nat
            intro!: terminates_in_state_intro[OF Seq] 
              IMP_Minus_fst_nat_correct nth_nat_loop_correct)+

definition cons_IMP_Minus :: "atomExp \<Rightarrow> atomExp \<Rightarrow> Com.com" 
  where "cons_IMP_Minus h t \<equiv> 
    ''a'' ::= (A h) ;;
    ''b'' ::= (A t) ;;
    IMP_Minus_prod_encode ;;
    ''cons'' ::= ((V ''prod_encode'') \<oplus> (N 1)) ;;
    ''prod_encode'' ::= (A (N 0))"

definition cons_IMP_Minus_time where "cons_IMP_Minus_time h t \<equiv>
  8 + IMP_Minus_prod_encode_time h t"

lemma cons_IMP_Minus_correct:
  "t \<noteq> (V ''a'') \<Longrightarrow>
    (cons_IMP_Minus h t, s) \<Rightarrow>\<^bsup>cons_IMP_Minus_time (atomVal h s) (atomVal t s)\<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''d'' := 0,
      ''triangle'' := 0,
      ''prod_encode'' := 0,
      ''cons'' := (atomVal h s) ## (atomVal t s))"
  unfolding cons_IMP_Minus_def cons_IMP_Minus_time_def cons_def
  by (cases t) (fastforce intro!: terminates_in_state_intro[OF Seq] IMP_Minus_prod_encode_correct)+

fun cons_list_IMP_Minus :: "atomExp list \<Rightarrow> Com.com" where
"cons_list_IMP_Minus [] = Com.SKIP" |
"cons_list_IMP_Minus (a # as) = (if as = [] 
  then 
    ''cons'' ::= (A a) ;;
    ''a'' ::= (A (N 0)) ;;
    ''b'' ::= (A (N 0)) ;;
    ''c'' ::= (A (N 0)) ;;
    ''d'' ::= (A (N 0)) ;;
    ''triangle'' ::= (A (N 0)) ;;
    ''prod_encode'' ::= (A (N 0))
  else
    cons_list_IMP_Minus as ;;
    cons_IMP_Minus a (V ''cons''))"

fun cons_list :: "nat list \<Rightarrow> nat" where
"cons_list [] = 0" |
"cons_list (a # as) = 
  (if as = [] 
   then a
   else a ## cons_list as)"

fun cons_list_IMP_Minus_time :: "nat list \<Rightarrow> nat" where
"cons_list_IMP_Minus_time [] = 1" | 
"cons_list_IMP_Minus_time (a # as) = 
  (if as = [] 
   then 14
   else cons_list_IMP_Minus_time as + cons_IMP_Minus_time a (cons_list as))"

lemma cons_list_IMP_Minus_correct:
  "as \<noteq> [] 
    \<Longrightarrow> (\<forall>i \<in> set as. i \<notin> V ` { ''cons'', ''a'', ''b'', ''c'', ''d'', ''triangle'', ''prod_encode''}) 
    \<Longrightarrow> (cons_list_IMP_Minus as, s) \<Rightarrow>\<^bsup>cons_list_IMP_Minus_time (map (\<lambda>i. atomVal i s) as)\<^esup>
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''cons'' := cons_list (map (\<lambda>i. atomVal i s) as))"
proof(induction as arbitrary: s)
  case (Cons a as)
  then show ?case
  proof (cases as)
    case Nil
    then show ?thesis
      by (fastforce intro!: terminates_in_time_state_intro[OF Seq'])
  next
    case (Cons b bs)

    hence "as \<noteq> []" by simp
    have *: "(\<forall>i \<in> set as. i \<notin> V ` { ''cons'', ''a'', ''b'', ''c'', ''d'',
       ''triangle'', ''prod_encode''})"
      using \<open>\<forall>i\<in>set (a # as). i \<notin> V ` {''cons'', ''a'', ''b'', ''c'', ''d'', ''triangle'',
             ''prod_encode''}\<close>
      by simp

    show ?thesis
      apply(cases a; rule terminates_in_state_intro)
      using \<open>as \<noteq> []\<close> 
        \<open>\<forall>i\<in>set (a # as). i \<notin> V ` {''cons'', ''a'', ''b'', ''c'', ''d'', ''triangle'',
           ''prod_encode''}\<close> 
      by(fastforce intro!: Cons.IH[OF _ *] cons_IMP_Minus_correct)+
  qed
qed auto

declare cons_list_IMP_Minus.simps [simp del]
declare cons_list_IMP_Minus_time.simps [simp del]

fun zero_variables :: "vname list \<Rightarrow> Com.com" where
"zero_variables [] = Com.SKIP" |
"zero_variables (a # as) = (a ::= (A (N 0)) ;; zero_variables as)"

definition zero_variables_time where "zero_variables_time vs \<equiv>
  1 + 2 * length vs"

lemma zero_variables_correct:
  "(zero_variables vs, s) 
    \<Rightarrow>\<^bsup>zero_variables_time vs\<^esup> (\<lambda>v. (if v \<in> set vs then 0 else s v))"
proof (induction vs arbitrary: s)
  case (Cons a vs)
  show ?case
    by(fastforce 
        intro: terminates_in_state_intro[OF Seq[OF Big_StepT.Assign Cons.IH]] 
        simp: zero_variables_time_def)
qed (auto simp: zero_variables_time_def)

declare zero_variables.simps [simp del]

(*"reverse_nat_acc acc e  n f =
  (if n = 0 then acc 
   else reverse_nat_acc ((hd_nat n) ## acc) (tl_nat n) )"*)

definition reverse_nat_acc_IMP_Minus_iteration where "reverse_nat_acc_IMP_Minus_iteration \<equiv>
  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  
  cons_IMP_Minus (V ''fst_nat'') (V ''e'') ;;

  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  
  ''e'' ::= (A (V ''cons'')) ;;
  ''f'' ::= (A (V ''snd_nat'')) ;;

  zero_variables [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'']"

definition reverse_nat_acc_IMP_Minus_iteration_time where 
  "reverse_nat_acc_IMP_Minus_iteration_time acc n \<equiv>
    8 + IMP_Minus_fst_nat_time (n - 1) + cons_IMP_Minus_time (hd_nat n) acc
    + IMP_Minus_fst_nat_time (n - 1)
    + zero_variables_time [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'']"

(*"reverse_nat_acc acc e  n f =
  (if n = 0 then acc 
   else reverse_nat_acc ((hd_nat n) ## acc) (tl_nat n) )"*)

lemma reverse_nat_acc_IMP_Minus_iteration_correct: 
  "(reverse_nat_acc_IMP_Minus_iteration, s) 
    \<Rightarrow>\<^bsup>reverse_nat_acc_IMP_Minus_iteration_time (s ''e'') (s ''f'')\<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''d'' := 0,
      ''e'' := ((hd_nat (s ''f'')) ## (s ''e'')),
      ''f'' := (tl_nat (s ''f'')),
      ''triangle'' := 0,
      ''prod_encode'' := 0,
      ''cons'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0)"
  unfolding reverse_nat_acc_IMP_Minus_iteration_def 
    reverse_nat_acc_IMP_Minus_iteration_time_def
  by(fastforce 
       simp: hd_nat_def tl_nat_def 
       intro!: terminates_in_time_state_intro[OF Seq']
       intro: IMP_Minus_fst_nat_correct IMP_Minus_snd_nat_correct zero_variables_correct
       cons_IMP_Minus_correct)

(* WHILE ''f'' \<noteq>0 DO reverse_nat_acc_IMP_Minus_loop_iteration *)

fun reverse_nat_acc_IMP_Minus_loop_time where 
"reverse_nat_acc_IMP_Minus_loop_time acc n = 
  (if n = 0 then 2 
   else 1 + reverse_nat_acc_IMP_Minus_iteration_time acc n + 
    reverse_nat_acc_IMP_Minus_loop_time ((hd_nat n) ## acc) (tl_nat n))"

lemma reverse_nat_acc_IMP_Minus_loop_correct[intro]: 
  "(WHILE ''f'' \<noteq>0 DO reverse_nat_acc_IMP_Minus_iteration, s) 
    \<Rightarrow>\<^bsup>reverse_nat_acc_IMP_Minus_loop_time (s ''e'') (s ''f'')\<^esup>
    (if s ''f'' \<noteq> 0 then
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := reverse_nat_acc (s ''e'') (s ''f''),
        ''f'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''cons'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0)
      else s)"
proof(induction "s ''e''" "s ''f''" arbitrary: s rule: reverse_nat_acc.induct)
  case 1
  then show ?case
  proof(cases "s ''f''")
    case 0
    then show ?thesis
      by (fastforce intro: terminates_in_time_state_intro[OF Big_StepT.WhileFalse])
  next
    case (Suc nat)
        
    then show ?thesis
      by(fastforce intro!: terminates_in_time_state_intro[OF
        Big_StepT.WhileTrue[OF _ reverse_nat_acc_IMP_Minus_iteration_correct 1(1)]])
  qed
qed

definition "reverse_nat_acc_IMP_Minus" where "reverse_nat_acc_IMP_Minus \<equiv>
  ''e'' ::= (A (V ''a'')) ;;
  ''f'' ::= (A (V ''b'')) ;;
  WHILE ''f'' \<noteq>0 DO reverse_nat_acc_IMP_Minus_iteration ;;
  ''reverse_nat_acc'' ::= (A (V ''e'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'', ''e'',
    ''triangle'', ''prod_encode'']"

definition reverse_nat_acc_IMP_Minus_time where "reverse_nat_acc_IMP_Minus_time acc n \<equiv>
  6 + reverse_nat_acc_IMP_Minus_loop_time acc n
  + zero_variables_time 
    [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'', ''e'',
      ''triangle'', ''prod_encode'']"

lemma reverse_nat_acc_IMP_Minus_correct:
  "(reverse_nat_acc_IMP_Minus, s) 
    \<Rightarrow>\<^bsup>reverse_nat_acc_IMP_Minus_time (s ''a'') (s ''b'')\<^esup>
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := 0,
        ''f'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''cons'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''reverse_nat_acc'' := reverse_nat_acc (s ''a'') (s ''b''))"
  unfolding reverse_nat_acc_IMP_Minus_def reverse_nat_acc_IMP_Minus_time_def
  apply(cases "s ''b''") 
  by(fastforce 
      intro!: HOL.ext terminates_in_time_state_intro[OF Seq'] 
      zero_variables_correct reverse_nat_acc_IMP_Minus_loop_correct
      intro:  reverse_nat_acc_IMP_Minus_loop_correct)+
  
end