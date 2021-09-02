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

lemma IMP_Minus_prod_encode_correct: 
  "(IMP_Minus_prod_encode, s) 
      \<Rightarrow>\<^bsup>mul_time (1 + s ''a'' + s ''b'') + 14\<^esup> 
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := prod_encode (s ''a'', s ''b''))"
  unfolding IMP_Minus_prod_encode_def prod_encode_def
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

end