\<^marker>\<open>creator Florian Kessler\<close>

theory Multiplication
  imports Big_Step_Small_Step_Equivalence "HOL-Library.Discrete"
begin

definition IMP_Minus_max_a_min_b where "IMP_Minus_max_a_min_b = 
  ''c'' ::= ((V ''a'') \<ominus> (V ''b'')) ;;
  IF ''c'' \<noteq>0 
  THEN
    (SKIP ;; SKIP ;;
     SKIP ;; SKIP ;;
     SKIP ;; SKIP ;;
     ''c'' ::= A (N 0))
  ELSE
    (''c'' ::= A (V ''a'') ;;
    ''a'' ::= A (V ''b'') ;;
    ''b'' ::= A (V ''c'') ;;
    ''c'' ::= A (N 0))"

lemma IMP_Minus_max_a_min_b_correct: 
    "(IMP_Minus_max_a_min_b, s) \<Rightarrow>\<^bsup>11\<^esup> s(''a'' := max (s ''a'') (s ''b''),
                                   ''b'' := min (s ''a'') (s ''b''), ''c'' := 0)" 
proof(cases "(s ''a'') \<le> (s ''b'')")
  case True
  then show ?thesis
    apply(auto simp: IMP_Minus_max_a_min_b_def numeral_eq_Suc
        intro!: Seq[OF Big_StepT.Assign Big_StepT.IfFalse])
    by(auto simp: assign_t_simp fun_eq_iff intro!: Seq)
next
  case False
  then show ?thesis 
    apply(auto simp: IMP_Minus_max_a_min_b_def numeral_eq_Suc seq_assign_t_simp 
        intro!: Seq[OF Big_StepT.Assign Big_StepT.IfTrue])
    by (auto simp: fun_eq_iff)
qed

definition mul_iteration where
"mul_iteration = 
  ''d'' ::= ((V ''b'') \<doteq>1) ;;
  IF ''d'' \<noteq>0
  THEN 
    ''c'' ::= ((V ''c'') \<oplus> (V ''a''))
  ELSE
    (SKIP ;; SKIP) ;;
  ''a'' ::= ((V ''a'') \<oplus> (V ''a'')) ;;
  ''b'' ::= ((V ''b'') \<then>) ;;
  ''d'' ::= A (N 0)"

lemma terminates_in_state_intro: "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' = s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro: "(c, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' 
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t'\<^esup> s''"
  by simp

lemma mul_iteration_effect:
  "(mul_iteration, s) \<Rightarrow>\<^bsup>11\<^esup> s(''a'' := 2 * s ''a'',
                               ''b'' := s ''b'' div 2,
                               ''c'' := (if s ''b'' mod 2 \<noteq> 0 then s ''c'' + s ''a'' else s ''c''),
                               ''d'' := 0)"
proof (cases "s ''b'' mod 2 \<noteq> 0")
  case True
  then show ?thesis
    apply(simp only: mul_iteration_def)
    apply(rule terminates_in_state_intro)
    (* Why does it work only with intro? *)
    apply(force simp: fun_eq_iff numeral_eq_Suc
        intro: terminates_in_state_intro
        intro!: Big_StepT.IfTrue)
    by(auto simp: fun_eq_iff numeral_eq_Suc)
next
  case False
  then show ?thesis
  by(force simp: mul_iteration_def fun_eq_iff numeral_eq_Suc 
        intro: terminates_in_state_intro)
qed

lemma mul_iteration_invariant:
  assumes "s ''c'' + s ''a'' * s ''b'' = x * y" "(mul_iteration, s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''c'' + s' ''a'' * s' ''b'' = x * y"
proof -
  have "s' = s(''a'' := 2 * s ''a'',
               ''b'' := s ''b'' div 2,
               ''c'' := (if s ''b'' mod 2 \<noteq> 0 then s ''c'' + s ''a'' else s ''c''),
               ''d'' := 0)"
    using bigstep_det mul_iteration_effect \<open>(mul_iteration, s) \<Rightarrow>\<^bsup>t\<^esup> s'\<close>
    by blast
  thus ?thesis
    using \<open>s ''c'' + s ''a'' * s ''b'' = x * y\<close>[symmetric]
    apply(auto simp: algebra_simps)
    by (smt (z3) add_mult_distrib2 mod_mult_div_eq mult.assoc mult.commute mult_numeral_1 
        numeral_1_eq_Suc_0)
qed

lemma mul_loop_correct:
  assumes "s ''b'' = k"
  shows "(WHILE ''b'' \<noteq>0 DO mul_iteration, s) 
    \<Rightarrow>\<^bsup>12 * (if s ''b'' = 0 then 0 else 1 + Discrete.log (s ''b'')) + 2\<^esup> 
    s(''a'' := s ''a'' * (2 :: nat) ^(if s ''b'' = 0 then 0 else 1 + Discrete.log (s ''b'')),
      ''b'' := 0,
      ''c'' := s ''c'' + s ''a'' * s ''b'',
      ''d'' := (if s ''b'' = 0 then s ''d'' else 0))"
  using assms
proof(induction k arbitrary: s rule: less_induct )
  case (less x)
  thus ?case
  proof (cases x)
  next
    case (Suc nat)
    hence "s ''b'' \<noteq> 0" 
      using \<open>s ''b'' = x\<close> 
      by simp

    let ?s' = "s(''a'' := 2 * s ''a'',
                 ''b'' := s ''b'' div 2,
                 ''c'' := (if s ''b'' mod 2 \<noteq> 0 then s ''c'' + s ''a'' else s ''c''),
                 ''d'' := 0)"
    let ?s'' = "?s'(''a'' := ?s' ''a'' 
                      * (2 :: nat)^(if ?s' ''b'' = 0 then 0 else 1 + Discrete.log (?s' ''b'')),
                  ''b'' := 0,
                  ''c'' := ?s' ''c'' + ?s' ''a'' * ?s' ''b'',
                  ''d'' := (if ?s' ''b'' = 0 then ?s' ''d'' else 0))"

    have remaining_iterations: "(WHILE ''b'' \<noteq>0 DO mul_iteration, ?s') 
      \<Rightarrow>\<^bsup>12 * (if ?s' ''b'' = 0 then 0 else 1 + Discrete.log (?s' ''b'')) + 2\<^esup> ?s''"
      using \<open>x = Suc nat\<close> \<open>s ''b'' = x\<close> 
      by (fastforce intro!: less.IH[where ?y = "x div 2"])

    have s''_is_goal: "?s'' = 
    s(''a'' := s ''a'' * (2 :: nat) ^(if s ''b'' = 0 then 0 else 1 + Discrete.log (s ''b'')),
      ''b'' := 0,
      ''c'' := s ''c'' + s ''a'' * s ''b'',
      ''d'' := (if s ''b'' = 0 then s ''d'' else 0))"
      using \<open>x = Suc nat\<close> \<open>s ''b'' = x\<close> 
      apply(auto simp: fun_eq_iff)
        apply (metis Discrete.log.simps One_nat_def div_less log_half neq0_conv power_Suc)
       apply presburger
      by (smt (z3) One_nat_def add.commute add_left_cancel add_mult_distrib2 
          mult.commute mult_2 mult_Suc numeral_2_eq_2 odd_two_times_div_two_succ)

    show ?thesis
      using \<open>x = Suc nat\<close> \<open>s ''b'' = x\<close> \<open>s ''b'' \<noteq> 0\<close> log_rec s''_is_goal
      by (fastforce simp: Euclidean_Division.div_eq_0_iff
          intro!: Big_StepT.WhileTrue[
            OF _ mul_iteration_effect
            terminates_in_state_intro[OF remaining_iterations]])
  qed (force intro: terminates_in_state_intro)
qed

definition IMP_minus_mul where "IMP_minus_mul =
  ''c'' ::= A (N 0) ;;
  WHILE ''b'' \<noteq>0 DO mul_iteration ;;
  ''a'' ::= A (N 0) ;;
  ''d'' ::= A (N 0)" 

definition mul_time where "mul_time y 
  \<equiv> 12 * (if y = 0 then 0 else 1 + Discrete.log y) + 8"

lemma IMP_minus_mul_correct: 
  shows "(IMP_minus_mul, s) 
    \<Rightarrow>\<^bsup>mul_time (s ''b'')\<^esup> 
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := s ''a'' * s ''b'',
      ''d'' := 0)"
  unfolding mul_time_def
  using mul_loop_correct
  by(force simp: IMP_minus_mul_def
           intro!: terminates_in_state_intro[OF Seq[OF Seq[OF Seq]]])
end