\<^marker>\<open>creator Florian Kessler\<close>

theory Multiplication
  imports Big_Step_Small_Step_Equivalence "HOL-Library.Discrete"
    Canonical_State_Transformers
begin

unbundle no_com_syntax

definition max_a_min_b_IMP_Minus where "max_a_min_b_IMP_Minus = 
  ''c'' ::= ((V ''a'') \<ominus> (V ''b'')) ;;
  IF ''c''\<noteq>0 
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

definition max_a_min_b_IMP_Minus_time where "max_a_min_b_IMP_Minus_time \<equiv> 11"

abbreviation max_a_min_b_IMP_Minus_state_transformer
  where "max_a_min_b_IMP_Minus_state_transformer p a b
    \<equiv> state_transformer p 
        [(''a'', max a b),
         (''b'', min a b),
         (''c'', 0)]"

lemma max_a_min_b_IMP_Minus_correct[intro]: 
  "(max_a_min_b_IMP_Minus p, s) \<Rightarrow>\<^bsup>max_a_min_b_IMP_Minus_time\<^esup> 
      max_a_min_b_IMP_Minus_state_transformer p (s (add_prefix p ''a''))
        (s (add_prefix p ''b'')) s" 
proof(cases "s (add_prefix p ''a'') \<le> s (add_prefix p ''b'')")
  case True
  then show ?thesis
    by(fastforce 
        simp: max_a_min_b_IMP_Minus_def numeral_eq_Suc
        max_a_min_b_IMP_Minus_time_def
        assign_t_simp
        intro!: terminates_in_time_state_intro[OF Seq[OF Big_StepT.Assign Big_StepT.IfFalse]])
next
  case False
  show ?thesis 
    unfolding max_a_min_b_IMP_Minus_def max_a_min_b_IMP_Minus_time_def
    using False
    by (fastforce intro!: terminates_in_time_state_intro[OF Seq'])+
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

lemma mul_iteration_effect:
  "(mul_iteration p, s) \<Rightarrow>\<^bsup>11\<^esup> state_transformer' p
                                 (\<lambda>s. 
                                  [(''a'', 2 * s ''a''),
                                   (''b'', s ''b'' div 2),
                                   (''c'', 
                                     (if s ''b'' mod 2 \<noteq> 0 
                                      then s ''c'' + s ''a''
                                      else s ''c'')),
                                   (''d'', 0)]) s"
    unfolding mul_iteration_def
    by (cases "s (add_prefix p ''b'') mod 2 \<noteq> 0")
       (fastforce intro!: terminates_in_time_state_intro[OF Seq'])+

lemma mul_loop_correct:
  assumes "s (add_prefix p ''b'') = k"
  shows "((WHILE ''b'' \<noteq>0 DO mul_iteration) p, s) 
    \<Rightarrow>\<^bsup>12 * (if s (add_prefix p ''b'') = 0 then 0 
             else 1 + Discrete.log (s (add_prefix p ''b''))) + 2\<^esup> 
    state_transformer' p
    (\<lambda>s. [(''a'', (s ''a'') * (2 :: nat)^(if s ''b'' = 0 then 0 else 1 + Discrete.log (s ''b''))),
          (''b'', 0),
          (''c'', s ''c'' + s ''a'' * s ''b''),
          (''d'', (if s ''b'' = 0 then s ''d'' else 0))]) s"
  using assms
proof(induction k arbitrary: s rule: less_induct )
  case (less x)
  thus ?case
  proof (cases x)
  next
    case (Suc nat)

    show ?thesis
      apply(rule terminates_in_time_state_intro[OF Big_StepT.WhileTrue[
              OF _ mul_iteration_effect less.IH[where ?y = "x div 2"]]])
      using \<open>x = Suc nat\<close> \<open>s (add_prefix p ''b'') = x\<close> log_rec 
           apply auto
        apply(auto 
          simp add: Euclidean_Division.div_eq_0_iff 
          intro!: HOL.ext)
       apply(presburger)
      using odd_two_times_div_two_nat[where ?n=nat] mult.commute
      by (smt (z3) One_nat_def Suc_pred mult.assoc mult_Suc_right)
  qed (force intro: terminates_in_state_intro)
qed

definition mul_IMP_minus where "mul_IMP_minus =
  ''c'' ::= A (N 0) ;;
  WHILE ''b'' \<noteq>0 DO mul_iteration ;;
  ''a'' ::= A (N 0) ;;
  ''d'' ::= A (N 0)" 

definition mul_IMP_Minus_time where "mul_IMP_Minus_time y 
  \<equiv> 12 * (if y = 0 then 0 else 1 + Discrete.log y) + 8"

abbreviation mul_IMP_Minus_state_transformer where "mul_IMP_Minus_state_transformer p a b \<equiv>
  state_transformer p  
    [(''a'', 0),
     (''b'', 0),
     (''c'',  a * b),
     (''d'', 0)]" 

lemma IMP_minus_mul_correct[intro]: 
  shows "(mul_IMP_minus p, s) 
    \<Rightarrow>\<^bsup>mul_IMP_Minus_time (s (add_prefix p ''b''))\<^esup> 
      mul_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) (s (add_prefix p ''b'')) s"
  unfolding mul_IMP_Minus_time_def mul_IMP_minus_def
  by(fastforce
      intro!: terminates_in_time_state_intro[OF Seq']
      intro: mul_loop_correct)

fun zero_variables where
"zero_variables [] = SKIP" |
"zero_variables (a # as) = (a ::= (A (N 0)) ;; zero_variables as)"

definition zero_variables_time where "zero_variables_time vs \<equiv>
  1 + 2 * length vs"

lemma zero_variables_correct[intro]:
  "(zero_variables vs p, s) 
    \<Rightarrow>\<^bsup>zero_variables_time vs\<^esup> 
      state_transformer p (map (\<lambda>v. (v, 0)) vs) s"
proof (induction vs arbitrary: s)
  case (Cons a vs)
  show ?case
    by(auto 
        intro!: terminates_in_state_intro[OF Seq[OF Big_StepT.Assign Cons.IH]] 
        simp: zero_variables_time_def map_add_def
        split: option.splits
        dest!: map_of_SomeD)
qed (auto simp: zero_variables_time_def)

declare zero_variables.simps [simp del]
end