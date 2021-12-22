\<^marker>\<open>creator Florian Kessler, Mohammad Abdulaziz\<close>

theory Multiplication
  imports Big_Step_Small_Step_Equivalence "HOL-Library.Discrete"
    Canonical_State_Transformers "../Lib/Polynomial_Growth_Functions"
begin


(*unbundle no_com_syntax*)

(*definition max_a_min_b_IMP_Minus where "max_a_min_b_IMP_Minus =
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
qed*)

record mul_state = mul_a::nat mul_b::nat mul_c::nat

definition "mul_state_upd s \<equiv>
      let
        d = (mul_b s) mod 2;
        mul_c = (if d \<noteq> 0 then mul_c s + mul_a s else mul_c s);
        mul_a = mul_a s + mul_a s;
        mul_b = (mul_b s) div 2;
        ret = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = mul_c\<rparr>
      in
        ret
"

function mul_imp:: "mul_state \<Rightarrow> mul_state" where
"mul_imp s = 
  (if mul_b s \<noteq> 0 then \<comment> \<open>While b \<noteq> 0\<close>
    (
      let
        next_iteration = mul_imp (mul_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination
  by  (relation "measure (\<lambda>s. mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

lemmas [simp del] = mul_imp.simps

lemma mul_imp_correct: "mul_c (mul_imp s) = mul_c s + mul_a s * mul_b s"
proof (induction s rule: mul_imp.induct)
  case (1 s)
  then show ?case
    apply(subst mul_imp.simps)
    apply (auto simp: mul_state_upd_def Let_def split: if_splits)
    by (metis (no_types, lifting) One_nat_def add.commute add_mult_distrib2 distrib_right mult.right_neutral mult_2 mult_div_mod_eq)
qed 

function mul_imp_time:: "nat \<Rightarrow> mul_state\<Rightarrow> nat" where
"mul_imp_time t s = 
(
    (if mul_b s \<noteq> 0 then \<comment> \<open>While b \<noteq> 0\<close>
      (
        let
          t = t + 1; \<comment> \<open>To account for while loop condition checking\<close>
          mul_d = (mul_b s) mod 2::nat;
          t = t + 2;
          mul_c = (if mul_d \<noteq> 0 then mul_c s + mul_a s else mul_c s);
          t = t + 1 + (if mul_d \<noteq> 0 then 2 else 2);
          mul_a = mul_a s + mul_a s;
          t = t + 2;
          mul_b = mul_b s div 2;
          t = t + 2;
          next_iteration = mul_imp_time t (mul_state_upd s)
        in
          next_iteration
      )
    else
      (
         \<comment> \<open>To account for the two steps of checking the condition and skipping the loop\<close>
        let
          t = t + 2;
          ret = t
        in
          ret
      )
    )
)"
  by pat_completeness auto
termination
  by  (relation "measure (\<lambda>(t, s). mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

lemmas [simp del] = mul_imp_time.simps

lemma mul_imp_time_acc: "(mul_imp_time (Suc t) s) = Suc (mul_imp_time t s)"
  by (induction t s arbitrary:  rule: mul_imp_time.induct)
     (auto simp add: mul_imp_time.simps mul_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition mul_IMP_minus where
"mul_IMP_minus \<equiv>
  (\<comment> \<open>if b \<noteq> 0 then\<close>
   WHILE ''b''\<noteq>0 DO
        \<comment> \<open>d = b mod 2;\<close>
        (''d'' ::= ((V ''b'') \<doteq>1);;
        \<comment> \<open>c = (if d \<noteq> 0 then c + a else c);\<close>
        IF ''d''\<noteq>0 THEN ''c'' ::= ((V ''c'') \<oplus> (V ''a'')) ELSE ''c'' ::= A (V ''c'');;
        \<comment> \<open>a = a + a;\<close>
        ''a'' ::= ((V ''a'') \<oplus> (V ''a''));;
        \<comment> \<open>b = b div 2;\<close>
        ''b'' ::= ((V ''b'') \<then>))
  )"

(*definition mul_IMP_Minus_state_transformer where "mul_IMP_Minus_state_transformer p s \<equiv>
  state_transformer p  
    [(''a'', mul_a s),(''b'',  mul_b s),(''c'',  mul_c s),(''d'', mul_d s)]"*)

definition "mul_imp_to_HOL_state p s =
  \<lparr>mul_a = s (add_prefix p ''a''), mul_b = (s (add_prefix p ''b'')),
   mul_c = (s (add_prefix p ''c''))\<rparr>"

lemma mul_imp_to_HOL_state_add_prefix: 
  "mul_imp_to_HOL_state (add_prefix p1 p2) s = mul_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (auto simp: mul_imp_to_HOL_state_def)

lemma mul_imp_to_HOL_state_add_prefix':
  "mul_imp_to_HOL_state (x # p2) s = mul_imp_to_HOL_state p2 (s o (add_prefix [x]))"
  by (auto simp: mul_imp_to_HOL_state_def)

lemma mul_IMP_minus_correct_time:
  "(invoke_subprogram p mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = (mul_imp_time 0 (mul_imp_to_HOL_state p s))"
  apply(induction "mul_imp_to_HOL_state p s" arbitrary: s s' t rule: mul_imp.induct)
  apply(simp only: mul_IMP_minus_def com_add_prefix.simps)
  apply(erule While_tE)
   apply(subst mul_imp_time.simps)
   apply(auto simp: mul_imp_time_acc mul_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst mul_imp_time.simps)
   apply(auto simp: mul_imp_time_acc mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  apply(subst mul_imp_time.simps)
  apply(auto simp: mul_imp_time_acc mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  done

lemma mul_IMP_minus_correct_function:
  "(invoke_subprogram p mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> s' (add_prefix p ''c'') = mul_c (mul_imp (mul_imp_to_HOL_state p s))"
  apply(induction "mul_imp_to_HOL_state p s" arbitrary: s s' t rule: mul_imp.induct)
  apply(simp only: mul_IMP_minus_def com_add_prefix.simps)
  apply(erule While_tE)
   apply(subst mul_imp.simps)
   apply(auto simp: mul_imp_to_HOL_state_def)[1]
  apply(dest_com')
  apply(erule Seq_tE)+
  apply(erule If_tE)
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst mul_imp.simps mul_imp_time.simps)
   apply(auto simp: mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  apply(subst mul_imp.simps mul_imp_time.simps)
  apply(auto simp: mul_imp_to_HOL_state_def mul_state_upd_def)[1]
  done

lemma mul_IMP_minus_correct_effects:
  "(invoke_subprogram p mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> (vars \<inter> set (all_variables (invoke_subprogram p mul_IMP_minus)) = {} \<longrightarrow> (\<forall>v\<in>vars. s v = s' v))"
 by (auto intro: com_only_vars)

lemma mul_IMP_minus_correct':
  "\<lbrakk>(invoke_subprogram p mul_IMP_minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (mul_imp_time 0 (mul_imp_to_HOL_state p s));
      s' (add_prefix p ''c'') = mul_c (mul_imp (mul_imp_to_HOL_state p s));
      (vars \<inter> set (all_variables (invoke_subprogram p mul_IMP_minus)) = {} \<Longrightarrow> (\<forall>v\<in>vars. s v = s' v))\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using mul_IMP_minus_correct_time mul_IMP_minus_correct_function mul_IMP_minus_correct_effects
  by auto

end