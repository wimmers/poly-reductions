\<^marker>\<open>creator Florian Kessler\<close>

theory Multiplication
  imports Big_Step_Small_Step_Equivalence "HOL-Library.Discrete"
    Canonical_State_Transformers "../Lib/Polynomial_Growth_Functions"
begin

unbundle no_com_syntax

(*
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
qed*)

record mul_state = mul_a::nat mul_b::nat mul_c::nat mul_d::nat

definition "mul_state_upd s \<equiv>
      let
        mul_d = (mul_b s) mod 2;
        mul_c = (if mul_d \<noteq> 0 then mul_c s + mul_a s else mul_c s);
        mul_a = mul_a s + mul_a s;
        mul_b = (mul_b s) div 2;
        ret = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = mul_c, mul_d = mul_d\<rparr>
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

lemma mul_imp_correct: "mul_c (mul_imp s) = mul_c s + mul_a s * mul_b s"
proof (induction s rule: mul_imp.induct)
  case (1 s)
  then show ?case
    apply(subst mul_imp.simps)
    apply (auto simp: mul_state_upd_def Let_def simp del: mul_imp.simps split: if_splits)
    by (metis (no_types, lifting) One_nat_def add.commute add_mult_distrib2 distrib_right mult.right_neutral mult_2 mult_div_mod_eq)
qed 

function mul_imp_time:: "mul_state \<Rightarrow> nat \<Rightarrow> nat" where
"mul_imp_time s t = 
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
          next_iteration = mul_imp_time (mul_state_upd s) t
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
  by  (relation "measure (\<lambda>(s, t). mul_b s)") (auto simp: mul_state_upd_def Let_def split: if_splits)

lemma mul_imp_time_acc: "(mul_imp_time s (Suc t)) = Suc (mul_imp_time s t)"
  by (induction s "t" arbitrary:  rule: mul_imp_time.induct)
     (auto simp add: mul_state_upd_def Let_def eval_nat_numeral split: if_splits)

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

definition mul_IMP_Minus_state_transformer where "mul_IMP_Minus_state_transformer p s \<equiv>
  state_transformer p  
    [(''a'', mul_a s),(''b'',  mul_b s),(''c'',  mul_c s),(''d'', mul_d s)]"

definition "mul_imp_to_HOL_state p s =
  \<lparr>mul_a = s (add_prefix p ''a''), mul_b = (s (add_prefix p ''b'')),
   mul_c = (s (add_prefix p ''c'')), mul_d =  (s (add_prefix p ''d''))\<rparr>"

lemma mul_IMP_minus_correct: 
  shows
   "(mul_IMP_minus p, s) 
    \<Rightarrow>\<^bsup>(mul_imp_time (mul_imp_to_HOL_state p s) 0)\<^esup> 
      mul_IMP_Minus_state_transformer p (mul_imp (mul_imp_to_HOL_state p s)) s"
proof(induction "mul_imp_to_HOL_state p s" arbitrary: s rule: mul_imp.induct)
  case 1
  then show ?case
    apply(subst mul_IMP_Minus_state_transformer_def)
    apply(subst mul_imp.simps)
    apply(subst mul_imp_time.simps)
    apply(subst Let_def)+
    apply(subst mul_IMP_minus_def)
    apply(rule WhileI[where y = "mul_imp_time (mul_state_upd (mul_imp_to_HOL_state p s)) 0"])
     apply(intro conjI)
       apply(rule Seq')
       apply(rule Seq')
         apply(rule Seq')
           apply(rule Big_StepT.Assign)
         apply(rule IfI)
                apply(rule Big_StepT.Assign)
                   apply(rule Big_StepT.Assign)
            apply rule
            apply rule
            apply(rule Big_StepT.Assign)
       apply(rule Big_StepT.Assign)
  apply(dest_com)
  apply(simp add: mul_imp_to_HOL_state_def)
         apply(simp add: mul_state_upd_def mul_imp_to_HOL_state_def)
        apply(auto simp add: Let_def mul_state_upd_def mul_imp_to_HOL_state_def
                   simp del: mul_imp.simps mul_imp_time.simps split: if_splits)[1]
        apply(auto simp add: Let_def mul_state_upd_def mul_imp_to_HOL_state_def
                   simp del: mul_imp.simps mul_imp_time.simps split: if_splits)[1]
    apply (simp add: mul_state_upd_def mul_IMP_Minus_state_transformer_def)
    apply (simp add: mul_state_upd_def mul_IMP_Minus_state_transformer_def)
    apply (simp add: mul_state_upd_def mul_IMP_Minus_state_transformer_def)
    apply (simp add: mul_IMP_minus_def)
        apply(auto simp add: Let_def mul_state_upd_def mul_imp_to_HOL_state_def state_transformer_def
                   simp del: mul_imp_time.simps split: if_splits)[1]
        apply(auto simp add: Let_def mul_state_upd_def mul_imp_to_HOL_state_def state_transformer_def
                   simp del: mul_imp_time.simps split: if_splits)[1]
    apply(subst mul_imp_time_acc)+
        apply(auto simp add: Let_def mul_state_upd_def mul_imp_to_HOL_state_def
                   simp del: mul_imp.simps mul_imp_time.simps split: if_splits)[1]
    apply(subst mul_imp_time_acc)+
        apply(auto simp add: Let_def mul_state_upd_def mul_imp_to_HOL_state_def
                   simp del: mul_imp.simps mul_imp_time.simps split: if_splits)[1]
    done
qed

lemma mul_IMP_minus_correct':
  shows
   "\<lbrakk>s_HOL = (mul_imp_to_HOL_state p s)\<rbrakk> \<Longrightarrow>
   (mul_IMP_minus p, s) 
    \<Rightarrow>\<^bsup>(mul_imp_time s_HOL 0)\<^esup> 
      mul_IMP_Minus_state_transformer p (mul_imp s_HOL) s"
  using mul_IMP_minus_correct
  by (auto simp del: mul_imp.simps)

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

definition mul_IMP_Minus_time :: "nat \<Rightarrow> nat" where "mul_IMP_Minus_time y 
  \<equiv> 12 * (if y = 0 then 0 else 1 + Discrete.log y) + 8"

definition exp2::"nat\<Rightarrow>nat"  where "exp2 y \<equiv> 2^y"

lemma log_exp_id: "Discrete.log  (exp2 x) = id x"
  apply(induct x)
  unfolding exp2_def by auto


lemma exp2_0: "exp2 x \<noteq> 0"
  unfolding exp2_def
  by auto

lemma poly_general_form:"poly (\<lambda>x. a*x+b)"
proof
  show "poly ((*) a)"
  proof (induct a)
    case 0
    then show ?case by auto
  next
    case (Suc a)
    have distrib_add: "((*) (Suc a)) = (\<lambda>x. (*) a x + x)" by auto
    from Suc have "poly (\<lambda>x. (*) a x)" by simp
    moreover have "poly (\<lambda>x. x)"  by (simp add: poly_linear)
    ultimately have "poly  (\<lambda>x. (*) a x + x)" by (simp add: poly_add)
    with distrib_add show ?case by simp 
  qed
next
  show "poly (\<lambda>x. b)" by simp
qed

lemma poly_intro: "(\<forall>x. f x = a*x + b) \<Longrightarrow> poly f"
proof -
  assume "\<forall>x. f x = a*x + b"
  hence "f = (\<lambda>x . a*x+b)" by auto
  with poly_general_form show "poly f" by auto
qed

lemma "poly (mul_IMP_Minus_time o exp2)"
  unfolding mul_IMP_Minus_time_def comp_def log_exp_id
  apply (auto simp add: exp2_0 )
  apply (rule poly_intro)
  by (auto simp add:algebra_simps)

definition polye:: "(nat \<Rightarrow>nat) \<Rightarrow> bool" where 
"polye f \<equiv> poly (f o exp2)"

lemma polye_comp1: 
"poly g \<Longrightarrow> polye f \<Longrightarrow> polye (g o f)"
  unfolding polye_def 
  by (simp add: comp_assoc poly_compose)

lemma polye_comp2: 
"mono f \<Longrightarrow> polye f \<Longrightarrow> polye (\<lambda>x . f (x + b))"
  unfolding polye_def  exp2_def comp_def
  oops

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