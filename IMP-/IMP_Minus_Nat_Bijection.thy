\<^marker>\<open>creator Florian Kessler\<close>

theory IMP_Minus_Nat_Bijection
  imports Multiplication "HOL-Library.Nat_Bijection" 
    "../Cook_Levin/IMP-_To_SAS+/IMP-_To_IMP--/Primitives"
begin

lemma xxx: "x \<noteq> y \<Longrightarrow> (s (x := aval a s)) y = s y"
  by auto

(*lemma AssignI'': 
  "\<exists>s'.((x ::= a, s) \<Rightarrow>\<^bsup> 2 \<^esup> s' \<and> (s' = s (x := aval a s)))"
  by (auto simp add: Assign eval_nat_numeral)
*)

unbundle IMP_Minus_Minus_Com.no_com_syntax

unbundle Com.no_com_syntax

record triangle_state = triangle_mul_state::mul_state triangle_a::nat triangle_triangle::nat

term Nat_Bijection.triangle

find_theorems Max_Constant.all_variables

(*definition triangle_IMP_Minus where "triangle_IMP_Minus \<equiv>
  [''a''] ''a'' ::= (A (V ''a'')) ;;
  [''a''] ''b'' ::= ((V ''a'') \<oplus> (N 1)) ;;
  invoke_subprogram ''a'' mul_IMP_minus ;;
  ''triangle'' ::= [''a''] ((V ''c'') \<then>) ;;
  ''a'' ::= (A (N 0))"
*)

definition "triangle_state_upd (s::triangle_state) \<equiv>
      let
        mul_a' = triangle_a s;
        mul_b' = (triangle_a s) + 1;
        mul_c' = 0;
        mul_d' = 0;
        (triangle_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c', mul_d = mul_d'\<rparr>;
        mul_ret = (mul_imp triangle_mul_state);
        triangle_triangle = (mul_c mul_ret) div 2;
        ret = \<lparr>triangle_mul_state = mul_ret, triangle_a = triangle_a s,triangle_triangle = triangle_triangle\<rparr>
      in
        ret
"

fun triangle_imp:: "triangle_state \<Rightarrow> triangle_state" where
"triangle_imp s = 
  (let
     ret = triangle_state_upd s
   in
     ret
  )"

lemmas [simp del] = triangle_imp.simps

lemma triangle_imp_correct: "triangle_triangle (triangle_imp s) = Nat_Bijection.triangle (triangle_a s)"
proof (induction s rule: triangle_imp.induct)
  case (1 s)
  then show ?case
    by (auto simp: triangle_imp.simps triangle_def triangle_state_upd_def Let_def mul_imp_correct split: if_splits)
qed 

fun triangle_imp_time:: "nat \<Rightarrow> triangle_state \<Rightarrow> nat" where
"triangle_imp_time t s = 
  (let
     mul_a' = triangle_a s;
     t = t + 2;
     mul_b' = (triangle_a s) + 1;
     t = t + 2;
     mul_c' = 0;
     t = t + 2;
     mul_d' = 0;
     t = t + 2;
     (triangle_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c', mul_d = mul_d'\<rparr>;
     mul_ret = (mul_imp triangle_mul_state);
     t = t + mul_imp_time 0 triangle_mul_state;
     triangle_triangle = mul_c mul_ret div 2;
     t = t + 2;
     triangle_a = triangle_a s;
     t = t + 2;
     ret = t
   in
     ret
  )"

lemmas [simp del] = triangle_imp_time.simps

lemma triangle_imp_time_acc: "(triangle_imp_time (Suc t) s) = Suc (triangle_imp_time t s)"
  by (induction t s rule: triangle_imp_time.induct)
     (auto simp add: triangle_imp_time.simps mul_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition triangle_IMP_minus where
"triangle_IMP_minus \<equiv>
  (
   \<comment> \<open>mul_a' = triangle_a s;\<close>
   [''mul''] ''a'' ::= (A (V ''a'')) ;;
   \<comment> \<open>mul_b' = (triangle_a s) + 1;\<close>
   [''mul''] ''b'' ::= ((V ''a'') \<oplus> (N 1));;
   \<comment> \<open>mul_c' = 0;\<close>
   [''mul''] ''c'' ::= (A (N 0)) ;;
   \<comment> \<open>mul_d' = 0;\<close>
   [''mul''] ''d'' ::= (A (N 0));;
   \<comment> \<open>(mul_state::mul_state) = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = 0, mul_d = 0\<rparr>;\<close>
   \<comment> \<open>mul_ret = (mul_imp mul_state);\<close>
   invoke_subprogram ''mul'' mul_IMP_minus;;
   \<comment> \<open>triangle_triangle = mul_c mul_ret div 2;\<close>
  ''triangle'' ::= [''mul''] ((V ''c'') \<then>);;
  ''a'' ::= A (V ''a'')
  )"


(*definition triangle_IMP_Minus_state_transformer where "triangle_IMP_Minus_state_transformer p s \<equiv>
 (state_transformer p [(''a'',  triangle_a s), (''triangle'',  triangle_triangle s)]) o
 (mul_IMP_Minus_state_transformer (''mul'' @ p) (triangle_mul_state s))"*)

definition "triangle_imp_to_HOL_state p s =
              \<lparr>triangle_mul_state = mul_imp_to_HOL_state (p @ ''mul'') s, 
               triangle_a = s (add_prefix p ''a''), triangle_triangle = (s (add_prefix p ''triangle''))\<rparr>"

lemma triangle_imp_to_HOL_state_add_prefix: 
  "triangle_imp_to_HOL_state (add_prefix p1 p2) s = triangle_imp_to_HOL_state p2 (s o (add_prefix p1))"
  by (auto simp only: triangle_imp_to_HOL_state_def append.assoc[symmetric] comp_def
                      mul_imp_to_HOL_state_add_prefix)

(*lemma rev_add_prefix_all_variables:
  "p1 \<noteq> [] \<Longrightarrow> (add_prefix p2 v \<notin> set (all_variables (invoke_subprogram p1 (c::pcom) p2)))"
  nitpick
  apply(induction p1 arbitrary: c p2)
  subgoal by auto
  subgoal apply auto


lemma rev_add_prefix_all_variables:"(add_prefix p v \<in> set (all_variables (invoke_subprogram p1 c p2)))
       = (rev (add_prefix p v) \<in> set (map rev (all_variables (invoke_subprogram p1 c p2))))"
  by auto
*)

lemma cons_append: "xs \<noteq> [] \<Longrightarrow> x # xs = [x] @ xs"
  by simp

lemma triangle_IMP_Minus_correct_function: 
  "(triangle_IMP_minus p, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p ''triangle'') = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state p s))"
  apply(simp only: triangle_IMP_minus_def triangle_imp.simps)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(simp only: comp_def, erule mul_IMP_minus_correct'[where vars = "{''traingle''}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: triangle_state_upd_def Let_def triangle_imp_to_HOL_state_def)[1]
  apply(auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma triangle_IMP_Minus_correct_time: 
  "(triangle_IMP_minus p, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = triangle_imp_time 0 (triangle_imp_to_HOL_state p s)"
  apply(simp only: triangle_IMP_minus_def)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst triangle_imp_time.simps)
  apply(subst (asm) comp_def, erule mul_IMP_minus_correct'[where vars = "(set (all_variables (triangle_IMP_minus p))) - (set (all_variables (mul_IMP_minus p)))"])
  \<comment> \<open>Warning: in the following, I am unfolding mul_imp_to_HOL_state_def. With more experiments, it
      should become clear if this will cascade down multiple layers\<close>
  apply(simp add: triangle_imp_time_acc triangle_imp_to_HOL_state_def triangle_state_upd_def)[1]
  apply (auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma triangle_IMP_Minus_correct_effects:
  "(triangle_IMP_minus p, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> (vars \<inter> set (all_variables (triangle_IMP_minus p)) = {} \<longrightarrow> (\<forall>v\<in>vars. s v = s' v))"
  by (auto intro: com_only_vars)

lemma triangle_IMP_minus_correct':
  "\<lbrakk>(triangle_IMP_minus p, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state p s));
      s' (add_prefix p ''triangle'') = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state p s));
      (vars \<inter> set (all_variables (triangle_IMP_minus p)) = {} \<Longrightarrow> (\<forall>v\<in>vars. s v = s' v))\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
        triangle_IMP_Minus_correct_effects
  by auto

end