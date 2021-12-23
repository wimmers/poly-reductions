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

(*unbundle IMP_Minus_Minus_Com.no_com_syntax

unbundle Com.no_com_syntax*)

record triangle_state = triangle_a::nat triangle_triangle::nat

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
        (triangle_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
        mul_ret = (mul_imp triangle_mul_state);
        triangle_triangle = (mul_c mul_ret) div 2;
        ret = \<lparr>triangle_a = triangle_a s,triangle_triangle = triangle_triangle\<rparr>
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
     (triangle_mul_state::mul_state) = \<lparr>mul_a = mul_a', mul_b = mul_b', mul_c = mul_c'\<rparr>;
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

definition triangle_IMP_Minus where
"triangle_IMP_Minus \<equiv>
  (
   \<comment> \<open>mul_a' = triangle_a s;\<close>
   (''mul'' @ ''a'') ::= (A (V ''a'')) ;;
   \<comment> \<open>mul_b' = (triangle_a s) + 1;\<close>
   (''mul'' @ ''b'') ::= ((V ''a'') \<oplus> (N 1));;
   \<comment> \<open>mul_c' = 0;\<close>
   (''mul'' @  ''c'') ::= (A (N 0)) ;;
   \<comment> \<open>(mul_state::mul_state) = \<lparr>mul_a = mul_a, mul_b = mul_b, mul_c = 0\<rparr>;\<close>
   \<comment> \<open>mul_ret = (mul_imp mul_state);\<close>
   invoke_subprogram ''mul'' mul_IMP_minus;;
   \<comment> \<open>triangle_triangle = mul_c mul_ret div 2;\<close>
  ''triangle'' ::= (V (''mul'' @ ''c'') \<then>);;
  ''a'' ::= A (V ''a'')
  )"


(*definition triangle_IMP_Minus_state_transformer where "triangle_IMP_Minus_state_transformer p s \<equiv>
 (state_transformer p [(''a'',  triangle_a s), (''triangle'',  triangle_triangle s)]) o
 (mul_IMP_Minus_state_transformer (''mul'' @ p) (triangle_mul_state s))"*)

definition "triangle_imp_to_HOL_state p s =
              \<lparr>triangle_a = s (add_prefix p ''a''), triangle_triangle = (s (add_prefix p ''triangle''))\<rparr>"

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
  "(invoke_subprogram p triangle_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p ''triangle'') = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state p s))"
  apply(simp only: triangle_IMP_Minus_def triangle_imp.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule mul_IMP_minus_correct[where vars = "{p @ ''traingle''}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: triangle_state_upd_def Let_def triangle_imp_to_HOL_state_def)[1]
  apply(auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma triangle_IMP_Minus_correct_time: 
  "(invoke_subprogram p triangle_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = triangle_imp_time 0 (triangle_imp_to_HOL_state p s)"
  apply(simp only: triangle_IMP_Minus_def com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst triangle_imp_time.simps)
  apply(erule mul_IMP_minus_correct[where vars = "{p @ ''triangle''}"])
  \<comment> \<open>Warning: in the following, I am unfolding mul_imp_to_HOL_state_def. With more experiments, it
      should become clear if this will cascade down multiple layers\<close>
  apply(simp add: triangle_imp_time_acc triangle_imp_to_HOL_state_def triangle_state_upd_def)[1]
  apply (auto simp: mul_imp_to_HOL_state_def)[1]
  done

lemma triangle_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ triangle_pref) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set triangle_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma triangle_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) triangle_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (triangle_imp_time 0 (triangle_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''triangle'') = triangle_triangle (triangle_imp (triangle_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using triangle_IMP_Minus_correct_time triangle_IMP_Minus_correct_function
        triangle_IMP_Minus_correct_effects 
  by auto

record prod_encode_state = prod_encode_a::nat prod_encode_b::nat prod_encode_ret::nat

definition "prod_encode_state_upd (s::prod_encode_state) \<equiv>
      let
        triangle_a = prod_encode_a s + prod_encode_b s;
        triangle_triangle' = 0;
        (triangle_state::triangle_state) = \<lparr>triangle_a = triangle_a, triangle_triangle = triangle_triangle'\<rparr>;
        triangle_ret = (triangle_imp triangle_state);
        prod_encode_ret = triangle_triangle triangle_ret;
        prod_encode_ret = prod_encode_ret + prod_encode_a s;
        ret = \<lparr>prod_encode_a = prod_encode_a s,prod_encode_b = prod_encode_b s, prod_encode_ret = prod_encode_ret\<rparr>
      in
        ret
"

fun prod_encode_imp:: "prod_encode_state \<Rightarrow> prod_encode_state" where
"prod_encode_imp s = 
  (let
     ret = prod_encode_state_upd s
   in
     ret
  )"

lemmas [simp del] = prod_encode_imp.simps

lemma prod_encode_imp_correct: "prod_encode_ret (prod_encode_imp s) = prod_encode (prod_encode_a s, prod_encode_b s)"
proof (induction s rule: prod_encode_imp.induct)
  case (1 s)
  then show ?case
    by (auto simp: prod_encode_imp.simps prod_encode_def prod_encode_state_upd_def Let_def triangle_imp_correct split: if_splits)
qed 

fun prod_encode_imp_time:: "nat \<Rightarrow> prod_encode_state \<Rightarrow> nat" where
"prod_encode_imp_time t s = 
  (let
     triangle_a = prod_encode_a s + prod_encode_b s;
     t = t + 2;
     triangle_triangle' = 0;
     t = t + 2;
     (triangle_state::triangle_state) = \<lparr>triangle_a = triangle_a, triangle_triangle = triangle_triangle'\<rparr>;
     triangle_ret = (triangle_imp triangle_state);
     t = t + triangle_imp_time 0 triangle_state;
     prod_encode_ret = triangle_triangle triangle_ret;
     t = t + 2;
     prod_encode_ret = prod_encode_ret + prod_encode_a s;
     t = t + 2;
     ret = t
   in
     ret
  )"

lemmas [simp del] = prod_encode_imp_time.simps

lemma prod_encode_imp_time_acc: "(prod_encode_imp_time (Suc t) s) = Suc (prod_encode_imp_time t s)"
  by (induction t s rule: prod_encode_imp_time.induct)
     (auto simp add: prod_encode_imp_time.simps Let_def eval_nat_numeral split: if_splits)

(*        triangle_a = prod_encode_a s + prod_encode_b s;
        (triangle_state::triangle_state) = \<lparr>triangle_a = triangle_a, triangle_triangle = 0\<rparr>;
        triangle_ret = (triangle_imp triangle_state);
        prod_encode_ret = triangle_triangle triangle_ret + prod_encode_a s;
*)

definition prod_encode_IMP_Minus where "prod_encode_IMP_Minus \<equiv>
  (''triangle.'' @ ''a'') ::= ((V ''a'') \<oplus> (V ''b'')) ;;
  (''triangle.'' @ ''triangle'') ::= (A (N 0)) ;;
  invoke_subprogram ''triangle.'' triangle_IMP_Minus ;;
  ''prod_encode'' ::= (A (V (''triangle.'' @ ''triangle''))) ;;
  ''prod_encode'' ::= ((V ''a'') \<oplus> (V ''prod_encode''))"

definition "prod_encode_imp_to_HOL_state p s =
  \<lparr>prod_encode_a = s (add_prefix p ''a''), prod_encode_b = s (add_prefix p ''b''), prod_encode_ret = (s (add_prefix p ''prod_encode''))\<rparr>"

lemma notD: "x \<notin> s \<Longrightarrow> (x \<in> s \<Longrightarrow> False)"
  by auto

lemma prod_encode_IMP_Minus_correct_function: 
  "(invoke_subprogram p prod_encode_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t \<^esup> s'
    \<Longrightarrow> s' (add_prefix p ''prod_encode'') = prod_encode_ret (prod_encode_imp (prod_encode_imp_to_HOL_state p s))"
  apply(simp only: prod_encode_IMP_Minus_def prod_encode_imp.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule triangle_IMP_Minus_correct[where vars = "{p @ ''a''}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_encode_state_upd_def Let_def prod_encode_imp_to_HOL_state_def)[1]
  apply(auto simp: triangle_imp_to_HOL_state_def)[1]
  done

lemma prod_encode_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_encode_IMP_Minus, s) 
      \<Rightarrow>\<^bsup>t\<^esup> s'
    \<Longrightarrow> t = prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state p s)"
  apply(simp only: prod_encode_IMP_Minus_def prod_encode_imp_time.simps com_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  \<comment> \<open>Variables that we want to preserve: variables of this program minus the variables of the
     program we call. If automation fails, this should be manually chosen variables.\<close>
  apply(erule triangle_IMP_Minus_correct[where vars = "{p @ ''a''}"])
  apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_encode_state_upd_def Let_def prod_encode_imp_to_HOL_state_def)[1]
  apply(auto simp: triangle_imp_to_HOL_state_def)[1]
  done

lemma prod_encode_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_encode_pref) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set prod_encode_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma prod_encode_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_encode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_encode_imp_time 0 (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''prod_encode'') = prod_encode_ret (prod_encode_imp (prod_encode_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_encode_IMP_Minus_correct_time prod_encode_IMP_Minus_correct_function
        prod_encode_IMP_Minus_correct_effects 
  by auto

record prod_decode_aux_state = prod_decode_aux_k::nat prod_decode_aux_m::nat

definition "prod_decode_aux_state_upd s \<equiv>
      let
        prod_decode_aux_k' = Suc (prod_decode_aux_k s);
        prod_decode_aux_m' = (prod_decode_aux_m s) - prod_decode_aux_k';
        ret = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>
      in
        ret
"

function prod_decode_aux_imp :: "prod_decode_aux_state \<Rightarrow> prod_decode_aux_state"
  where "prod_decode_aux_imp s =    
    (if prod_decode_aux_m s - prod_decode_aux_k s  \<noteq> 0 \<comment> \<open>while condition\<close>
     then
       let
         next_iteration = prod_decode_aux_imp (prod_decode_aux_state_upd s)
       in
         next_iteration
     else
       s)"
  by pat_completeness auto
termination
  by  (relation "measure (\<lambda>s. prod_decode_aux_m s)")  (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)

declare prod_decode_aux_imp.simps [simp del]

lemma prod_decode_aux_imp_correct:
  "prod_decode_aux_m (prod_decode_aux_imp s) = fst (prod_decode_aux (prod_decode_aux_k s) (prod_decode_aux_m s))"(is ?g1)
  "prod_decode_aux_k (prod_decode_aux_imp s) - prod_decode_aux_m (prod_decode_aux_imp s) = snd (prod_decode_aux (prod_decode_aux_k s) (prod_decode_aux_m s))" (is ?g2)
proof-
  show ?g1
  proof (induction s rule: prod_decode_aux_imp.induct)
    case (1 s)
    then show ?case
      apply(subst prod_decode_aux_imp.simps)
      apply (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)
       apply (metis diff_is_0_eq prod_decode_aux.simps prod_decode_aux_imp.simps prod_decode_aux_state_upd_def)
      by (simp add: prod_decode_aux.simps prod_decode_aux_imp.simps)
  qed
  show ?g2
  proof (induction s rule: prod_decode_aux_imp.induct)
    case (1 s)
    then show ?case
      apply(subst prod_decode_aux_imp.simps)
      apply (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)
       apply (metis diff_is_0_eq prod_decode_aux.simps prod_decode_aux_imp.simps prod_decode_aux_state_upd_def)
      by (simp add: prod_decode_aux.simps prod_decode_aux_imp.simps)
  qed
qed 

function prod_decode_aux_imp_time:: "nat \<Rightarrow> prod_decode_aux_state\<Rightarrow> nat" where
"prod_decode_aux_imp_time t s = 
(
    (if prod_decode_aux_m s - prod_decode_aux_k s \<noteq> 0 then \<comment> \<open>While\<close>
      (
        let
          t = t + 3; \<comment> \<open>To account for while loop condition checking and difference computation\<close>
          prod_decode_aux_k' = Suc (prod_decode_aux_k s);
          t = t + 2;
          prod_decode_aux_m' = (prod_decode_aux_m s) - prod_decode_aux_k';
          t = t + 2;
          next_iteration = prod_decode_aux_imp_time t (prod_decode_aux_state_upd s)
        in
          next_iteration
      )
    else
      (
         \<comment> \<open>To account for the two steps of checking the condition, skipping the loop, and the difference computation\<close>
        let
          t = t + 4;
          ret = t
        in
          ret
      )
    )
)"
  by pat_completeness auto
termination
  by  (relation "measure (\<lambda>(t, s). prod_decode_aux_m s)")  (auto simp: prod_decode_aux_state_upd_def Let_def split: if_splits)

lemmas [simp del] = prod_decode_aux_imp_time.simps

lemma prod_decode_aux_imp_time_acc: "(prod_decode_aux_imp_time (Suc t) s) = Suc (prod_decode_aux_imp_time t s)"
  by (induction t s arbitrary:  rule: prod_decode_aux_imp_time.induct)
     (auto simp add: prod_decode_aux_imp_time.simps prod_decode_aux_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition prod_decode_aux_IMP_Minus where
"prod_decode_aux_IMP_Minus \<equiv>
  (\<comment> \<open>if prod_decode_aux_m s - prod_decode_aux_k s \<noteq> 0 then\<close>
   ''diff'' ::= ((V ''m'') \<ominus> (V ''k''));;
   WHILE ''diff''\<noteq>0 DO (
        \<comment> \<open>prod_decode_aux_k' = Suc (prod_decode_aux_k s);\<close>
        ''k'' ::= ((V ''k'') \<oplus> (N 1));;
        \<comment> \<open>prod_decode_aux_m' = (prod_decode_aux_m s) - prod_decode_aux_k';\<close>
        ''m'' ::= ((V ''m'') \<ominus> (V ''k''));;
        ''diff'' ::= ((V ''m'') \<ominus> (V ''k'')))
  )"

definition "prod_decode_aux_imp_to_HOL_state p s =
  \<lparr>prod_decode_aux_k = s (add_prefix p ''k''), prod_decode_aux_m = (s (add_prefix p ''m''))\<rparr>"

lemma prod_decode_aux_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p ''m'') = 
       prod_decode_aux_m (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state p s))"
  apply(induction "prod_decode_aux_imp_to_HOL_state p s" arbitrary: s s' t rule: prod_decode_aux_imp.induct)
  apply(simp only: prod_decode_aux_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps)
  apply(erule Seq_tE)
  apply(erule While_tE)
   apply(drule AssignD)+
   apply(subst prod_decode_aux_imp.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(erule Seq_tE)
  apply(erule Seq_tE_While_init)
  apply simp
  apply(dest_com_init_while)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst prod_decode_aux_imp.simps mul_imp_time.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def prod_decode_aux_state_upd_def)[1]
  done

lemma prod_decode_aux_IMP_Minus_correct_function_2: 
  "(invoke_subprogram p prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p ''k'') = 
       prod_decode_aux_k (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state p s))"
  apply(induction "prod_decode_aux_imp_to_HOL_state p s" arbitrary: s s' t rule: prod_decode_aux_imp.induct)
  apply(simp only: prod_decode_aux_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps)
  apply(erule Seq_tE)
  apply(erule While_tE)
   apply(drule AssignD)+
   apply(subst prod_decode_aux_imp.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(erule Seq_tE)
  apply(erule Seq_tE_While_init)
  apply assumption
  apply(dest_com_init_while)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst prod_decode_aux_imp.simps mul_imp_time.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def prod_decode_aux_state_upd_def)[1]
  done

lemma prod_decode_aux_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = 
       prod_decode_aux_imp_time 0 (prod_decode_aux_imp_to_HOL_state p s)"
  apply(induction "prod_decode_aux_imp_to_HOL_state p s" arbitrary: s s' t rule: prod_decode_aux_imp.induct)
  apply(simp only: prod_decode_aux_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps)
  apply(erule Seq_tE)
  apply(erule While_tE)
   apply(drule AssignD)+
   apply(subst prod_decode_aux_imp_time.simps)
   apply(auto simp: prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(erule Seq_tE)
  apply(erule Seq_tE_While_init)
  apply assumption
  apply(dest_com_init_while)
  apply(erule Seq_tE)+
   apply(drule AssignD)+
   apply(elim conjE)
   apply(subst prod_decode_aux_imp_time.simps mul_imp_time.simps)
  apply(auto simp: prod_decode_aux_imp_to_HOL_state_def prod_decode_aux_state_upd_def
                   eval_nat_numeral prod_decode_aux_imp_time_acc)[1]
  done

lemma prod_decode_aux_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_decode_aux_pref) prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set prod_decode_aux_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma prod_decode_aux_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_decode_aux_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_decode_aux_imp_time 0 (prod_decode_aux_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''m'') = prod_decode_aux_m (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''k'') = prod_decode_aux_k (prod_decode_aux_imp (prod_decode_aux_imp_to_HOL_state (p1 @ p2) s));      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_decode_aux_IMP_Minus_correct_time prod_decode_aux_IMP_Minus_correct_function_1
        prod_decode_aux_IMP_Minus_correct_function_2
        prod_decode_aux_IMP_Minus_correct_effects 
  by auto

record prod_decode_state = prod_decode_m::nat prod_decode_fst_ret::nat prod_decode_snd_ret::nat

definition "prod_decode_state_upd s \<equiv>
      let
        prod_decode_aux_k' = 0;
        prod_decode_aux_m' = (prod_decode_m s);
        prod_decode_aux_state = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>;
        prod_decode_aux_ret = prod_decode_aux_imp prod_decode_aux_state;
        fst_ret' = prod_decode_aux_m prod_decode_aux_ret;
        snd_ret' = prod_decode_aux_k prod_decode_aux_ret - prod_decode_aux_m prod_decode_aux_ret;
        ret = \<lparr>prod_decode_m = prod_decode_m s, fst_ret = fst_ret', snd_ret = snd_ret'\<rparr>
      in
        ret
"

fun prod_decode_imp :: "prod_decode_state \<Rightarrow> prod_decode_state"
  where "prod_decode_imp s =    
    (let
       ret = (prod_decode_state_upd s)
     in
         ret)
"

declare prod_decode_imp.simps [simp del]

lemma prod_decode_imp_correct:
   "prod_decode_fst_ret (prod_decode_imp s) = fst (prod_decode (prod_decode_m s))"
   "prod_decode_snd_ret (prod_decode_imp s) = snd (prod_decode (prod_decode_m s))"
   apply(subst prod_decode_imp.simps)
  apply (auto simp: prod_decode_aux_imp_correct(1) prod_decode_def prod_decode_imp.simps prod_decode_state_upd_def  Let_def split: if_splits)[1]
   apply(subst prod_decode_imp.simps)
  apply (auto simp: prod_decode_aux_imp_correct(2) prod_decode_def prod_decode_imp.simps prod_decode_state_upd_def  Let_def split: if_splits)[1]
  done


fun prod_decode_imp_time:: "nat \<Rightarrow> prod_decode_state\<Rightarrow> nat" where
  "prod_decode_imp_time t s = 
(
        let
          prod_decode_aux_k' = 0;
          t = t + 2;
          prod_decode_aux_m' = (prod_decode_m s);
          t = t + 2;
          prod_decode_aux_state = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>;
          prod_decode_aux_ret = prod_decode_aux_imp prod_decode_aux_state;
          t = t + prod_decode_aux_imp_time 0 prod_decode_aux_state;
          fst_ret' = prod_decode_aux_m prod_decode_aux_ret;
          t = t + 2;
          snd_ret' = prod_decode_aux_k prod_decode_aux_ret - prod_decode_aux_m prod_decode_aux_ret;
          t = t + 2;
          ret = t
        in
          ret
      )
"

lemmas [simp del] = prod_decode_imp_time.simps

lemma prod_decode_imp_time_acc: "(prod_decode_imp_time (Suc t) s) = Suc (prod_decode_imp_time t s)"
  by (induction t s arbitrary:  rule: prod_decode_imp_time.induct)
     (auto simp add: prod_decode_imp_time.simps prod_decode_state_upd_def Let_def eval_nat_numeral split: if_splits)

definition prod_decode_IMP_Minus where
"prod_decode_IMP_Minus \<equiv>
  (     \<comment> \<open>prod_decode_aux_k' = 0;\<close>
   (''prod_decode_aux.'' @ ''k'') ::= (A (N 0));;
        \<comment> \<open>prod_decode_aux_m' = (prod_decode_m s);\<close>
   (''prod_decode_aux.'' @ ''m'') ::= (A (V ''m''));;
        \<comment> \<open>prod_decode_aux_state = \<lparr>prod_decode_aux_k = prod_decode_aux_k', prod_decode_aux_m = prod_decode_aux_m'\<rparr>;\<close>
        \<comment> \<open>prod_decode_aux_ret = prod_decode_aux_imp prod_decode_aux_state;\<close>
   invoke_subprogram ''prod_decode_aux.'' prod_decode_aux_IMP_Minus;;
        \<comment> \<open>fst_ret' = prod_decode_aux_m prod_decode_aux_ret;\<close>
   ''fst_ret'' ::= (A (V (''prod_decode_aux.'' @ ''m'')));;
        \<comment> \<open>snd_ret' = prod_decode_aux_k prod_decode_aux_ret - prod_decode_aux_m prod_decode_aux_ret;\<close>
   ''snd_ret'' ::= ((V (''prod_decode_aux.'' @ ''k'')) \<ominus> (V (''prod_decode_aux.'' @ ''m'')))
  )"

definition "prod_decode_imp_to_HOL_state p s =
  \<lparr>prod_decode_m = (s (add_prefix p ''m'')), prod_decode_fst_ret = (s (add_prefix p ''fst_ret'')) , prod_decode_snd_ret = (s (add_prefix p ''snd_ret''))\<rparr>"

lemma prod_decode_IMP_Minus_correct_function_1: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p ''fst_ret'') = prod_decode_fst_ret (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(simp only: prod_decode_IMP_Minus_def prod_decode_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_aux_IMP_Minus_correct[where vars = "{p @ ''m''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_decode_state_upd_def Let_def prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma prod_decode_IMP_Minus_correct_function_2: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p ''snd_ret'') = prod_decode_snd_ret (prod_decode_imp (prod_decode_imp_to_HOL_state p s))"
  apply(simp only: prod_decode_IMP_Minus_def prod_decode_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_aux_IMP_Minus_correct[where vars = "{p @ ''m''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_decode_state_upd_def Let_def prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma prod_decode_IMP_Minus_correct_time: 
  "(invoke_subprogram p prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = (prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state p s))"
  apply(simp only: prod_decode_IMP_Minus_def prod_decode_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_aux_IMP_Minus_correct[where vars = "{p @ ''m''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: prod_decode_state_upd_def Let_def prod_decode_aux_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma prod_decode_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ prod_decode_pref) prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set prod_decode_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma prod_decode_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) prod_decode_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (prod_decode_imp_time 0 (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''fst_ret'') = prod_decode_fst_ret (prod_decode_imp (prod_decode_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''snd_ret'') = prod_decode_snd_ret (prod_decode_imp (prod_decode_imp_to_HOL_state (p1 @ p2) s));      \<And>v. p1 @ v \<in> vars \<Longrightarrow> \<not> (set p2 \<subseteq> set v) \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using prod_decode_IMP_Minus_correct_time prod_decode_IMP_Minus_correct_function_1
        prod_decode_IMP_Minus_correct_function_2
        prod_decode_IMP_Minus_correct_effects 
  by auto

record hd_state = hd_xs::nat hd_ret::nat

definition "hd_state_upd s \<equiv>
      let
        prod_decode_m' = hd_xs s - 1;
        prod_decode_fst_ret' = 0;
        prod_decode_snd_ret' = 0;
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        hd_ret' = prod_decode_fst_ret prod_decode_ret;
        ret = \<lparr>hd_xs = hd_xs s, hd_ret = hd_ret'\<rparr>
      in
        ret
"

fun hd_imp :: "hd_state \<Rightarrow> hd_state"
  where "hd_imp s =    
    (let
       ret = (hd_state_upd s)
     in
         ret)
"

declare hd_imp.simps [simp del]

lemma hd_imp_correct:
   "hd_ret (hd_imp s) = hd_nat (hd_xs s)"
  by (subst hd_imp.simps) (auto simp: prod_decode_imp_correct hd_nat_def fst_nat_def hd_imp.simps hd_state_upd_def Let_def split: if_splits)[1]

fun hd_imp_time:: "nat \<Rightarrow> hd_state\<Rightarrow> nat" where
  "hd_imp_time t s = 
(
      let
        prod_decode_m' = hd_xs s - 1;
        t = t + 2;
        prod_decode_fst_ret' = 0;
        t = t + 2;
        prod_decode_snd_ret' = 0;
        t = t + 2;
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        t = t + prod_decode_imp_time 0 prod_decode_state;
        hd_ret' = prod_decode_fst_ret prod_decode_ret;
        t = t + 2;
        ret = t
      in
        ret
      )
"

lemmas [simp del] = hd_imp_time.simps

lemma hd_imp_time_acc: "(hd_imp_time (Suc t) s) = Suc (hd_imp_time t s)"
  by (induction t s arbitrary:  rule: hd_imp_time.induct)
     (auto simp add: hd_imp_time.simps split: if_splits)

definition hd_IMP_Minus where
"hd_IMP_Minus \<equiv>
  (     \<comment> \<open>prod_decode_m' = hd_xs s - 1;\<close>
        (''prod_decode.'' @ ''m'') ::= ((V ''xs'') \<ominus> (N 1));;
        \<comment> \<open>prod_decode_fst_ret' = 0;\<close>
        (''prod_decode.'' @ ''fst_ret'') ::= (A (N 0));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (''prod_decode.'' @ ''snd_ret'') ::= (A (N 0));;
        \<comment> \<open>prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;\<close>
        \<comment> \<open>prod_decode_ret = prod_decode_imp prod_decode_state;\<close>
        invoke_subprogram ''prod_decode.'' prod_decode_IMP_Minus;;
        \<comment> \<open>hd_ret' = prod_decode_fst_ret prod_decode_ret;\<close>
        (''hd_ret'') ::= (A (V (''prod_decode.'' @ ''fst_ret'')))
  )"

definition "hd_imp_to_HOL_state p s =
  \<lparr>hd_xs = (s (add_prefix p ''xs'')), hd_ret = (s (add_prefix p ''hd_ret''))\<rparr>"

lemma hd_IMP_Minus_correct_function: 
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p ''hd_ret'') = hd_ret (hd_imp (hd_imp_to_HOL_state p s))"
  apply(simp only: hd_IMP_Minus_def hd_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ ''xs''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: hd_state_upd_def Let_def hd_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma hd_IMP_Minus_correct_time: 
  "(invoke_subprogram p hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = hd_imp_time 0 (hd_imp_to_HOL_state p s)"
  apply(simp only: hd_IMP_Minus_def hd_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ ''xs''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: hd_state_upd_def Let_def hd_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma hd_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ hd_pref) hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set hd_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma hd_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) hd_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (hd_imp_time 0 (hd_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''hd_ret'') = hd_ret (hd_imp (hd_imp_to_HOL_state (p1 @ p2) s))\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using hd_IMP_Minus_correct_time hd_IMP_Minus_correct_function
        hd_IMP_Minus_correct_effects 
  by auto

record tl_state = tl_xs::nat tl_ret::nat

definition "tl_state_upd s \<equiv>
      let
        prod_decode_m' = tl_xs s - 1;
        prod_decode_fst_ret' = 0;
        prod_decode_snd_ret' = 0;
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        tl_ret' = prod_decode_snd_ret prod_decode_ret;
        ret = \<lparr>tl_xs = tl_xs s, tl_ret = tl_ret'\<rparr>
      in
        ret
"

fun tl_imp :: "tl_state \<Rightarrow> tl_state"
  where "tl_imp s =    
    (let
       ret = (tl_state_upd s)
     in
         ret)
"

declare tl_imp.simps [simp del]

lemma tl_imp_correct:
   "tl_ret (tl_imp s) = tl_nat (tl_xs s)"
  by (subst tl_imp.simps) (auto simp: prod_decode_imp_correct tl_nat_def snd_nat_def tl_imp.simps tl_state_upd_def Let_def split: if_splits)[1]

fun tl_imp_time:: "nat \<Rightarrow> tl_state\<Rightarrow> nat" where
  "tl_imp_time t s = 
(
      let
        prod_decode_m' = tl_xs s - 1;
        t = t + 2;
        prod_decode_fst_ret' = 0;
        t = t + 2;
        prod_decode_snd_ret' = 0;
        t = t + 2;
        prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_fst_ret = prod_decode_fst_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;
        prod_decode_ret = prod_decode_imp prod_decode_state;
        t = t + prod_decode_imp_time 0 prod_decode_state;
        tl_ret' = prod_decode_snd_ret prod_decode_ret;
        t = t + 2;
        ret = t
      in
        ret
      )
"

lemmas [simp del] = tl_imp_time.simps

lemma tl_imp_time_acc: "(tl_imp_time (Suc t) s) = Suc (tl_imp_time t s)"
  by (induction t s arbitrary:  rule: tl_imp_time.induct)
     (auto simp add: tl_imp_time.simps split: if_splits)

definition tl_IMP_Minus where
"tl_IMP_Minus \<equiv>
  (     \<comment> \<open>prod_decode_m' = tl_xs s - 1;\<close>
        (''prod_decode.'' @ ''m'') ::= ((V ''xs'') \<ominus> (N 1));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (''prod_decode.'' @ ''fst_ret'') ::= (A (N 0));;
        \<comment> \<open>prod_decode_snd_ret' = 0;\<close>
        (''prod_decode.'' @ ''snd_ret'') ::= (A (N 0));;
        \<comment> \<open>prod_decode_state = \<lparr>prod_decode_m = prod_decode_m', prod_decode_snd_ret = prod_decode_snd_ret', prod_decode_snd_ret = prod_decode_snd_ret'\<rparr>;\<close>
        \<comment> \<open>prod_decode_ret = prod_decode_imp prod_decode_state;\<close>
        invoke_subprogram ''prod_decode.'' prod_decode_IMP_Minus;;
        \<comment> \<open>tl_ret' = prod_decode_snd_ret prod_decode_ret;\<close>
        (''tl_ret'') ::= (A (V (''prod_decode.'' @ ''snd_ret'')))
  )"

definition "tl_imp_to_HOL_state p s =
  \<lparr>tl_xs = (s (add_prefix p ''xs'')), tl_ret = (s (add_prefix p ''tl_ret''))\<rparr>"

lemma tl_IMP_Minus_correct_function: 
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p ''tl_ret'') = tl_ret (tl_imp (tl_imp_to_HOL_state p s))"
  apply(simp only: tl_IMP_Minus_def tl_imp.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ ''xs''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: tl_state_upd_def Let_def tl_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma tl_IMP_Minus_correct_time: 
  "(invoke_subprogram p tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = tl_imp_time 0 (tl_imp_to_HOL_state p s)"
  apply(simp only: tl_IMP_Minus_def tl_imp_time.simps com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply(erule Seq_tE)+
  apply(erule prod_decode_IMP_Minus_correct[where vars = "{p @ ''xs''}"])
   apply(drule AssignD)+
  apply(elim conjE impE)
  apply(auto simp: tl_state_upd_def Let_def tl_imp_to_HOL_state_def)[1]
  apply(auto simp: prod_decode_imp_to_HOL_state_def)[1]
  done

lemma tl_IMP_Minus_correct_effects:
  "(invoke_subprogram (p @ tl_pref) tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> p @ v \<in> vars \<Longrightarrow> \<not> (set tl_pref \<subseteq> set v) \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
  using com_add_prefix_valid_subset com_only_vars
  by blast

lemma tl_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) tl_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
     \<lbrakk>t = (tl_imp_time 0 (tl_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) ''tl_ret'') = tl_ret (tl_imp (tl_imp_to_HOL_state (p1 @ p2) s))\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using tl_IMP_Minus_correct_time tl_IMP_Minus_correct_function
        tl_IMP_Minus_correct_effects 
  by auto

end