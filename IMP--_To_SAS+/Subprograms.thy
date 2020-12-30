\<^marker>\<open>creator Florian Keßler\<close>

theory Subprograms imports Small_StepT Domains
begin

fun all_subprograms :: "com \<Rightarrow> com list" where
"all_subprograms (SKIP) = [SKIP]" |
"all_subprograms (Assign v aexp) = [(Assign v aexp), SKIP]" |
"all_subprograms (c1 ;; c2) = (map (\<lambda> c. c ;; c2) (all_subprograms c1)) @ all_subprograms c1 
  @ all_subprograms c2" |
"all_subprograms (If v c1 c2) = [(If v c1 c2)] @ all_subprograms c1 @ all_subprograms c2" |
"all_subprograms (While v c) = [(While v c), SKIP] @ all_subprograms c @ 
  (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))"

definition enumerate_subprograms :: "com \<Rightarrow> com list" where
"enumerate_subprograms c = remdups (all_subprograms c)"

fun all_variables :: "com \<Rightarrow> vname list" where
"all_variables (SKIP) = []" |
"all_variables (Assign v aexp) = [ v ] @ (case aexp of 
  A a \<Rightarrow> (case a of V v2 \<Rightarrow> [ v2 ] | N _ \<Rightarrow> []) |
  Plus a b \<Rightarrow> [ a ] |
  Sub a b \<Rightarrow> [ a ])" |
"all_variables (c1 ;; c2) = []" |
"all_variables (If v c1 c2) = [ v ]" |
"all_variables (While v c) = [ v ]"

definition enumerate_variables :: "com \<Rightarrow> vname list" where
"enumerate_variables c = remdups (concat (map all_variables (enumerate_subprograms c)))"

declare enumerate_subprograms_def[simp] 

lemma c_in_all_subprograms_c[simp]: "c \<in> set (enumerate_subprograms c)" 
  by (induction c) auto

lemma enumerate_variables_all_variables[simp]: "x \<in> set (all_variables c) \<Longrightarrow> x \<in> set (enumerate_variables c)"
  using c_in_all_subprograms_c by (auto simp: enumerate_variables_def)

lemma enumerate_subprograms_complete_step: "(c1, s1) \<rightarrow> (c2, s2) 
  \<Longrightarrow> c2 \<in> set (enumerate_subprograms c1)"
apply (induction c1 s1 c2 s2 rule: small_step_induct)
  using c_in_all_subprograms_c apply(auto)
done

lemma enumerate_subprograms_transitive: "c2 \<in> set (enumerate_subprograms c1) \<Longrightarrow> 
  c3 \<in> set (enumerate_subprograms c2) \<Longrightarrow> c3 \<in> set (enumerate_subprograms c1)"
proof (induction c1 arbitrary: c2 c3 rule: all_subprograms.induct)
  case (4 v c4 c5)
  then have "(c2 = (If v c4 c5)) \<or> (c2 \<in> set (all_subprograms c4)) 
              \<or> (c2 \<in> set (all_subprograms c5))"
      by (metis Un_iff all_subprograms.simps append.simps append.simps enumerate_subprograms_def set_ConsD set_append set_remdups)
  then show ?case
  proof (elim disjE)
    assume "c2 \<in> set (all_subprograms c5)" 
    then show ?thesis using 4 by auto
  next
    assume "c2 \<in> set (all_subprograms c4)"
    then show ?thesis using 4 by auto
  next
    assume "c2 = (If v c4 c5)"
    then show ?thesis using 4 by auto
  qed
next
  case (5 v c)
  then have "c2 \<in> set (all_subprograms (While v c))" by (metis enumerate_subprograms_def set_remdups)
  then have "c2 \<in> set ([While v c, SKIP] @ all_subprograms c @ map (\<lambda> x. x ;; (While v c)) (all_subprograms c))" 
    by (metis all_subprograms.simps enumerate_subprograms_def map_eq_conv set_append set_remdups) 
  then have "(c2 = (While v c)) \<or> c2 = SKIP \<or> (c2 \<in> set (all_subprograms c)) 
              \<or> (c2 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c)))" by simp
  then show ?case
  proof (elim disjE)
    assume "c2 = (While v c)"
    then show ?thesis using 5 by auto
  next
    assume "c2 = SKIP"
    then show ?thesis using 5 by auto
  next
    assume "c2 \<in> set (all_subprograms c)"
    then show ?thesis using 5 
      by (metis Un_iff all_subprograms.simps enumerate_subprograms_def set_append set_remdups)
  next
    assume "c2 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))"
    then obtain c' where *: "c2 = c' ;; (While v c) \<and> c' \<in> set (all_subprograms c)" by auto
    then have "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c')) \<or> c3 \<in> set (all_subprograms c')
      \<or> c3 \<in> set (all_subprograms (While v c))" using 5 by auto
    then show ?thesis
    proof (elim disjE)
      assume "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c'))"
      then have "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))" using * 5 by auto
      then show ?thesis by auto
    next
      assume "c3 \<in> set (all_subprograms c')"
      then have "c3 \<in> set (all_subprograms c)" using * 5 by auto
      then show ?thesis by auto
    next
      assume "c3 \<in> set (all_subprograms (While v c))"
      then show ?thesis using 5 by (metis enumerate_subprograms_def set_remdups)
    qed
  qed
qed auto

lemma enumerate_subprograms_complete: "(c1, s1)\<rightarrow>\<^bsup>t\<^esup> (c2, s2)
  \<Longrightarrow>  c2 \<in> set (enumerate_subprograms c1)"
proof(induction t arbitrary: c1 s1 c2 s2)
  case 0
  then show ?case using c_in_all_subprograms_c by auto
next
  case (Suc t)
  then obtain c1' s1' where "((c1, s1) \<rightarrow> (c1', s1')) \<and> ((c1', s1')\<rightarrow>\<^bsup>t\<^esup> (c2, s2))" by auto
  then show ?case using enumerate_subprograms_transitive Suc enumerate_subprograms_complete_step 
    by blast
qed

lemma SKIP_in_enumerate_subprograms[simp]: "SKIP \<in> set (enumerate_subprograms c)" 
  by (induction c rule: all_subprograms.induct) auto

lemma enumerate_subprograms_enumerate_variables: "c' \<in> set (enumerate_subprograms c) 
  \<Longrightarrow> set (enumerate_variables c') \<subseteq> set (enumerate_variables c)" 
 by (auto simp: enumerate_variables_def) 
     (metis enumerate_subprograms_def enumerate_subprograms_transitive set_remdups)


lemma enumerate_subprograms_max_constant: "c' \<in> set (enumerate_subprograms c)
  \<Longrightarrow> max_constant c' \<le> max_constant c"
  by (induction c arbitrary: c' rule: all_subprograms.induct)
       (fastforce  split: if_splits)+

end