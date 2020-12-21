\<^marker>\<open>creator Florian Keßler\<close>

section "Correctness"

theory Correctness imports Reduction
begin

definition imp_minus_sas_plus_equivalent_states :: "com \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> imp_state \<Rightarrow> sas_state \<Rightarrow> bool" where
"imp_minus_sas_plus_equivalent_states c c1 r is ss = (ss PC = Some (Num (index_of (all_subprograms c) c1)) 
  \<and> list_all (\<lambda>v. ss (VN v) = Some (Num (is v)) \<or> (is v > r \<and> ss (VN v) = Some \<omega>)) (enumerate_variables c))"  

lemma imp_minus_sas_plus_equivalent_states_assign:
  assumes "t' \<le> t"
    "imp_minus_sas_plus_equivalent_states c (x ::= a) (t' * max_constant c) s ss1"
  shows "imp_minus_sas_plus_equivalent_states c SKIP ((t' - Suc 0) * max_constant c)
     (\<lambda>y. if y = x then aval a s else s y)
     (ss1(VN x \<mapsto> Num (aval a s), PC \<mapsto> Num (index_of (all_subprograms c) SKIP)))"
proof -
  let ?ss2 = "ss1(VN x \<mapsto> Num (t * max_constant c), PC \<mapsto> Num (index_of (all_subprograms c) SKIP))"
  let ?is2 = "\<lambda>a. if a = x then aval (A (N (t * max_constant c))) s else s a"
  let ?r1 = "t' * max_constant c"
  let ?r2 = "(t' - Suc 0) * max_constant c"
  have "v \<in> set (enumerate_variables c)
     \<Longrightarrow> ?ss2 (VN v) = Some (Num (?is2 v)) \<or> (?is2 v > ?r2 \<and> ?ss2 (VN v) = Some \<omega>)" for v 
  proof -
    assume "v \<in> set (enumerate_variables c)"
    moreover have "list_all (\<lambda>v. ss1 (VN v) 
      = Some (Num (s v)) \<or> (s v > ?r1 \<and> ss1 (VN v) = Some \<omega>)) (enumerate_variables c)"
      using assms by(auto simp: imp_minus_sas_plus_equivalent_states_def)
    ultimately have "ss1 (VN v) = Some (Num (s v)) \<or> (s v > ?r1 \<and> ss1 (VN v) = Some \<omega>)" 
      by (simp add: list_all_iff)
    then show ?thesis using diff_mult_distrib by auto
  qed
  then show ?thesis using assms 
    by (fastforce simp: imp_minus_sas_plus_equivalent_states_def list_all_iff)
qed

lemma "a \<noteq> c \<Longrightarrow> f(a \<mapsto> b, c \<mapsto> d) = (\<lambda>x. if x = a then Some b else (f(c \<mapsto> d)) x)" 
  by auto


lemma imp_minus_minus_to_sas_plus_single_step:
   "(c1, is1) \<rightarrow> (c2, is2) \<Longrightarrow> cs = all_subprograms c \<Longrightarrow> c1 \<in> set cs \<Longrightarrow> t' \<le> t \<Longrightarrow> t > 0
  \<Longrightarrow> imp_minus_sas_plus_equivalent_states c c1 (t' *  (max_constant c)) is1 ss1 
  \<Longrightarrow> (\<exists>op \<in> set (com_to_operators cs c1 (domain c t)). \<exists>ss2.
     imp_minus_sas_plus_equivalent_states c c2 ((t' - 1) *  (max_constant c)) is2 ss2
    \<and> is_operator_applicable_in ss1 op
    \<and> execute_operator_sas_plus ss1 op = ss2)"
proof (induction c1 is1 c2 is2 rule: small_step_induct)
  case (Assign x a s)
  let ?i = "index_of cs (x ::= a)"
  let ?j = "index_of cs SKIP"
  have "SKIP \<in> set (all_subprograms c)" using SKIP_in_enumerate_subprograms by simp
  moreover then have "SKIP \<in> set cs" using Assign by blast
  have "aval a s \<le> t * (max_constant c) \<or> aval a s > t * (max_constant c)" by auto
  show ?case
  proof (cases a)
    case (A atom)
    then show ?thesis
    proof (cases atom)
      case (N val)
      let ?op = "\<lparr> precondition_of = [(PC, Num ?i)], 
                  effect_of = [(PC, Num ?j), (VN x, (if val \<le> t * (max_constant c) then Num val else \<omega>))]\<rparr>"
      let ?ss2 = "ss1(VN x \<mapsto> Num val, PC \<mapsto> Num ?j)"
      have "val \<le> max_constant c" using enumerate_subprograms_max_constant Assign A N by fastforce
      then have "Num val \<in> set (domain c t)" using Assign by (auto simp: domain_def Let_def) 
          (metis Suc_lessI add.right_neutral atLeastLessThan_iff image_eqI lambda_zero le_0_eq le_less_trans le_neq_implies_less n_less_m_mult_n nat_le_linear times_nat.simps(2))
      moreover have "?op \<in> set (com_to_operators cs (x ::= a) (domain c t))" 
        using A N by (auto simp: domain_def Let_def)
      moreover have "is_operator_applicable_in ss1 ?op" using Assign 
        by (auto simp: imp_minus_sas_plus_equivalent_states_def)
           (metis (no_types) fun_upd_triv map_le_empty map_le_upd)
      moreover have "imp_minus_sas_plus_equivalent_states c SKIP ((t' - Suc 0) * max_constant c) 
        (\<lambda>y. if y = x then val else s y)
        ?ss2" using Assign A N 
        by (smt atomVal.simps aval.simps imp_minus_sas_plus_equivalent_states_def list_all_iff imp_minus_sas_plus_equivalent_states_assign[OF Assign(3) Assign(5)])
      moreover have "ss1(VN x \<mapsto> Num val, PC \<mapsto> Num (index_of (all_subprograms c) SKIP)) 
        = (\<lambda>a. if a = PC then Some (Num (index_of (all_subprograms c) SKIP)) else (ss1(VN x \<mapsto> Num val)) a)" by auto
      ultimately show ?thesis using Assign A N by (simp add: domain_def Let_def)
    next
      case (V var)
      then show ?thesis sorry
    qed
  next
    case (Plus x21 x22)
    then show ?thesis sorry
  next
    case (Sub x31 x32)
    then show ?thesis sorry
  qed
next
  case (Seq1 c\<^sub>2 s)
  then show ?case sorry
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case sorry
next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  then show ?case sorry
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  then show ?case sorry
next
  case (WhileTrue s b c)
  then show ?case sorry
next
  case (WhileFalse s b c)
  then show ?case sorry
qed
      

end