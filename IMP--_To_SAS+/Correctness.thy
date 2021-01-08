\<^marker>\<open>creator Florian Keßler\<close>

section "Correctness"

theory Correctness imports Reduction
begin 

definition imp_minus_sas_plus_equivalent_states :: "com \<Rightarrow> com \<Rightarrow> imp_state \<Rightarrow> sas_state \<Rightarrow> bool" where
"imp_minus_sas_plus_equivalent_states c c1 is ss = (ss PC = Some (PCV c1) 
  \<and> list_all (\<lambda> v. ss (VN v) = Some (EV (is v))) (enumerate_variables c))"

lemma [simp]: "imp_minus_sas_plus_equivalent_states c c1 is ss 
  \<Longrightarrow> v \<in> set (enumerate_variables c)
  \<Longrightarrow> is v = Num 0 \<longleftrightarrow> ss (VN v) = Some (EV (Num 0))"
  by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def)

lemma [simp]: "[VN v \<mapsto> y, PC \<mapsto> x] \<subseteq>\<^sub>m s = (s PC = Some x \<and> s (VN v) = Some y)"
  by (auto simp: map_le_def)

lemma [simp]: "[PC \<mapsto> x] \<subseteq>\<^sub>m s \<longleftrightarrow> (s PC = Some x)" 
  by (auto simp: map_le_def)

lemma map_of_list_update: "distinct (map fst l) \<Longrightarrow> length l > 0 \<Longrightarrow> fst (l ! 0) = x  \<Longrightarrow> z \<noteq> x
  \<Longrightarrow> map_of (list_update l 0 (x, y)) z = map_of l z"
  by (induction l) auto

lemma [simp]: assumes "op \<in> set (com_to_operators c d)"
  shows "map_of (list_update (effect_of op) 0 (PC, y)) = (map_of (effect_of op))(PC \<mapsto> y)"
proof -
  have "map_of (list_update (effect_of op) 0 (PC, y)) x = ((map_of (effect_of op))(PC \<mapsto> y)) x" for x
    using assms com_to_operators_variables_distinct effect_nonempty 
      map_of_list_update[where ?l = "effect_of op"]
    by (auto) 
      (metis effect_nonempty fst_of_effect map_of_eq_Some_iff set_update_memI update_preserve_distinct)
  then show ?thesis by auto
qed

lemma [simp]: assumes "op \<in> set (com_to_operators c d)"
  shows "map_of (list_update (precondition_of op) 0 (PC, y)) = (map_of (precondition_of op))(PC \<mapsto> y)"
proof -
  have "map_of (list_update (precondition_of op) 0 (PC, y)) x = ((map_of (precondition_of op))(PC \<mapsto> y)) x" for x
    using assms com_to_operators_variables_distinct precondition_nonempty 
      map_of_list_update[where ?l = "precondition_of op"]
    by (auto) 
     (metis precondition_nonempty fst_of_precondition map_of_eq_Some_iff set_update_memI update_preserve_distinct)
  then show ?thesis by auto
qed

lemma pc_of_op: "op \<in> set (com_to_operators c2 d) 
  \<Longrightarrow> imp_minus_sas_plus_equivalent_states c c1 is ss2 \<Longrightarrow> ss1 \<then>\<^sub>+ op = ss2
  \<Longrightarrow> pc_to_com (effect_of op) = c1" 
  by (auto simp: imp_minus_sas_plus_equivalent_states_def com_to_operators_variables_distinct)

lemma effect_in_updated[simp]: 
  assumes "op' \<in> set (com_to_operators c d)" 
    "map_of (precondition_of op') = (map_of (precondition_of op))(PC \<mapsto> PCV c)"
    "map_of (effect_of op') = (map_of (effect_of op))(PC \<mapsto> PCV (pc_to_com (effect_of op')))"
    "s \<then>\<^sub>+ op = s'"
  shows "s(PC \<mapsto> PCV c) \<then>\<^sub>+ op' = s'(PC \<mapsto> PCV (pc_to_com (effect_of op')))" 
proof -
  have "(s(PC \<mapsto> PCV c)  \<then>\<^sub>+ op') x = (s'(PC \<mapsto> PCV (pc_to_com (effect_of op')))) x" for x
    using assms PC_in_effect_precondition com_to_operators_variables_distinct apply auto
    by (metis fun_upd_other map_add_def)
  then show ?thesis by auto
qed

lemma applicable_in_PC_updated: "m \<subseteq>\<^sub>m s(PC \<mapsto> y) \<Longrightarrow> s PC = Some x \<Longrightarrow> m(PC \<mapsto> x) \<subseteq>\<^sub>m s"
  by (simp add: map_le_def)

lemma [simp]: "(s(PC \<mapsto> y) ++ (map_of m))(PC \<mapsto> x) = (s ++ (map_of m))(PC \<mapsto> x)"
proof -
  have "((s(PC \<mapsto> y) ++ (map_of m))(PC \<mapsto> x)) z = ((s ++ (map_of m))(PC \<mapsto> x)) z" for z
    by (simp add: fun_upd_def map_add_def)
  then show ?thesis by auto
qed

lemma sas_plus_to_imp_minus_minus_single_step:
  "op \<in> set (com_to_operators c1 (domain c t)) \<Longrightarrow> cs = enumerate_subprograms c 
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c) \<Longrightarrow> t > 0 
  \<Longrightarrow> imp_minus_sas_plus_equivalent_states c c1 is1 ss1
  \<Longrightarrow> is_operator_applicable_in ss1 op
  \<Longrightarrow> ss1 \<then>\<^sub>+ op = ss2
  \<Longrightarrow> the (ss2 PC) = PCV c2
  \<Longrightarrow> (\<exists>is2. ((c1, is1) \<rightarrow>\<^bsub>t * max_constant c\<^esub> (c2, is2)) \<and>
      imp_minus_sas_plus_equivalent_states c c2 is2 ss2)"
proof (induction c1 arbitrary: op ss1 ss2 is1 c2)
  case (Assign x a)
  let ?is2 = "is1(x := eval a is1 (t * max_constant c))"
  have "imp_minus_sas_plus_equivalent_states c SKIP ?is2 ss2" using Assign
  proof (cases a)
    case (A atom)
    then show ?thesis
    proof (cases atom)
      case (N val)
      then show ?thesis using Assign A
        by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def)
    next
      case (V var)
      have "var \<in> set (enumerate_variables c)" 
        using Assign A V enumerate_subprograms_enumerate_variables by fastforce
      then show ?thesis using Assign A V 
        by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def)
    qed
  qed (auto simp: enumerate_variables_def imp_minus_sas_plus_equivalent_states_def list_all_def 
        split: EVal.splits)
  then show ?case using Assign imp_minus_sas_plus_equivalent_states_def by auto
next
  case (Seq cA cB)
  have "cA = SKIP \<or> cA \<noteq> SKIP" by auto
  then show ?case
  proof (elim disjE)
    assume "cA = SKIP"
    then show ?thesis using Seq by (fastforce simp: imp_minus_sas_plus_equivalent_states_def)
  next
    assume "cA \<noteq> SKIP"
    then obtain op' where op'_def: "op' \<in> set (com_to_operators cA (domain c t)) 
      \<and> op = (let c1' = pc_to_com (effect_of op') in 
      \<lparr> precondition_of = 
        list_update (precondition_of op') 0 (PC, PCV (cA ;; cB)),
        effect_of = 
        list_update (effect_of op') 0 (PC, PCV (c1' ;; cB))\<rparr>)" using Seq by auto
    let ?c1' = "pc_to_com (effect_of op')"
    let ?ss1' = "ss1(PC \<mapsto> PCV cA)"
    let ?ss2' = "ss2(PC \<mapsto> PCV ?c1')"
    have "cA \<in> set (enumerate_subprograms (cA ;; cB))" using c_in_all_subprograms_c by auto
    then have "cA \<in> set (enumerate_subprograms c)" 
      using Seq enumerate_subprograms_transitive by blast
    moreover have "imp_minus_sas_plus_equivalent_states c cA is1 ?ss1'" 
      using Seq by (auto simp: imp_minus_sas_plus_equivalent_states_def)
    moreover have "map_of (precondition_of op') = (map_of (precondition_of op))(PC \<mapsto> PCV cA)"
      using op'_def Seq com_to_operators_variables_distinct by auto
    moreover then have "is_operator_applicable_in ?ss1' op'" 
      using Seq op'_def by auto
    moreover have "map_of (effect_of op') = map_of (effect_of op)(PC \<mapsto> PCV (pc_to_com (effect_of op')))"
      using op'_def Seq com_to_operators_variables_distinct by auto
    moreover then have "?ss1' \<then>\<^sub>+ op' = ?ss2'" using Seq op'_def by auto
    (* TODO: simplify this proof (Seq(1)) *)
    ultimately have "\<exists>is2. (cA, is1) \<rightarrow>\<^bsub>t * max_constant c\<^esub> (?c1', is2) \<and>
      imp_minus_sas_plus_equivalent_states c ?c1' is2 ?ss2'" using Seq op'_def by fastforce
    then show ?thesis using Seq op'_def 
      by(fastforce simp: imp_minus_sas_plus_equivalent_states_def) 
  qed
next
  case (If b cA cB)
  then have "c2 = (if ss1 (VN b) \<noteq> Some (EV (Num 0)) then cA else cB)" by auto
  moreover have "b \<in> set (enumerate_variables (IF b\<noteq>0 THEN cA ELSE cB))" by auto
  moreover then have "b \<in> set (enumerate_variables c)" 
    using If enumerate_subprograms_enumerate_variables by blast
  ultimately show ?case using If
    by (fastforce simp: imp_minus_sas_plus_equivalent_states_def)
next
  case (While b cA)
  then have "c2 = (if ss1 (VN b) \<noteq> Some (EV (Num 0)) then cA ;; WHILE b \<noteq>0 DO cA else SKIP)" 
    by auto
  moreover have "b \<in> set (enumerate_variables (WHILE b\<noteq>0 DO cA))" by auto
  moreover then have "b \<in> set (enumerate_variables c)" 
    using While enumerate_subprograms_enumerate_variables by blast
  ultimately show ?case using While enumerate_subprograms_enumerate_variables 
    by (fastforce simp: imp_minus_sas_plus_equivalent_states_def)
qed auto

lemma imp_minus_minus_to_sas_plus_single_step:
   "(c1, is1) \<rightarrow>\<^bsub>r\<^esub> (c2, is2) \<Longrightarrow> cs = enumerate_subprograms c \<Longrightarrow> r = t * max_constant c 
  \<Longrightarrow> c1 \<in> set cs \<Longrightarrow> t > 0 
  \<Longrightarrow> (\<forall>v. EV (is1 v) \<in> set (domain c t))
  \<Longrightarrow> imp_minus_sas_plus_equivalent_states c c1 is1 ss1
  \<Longrightarrow> (\<exists>op \<in> set (com_to_operators c1 (domain c t)). \<exists>ss2.
     imp_minus_sas_plus_equivalent_states c c2 is2 (execute_operator_sas_plus ss1 op)
    \<and> is_operator_applicable_in ss1 op)"
proof (induction c1 is1 r c2 is2 arbitrary: ss1 rule: \<omega>_small_step_induct)
  case (Assign x a s r)
  let ?ss2 = "ss1(VN x \<mapsto> EV (eval a s (t * max_constant c)), PC \<mapsto> PCV SKIP)"
  have "(\<exists>op \<in> set (com_to_operators (x ::= a) (domain c t)). 
     imp_minus_sas_plus_equivalent_states c SKIP (s(x := eval a s (t * max_constant c)))  ?ss2
    \<and> is_operator_applicable_in ss1 op
    \<and> execute_operator_sas_plus ss1 op = ?ss2)" using Assign
  proof (cases a)
    case (A atom)
    then show ?thesis
    proof (cases atom)
      case (N val)
      then show ?thesis using Assign A
        by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def)
    next
      case (V var)
      have "var \<in> set (enumerate_variables c)" 
        using Assign A V enumerate_subprograms_enumerate_variables by fastforce
      then show ?thesis using Assign A V
        by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def)
    qed
  next
    case (Plus var val)
    then show ?thesis using Assign Plus 
        enumerate_subprograms_enumerate_variables enumerate_variables_def
      by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def split: EVal.splits)
  next
    case (Sub var val)
    then show ?thesis using Assign Sub 
        enumerate_subprograms_enumerate_variables enumerate_variables_def
      by (auto simp: imp_minus_sas_plus_equivalent_states_def list_all_def split: EVal.splits)
  qed 
  then show ?case using Assign by metis
next
  case (Seq2 c\<^sub>1 s r c\<^sub>1' s' c\<^sub>2)
  let ?ss1' = "ss1(PC \<mapsto> PCV c\<^sub>1)"
  have "c\<^sub>1 \<in> set (enumerate_subprograms (c\<^sub>1 ;; c\<^sub>2))" using c_in_all_subprograms_c by auto
  then have "c\<^sub>1 \<in> set (enumerate_subprograms c)" using Seq2 enumerate_subprograms_transitive by blast
  then have "(\<exists>op' \<in> set (com_to_operators c\<^sub>1 (domain c t)). \<exists>ss2'.
   imp_minus_sas_plus_equivalent_states c c\<^sub>1' s' ss2'
    \<and> is_operator_applicable_in ?ss1' op'
    \<and> execute_operator_sas_plus ?ss1' op' = ss2')" 
    using Seq2 by (auto simp: imp_minus_sas_plus_equivalent_states_def)
  then obtain op' ss2' where op'_def: "(op' \<in> set (com_to_operators c\<^sub>1 (domain c t)) \<and>
   imp_minus_sas_plus_equivalent_states c c\<^sub>1' s' ss2'
    \<and> is_operator_applicable_in ?ss1' op'
    \<and> execute_operator_sas_plus ?ss1' op' = ss2')" by blast
  let ?op = "\<lparr> precondition_of = 
        list_update (precondition_of op') 0 (PC, PCV (c\<^sub>1 ;; c\<^sub>2)),
        effect_of = 
        list_update (effect_of op') 0 (PC, PCV (c\<^sub>1' ;; c\<^sub>2))\<rparr>"
  let ?ss2 = "ss2'(PC \<mapsto> PCV (c\<^sub>1' ;; c\<^sub>2))"
  have "?op \<in> set (com_to_operators (c\<^sub>1 ;; c\<^sub>2) (domain c t))" 
    using Seq2 op'_def by (auto simp: pc_of_op)
  moreover have "imp_minus_sas_plus_equivalent_states c (c\<^sub>1' ;; c\<^sub>2) s' ?ss2" 
    using op'_def by (auto simp: imp_minus_sas_plus_equivalent_states_def)
  moreover have "is_operator_applicable_in ss1 ?op" 
    using op'_def Seq2 by (auto simp: applicable_in_PC_updated imp_minus_sas_plus_equivalent_states_def)
  moreover have "?ss2 = execute_operator_sas_plus ss1 ?op"
    using Seq2 op'_def by (auto simp: imp_minus_sas_plus_equivalent_states_def)
  ultimately show ?case using Seq2 by metis
next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  then have "b \<in> set (enumerate_variables c)" 
    using enumerate_subprograms_enumerate_variables by fastforce
  then show ?case using IfTrue 
    by (auto simp: imp_minus_sas_plus_equivalent_states_def)
     (metis (mono_tags, lifting) list_all_iff)
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  then have "b \<in> set (enumerate_variables c)" 
    using enumerate_subprograms_enumerate_variables by fastforce
  then show ?case using IfFalse
    by (auto simp: imp_minus_sas_plus_equivalent_states_def)
next
  case (WhileTrue s b c1)
  then have "b \<in> set (enumerate_variables c)" 
    using enumerate_subprograms_enumerate_variables by fastforce
  then show ?case using WhileTrue 
    by (auto simp: imp_minus_sas_plus_equivalent_states_def)
      (metis (mono_tags, lifting) list_all_iff)
next
  case (WhileFalse s b c1)
  then have "b \<in> set (enumerate_variables c)" 
    using enumerate_subprograms_enumerate_variables by fastforce
  then show ?case using WhileFalse
    by (auto simp: imp_minus_sas_plus_equivalent_states_def)
qed (auto simp: imp_minus_sas_plus_equivalent_states_def)

end