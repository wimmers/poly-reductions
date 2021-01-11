\<^marker>\<open>creator Florian Keßler\<close>

section "Correctness"

theory Correctness imports Reduction SAS_Plus_Plus_Semantics
begin 

definition imp_minus_state_to_sas_plus :: "(com \<times> imp_state) \<Rightarrow> sas_state" where
"imp_minus_state_to_sas_plus ci = ((\<lambda>x. Some (EV x)) \<circ>\<^sub>m (snd ci)
  \<circ>\<^sub>m (\<lambda>x. (case x of VN v \<Rightarrow> Some v)))
  (PC \<mapsto> PCV (fst ci))"

definition sas_plus_state_to_imp_minus:: "sas_state \<Rightarrow> (com \<times> imp_state)" where
"sas_plus_state_to_imp_minus ss = ((case (the (ss PC)) of (PCV c) \<Rightarrow> c), 
  (\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m ss \<circ>\<^sub>m (\<lambda>x. Some (VN x)))"

definition sane_sas_plus_state:: "sas_state \<Rightarrow> bool" where
"sane_sas_plus_state ss \<equiv> (\<exists>x. ss PC = Some (PCV x)) \<and> 
  (\<forall>v. VN v \<in> dom ss \<longrightarrow> (\<exists>x. ss (VN v) = Some (EV x)))"

lemma [simp]: "sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is)) = (c, is)" 
proof -
  have "(snd (sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is)))) x = is x" for x
    by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
        map_comp_def option.case_eq_if)
  then show ?thesis
    by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def)
qed

lemma [simp]: 
  assumes "sane_sas_plus_state ss "
  shows "imp_minus_state_to_sas_plus (sas_plus_state_to_imp_minus ss) = ss" 
proof -
  have "(imp_minus_state_to_sas_plus (sas_plus_state_to_imp_minus ss)) x = ss x" for x using assms
    by (fastforce simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
        sane_sas_plus_state_def option.case_eq_if map_comp_def split: variable.splits)
  then show ?thesis by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def)
qed

lemma [simp]: "sas_plus_state_to_imp_minus 
  ((imp_minus_state_to_sas_plus (c, is))(VN x \<mapsto> EV y, PC \<mapsto> PCV z)) 
  = (z, (is(x \<mapsto> y)))"
  by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def option.case_eq_if 
      map_comp_def)

lemma [simp]: "(imp_minus_state_to_sas_plus (c, s1) = imp_minus_state_to_sas_plus (c, s2))
  \<longleftrightarrow> s1 = s2" 
proof
  assume a: "imp_minus_state_to_sas_plus (c, s1) = imp_minus_state_to_sas_plus (c, s2)"
  have "\<forall>v. (s1 v = s2 v)"
  proof (rule ccontr)
    assume "\<not> (\<forall>v. s1 v = s2 v)"
    then obtain v where "s1 v \<noteq> s2 v" by blast
    then have "imp_minus_state_to_sas_plus (c, s1) (VN v) \<noteq> imp_minus_state_to_sas_plus (c, s2) (VN v)"
      by (auto simp: imp_minus_state_to_sas_plus_def map_comp_def domD domIff split: option.splits)
    then show "False" using a by simp
  qed
  then show "s1 = s2" by auto
qed auto

lemma sas_plus_state_to_imp_minus_of_effect: 
  assumes "op \<in> set (com_to_operators c1 (domain cA t))"
  shows "sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op)) 
  = (pc_to_com (effect_of op), is 
  ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m (map_of (effect_of op)) \<circ>\<^sub>m (\<lambda>x. Some (VN x))))"
proof -
  have "fst (sas_plus_state_to_imp_minus 
    (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))) = pc_to_com (effect_of op)"
    using assms by(auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
                   com_to_operators_variables_distinct) 
  moreover have "snd (sas_plus_state_to_imp_minus 
    (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))) a = (is ++ ((\<lambda>x. (case x of 
      EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m (map_of (effect_of op)) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a"
    for a using assms
    by(auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
      option.case_eq_if map_comp_def map_add_def com_to_operators_variables_distinct 
      split: domain_element.splits)
  moreover then have "snd (sas_plus_state_to_imp_minus 
    (imp_minus_state_to_sas_plus (c, is) ++ map_of (effect_of op))) = (is 
   ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m (map_of (effect_of op)) \<circ>\<^sub>m (\<lambda>x. Some (VN x))))"
    by auto
  ultimately show ?thesis using assms by (metis prod.collapse)
qed

lemma [simp]: "imp_minus_state_to_sas_plus (c1, is) = ss
  \<Longrightarrow> v \<in> set (enumerate_variables c)
  \<Longrightarrow> is v = Some (Num 0) \<longleftrightarrow> ss (VN v) = Some (EV (Num 0))"
  by (auto simp: imp_minus_state_to_sas_plus_def option.case_eq_if map_comp_def split: if_splits)

lemma [simp]: "(imp_minus_state_to_sas_plus (c1, is1))(PC \<mapsto> PCV c2) 
  = imp_minus_state_to_sas_plus (c2, is1)"
  by(auto simp: imp_minus_state_to_sas_plus_def option.case_eq_if)

lemma [simp]: "sas_plus_state_to_imp_minus
  (\<lambda>a. if a = PC then Some (PCV c1)
       else ss a)
  = (c1, snd (sas_plus_state_to_imp_minus ss))"
  by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def map_comp_def)

lemma [simp]: "sas_plus_state_to_imp_minus (ss(PC \<mapsto> PCV c)) 
  = (c, snd (sas_plus_state_to_imp_minus ss))"
  by (auto simp: sas_plus_state_to_imp_minus_def map_comp_def)

lemma [simp]: "(imp_minus_state_to_sas_plus (c, s) (VN x) = Some y) 
  \<longleftrightarrow> ((map_option EV (s x)) = Some y)"
  by (simp add: imp_minus_state_to_sas_plus_def map_comp_Some_iff)

lemma imp_minus_state_to_sas_plus_of_effect: 
  assumes "op \<in> set (com_to_operators cB (domain cA t))"
  shows "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2) =
    imp_minus_state_to_sas_plus (c2, s')) \<longleftrightarrow> ((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')"
proof
  assume *: "(imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2) 
    = imp_minus_state_to_sas_plus (c2, s')"
  have "\<forall>a. (s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a = s' a"
  proof(rule ccontr)
    assume "\<not>(\<forall>a. (s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
      \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a = s' a)"
    then obtain a where "(s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
      \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) a \<noteq> s' a" by auto
    then have "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2)) (VN a)
      \<noteq> imp_minus_state_to_sas_plus (c2, s') (VN a)"
      by(auto simp: imp_minus_state_to_sas_plus_def map_comp_def map_add_def domD domIff 
            split: option.splits)
    then show "False" using * by auto
  qed
  then show "((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')" by auto
next
  assume *: "((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')"
  then have "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2)) a
      = imp_minus_state_to_sas_plus (c2, s') a" for a
    using assms by(cases a) (auto simp: com_to_operators_variables_distinct 
        imp_minus_state_to_sas_plus_def map_comp_def map_add_def option.case_eq_if
        split: option.splits domain_element.splits)
  then show "(imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))(PC \<mapsto> PCV c2) 
    = imp_minus_state_to_sas_plus (c2, s')" by auto
qed

lemma imp_minus_state_to_sas_plus_of_effect': 
  assumes "op \<in> set (com_to_operators cB (domain cA t))"
  shows "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op)) =
    imp_minus_state_to_sas_plus (c2, s')) \<longleftrightarrow> ((pc_to_com (effect_of op) = c2) \<and> 
  (s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')"
proof -
  have "imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op) = 
    ((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))
    (PC \<mapsto> PCV (pc_to_com (effect_of op))))"
    using assms com_to_operators_variables_distinct by auto
  moreover have "((imp_minus_state_to_sas_plus (c1, s) ++ map_of (effect_of op))
  (PC \<mapsto> PCV (pc_to_com (effect_of op))) =
    imp_minus_state_to_sas_plus ((pc_to_com (effect_of op)), s')) 
    \<longleftrightarrow> ((s ++ ((\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) 
    \<circ>\<^sub>m map_of (effect_of op) \<circ>\<^sub>m (\<lambda>x. Some (VN x)))) = s')" 
    using assms imp_minus_state_to_sas_plus_of_effect by simp
  ultimately show ?thesis using assms imp_minus_state_to_sas_plus_def map_upd_eqD1 by fastforce
qed

lemma [simp]: "(\<lambda>v. case v of VN v \<Rightarrow> f v | PC \<Rightarrow> Some x) =
    (\<lambda>v. case v of VN v \<Rightarrow> f v | PC \<Rightarrow> y)(PC \<mapsto> x)"
proof - 
  have "(case v of VN v \<Rightarrow> f v | PC \<Rightarrow> Some x) 
    = ((\<lambda>v. case v of VN v \<Rightarrow> f v | PC \<Rightarrow> y)(PC \<mapsto> x)) v" for v
    by (cases v) auto
  then show ?thesis by auto
qed

lemma updated_state_is_sane:
  assumes "op \<in> set (com_to_operators c (domain cA t))" 
    "sane_sas_plus_state ss1"
  shows "sane_sas_plus_state (ss1 \<then>\<^sub>+ op)"
proof -
  have "\<exists>x. (VN v, EV x) \<in> set (effect_of op) \<or> map_of (effect_of op) (VN v) = None" for v
    using assms variables_in_effect by simp
  then show ?thesis using assms
    by(auto simp: sane_sas_plus_state_def com_to_operators_variables_distinct map_add_Some_iff)
qed

lemma [simp]: "(\<lambda>a. if a = PC then Some (PCV c2) 
   else (imp_minus_state_to_sas_plus (c1, is1)) a) 
    = imp_minus_state_to_sas_plus (c2, is1)"
proof -
  have "(if a = PC then Some (PCV c2) else ((imp_minus_state_to_sas_plus (c1, is1)) a))
    = (imp_minus_state_to_sas_plus (c2, is1)) a" for a
    by (auto simp: imp_minus_state_to_sas_plus_def split: variable.splits)
  then show ?thesis by auto
qed

lemma [simp]: 
  assumes "y \<in> set (domain c t)" 
  shows "imp_minus_state_to_sas_plus (c1, s)(VN x \<mapsto> y, PC \<mapsto> PCV z) =
  imp_minus_state_to_sas_plus (z, s(x := (case y of EV y' \<Rightarrow> Some y' | _ \<Rightarrow> None)))"
proof-
  have "(imp_minus_state_to_sas_plus (c1, s)(VN x \<mapsto> y, PC \<mapsto> PCV z)) a =
  imp_minus_state_to_sas_plus (z, s(x := (case y of EV y' \<Rightarrow> Some y' | _ \<Rightarrow> None))) a" for a
    using assms apply(auto simp: imp_minus_state_to_sas_plus_def domain_def Let_def map_comp_def 
          split: option.splits domain_element.splits)
    by (metis option.inject variable.exhaust variable.simps)+
  then show ?thesis by auto
qed


lemma [simp]: "(\<lambda>a. if a = PC then Some (PCV c2) 
   else (imp_minus_state_to_sas_plus (c1, is1)(VN x \<mapsto> EV y)) a) 
    = imp_minus_state_to_sas_plus (c2, is1(x \<mapsto> y))"
proof -
  have "(if a = PC then Some (PCV c2) else ((imp_minus_state_to_sas_plus (c1, is1)(VN x \<mapsto> EV y)) a))
    = (imp_minus_state_to_sas_plus (c2, is1(x \<mapsto> y))) a" for a
    by (auto simp: imp_minus_state_to_sas_plus_def map_comp_def split: variable.splits)
  then show ?thesis by auto
qed

lemma [simp]: 
  assumes "y \<in> set (domain c t)"
  shows "sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus 
  (x ::= A (V var), is1)(VN x \<mapsto> y, PC \<mapsto> PCV z)) =
          (z, is1(x \<mapsto> (case y of EV y' \<Rightarrow> y')))"
proof -
  have "(snd (sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus
  (x ::= A (V var), is1)(VN x \<mapsto> y, PC \<mapsto> PCV z)))) a =
           (is1(x \<mapsto> (case y of EV y' \<Rightarrow> y'))) a" for a using assms
    by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def option.case_eq_if
        domain_def Let_def map_comp_def split: variable.splits)
  then show ?thesis 
    using assms by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def)
qed

lemma [simp]: 
  "snd (sas_plus_state_to_imp_minus
                (imp_minus_state_to_sas_plus (c, is)(VN x \<mapsto> y))) 
    = is(x := (case y of EV y' \<Rightarrow> Some y' | _ \<Rightarrow> None))"
  by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
      domain_def Let_def map_comp_def option.case_eq_if)

lemma [simp]: "(is(x := case y of EV y' \<Rightarrow> Some y' | _ \<Rightarrow> None) = is(x \<mapsto> z)) 
  \<longleftrightarrow> (y = EV z)"
  apply(cases y)
  using fun_upd_eqD map_upd_eqD1 by fastforce+

lemma [simp]: " s(x := case z of EV z' \<Rightarrow> Some z' | _ \<Rightarrow> None) = (\<lambda>a. if a = x then Some y else s a)
  \<longleftrightarrow> (z = EV y)"
  apply(cases z)
   apply(auto)
   apply(smt fun_upd_same option.inject)
  by (smt fun_upd_apply option.distinct)

lemma [simp]: "(s(x \<mapsto> y) = (\<lambda>a. if a = x then Some z else s a))
  \<longleftrightarrow> (y = z)"
  apply(auto)
  by (meson map_upd_Some_unfold)

lemma [simp]: "[VN v \<mapsto> y, PC \<mapsto> x] \<subseteq>\<^sub>m s = (s PC = Some x \<and> s (VN v) = Some y)"
  by (auto simp: map_le_def)

lemma [simp]: "[VN v \<mapsto> y, PC \<mapsto> x] \<subseteq>\<^sub>m (imp_minus_state_to_sas_plus (c1, is)) 
  = (x = PCV c1 \<and> map_option EV (is v) = Some y)"
  by (auto simp: map_le_def imp_minus_state_to_sas_plus_def option.case_eq_if map_comp_def)

lemma [simp]: "op \<in> set (com_to_operators c1 d) \<Longrightarrow> 
  map_of (precondition_of op)(PC \<mapsto> PCV c2) \<subseteq>\<^sub>m imp_minus_state_to_sas_plus (c2, s)
  \<longleftrightarrow>  map_of (precondition_of op) \<subseteq>\<^sub>m imp_minus_state_to_sas_plus (c1, s)"
  by(auto simp: imp_minus_state_to_sas_plus_def map_le_def)

lemma applicable_in_imp_minus_then[simp]: 
  "is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is)) 
  \<lparr>precondition_of = [(PC, x), (VN v, y)], effect_of = effect\<rparr> 
  \<longleftrightarrow> (x = PCV c1 \<and> map_option EV (is v) = Some y)"
  by (auto simp: map_le_def imp_minus_state_to_sas_plus_def option.case_eq_if map_comp_def)

lemma [simp]: "op \<in> set ((imp_minus_minus_to_sas_plus c I G t)\<^sub>\<O>\<^sub>+) 
  \<Longrightarrow> is_operator_applicable_in s op 
  \<Longrightarrow> op \<in> set (com_to_operators (fst (sas_plus_state_to_imp_minus s)) (domain c t))"
  apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def 
      sas_plus_state_to_imp_minus_def)
proof -
  fix x
  assume  "map_of (precondition_of op) \<subseteq>\<^sub>m s"
    "op \<in> set (com_to_operators x (domain c t))"
  moreover then have "(map_of (precondition_of op)) PC = Some (PCV x)" by auto
  ultimately have "the (s PC) = PCV x" by (metis domI map_le_def option.sel)
  then show "op \<in> set (com_to_operators (case the (s PC) of PCV c \<Rightarrow> c) (domain c t))" 
    by (simp add: \<open>op \<in> set (com_to_operators x (domain c t))\<close>)
qed

lemma [simp]: "[PC \<mapsto> x] \<subseteq>\<^sub>m s \<longleftrightarrow> (s PC = Some x)" 
  by (auto simp: map_le_def)

lemma [simp]: "[PC \<mapsto> x] \<subseteq>\<^sub>m (imp_minus_state_to_sas_plus (c1, is)) 
  = (x = PCV c1)"
  by (auto simp: map_le_def imp_minus_state_to_sas_plus_def)

lemma [simp]: "(imp_minus_state_to_sas_plus (c1, is)) PC = Some (PCV c1)" 
  by (simp add: imp_minus_state_to_sas_plus_def)

lemma [simp]: "(imp_minus_state_to_sas_plus (c, is) (VN x) = Some (EV y)) 
  \<longleftrightarrow> (is x = Some y)"
  by(auto simp: imp_minus_state_to_sas_plus_def map_comp_Some_iff)

lemma [simp]: "imp_minus_state_to_sas_plus (c, is) (VN x) = Some y \<Longrightarrow>
       (y \<noteq> EV (Num 0)) \<longleftrightarrow> (is x \<noteq> Some (Num 0))"
  by(auto simp: imp_minus_state_to_sas_plus_def map_comp_Some_iff)

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

lemma pc_of_op: 
  assumes "op \<in> set (com_to_operators c2 d)"
    "ss2 = imp_minus_state_to_sas_plus (c1, is)" 
    "ss1 \<then>\<^sub>+ op = ss2"
  shows "pc_to_com (effect_of op) = c1" 
proof -
  have "(ss1 \<then>\<^sub>+ op) PC = Some (PCV c1)" using assms by simp
  then show ?thesis using assms com_to_operators_variables_distinct by auto
qed

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
  "op \<in> set (com_to_operators c1 (domain c t))
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c) \<Longrightarrow> t > 0 
  \<Longrightarrow> is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is1)) op
  \<Longrightarrow> (c1, is1) \<rightarrow>\<^bsub>t * max_constant c\<^esub> 
  sas_plus_state_to_imp_minus ((imp_minus_state_to_sas_plus (c1, is1)) \<then>\<^sub>+ op)"
proof (induction c1 arbitrary: op is1)
  case (Assign x a)
  have "sas_plus_state_to_imp_minus ((imp_minus_state_to_sas_plus ((x ::= a), is1)) \<then>\<^sub>+ op)
    = (SKIP, is1(x \<mapsto> eval a is1 (t * max_constant c)))" using Assign
  proof (cases a)
    case (A atom)
    then show ?thesis using Assign
    proof (cases atom)
      case (V var)
      have "var \<in> set (enumerate_variables c)" 
        using Assign A V enumerate_subprograms_enumerate_variables by fastforce
      then show ?thesis using Assign A V by auto
    qed auto
  next
    case (Plus var val)
    then have "precondition_of op = [(PC, PCV (x ::= a)), (VN var, EV (the (is1 var)))]"
      using Assign Plus applicable_in_imp_minus_then by auto
    then show ?thesis using Assign Plus apply auto using num_in_domain_iff by metis
  next
    case (Sub var val)
    then have "precondition_of op = [(PC, PCV (x ::= a)), (VN var, EV (the (is1 var)))]"
      using Assign Sub applicable_in_imp_minus_then by auto
    then show ?thesis using Assign Sub apply auto using num_in_domain_iff by metis
  qed
  then show ?case using Assign by auto
next
  case (Seq cA cB)
  have "cA = SKIP \<or> cA \<noteq> SKIP" by auto
  then show ?case using Seq
  proof (elim disjE)
    assume "cA \<noteq> SKIP"
    then obtain op' where op'_def: "op' \<in> set (com_to_operators cA (domain c t)) 
      \<and> op = (let c1' = pc_to_com (effect_of op') in 
      \<lparr> precondition_of = list_update (precondition_of op') 0 (PC, PCV (cA ;; cB)),
        effect_of = list_update (effect_of op') 0 (PC, PCV (c1' ;; cB))\<rparr>)" using Seq by auto
    let ?c1' = "pc_to_com (effect_of op')"
    let ?ss1' = "(imp_minus_state_to_sas_plus ((cA ;; cB), is1))(PC \<mapsto> PCV cA)"
    let ?ss2' = "((imp_minus_state_to_sas_plus ((cA ;; cB), is1)) \<then>\<^sub>+ op)(PC \<mapsto> PCV ?c1')"
    have "cA \<in> set (enumerate_subprograms (cA ;; cB))" using c_in_all_subprograms_c by auto
    then have "cA \<in> set (enumerate_subprograms c)" 
      using Seq enumerate_subprograms_transitive by blast
    moreover have "imp_minus_state_to_sas_plus (cA, is1) = ?ss1'" by auto
    moreover have "map_of (precondition_of op') = (map_of (precondition_of op))(PC \<mapsto> PCV cA)"
      using op'_def Seq com_to_operators_variables_distinct by auto
    moreover then have "is_operator_applicable_in ?ss1' op'" 
      using Seq op'_def by (metis is_operator_applicable_in_def map_le_upd)
    moreover have "map_of (effect_of op') = map_of (effect_of op)(PC \<mapsto> PCV (pc_to_com (effect_of op')))"
      using op'_def Seq com_to_operators_variables_distinct by auto
    moreover then have "?ss1' \<then>\<^sub>+ op' = ?ss2'" using Seq op'_def
      using calculation(3) effect_in_updated by blast
    (* TODO: simplify this proof (Seq(1)) *)
    ultimately have "(cA, is1) \<rightarrow>\<^bsub>t * max_constant c\<^esub> sas_plus_state_to_imp_minus ?ss2'" 
      using Seq op'_def by metis
    then show ?thesis using Seq op'_def by auto
  qed auto
qed auto

lemma sas_plus_to_imp_minus_minus:
  "set ops \<subseteq> set ((imp_minus_minus_to_sas_plus c I G t)\<^sub>\<O>\<^sub>+) 
  \<Longrightarrow> t > 0
  \<Longrightarrow> length ops < t
  \<Longrightarrow> sane_sas_plus_state ss1
  \<Longrightarrow> execute_serial_plan_sas_plus ss1 ops = ss2
  \<Longrightarrow> (\<exists>t'. t' \<le> length ops 
  \<and> sas_plus_state_to_imp_minus ss1 \<rightarrow>\<^bsub>t * max_constant c\<^esub>\<^bsup>t'\<^esup> sas_plus_state_to_imp_minus ss2)"
proof (induction ops arbitrary: ss1)
  case (Cons op ops)
  let ?c1 = "fst (sas_plus_state_to_imp_minus ss1)"
  let ?is1 = "snd (sas_plus_state_to_imp_minus ss1)"
  let ?ss1' = "ss1 \<then>\<^sub>+ op" 
  have "is_operator_applicable_in ss1 op \<or> \<not>(is_operator_applicable_in ss1 op)" by auto
  then show ?case using Cons
  proof (elim disjE)
    assume a: "is_operator_applicable_in ss1 op"
    then have op_in_cto_c1: "op \<in> set (com_to_operators ?c1 (domain c t))" using Cons by auto
    moreover then have "?c1 \<in> set (enumerate_subprograms c)" using Cons a 
      apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
      by (metis PC_of_precondition domain_element.simps op_in_cto_c1)
    ultimately have c1_to_c1': "(?c1, ?is1) \<rightarrow>\<^bsub>t * max_constant c\<^esub> sas_plus_state_to_imp_minus 
      (imp_minus_state_to_sas_plus (?c1, ?is1) \<then>\<^sub>+ op)" 
      apply(rule sas_plus_to_imp_minus_minus_single_step)
      using Cons a op_in_cto_c1 by auto
    moreover then have "execute_serial_plan_sas_plus ?ss1' ops = ss2"
      and "sane_sas_plus_state ?ss1'" 
      using Cons a op_in_cto_c1 updated_state_is_sane by auto 
    ultimately have "\<exists>t'. t' \<le> length ops \<and> sas_plus_state_to_imp_minus ?ss1' 
      \<rightarrow>\<^bsub>t * max_constant c\<^esub>\<^bsup>t'\<^esup> sas_plus_state_to_imp_minus ss2"
      using Cons by(auto)
    moreover have "imp_minus_state_to_sas_plus (?c1, ?is1) \<then>\<^sub>+ op = ?ss1'" using Cons by auto
    ultimately show ?case using c1_to_c1' by auto
  qed auto
qed auto

lemma imp_minus_minus_to_sas_plus_single_step:
   "(c1, is1) \<rightarrow>\<^bsub>r\<^esub> (c2, is2)  \<Longrightarrow> r = t * max_constant c 
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c)
  \<Longrightarrow> dom is1 = set (enumerate_variables c)
  \<Longrightarrow> (\<forall>v x. is1 v = Some (Num x) \<longrightarrow> x \<le> r)
  \<Longrightarrow> (\<exists>op \<in> set (com_to_operators c1 (domain c t)).
      execute_operator_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) op 
        =  imp_minus_state_to_sas_plus (c2, is2)
    \<and> is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is1)) op)"
proof (induction c1 is1 r c2 is2 rule: \<omega>_small_step_induct)
  case (Assign x a s r)
  let ?ss1 = "imp_minus_state_to_sas_plus (x ::= a, s)"
  let ?ss2 = "imp_minus_state_to_sas_plus (SKIP, s(x \<mapsto> eval a s (t * max_constant c)))"
  show ?case
  proof (cases a)
    case (A atom)
    then show ?thesis using Assign
    proof (cases atom)
      case (V var)
      have "var \<in> set (enumerate_variables c)" 
        using Assign A V enumerate_subprograms_enumerate_variables by fastforce
      then show ?thesis using Assign A V by (auto split: EVal.splits) force+
    qed auto
  next
    case (Plus var val)
    have "var \<in> set (enumerate_variables c)" 
      using Assign Plus enumerate_subprograms_enumerate_variables by fastforce
    then obtain y where  "s var = Some y" using Assign by force
    then show ?thesis using Assign Plus by (auto split: EVal.splits domain_element.splits)
  next
    case (Sub var val)
    have "var \<in> set (enumerate_variables c)" 
      using Assign Sub enumerate_subprograms_enumerate_variables by fastforce
    then obtain y where  "s var = Some y" using Assign by force
    then show ?thesis using Assign Sub by (auto split: EVal.splits domain_element.splits)
  qed
next
  case (Seq2 c\<^sub>1 s r c\<^sub>1' s' c\<^sub>2)
  have "c\<^sub>1 \<in> set (enumerate_subprograms (c\<^sub>1 ;; c\<^sub>2))" using c_in_all_subprograms_c by auto
  then have "c\<^sub>1 \<in> set (enumerate_subprograms c)" using Seq2 enumerate_subprograms_transitive by blast
  then obtain op' where op'_def: "op' \<in> set (com_to_operators c\<^sub>1 (domain c t)) \<and>
    execute_operator_sas_plus (imp_minus_state_to_sas_plus (c\<^sub>1, s)) op'
        =  imp_minus_state_to_sas_plus (c\<^sub>1', s')
    \<and> is_operator_applicable_in (imp_minus_state_to_sas_plus (c\<^sub>1, s)) op'" 
    using Seq2 by fastforce
  let ?op = "\<lparr> precondition_of = list_update (precondition_of op') 0 (PC, PCV (c\<^sub>1 ;; c\<^sub>2)),
        effect_of = list_update (effect_of op') 0 (PC, PCV (c\<^sub>1' ;; c\<^sub>2))\<rparr>"
  have "?op \<in> set (com_to_operators (c\<^sub>1 ;; c\<^sub>2) (domain c t))"
    and "execute_operator_sas_plus (imp_minus_state_to_sas_plus ((c\<^sub>1 ;; c\<^sub>2), s)) ?op 
        = imp_minus_state_to_sas_plus ((c\<^sub>1' ;; c\<^sub>2), s')"
    and "is_operator_applicable_in (imp_minus_state_to_sas_plus ((c\<^sub>1 ;; c\<^sub>2), s)) ?op"
    using Seq2 op'_def imp_minus_state_to_sas_plus_of_effect imp_minus_state_to_sas_plus_of_effect'
    by auto
  then show ?case using Seq2 by blast
next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  have "b \<in> set (enumerate_variables c)" 
      using IfTrue enumerate_subprograms_enumerate_variables by fastforce
  then obtain y where "s b = Some y" by (metis IfTrue domD)
  then show ?case using IfTrue by (cases y) auto 
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  have "b \<in> set (enumerate_variables c)" 
      using IfFalse enumerate_subprograms_enumerate_variables by fastforce
  then obtain y where "s b = Some y" by (metis IfFalse domD)
  then show ?case using IfFalse by (cases y) auto
next
  case (WhileTrue s b c1)
  have "b \<in> set (enumerate_variables c)" 
      using WhileTrue enumerate_subprograms_enumerate_variables by fastforce
  then obtain y where "s b = Some y" by (metis WhileTrue domD)
  then show ?case using WhileTrue by (cases y) auto
next
  case (WhileFalse s b c1)
  have "b \<in> set (enumerate_variables c)" 
      using WhileFalse enumerate_subprograms_enumerate_variables by fastforce
  then obtain y where "s b = Some y" by (metis WhileFalse domD)
  then show ?case using WhileFalse by (cases y) auto
qed auto

lemma imp_minus_minus_to_sas_plus:
   "(c1, is1) \<rightarrow>\<^bsub>t * max_constant c \<^esub>\<^bsup>t'\<^esup> (c2, is2)
  \<Longrightarrow> t' < t
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c)
  \<Longrightarrow> dom is1 = set (enumerate_variables c)
  \<Longrightarrow> (\<forall>v x. is1 v = Some (Num x) \<longrightarrow> x \<le> t * max_constant c)
  \<Longrightarrow> (\<exists>ops. set ops \<subseteq> set ((imp_minus_minus_to_sas_plus c I G t)\<^sub>\<O>\<^sub>+)
     \<and> length ops = t'
     \<and> (execute_serial_plan_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) ops)
        = imp_minus_state_to_sas_plus (c2, is2))"
proof (induction t' arbitrary: c1 is1)
  case (Suc t')
  then obtain c1' is1' where c1'_def: "(c1, is1) \<rightarrow>\<^bsub>t * max_constant c \<^esub> (c1', is1')
    \<and> (c1', is1') \<rightarrow>\<^bsub>t * max_constant c \<^esub>\<^bsup>t'\<^esup> (c2, is2)" by auto
  then obtain op where op_def: "op \<in> set (com_to_operators c1 (domain c t))
    \<and> execute_operator_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) op 
        =  imp_minus_state_to_sas_plus (c1', is1')
    \<and> is_operator_applicable_in (imp_minus_state_to_sas_plus (c1, is1)) op" 
    using imp_minus_minus_to_sas_plus_single_step Suc by metis
  have "max_constant c1 \<le> max_constant c" using Suc enumerate_subprograms_max_constant by simp
  then have "max_constant c1 \<le> t * max_constant c" using Suc(3) mult_eq_if by simp
  then have "dom is1' = set (enumerate_variables c)" 
    and "(\<forall>v x. is1' v = Some (Num x) \<longrightarrow> x \<le> t * max_constant c)" 
    using \<omega>_small_step_values_cant_exceed_bound_step[where ?c2.0="c1'"] c1'_def Suc 
        step_doesnt_add_variables
     apply (auto simp: domIff)
    by (metis Suc.prems(4) domD domIff option.simps(3) step_doesnt_add_variables)+
  moreover have "c1' \<in> set (enumerate_subprograms c)" using c1'_def 
      enumerate_subprograms_complete_step' enumerate_subprograms_transitive 
    apply(cases t) 
    using Suc.prems by blast+
  ultimately obtain ops where ops_def: "set ops \<subseteq> set ((imp_minus_minus_to_sas_plus c I G t)\<^sub>\<O>\<^sub>+)
     \<and> length ops = t'
     \<and> (execute_serial_plan_sas_plus (imp_minus_state_to_sas_plus (c1', is1')) ops)
        = imp_minus_state_to_sas_plus (c2, is2)"
    using Suc c1'_def Suc_lessD by blast
  let ?ops' = "op # ops"
  have "set ?ops' \<subseteq> set ((imp_minus_minus_to_sas_plus c I G t)\<^sub>\<O>\<^sub>+)
     \<and> length ?ops' = Suc t'
     \<and> (execute_serial_plan_sas_plus (imp_minus_state_to_sas_plus (c1, is1)) ?ops')
        = imp_minus_state_to_sas_plus (c2, is2)"
    using Suc c1'_def op_def ops_def
    by (auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
  then show ?case by blast
qed auto

lemma \<omega>_imp_minus_minus_to_sas_plus_plus:
  assumes "(c, is1) \<rightarrow>\<^bsub>t * max_constant c \<^esub>\<^bsup>t'\<^esup> (SKIP, is2)"
   "t' < t" 
   "dom is1 = set (enumerate_variables c)"
   "(\<forall>v x. is1 v = Some (Num x) \<longrightarrow> x \<le> t * max_constant c)"
   "I \<subseteq>\<^sub>m is1"
  shows "(\<exists>plan.
     is_serial_solution_for_problem (imp_minus_minus_to_sas_plus c I is2 t) plan
     \<and> length plan = t')"
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I is2 t"
  let ?I' = "imp_minus_state_to_sas_plus (c, is1)" 
  obtain plan where plan_def: "set plan \<subseteq> set ((?\<Psi>)\<^sub>\<O>\<^sub>+)
     \<and> length plan = t'
     \<and> (execute_serial_plan_sas_plus ?I' plan)
        = imp_minus_state_to_sas_plus (SKIP, is2)"
    using imp_minus_minus_to_sas_plus[OF assms(1)] assms c_in_all_subprograms_c by auto
  moreover then have "(?\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus ?I' plan"
    and "dom ?I' = set (((?\<Psi>))\<^sub>\<V>\<^sub>+)"
    and "((?\<Psi>)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m ?I'"
    using assms plan_def
    apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def sas_state_by_pc_and_vars_def 
        imp_minus_state_to_sas_plus_def map_comp_def map_le_def split: option.splits variable.splits)
    by auto
  ultimately have "is_serial_solution_for_problem ?\<Psi> plan" 
    using assms
    by(auto simp: is_serial_solution_for_problem_def Let_def list_all_def ListMem_iff)
  then show ?thesis using plan_def by blast
qed

end