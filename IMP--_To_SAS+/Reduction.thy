\<^marker>\<open>creator Florian Keßler\<close>

section "Reduction"

theory Reduction imports  SAS_Plus_Plus_Representation Omega_Small_StepT
begin

datatype domain_element = EV EVal | PCV com

definition domain :: "com \<Rightarrow> nat \<Rightarrow> domain_element list" where
"domain c t = (let m = max_constant c in map (\<lambda>i. EV (Num i))  [0 ..<(t * m + 1)]) @ [EV \<omega>]"

lemma zero_in_domain[simp]: "ListMem (EV (Num 0)) (domain c t)"
  by (auto simp: domain_def Let_def ListMem_iff)

lemma omega_in_domain[simp]: "ListMem (EV \<omega>) (domain c t)"
  by (auto simp: domain_def Let_def ListMem_iff)

lemma [simp]: "(EV \<omega>) \<in> set (domain c t)"
  by (auto simp: domain_def Let_def ListMem_iff)

lemma num_in_domain_iff[simp]: "(EV (Num x)) \<in> set (domain c t) = (x \<le> t * (max_constant c))"
  by (auto simp: domain_def Let_def)

lemma [simp]: "((PCV i) \<in> set (domain c t)) = False" 
  by (auto simp: domain_def Let_def)

lemma [simp]: "domain c t \<noteq> []"
  by (simp add: domain_def)

datatype variable = VN vname | PC

type_synonym operator = "(variable, domain_element) sas_plus_operator"
type_synonym sas_state = "(variable, domain_element) State_Variable_Representation.state"
type_synonym imp_state = EState
type_synonym problem = "(variable, domain_element) sas_plus_problem"

definition pc_to_com :: "(variable \<times> domain_element) list \<Rightarrow> com" where
"pc_to_com l = (case  l ! 0 of (_, PCV x) \<Rightarrow> x)"

fun com_to_operators :: "com \<Rightarrow> domain_element list \<Rightarrow> operator list" where
"com_to_operators (SKIP) d = []" |
"com_to_operators (v ::= aexp) d = 
  (case aexp of
    A a \<Rightarrow> (case a of
      N val \<Rightarrow> [\<lparr> precondition_of = [(PC, PCV (v ::= aexp))], 
                  effect_of = [(PC, PCV SKIP), (VN v, (if (EV (Num val)) \<in> set d then EV (Num val) else EV \<omega>))]\<rparr>] |
      V var \<Rightarrow> map (\<lambda> x. \<lparr> precondition_of = [(PC, PCV (v ::= aexp)), (VN var, x)], 
                           effect_of = [(PC, PCV SKIP), (VN v, x)]\<rparr>) d) |
    Plus a b \<Rightarrow> map (\<lambda> x.  \<lparr> precondition_of = [(PC, PCV (v ::= aexp)), (VN a, x)], 
                             effect_of = [(PC, PCV SKIP), (VN v, (case x of 
      EV (Num y) \<Rightarrow> EV (if EV (Num (y + b)) \<in> set d then Num (y + b) else \<omega>) | 
      _ \<Rightarrow> EV \<omega>))]\<rparr>) d | 
    Sub a b \<Rightarrow> map (\<lambda> x.  \<lparr> precondition_of = [(PC, PCV (v ::= aexp)), (VN a, x)], 
                            effect_of = [(PC, PCV SKIP), (VN v, (case x of 
      EV (Num y) \<Rightarrow> EV (if EV (Num (y - b)) \<in> set d then Num (y - b) else \<omega>) | 
      _ \<Rightarrow> EV \<omega>))]\<rparr>) d)" |
"com_to_operators (c1;; c2) d = 
  (if c1 = SKIP then  [\<lparr> precondition_of = [(PC, PCV (c1 ;; c2))],
                                                   effect_of = [(PC, PCV c2)]\<rparr>]
   else (let ops = com_to_operators c1 d in map (\<lambda> op. 
    (let c1' = pc_to_com (effect_of op) in 
      \<lparr> precondition_of = 
        list_update (precondition_of op) 0 (PC, PCV (c1 ;; c2)),
        effect_of = 
        list_update (effect_of op) 0 (PC, PCV (c1' ;; c2))\<rparr>)) ops))" |
"com_to_operators (IF v\<noteq>0 THEN c1 ELSE c2) d = (let i = PCV (IF v\<noteq>0 THEN c1 ELSE c2)
   in map (\<lambda> x. 
    \<lparr> precondition_of = [(PC, i), (VN v, x)], 
      effect_of = [(PC, PCV (if x = EV (Num 0) then c2 else c1))]\<rparr>) d)" |
"com_to_operators (WHILE v\<noteq>0 DO c) d = (let i = PCV (WHILE v\<noteq>0 DO c) ;
  j = PCV (c ;; (WHILE v\<noteq>0 DO c)); k = PCV SKIP in map (\<lambda> x. 
    \<lparr> precondition_of = [(PC, i), (VN v, x)], 
      effect_of = [(PC, (if x = EV (Num 0) then k else j))]\<rparr>) d)"

lemma precondition_nonempty[simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> length (precondition_of op) > 0"
  by (induction c d arbitrary: op rule: com_to_operators.induct)
    (auto split: aexp.splits if_splits atomExp.splits)

lemma effect_nonempty[simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> length (effect_of op) > 0"
  by (induction c d arbitrary: op rule: com_to_operators.induct)
    (auto split: aexp.splits if_splits atomExp.splits)

lemma PC_in_effect_precondition: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> (\<exists>y1 y2. (PC, PCV y1) = (precondition_of op) ! 0 \<and> (PC, PCV y2) = (effect_of op) ! 0)"
proof(induction c d arbitrary: op rule: com_to_operators.induct)
  case (2 v aexp d)
  then show ?case by (cases aexp) (auto simp: Let_def split: atomExp.splits)
next
  case (3 c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case using 3 precondition_nonempty effect_nonempty by (auto split: if_splits)
qed auto

lemma fst_of_effect[simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> fst (effect_of op ! 0) = PC" 
  using PC_in_effect_precondition by (metis fst_conv)

lemma fst_of_precondition[simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> fst (precondition_of op ! 0) = PC" 
  using PC_in_effect_precondition by (metis fst_conv)

lemma com_to_operators_seq_registers:
  assumes "c1 \<noteq> SKIP" and  "op \<in> set (com_to_operators (c1 ;; c2) d)" 
    and "(VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op)"
  shows "\<exists>op'. op' \<in> set (com_to_operators c1 d) 
          \<and> ((VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op'))"
proof -
  obtain op' where "op' \<in> set (com_to_operators c1 d) 
    \<and> op = (let c1' = pc_to_com (effect_of op') in 
      \<lparr> precondition_of = 
        list_update (precondition_of op') 0 (PC, PCV (c1 ;; c2)),
        effect_of = 
        list_update (effect_of op') 0 (PC, PCV (c1' ;; c2))\<rparr>)" using assms by auto
  moreover then have "(VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op')" 
    using assms PC_in_effect_precondition precondition_nonempty effect_nonempty 
    by (metis (no_types, lifting) eq_fst_iff in_set_conv_nth length_list_update nth_list_update 
        sas_plus_operator.select_convs sas_plus_operator.select_convs variable.simps)
  ultimately show ?thesis by auto
qed

lemma com_to_operators_registers_in_d: 
  "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> ((VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op)) \<Longrightarrow> EV \<omega> \<in> set d 
  \<Longrightarrow> y \<in> set d"
proof (induction c d arbitrary: op rule: com_to_operators.induct)
  case (3 c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case
  proof (elim disjE)
    assume "c1 \<noteq> SKIP"
    then show ?thesis using 3 com_to_operators_seq_registers by blast
  next
    assume "c1 = SKIP" 
    then show ?thesis using 3 by auto
  qed
qed (auto simp: Let_def split: aexp.splits atomExp.splits if_splits domain_element.splits EVal.splits)

lemma update_preserve_distinct: "distinct (map fst l) \<Longrightarrow> fst (l ! 0) = x 
  \<Longrightarrow> distinct (map fst (l[0 := (x, y)]))"
  by (induction l) auto

lemma com_to_operators_variables_distinct: 
  "op \<in> set (com_to_operators c d) \<Longrightarrow> (l = precondition_of op \<or> l = effect_of op)
  \<Longrightarrow> distinct (map fst l)"
by (induction c d arbitrary: op l rule: com_to_operators.induct)
 (auto simp: Let_def update_preserve_distinct split: aexp.splits atomExp.splits if_splits)

lemma PC_of_precondition[simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> (PC, y) \<in> set (precondition_of op) \<longleftrightarrow> y = PCV c"
  using com_to_operators_variables_distinct PC_in_effect_precondition
  apply(cases c)
      apply(auto simp: pc_to_com_def split: aexp.splits atomExp.splits if_splits)
  by(metis eq_key_imp_eq_value fst_of_precondition precondition_nonempty 
      set_update_memI update_preserve_distinct)+

lemma [simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> (map_of (precondition_of op)) PC = Some (PCV c)"
  using PC_of_precondition com_to_operators_variables_distinct by auto

lemma [simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> pc_to_com (precondition_of op) = c"
  using PC_of_precondition  
  by (metis PC_in_effect_precondition domain_element.simps nth_mem old.prod.case pc_to_com_def 
      precondition_nonempty)

lemma [simp]: "op \<in> set (com_to_operators c d) 
  \<Longrightarrow> (PC, y) \<in> set (effect_of op) \<longleftrightarrow> y = PCV (pc_to_com (effect_of op))"
  using com_to_operators_variables_distinct PC_in_effect_precondition 
  by (auto simp: pc_to_com_def)
   (metis domain_element.simps effect_nonempty eq_key_imp_eq_value nth_mem old.prod.case)+

lemma com_to_operators_PC_is_subprogram: 
  "op \<in> set (com_to_operators c d)
  \<Longrightarrow>  (pc_to_com (precondition_of op) \<in> set (enumerate_subprograms c)
      \<and> pc_to_com (effect_of op) \<in> set (enumerate_subprograms c))"
  apply (induction c d arbitrary: op rule: com_to_operators.induct)
  using c_in_all_subprograms_c precondition_nonempty effect_nonempty
      by (auto simp: Let_def pc_to_com_def split: if_splits aexp.splits atomExp.splits)

lemma com_to_operators_variables_in_enumerate_variables: "op \<in> set (com_to_operators c d)
  \<Longrightarrow> ((VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op))
  \<Longrightarrow> x \<in> set (enumerate_variables c)"
proof (induction c d arbitrary: op rule: com_to_operators.induct)
  case (3 c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by auto
  then show ?case
  proof (elim disjE)
    assume "c1 = SKIP"
    then show ?thesis using 3 by auto
  next
    assume "c1 \<noteq> SKIP"
    moreover then obtain op' where "op' \<in> set (com_to_operators c1 d) 
          \<and> ((VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op'))"
      using 3 com_to_operators_seq_registers by presburger
    moreover have "c1 \<in> set (enumerate_subprograms (c1 ;; c2))" using c_in_all_subprograms_c by auto
    moreover then have "set (enumerate_variables c1) \<subseteq> set (enumerate_variables (c1 ;; c2))"
      using enumerate_subprograms_enumerate_variables
      by simp
    ultimately show ?thesis using 3 by auto
  qed
qed (auto simp: Let_def  split: aexp.splits atomExp.splits if_splits)

lemma [simp]: 
  assumes "op \<in> set (com_to_operators c1 d)"
    "(a, b) \<in> set (precondition_of op)"
    "c1 \<in> set (enumerate_subprograms c)"
    "a \<notin> VN ` set (enumerate_variables c)" 
  shows "a = PC"
proof (cases a)
  case (VN v)
  have "set (enumerate_variables c1) \<subseteq> set (enumerate_variables c)" 
    using assms enumerate_subprograms_enumerate_variables by auto
  then show ?thesis using VN com_to_operators_variables_in_enumerate_variables assms by blast
qed auto

lemma [simp]: 
  assumes "op \<in> set (com_to_operators c1 d)"
    "(a, b) \<in> set (effect_of op)"
    "c1 \<in> set (enumerate_subprograms c)"
    "a \<notin> VN ` set (enumerate_variables c)" 
  shows "a = PC"
proof (cases a)
  case (VN v)
  have "set (enumerate_variables c1) \<subseteq> set (enumerate_variables c)" 
    using assms enumerate_subprograms_enumerate_variables by auto
  then show ?thesis using VN com_to_operators_variables_in_enumerate_variables assms by blast
qed auto

definition coms_to_operators :: "com list \<Rightarrow> domain_element list \<Rightarrow> operator list" where
"coms_to_operators cs d = concat (map (\<lambda> c. com_to_operators c d) cs)"

definition sas_state_by_pc_and_vars :: 
  "com list \<Rightarrow> com  \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> domain_element list \<Rightarrow> sas_state" where
"sas_state_by_pc_and_vars cs c vs d =  (\<lambda> v. (case v of 
  VN vn \<Rightarrow> (case vs vn of Some x \<Rightarrow> (if EV (Num x) \<in> set d then Some (EV (Num x)) else Some (EV \<omega>)) |
                          None \<Rightarrow> None) |
  PC \<Rightarrow> Some (PCV c)))"

lemma sas_state_by_pc_and_vars_variables_in_d: 
  "x \<noteq> PC \<Longrightarrow> (sas_state_by_pc_and_vars cs c vs d) x = Some y 
  \<Longrightarrow> (y = EV \<omega> \<or> y \<in> set d)"
  by (auto simp: sas_state_by_pc_and_vars_def split: variable.splits option.splits if_splits)

definition imp_minus_minus_to_sas_plus :: "com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> problem" where
"imp_minus_minus_to_sas_plus c vs t = (let cs = enumerate_subprograms c ; 
  d = domain c t in let
  initial_vs = vs|`(set (enumerate_variables c)) ;
  pc_d = map (\<lambda> i. PCV i) cs in
    \<lparr> variables_of = PC # (map (\<lambda> v. VN v) (enumerate_variables c)),
      operators_of = coms_to_operators cs d, 
      initial_of = sas_state_by_pc_and_vars cs c initial_vs d,
      goal_of = sas_state_by_pc_and_vars cs SKIP Map.empty d,
      range_of = (map_of (map (\<lambda> v. (VN v, d)) (enumerate_variables c)))(PC \<mapsto> pc_d)\<rparr>)"

lemma range_defined: 
  assumes "v \<in> set (variables_of (imp_minus_minus_to_sas_plus c vs t))" 
  shows "(\<exists>y. range_of (imp_minus_minus_to_sas_plus c vs t) v = Some y)"
proof(cases v)
  case (VN x)
  then have "(VN x, domain c t) \<in> set (map (\<lambda> v. (VN v, domain c t)) (enumerate_variables c))" 
    using assms by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)    
  then show ?thesis using VN by (auto simp: Let_def imp_minus_minus_to_sas_plus_def weak_map_of_SomeI) 
qed (auto simp: imp_minus_minus_to_sas_plus_def Let_def)

lemma range_non_empty: 
  assumes "v \<in> set (variables_of (imp_minus_minus_to_sas_plus c vs t))" 
  shows "(\<exists>y. y \<in> range_of' (imp_minus_minus_to_sas_plus c vs t) v)"
proof (cases v)
  case (VN x)
  then have *: "(VN x, domain c t) \<in> set (map (\<lambda> v. (VN v, domain c t)) (enumerate_variables c))" 
    using assms by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)
  then have "range_of (imp_minus_minus_to_sas_plus c vs t) v = Some (domain c t)" 
    using VN by (simp add: Let_def imp_minus_minus_to_sas_plus_def) 
       (smt Pair_inject * ex_map_conv map_of_SomeD weak_map_of_SomeI)
  then show ?thesis using assms VN by (simp add: range_of'_def)
     (meson ListMem_iff omega_in_domain)
next
  case PC
  then show ?thesis using SKIP_in_enumerate_subprograms
    by (auto simp:  range_of'_def Let_def imp_minus_minus_to_sas_plus_def) 
      (metis empty_iff empty_set) 
qed

lemma [simp]: "x \<in> set l \<Longrightarrow> (map_of (map (\<lambda>v. (VN v, d)) l) (VN x)) = Some d"
  by (induction l) auto

lemma distinct_list_all: 
  assumes "distinct (map fst l)" 
  shows "list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') l) l"
proof -
  have "(v1, a1) \<in> set l \<Longrightarrow> list_all (\<lambda>(v', a'). v1 \<noteq> v' \<or> a1 = a') l" for v1 a1
  proof -
    assume "(v1, a1) \<in> set l"
    then have "(v2, a2) \<in> set l \<Longrightarrow> v1 \<noteq> v2 \<or> a1 = a2" for v2 a2 
      using assms by (meson eq_key_imp_eq_value)
    then show ?thesis using Ball_set_list_all by blast
  qed
  then show ?thesis
    by (metis (no_types, lifting) case_prodI2 list.pred_set)
qed 

lemma op_applicable_then_PC: "op \<in> set ((imp_minus_minus_to_sas_plus c vs t)\<^sub>\<O>\<^sub>+) 
  \<Longrightarrow> is_operator_applicable_in s op \<Longrightarrow> the (s PC) = PCV c1 
  \<Longrightarrow> op \<in> set (com_to_operators c1 (domain c t))"
  apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
proof -
  fix x
  assume  "map_of (precondition_of op) \<subseteq>\<^sub>m s"
    "the (s PC) = PCV c1"
    "op \<in> set (com_to_operators x (domain c t))"
  moreover then have "(map_of (precondition_of op)) PC = Some (PCV x)" by auto
  ultimately have "x = c1" 
    by (metis (mono_tags, lifting) domIff domain_element.inject map_le_def option.sel option.simps)
  then show ?thesis
    using \<open>op \<in> set (com_to_operators x (domain c t))\<close> by blast
qed

lemma [simp]: "PCV x \<in> PCV ` y \<longleftrightarrow> x \<in> y" by auto

lemma operators_valid: 
  assumes "cs = enumerate_subprograms c" and "c1 \<in> set cs" and "d = domain c t"
         and  "op \<in> set (com_to_operators c1 d)"
  shows "is_valid_operator_sas_plus (imp_minus_minus_to_sas_plus c vs t) op" 
proof -                   
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c vs t"
  let ?pre = "precondition_of op" and ?eff = "effect_of op" and ?vs = "variables_of ?\<Psi>" 
      and ?D = "range_of ?\<Psi>" and ?pc_d = "map (\<lambda> i. PCV i) (enumerate_subprograms c)"

  have *: "list_all (\<lambda>(v, a). ListMem v ?vs) ?pre \<and> list_all (\<lambda>(v, a). ListMem v ?vs) ?eff"
    using assms by(auto simp: imp_minus_minus_to_sas_plus_def Let_def ListMem_iff list_all_def)

  have "((VN x, a) \<in> set ?pre \<or> (VN x, a) \<in> set ?eff) \<Longrightarrow> ?D (VN x) = Some d \<and> a \<in> set d" for x a
    using assms com_to_operators_registers_in_d com_to_operators_variables_in_enumerate_variables
        enumerate_subprograms_enumerate_variables 
    by (fastforce simp: imp_minus_minus_to_sas_plus_def Let_def)    
  then have "((v, a) \<in> set ?pre \<or> (v, a) \<in> set ?eff) \<Longrightarrow> (?D v \<noteq> None \<and> ListMem a (the (?D v)))" for v a
    using com_to_operators_PC_is_subprogram assms enumerate_subprograms_transitive
    by (cases v) 
      (auto simp: imp_minus_minus_to_sas_plus_def Let_def ListMem_iff Ball_set_list_all)
  then have "list_all (\<lambda>(v, a). (?D v \<noteq> None) \<and> ListMem a (the (?D v))) ?pre" 
    and "list_all (\<lambda>(v, a). (?D v \<noteq> None) \<and> ListMem a (the (?D v))) ?eff" 
    using Ball_set_list_all by blast+

  then show ?thesis 
    using com_to_operators_variables_distinct assms distinct_list_all *
    by (fastforce simp: is_valid_operator_sas_plus_def Let_def) 
qed

lemma in_range_of_restricted_then: "(f |` S) x = Some y \<Longrightarrow> x \<in> S" 
  by (metis option.simps restrict_out)

lemma imp_minus_minus_to_sas_plus_valid: 
  "is_valid_problem_sas_plus_plus (imp_minus_minus_to_sas_plus c vs t)"
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c vs t"
  let ?ops = "operators_of ?\<Psi>"
      and ?vs = "variables_of ?\<Psi>"
      and ?I = "initial_of ?\<Psi>"
      and ?G = "goal_of ?\<Psi>"
      and ?D = "range_of ?\<Psi>"
  have "\<forall>x \<in> set ?ops. is_valid_operator_sas_plus ?\<Psi> x" 
    and "\<forall>v \<in> set ?vs. length (the (?D v)) > 0" 
    and "\<forall>v. ?I v \<noteq> None \<longrightarrow> ListMem v ?vs"
    and "\<forall>v. ?G v \<noteq> None \<longrightarrow> ListMem v ?vs"
    and "\<forall>v. ?G v \<noteq> None \<longrightarrow> ListMem (the (?G v)) (the (?D v))"
    using operators_valid c_in_all_subprograms_c[where ?c = c] in_range_of_restricted_then
      SKIP_in_enumerate_subprograms
    by (auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def 
        sas_state_by_pc_and_vars_def ListMem_iff split: variable.splits option.splits) fast
  moreover then have "?I v \<noteq> None \<Longrightarrow> ListMem (the (?I v)) (the (?D v))" for v
    using c_in_all_subprograms_c
    by (fastforce simp: imp_minus_minus_to_sas_plus_def Let_def sas_state_by_pc_and_vars_def 
        ListMem_iff split: variable.splits option.splits if_splits) 
  ultimately show ?thesis
    by (auto simp: is_valid_problem_sas_plus_plus_def range_defined list_all_def)
qed

end