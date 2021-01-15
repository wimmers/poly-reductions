\<^marker>\<open>creator Florian Keßler\<close>

section "SAS++ to SAS+"

theory SAS_Plus_Plus_To_SAS_Plus imports SAS_Plus_Plus
begin 

datatype 'v variable =  Var 'v | Stage
datatype 'd domain_element = DE 'd | Init | NonInit
                                                               
type_synonym ('v, 'd) state = "('v, 'd) State_Variable_Representation.state"
type_synonym ('v, 'd) operator = "('v variable, 'd domain_element) sas_plus_operator"
type_synonym ('v, 'd) problem = "('v variable, 'd domain_element) sas_plus_problem"

definition SAS_Plus_Plus_State_To_SAS_Plus:: 
  "('d domain_element \<times> ('v, 'd) state) \<Rightarrow> ('v variable, 'd domain_element) state" where
"SAS_Plus_Plus_State_To_SAS_Plus is = ((\<lambda>x. Some (DE x)) \<circ>\<^sub>m (snd is)
  \<circ>\<^sub>m (\<lambda>x. (case x of Var x \<Rightarrow> Some x | Stage \<Rightarrow> None)))(Stage \<mapsto> (fst is))"

lemma SAS_Plus_Plus_State_To_SAS_Plus_eq_iff_snd_eq[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (i, s) = SAS_Plus_Plus_State_To_SAS_Plus (i, s') 
  \<longleftrightarrow> s = s'" 
  apply (auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff 
      split: option.splits variable.splits)
  by (metis option.exhaust_sel)

lemma SAS_Plus_Plus_State_To_SAS_Plus_update_stage[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (a, s)(Stage \<mapsto> b) = SAS_Plus_Plus_State_To_SAS_Plus (b, s)"
  by (auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff)

lemma SAS_Plus_Plus_State_To_SAS_Plus_map_le[simp]: 
  "SAS_Plus_Plus_State_To_SAS_Plus (a, s) \<subseteq>\<^sub>m m 
    \<Longrightarrow> SAS_Plus_Plus_State_To_SAS_Plus (b, s) \<subseteq>\<^sub>m m(Stage \<mapsto> b)" 
  by(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_le_def map_comp_def 
      split: option.splits variable.splits)

definition SAS_Plus_Plus_Operator_To_SAS_Plus_Operator:: 
  "('v, 'd) sas_plus_operator \<Rightarrow> ('v, 'd) operator" where
"SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op = 
  \<lparr> precondition_of = (Stage, NonInit) # (map (\<lambda> x. (Var (fst x), DE (snd x))) (precondition_of op)),
    effect_of = (map (\<lambda> x. (Var (fst x), DE (snd x))) (effect_of op))\<rparr>"

lemma dom_of_map_of_map[simp]: 
  "dom (map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l)) = (\<lambda>x. Var (fst x)) ` set l" 
  apply(induction l)
  apply(auto)
  by (metis (mono_tags, lifting) domD fst_conv imageI)

lemma map_of_map_eq_None_iff[simp]: "(map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l) (Var y) = None)
  \<longleftrightarrow> (y \<notin> fst ` set l)"
  apply(induction l)
  by(auto)

lemma map_of_map_eq_Some_iff[simp]: "(map_of (map (\<lambda>x. (Var (fst x), DE (snd x))) l) (Var x) = Some (DE y))
  \<longleftrightarrow> (map_of l x = Some y)"
  apply(induction l)
  by(auto)

lemma SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_applicable[simp]: 
  "is_operator_applicable_in (SAS_Plus_Plus_State_To_SAS_Plus (i, s)) 
    (SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op)
  \<longleftrightarrow> (i = NonInit \<and> is_operator_applicable_in s op)"
  apply(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def 
      SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def)
    apply(simp_all add: map_le_def)
   apply(auto split: option.splits variable.splits)
  apply(frule map_of_SomeD)
    apply auto
  by (metis domI weak_map_of_SomeI)+

lemma SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_execute[simp]:
  "SAS_Plus_Plus_State_To_SAS_Plus (i, s) ++ map_of (effect_of (SAS_Plus_Plus_Operator_To_SAS_Plus_Operator op))
  = SAS_Plus_Plus_State_To_SAS_Plus(i, s \<then>\<^sub>+ op)" 
  using map_of_SomeD
  apply(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_comp_def fun_eq_iff map_add_def 
      SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def split: option.splits variable.splits)
  apply force+
  prefer 9 using map_of_SomeD apply fastforce
  using map_of_map_eq_None_iff map_of_map_eq_Some_iff
  by (metis (mono_tags, lifting) map_of_eq_None_iff map_of_map_eq_Some_iff option.simps 
      option.distinct domI  domIff option.simps)+

lemma execute_SAS_Plus_Plus_ops_in_SAS_Plus[simp]:
  "execute_serial_plan_sas_plus (SAS_Plus_Plus_State_To_SAS_Plus (NonInit, s))
    (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ops) 
    = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, execute_serial_plan_sas_plus s ops)"
  apply(induction ops arbitrary: s)
   apply(simp add: SAS_Plus_Plus_State_To_SAS_Plus_def 
      SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def)
  by(auto simp: SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_applicable[simplified])

definition initialization_operators:: "('v, 'd) sas_plus_problem \<Rightarrow> ('v, 'd) operator list" where
"initialization_operators P = \<lparr> precondition_of = [], effect_of = [(Stage, NonInit)]\<rparr> #
  concat (map (\<lambda> v. (if v \<in> dom ((P)\<^sub>I\<^sub>+) then [] 
    else map (\<lambda> y. \<lparr> precondition_of = [(Stage, Init)],  effect_of = [(Var v, DE y)]\<rparr>) 
      (the (range_of P v)))) ((P)\<^sub>\<V>\<^sub>+))"

lemma in_initialization_operators_iff[simp]: 
  "\<lparr>precondition_of = [(Stage, Init)], effect_of = [(Var x, DE y)]\<rparr> 
    \<in> set (initialization_operators P) 
  \<longleftrightarrow> (x \<in> set ((P)\<^sub>\<V>\<^sub>+) \<and> ((P)\<^sub>I\<^sub>+) x = None \<and> y \<in> set (the (range_of P x)))"
  by(auto simp: initialization_operators_def)

definition initial_state:: 
  "('v, 'd) sas_plus_problem \<Rightarrow> ('v variable, 'd domain_element) state" where
"initial_state P = (\<lambda> v.
  (case v of 
    Var var \<Rightarrow> (if var \<in> set ((P)\<^sub>\<V>\<^sub>+) then Some (DE (case ((P)\<^sub>I\<^sub>+) var of 
        (Some val) \<Rightarrow> val |
        None \<Rightarrow> (the (range_of P var)) ! 0))
      else None) |
    Stage \<Rightarrow> Some Init))"

definition SAS_Plus_Plus_To_SAS_Plus:: "('v, 'd) sas_plus_problem \<Rightarrow> ('v, 'd) problem" where
"SAS_Plus_Plus_To_SAS_Plus P = \<lparr> variables_of = Stage # (map Var ((P)\<^sub>\<V>\<^sub>+)),
      operators_of = (initialization_operators P) 
        @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator ((P)\<^sub>\<O>\<^sub>+)), 
      initial_of = initial_state P ,
      goal_of = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, ((P)\<^sub>G\<^sub>+)),
      range_of = ((\<lambda>x. Some (map DE x)) \<circ>\<^sub>m (range_of P) 
        \<circ>\<^sub>m (\<lambda>x. (case x of Var x \<Rightarrow> Some x | Stage \<Rightarrow> None)))(Stage \<mapsto> [Init, NonInit])\<rparr>"

lemma Var_not_in_map_Var_iff[simp]: "Var x \<notin> Var ` S \<longleftrightarrow> x \<notin> S" by auto

lemma SAS_Plus_Plus_To_SAS_Plus_valid: 
  assumes "is_valid_problem_sas_plus_plus P"
  shows "is_valid_problem_sas_plus (SAS_Plus_Plus_To_SAS_Plus P)" 
  using assms apply(auto simp: is_valid_problem_sas_plus_plus_def is_valid_problem_sas_plus_def 
      SAS_Plus_Plus_To_SAS_Plus_def list_all_def is_valid_operator_sas_plus_def Let_def
      initialization_operators_def SAS_Plus_Plus_Operator_To_SAS_Plus_Operator_def ListMem_iff)
               apply auto
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
          apply blast
         apply blast
         apply(auto simp: initial_state_def map_comp_def SAS_Plus_Plus_State_To_SAS_Plus_def 
        split: variable.splits if_splits option.splits)
  by (meson assms is_valid_problem_sas_plus_plus_then(1) range_of_not_empty)+

lemma stage_of_initial_state[simp]: "((SAS_Plus_Plus_To_SAS_Plus P)\<^sub>I\<^sub>+) Stage = Some Init" 
  by(auto simp: SAS_Plus_Plus_To_SAS_Plus_def initial_state_def)

definition initialization_sequence:: "('v \<times> 'd) list \<Rightarrow> ('v, 'd) operator list" where
  "initialization_sequence vs = map (\<lambda>v. \<lparr> precondition_of = [(Stage, Init)],  
      effect_of = [(Var (fst v), DE (snd v))]\<rparr>) vs"

lemma result_of_initialization_sequence[simp]: 
  assumes "I Stage = Some Init"
    "distinct (map fst vs)"
  shows "execute_serial_plan_sas_plus I (initialization_sequence vs) = 
  I ++ SAS_Plus_Plus_State_To_SAS_Plus (Init, map_of vs)"
using assms proof (induction vs arbitrary: I)
  case Nil
  then show ?case using Nil
    by (auto simp: initialization_sequence_def SAS_Plus_Plus_State_To_SAS_Plus_def map_add_def)
next
  case (Cons v vs)
  hence "execute_serial_plan_sas_plus I (initialization_sequence (v # vs)) 
    = execute_serial_plan_sas_plus (I(Var (fst v) \<mapsto> DE (snd v))) (initialization_sequence vs)"
    by (auto simp: initialization_sequence_def map_le_def)
  also have "... = I ++ SAS_Plus_Plus_State_To_SAS_Plus (Init, map_of (v # vs))" using Cons
    by(auto simp: SAS_Plus_Plus_State_To_SAS_Plus_def map_add_def fun_eq_iff map_comp_def 
        rev_image_eqI split: option.splits variable.splits)
  ultimately show ?case by metis
qed

lemma initialization_sequence_chain_applicable_condition[simp]:
  assumes "s Stage = Some Init"
  shows "chain_applicable s (initialization_sequence vs)"
  using assms apply(induction vs arbitrary: s)
  by(auto simp:  initialization_sequence_def map_le_def)

lemma map_of_conact_map_cases_eq_Some[simp]: 
  "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y 
  \<longleftrightarrow> (x \<in> set l \<and> f x = y \<and> m x = None)"
proof
  assume "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y" 
  then show "x \<in> set l \<and> f x = y \<and> m x = None"  
    apply -
    apply(drule map_of_SomeD)
    by(auto)
next
  assume "x \<in> set l \<and> f x = y \<and> m x = None"
  hence "(x, y) \<in> set (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l))"
    by auto
  moreover have "\<forall>y'. (x, y') \<in> set (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l))
    \<longrightarrow> y' = f x" by auto
  ultimately show "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y"
    by (metis (no_types, lifting) map_of_SomeD weak_map_of_SomeI)
qed

lemma map_of_conact_map_cases_eq_None[simp]: 
  "map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = None 
  \<longleftrightarrow> (x \<notin> set l \<or> m x \<noteq> None)"
proof -
  have "(map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = None)
    = (\<not>(\<exists>y. map_of (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) l)) x = Some y))"
    by fastforce
  also have "... = (\<not>(\<exists>y. x \<in> set l \<and> f x = y \<and> m x = None))" by auto
  ultimately show ?thesis by simp
qed

lemma distinct_map_fst_concat[simp]:
  "distinct (map fst (concat (map (\<lambda>v. case m v of None \<Rightarrow> [(v, f v)] | Some x \<Rightarrow> []) (remdups l))))"
  apply(induction l) 
  by(auto split: option.splits)

lemma length_concat_map[simp]: 
  "length (concat (map (\<lambda>v. case m v of None \<Rightarrow> [f v] | Some _ \<Rightarrow> []) (remdups l))) \<le> length l"
  apply(induction l)
  by(auto split: option.splits)

lemma SAS_Plus_Plus_To_SAS_Plus:
  assumes "is_valid_problem_sas_plus_plus P" 
    "is_serial_solution_for_problem_sas_plus_plus P plan"
  shows "\<exists>prefix. length prefix \<le> length ((P)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus P) 
        (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))" 
proof -
  obtain I where I_def: "((P)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I \<and> dom I = set ((P)\<^sub>\<V>\<^sub>+)
        \<and> (\<forall> v \<in> set ((P)\<^sub>\<V>\<^sub>+). the (I v) \<in> range_of' P v)
        \<and> ((P)\<^sub>G\<^sub>+) \<subseteq>\<^sub>m execute_serial_plan_sas_plus I plan
        \<and> list_all (\<lambda>op. ListMem op ((P)\<^sub>\<O>\<^sub>+)) plan" using assms 
    by (auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def)
  let ?P' = "SAS_Plus_Plus_To_SAS_Plus P"
  let ?missing_vs = "(concat (map (\<lambda>v. case ((P)\<^sub>I\<^sub>+) v of Some _ \<Rightarrow> [] |
    None \<Rightarrow> [(v, the (I v))]) (remdups ((P)\<^sub>\<V>\<^sub>+))))"
  let ?prefix' = "initialization_sequence ?missing_vs"
  let ?prefix = "?prefix' @ [\<lparr> precondition_of = [], effect_of = [(Stage, NonInit)]\<rparr>]"
  have "execute_serial_plan_sas_plus ((?P')\<^sub>I\<^sub>+) ?prefix' 
    = SAS_Plus_Plus_State_To_SAS_Plus (Init, I)" using I_def
    apply(auto simp: SAS_Plus_Plus_To_SAS_Plus_def SAS_Plus_Plus_State_To_SAS_Plus_def map_le_def
        initial_state_def map_add_def map_comp_def fun_eq_iff split: option.splits variable.splits)
    by (metis domI option.inject)
  hence "execute_serial_plan_sas_plus ((?P')\<^sub>I\<^sub>+) 
    (?prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan)) 
    = SAS_Plus_Plus_State_To_SAS_Plus (NonInit, execute_serial_plan_sas_plus I plan)" by auto
  hence "((?P')\<^sub>G\<^sub>+) \<subseteq>\<^sub>m execute_serial_plan_sas_plus ((?P')\<^sub>I\<^sub>+) 
    (?prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))" using I_def 
    apply(auto simp:  SAS_Plus_Plus_To_SAS_Plus_def SAS_Plus_Plus_State_To_SAS_Plus_def 
        map_add_def map_comp_def split: option.splits variable.splits)
    apply(simp add: map_le_def fun_eq_iff)
    by (metis (no_types, lifting) domIff option.case_eq_if)
  hence "length ?prefix \<le> length ((P)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus P) 
        (?prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))"
    using I_def
    apply(auto simp: is_serial_solution_for_problem_def Let_def list_all_def 
        initialization_sequence_def ListMem_iff SAS_Plus_Plus_To_SAS_Plus_def range_of'_def 
        split: option.splits)
    by (simp add: initialization_operators_def)
  then show ?thesis by blast
qed

end