\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to SAS+"

theory IMP_Minus_To_SAS_Plus
  imports "IMP-_To_IMP--/IMP_Minus_To_IMP_Minus_Minus" 
    "IMP--_To_SAS++/IMP_Minus_Minus_To_SAS_Plus_Plus_Correctness"
    "SAS++_To_SAS+/SAS_Plus_Plus_To_SAS_Plus"
    "IMP_Minus_Max_Constant"
    "HOL-Library.Discrete"
begin

type_synonym SAS_problem = "(IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations.variable, 
  IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations.domain_element) problem" 

definition bit_length where "bit_length x \<equiv>  Discrete.log x + 1"

lemma le_two_to_the_bit_length_intro: "x \<le> y \<Longrightarrow> x \<le> 2 ^ (bit_length y)"
  apply(auto simp: bit_length_def)
  by (metis leD log_exp2_gt max.strict_coboundedI2 max_def)

definition max_input_bits:: "IMP_Minus_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"max_input_bits c I r = 
  bit_length (max (max (Max (ran I)) r) (IMP_Minus_Max_Constant.max_constant c))" 

definition IMP_Minus_to_SAS_Plus:: "IMP_Minus_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> (vname \<rightharpoonup> nat) 
  \<Rightarrow>  nat \<Rightarrow> SAS_problem" where
"IMP_Minus_to_SAS_Plus c I r G t = (let 
  n = t + max_input_bits c I r + 1;
  t' = (100 * n * (t - 1) + 51) in
  (let c' = IMP_Minus_To_IMP_Minus_Minus c n in
  (let I' = ((\<lambda>x. Some (Num x)) \<circ>\<^sub>m (IMP_Minus_State_To_IMP_Minus_Minus_partial I n)) 
    |` (set (enumerate_variables c')) ;
  G' = ((\<lambda>x. Some (Num x)) \<circ>\<^sub>m (IMP_Minus_State_To_IMP_Minus_Minus_partial G n))
    |` (set (enumerate_variables c')) in 
  SAS_Plus_Plus_To_SAS_Plus (imp_minus_minus_to_sas_plus c' I' G' t'))))"

lemma le_mul_intro: "0 < b \<Longrightarrow> a \<le> b \<Longrightarrow> (1 :: nat) < c \<Longrightarrow> a < c * b" 
  by (metis One_nat_def dual_order.strict_trans le_neq_implies_less n_less_m_mult_n)

lemma IMP_Minus_to_SAS_Plus_correctness:
  assumes
    "I \<subseteq>\<^sub>m Some \<circ> s1" 
    "finite (range s1)" 
    "Max (range s1) < r"
    "G \<subseteq>\<^sub>m Some \<circ> s2"
    "(c, s1) \<Rightarrow>\<^bsup>t\<^esup> s2"
  shows "\<exists>plan. length plan \<le> 100 * (max_input_bits c I r + t + 1) * (t - 1) 
      + (max_input_bits c I r + t + 1 + 1) * (num_variables c + 2) + 52
      \<and> is_serial_solution_for_problem (IMP_Minus_to_SAS_Plus c I r G t) plan"
proof -
  let ?n = "t + max_input_bits c I r + 1"
  let ?c' = "IMP_Minus_To_IMP_Minus_Minus c ?n"
  let ?s1' = "IMP_Minus_State_To_IMP_Minus_Minus s1 ?n"
  let ?s2' = "IMP_Minus_State_To_IMP_Minus_Minus s2 ?n"
  let ?I = "((\<lambda>x. Some (Num x)) \<circ>\<^sub>m (IMP_Minus_State_To_IMP_Minus_Minus_partial I ?n))
    |` (set (enumerate_variables ?c'))"
  let ?G = "((\<lambda>x. Some (Num x)) \<circ>\<^sub>m (IMP_Minus_State_To_IMP_Minus_Minus_partial G ?n))
    |` (set (enumerate_variables ?c'))"
  let ?t = "100 * ?n * (t - 1) + 51"
  let ?sas_plus_plus_problem 
    = "imp_minus_minus_to_sas_plus (IMP_Minus_To_IMP_Minus_Minus c ?n) ?I ?G ?t"

  have "t_small_step_fun (100 * ?n * (t - 1) + 50) 
      (IMP_Minus_To_IMP_Minus_Minus c ?n, IMP_Minus_State_To_IMP_Minus_Minus s1 ?n)
     = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus s2 ?n)" 
    apply - apply(rule IMP_Minus_To_IMP_Minus_Minus)
    using assms apply(auto simp: max.strict_coboundedI1 max.strict_coboundedI2 max_input_bits_def 
        power_add intro!: le_mul_intro le_two_to_the_bit_length_intro) 
    by (metis less_imp_le_nat max.coboundedI1 max.commute)

  then obtain t' where t'_def: "t' \<le> 100 * ?n * (t - 1) + 50" "(?c', ?s1') \<rightarrow>\<^bsup>t'\<^esup> (SKIP, ?s2')" 
    using t_small_step_fun_t_small_step_equivalence by auto

  let ?s1'' = "canonical_\<omega>_state (t' + 1) ?c' ?s1'"
  have "\<exists>s2''. ((?c', ?s1'') \<rightarrow>\<^bsub>?t\<^esub>\<^bsup>t'\<^esup> (SKIP, s2'')) 
    \<and> dom s2'' = set (enumerate_variables ?c') 
    \<and> \<omega>_equivalent ((t' + 1) - t' * IMP_Minus_Minus_Domains.max_constant ?c') ?s2' s2''"
    using  t'_def c_in_all_subprograms_c  IMP_Minus_To_IMP_Minus_Minus_max_constant
    apply(auto simp: canonical_\<omega>_state_\<omega>_equivalent le_imp_less_Suc 
        intro!: small_step_omega_equivalence)
    by(auto simp: canonical_\<omega>_state_def split: if_splits)
  then obtain s2'' where s2''_def: "((?c', ?s1'') \<rightarrow>\<^bsub>?t\<^esub>\<^bsup>t'\<^esup> (SKIP, s2'')) "
    "dom s2'' = set (enumerate_variables ?c')"
    "\<omega>_equivalent ((t' + 1) - t' * IMP_Minus_Minus_Domains.max_constant ?c') ?s2' s2''" by blast
  hence "\<omega>_equivalent 1 ?s2' s2''" 
    apply - apply(rule \<omega>_equivalent_increasing') 
    using IMP_Minus_To_IMP_Minus_Minus_max_constant apply auto
    by (metis Nat.le_add_diff One_nat_def add.commute nat_mult_1_right nat_mult_le_cancel_disj 
        plus_1_eq_Suc)
  hence "?G v = Some y \<Longrightarrow> s2'' v = Some y" for v y
  proof-
    assume "?G v = Some y"
    then obtain y' where "y = Num y'" by(auto simp: map_comp_Some_iff)
    hence "?s2' v = y'" using \<open>?G v = Some y\<close> \<open>G \<subseteq>\<^sub>m Some \<circ> s2\<close> 
      by(auto simp: map_le_def map_comp_Some_iff IMP_Minus_State_To_IMP_Minus_Minus_partial_def 
        IMP_Minus_State_To_IMP_Minus_Minus_def dom_def var_to_var_bit_eq_Some_iff
          split: option.splits if_splits)+
    moreover have "v \<in> dom s2''" using \<open>?G v = Some y\<close> \<open>dom s2'' = set (enumerate_variables ?c')\<close>
      by auto
    ultimately show "s2'' v = Some y" using \<open>\<omega>_equivalent 1 ?s2' s2''\<close> \<open>y = Num y'\<close>
      by(auto simp: \<omega>_equivalent_def less_nth_bit_iff
            dom_def var_to_var_bit_eq_Some_iff IMP_Minus_State_To_IMP_Minus_Minus_bounded
            split: option.splits if_splits)
  qed
  hence "?G \<subseteq>\<^sub>m s2''" by (auto simp: map_le_def)

  let ?ss1'' = "imp_minus_state_to_sas_plus (?c', ?s1'')" 
  let ?ss2'' = "imp_minus_state_to_sas_plus (SKIP, s2'')" 
  have "max 1 (IMP_Minus_Minus_Domains.max_constant ?c') = 1" 
    using IMP_Minus_To_IMP_Minus_Minus_max_constant by (simp add: max.absorb1)
  hence "\<exists>plan. is_serial_solution_for_problem_sas_plus_plus ?sas_plus_plus_problem plan
     \<and> length plan = t'"
    using s2''_def t'_def 
    apply(auto simp: canonical_\<omega>_state_def IMP_Minus_State_To_IMP_Minus_Minus_def 
      IMP_Minus_To_IMP_Minus_Minus_variables split: if_splits option.splits 
      intro!: \<omega>_imp_minus_minus_to_sas_plus_plus[where ?is1.0="?s1''"] nth_bit_le_intro)
     using \<open>I \<subseteq>\<^sub>m Some \<circ> s1\<close> 
      apply(fastforce simp: map_le_def canonical_\<omega>_state_eq_Some_iff 
        IMP_Minus_State_To_IMP_Minus_Minus_def
        map_comp_def IMP_Minus_State_To_IMP_Minus_Minus_partial_def dom_def nth_bit_le_intro
        IMP_Minus_To_IMP_Minus_Minus_variables
        elim!: set_mp[OF IMP_Minus_To_IMP_Minus_Minus_variables]
        split!: option.splits if_splits)
     using \<open>?G \<subseteq>\<^sub>m s2''\<close> by auto
   then obtain plan where plan_def: 
     "is_serial_solution_for_problem_sas_plus_plus ?sas_plus_plus_problem plan"
      "length plan = t'" by blast

   hence "\<exists>prefix. length prefix \<le> length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus ?sas_plus_plus_problem) 
        (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))"
     apply -
     apply(rule SAS_Plus_Plus_To_SAS_Plus)
     apply(rule imp_minus_minus_to_sas_plus_valid)
     by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_partial_def map_comp_def nth_bit_le_intro
         split: option.splits)
   then obtain prefix where prefix_def: "length prefix \<le> length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus ?sas_plus_plus_problem) 
        (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))" by blast
   let ?plan' = "prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan)"
   have "length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) \<le> (?n + 1) * (num_variables c + 2) + 1" using 
     IMP_Minus_To_IMP_Minus_Minus_variables_length[where ?c=c 
         and ?n="(Suc (t + max_input_bits c I r))"] 
     by(auto simp: imp_minus_minus_to_sas_plus_def Let_def)
   hence "length prefix \<le> (?n + 1) * (num_variables c + 2) + 2" using prefix_def by simp
   hence "length ?plan' \<le> 100 * ?n * (t - 1) + (?n + 1) * (num_variables c + 2) + 52
      \<and> is_serial_solution_for_problem (IMP_Minus_to_SAS_Plus c I r G t) ?plan'"
     using plan_def prefix_def t'_def by(auto simp: IMP_Minus_to_SAS_Plus_def Let_def)
   thus ?thesis by (metis add.commute)
 qed
    

end