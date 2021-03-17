\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to SAS+"

theory IMP_Minus_To_SAS_Plus
  imports "IMP-_To_IMP--/IMP_Minus_To_IMP_Minus_Minus" 
    "IMP--_To_SAS++/IMP_Minus_Minus_To_SAS_Plus_Plus_Correctness"
    "SAS++_To_SAS+/SAS_Plus_Plus_To_SAS_Plus"
    "IMP_Minus_Max_Constant"
begin

text \<open> We combine our reduction steps from IMP- to IMP--, then from IMP-- to SAS++ and finally 
  from SAS++ to SAS+ to give a reduction IMP- to SAS+. We then proceed to show the correctness of
  this reduction, by combining the correctness results we have derived for the individual parts
  of the reduction. \<close> 

type_synonym SAS_problem = "(IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations.variable, 
  IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations.domain_element) problem" 

lemma le_two_to_the_bit_length_intro: "x \<le> y \<Longrightarrow> x \<le> 2 ^ (bit_length y)"
  apply(auto simp: bit_length_def)
  by (metis leD log_exp2_gt max.strict_coboundedI2 max_def)

definition max_input_bits:: "IMP_Minus_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"max_input_bits c I r = 
  bit_length (max (max (Max (ran I)) r) (IMP_Minus_Max_Constant.max_constant c))" 

lemma bit_at_index_geq_max_input_bits_is_zero: "x < r \<Longrightarrow> max_input_bits c I r \<le> b  
  \<Longrightarrow> nth_bit x b = Zero" 
proof-
  assume "x < r" "max_input_bits c I r \<le> b" 
  hence "bit_length x \<le> bit_length r" using bit_length_monotonic by simp
  hence "bit_length x \<le> max_input_bits c I r" apply(auto simp: max_input_bits_def)
    using bit_length_monotonic  by (metis dual_order.trans max.cobounded2 max_def)
  thus ?thesis using \<open>max_input_bits c I r \<le> b\<close>
    by(auto simp: max_input_bits_def intro!: bit_geq_bit_length_is_Zero)
qed

lemma bit_at_index_geq_max_input_bits_is_zero_in_initial_state: "finite (ran I) 
  \<Longrightarrow> max_input_bits c I r \<le> b
  \<Longrightarrow> I x = Some y \<Longrightarrow> nth_bit y b = Zero"
proof-
  assume "finite (ran I)" "I x = Some y" "max_input_bits c I r \<le> b" 
  hence "bit_length y \<le> bit_length (Max (ran I))" using bit_length_monotonic
    by (meson Max_ge ranI)
  hence "bit_length y \<le> max_input_bits c I r" apply(auto simp: max_input_bits_def)
    using bit_length_monotonic  by (metis dual_order.trans max.cobounded2 max_def)
  thus ?thesis using \<open>max_input_bits c I r \<le> b\<close>
    by(auto simp: max_input_bits_def intro!: bit_geq_bit_length_is_Zero)
qed

lemma max_constant_less_two_to_the_max_input_bits: "max_constant c < 2 ^ (max_input_bits c I r)" 
  apply(auto simp: max_input_bits_def bit_length_def algebra_simps)
  using log_exp2_gt max_less_iff_conj by blast

lemma initial_state_element_less_two_to_the_max_input_bits: 
  assumes "finite (ran I)" "I x = Some y" 
  shows "y < (2 :: nat) ^ (max_input_bits c I r)" 
proof -
  have "y \<le> Max (ran I)" using assms by (meson Max_ge ranI)
  thus ?thesis using log_exp2_gt max_less_iff_conj
    by(fastforce simp: max_input_bits_def bit_length_def algebra_simps)
qed

definition IMP_Minus_initial_to_IMP_Minus_Minus:: "(vname \<rightharpoonup> nat) 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (vname \<rightharpoonup> bit)" where
"IMP_Minus_initial_to_IMP_Minus_Minus I n guess_range = (\<lambda>v. 
  (case var_to_operand_bit v of 
    Some (CHR ''a'', k) \<Rightarrow> if k < n then Some Zero else None |
    Some (CHR ''b'', k) \<Rightarrow> if k < n then Some Zero else None | 
    _ \<Rightarrow> (if v = ''carry'' then Some Zero 
  else (IMP_Minus_State_To_IMP_Minus_Minus_partial I n guess_range) v)))" 


definition IMP_Minus_to_SAS_Plus:: "IMP_Minus_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> (vname \<rightharpoonup> nat) 
  \<Rightarrow>  nat \<Rightarrow> SAS_problem" where
"IMP_Minus_to_SAS_Plus c I r G t = (let 
  guess_range = max_input_bits c I r;
  n = t + guess_range + 1;
  c' = IMP_Minus_To_IMP_Minus_Minus c n;
  I' = IMP_Minus_initial_to_IMP_Minus_Minus I n guess_range
    |` (set (enumerate_variables c')) ;
  G' = (IMP_Minus_State_To_IMP_Minus_Minus_partial G n n) |` (set (enumerate_variables c')) in 
  SAS_Plus_Plus_To_SAS_Plus (imp_minus_minus_to_sas_plus c' I' G'))"

lemma le_mul_intro: "0 < b \<Longrightarrow> a \<le> b \<Longrightarrow> (1 :: nat) < c \<Longrightarrow> a < c * b" 
  by (metis One_nat_def dual_order.strict_trans le_neq_implies_less n_less_m_mult_n)

text \<open> First direction of the correctness proof for the IMP- to SAS+ reduction, showing that when
       the IMP- program terminates in some state, then in SAS+ there is a plan that will reach any
      goal state that matches the end state of the IMP- program, such that the plan is polynomially
      longer than the execution in IMP-. The constants used to bound the length of the plan have
      no significance, rather they are just derived by adding up the various constants that we
      used in the correctness proofs for the different parts of the reduction. \<close> 

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
  let ?guess_range = " max_input_bits c I r"
  let ?n = "t + ?guess_range + 1"
  let ?c' = "IMP_Minus_To_IMP_Minus_Minus c ?n"
  let ?s1' = "IMP_Minus_State_To_IMP_Minus_Minus s1 ?n |` (set (enumerate_variables ?c'))"
  let ?s2' = "IMP_Minus_State_To_IMP_Minus_Minus s2 ?n |` (set (enumerate_variables ?c'))"
  let ?I = "(IMP_Minus_initial_to_IMP_Minus_Minus I ?n ?guess_range) 
    |` (set (enumerate_variables ?c'))"
  let ?G = "(IMP_Minus_State_To_IMP_Minus_Minus_partial G ?n ?n) 
    |` (set (enumerate_variables ?c'))"
  let ?t = "100 * ?n * (t - 1) + 51"
  let ?sas_plus_plus_problem 
    = "imp_minus_minus_to_sas_plus (IMP_Minus_To_IMP_Minus_Minus c ?n) ?I ?G"

  have "?n > 0" by simp

  have "t_small_step_fun (100 * ?n * (t - 1) + 50) 
      (IMP_Minus_To_IMP_Minus_Minus c ?n, IMP_Minus_State_To_IMP_Minus_Minus s1 ?n)
     = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus s2 ?n)" 
    apply - apply(rule IMP_Minus_To_IMP_Minus_Minus)
    using assms apply(auto simp: max.strict_coboundedI1 max.strict_coboundedI2 max_input_bits_def 
        power_add intro!: le_mul_intro le_two_to_the_bit_length_intro) 
    by (metis less_imp_le_nat max.coboundedI1 max.commute)

  then have "\<exists>t' \<le> 100 * ?n * (t - 1) + 50. (?c', ?s1') \<rightarrow>\<^bsup>t'\<^esup> (SKIP, ?s2')" 
    apply -  apply(rule iffD1[OF t_small_step_fun_t_small_step_equivalence])
    by(auto simp: t_small_step_fun_restrict_variables)
  then obtain t' where t'_def: "t' \<le> 100 * ?n * (t - 1) + 50" "(?c', ?s1') \<rightarrow>\<^bsup>t'\<^esup> (SKIP, ?s2')" 
    by blast

  hence "?G v = Some y \<Longrightarrow> ?s2' v = Some y" for v y
    using \<open>G \<subseteq>\<^sub>m Some \<circ> s2\<close> 
    apply(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_def var_to_var_bit_eq_Some_iff
          IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def 
           IMP_Minus_State_To_IMP_Minus_Minus_partial_def map_le_def map_comp_def dom_def
           split!: option.splits if_splits char.splits bool.splits)
    apply(frule var_bit_in_IMP_Minus_Minus_variables_then_bit_less_n[OF \<open>?n > 0\<close>, simplified])
    by simp
  hence "?G \<subseteq>\<^sub>m ?s2'" by (auto simp: map_le_def)

  have "?I v = Some y \<Longrightarrow> ?s1' v = Some y" for v y
    apply auto
    apply(drule set_mp[OF IMP_Minus_To_IMP_Minus_Minus_variables[OF \<open>?n > 0\<close>, simplified]])
    apply(cases "v = ''carry''")
    using \<open>I \<subseteq>\<^sub>m Some \<circ> s1\<close>
     apply(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_partial_def 
        IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def dom_def
        IMP_Minus_State_To_IMP_Minus_Minus_def map_comp_def map_le_def 
        IMP_Minus_initial_to_IMP_Minus_Minus_def
        split: if_splits option.splits)
    using \<open>finite (range s1)\<close> \<open>Max (range s1) < r\<close> 
    by(auto intro: bit_at_index_geq_max_input_bits_is_zero)
  hence "?I  \<subseteq>\<^sub>m ?s1'" by (auto simp: map_le_def)

  let ?ss1'' = "imp_minus_state_to_sas_plus (?c', ?s1')" 
  let ?ss2'' = "imp_minus_state_to_sas_plus (SKIP, ?s2')" 
  obtain plan where plan_def: 
     "is_serial_solution_for_problem_sas_plus_plus ?sas_plus_plus_problem plan"
     "length plan = t'"
    apply- apply(rule exE[OF imp_minus_minus_to_sas_plus_plus[OF \<open>(?c', ?s1') \<rightarrow>\<^bsup>t'\<^esup> (SKIP, ?s2')\<close>,
            where ?I="?I" and ?G="?G"]])
       apply auto
      apply(drule set_mp[OF IMP_Minus_To_IMP_Minus_Minus_variables[OF \<open>?n > 0\<close>, simplified]])
      using \<open>?I  \<subseteq>\<^sub>m ?s1'\<close> \<open>?G \<subseteq>\<^sub>m ?s2'\<close> by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_def 
        IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

   hence "\<exists>prefix. length prefix \<le> length ((?sas_plus_plus_problem)\<^sub>\<V>\<^sub>+) + 1 
    \<and> is_serial_solution_for_problem (SAS_Plus_Plus_To_SAS_Plus ?sas_plus_plus_problem) 
        (prefix @ (map SAS_Plus_Plus_Operator_To_SAS_Plus_Operator plan))"
     apply -
     apply(rule SAS_Plus_Plus_To_SAS_Plus)
     apply(rule imp_minus_minus_to_sas_plus_valid)
     by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_partial_def map_comp_def 
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

lemma not_in_superset_of_dom_then_None: "dom s \<subseteq> S \<Longrightarrow> x \<notin> S \<Longrightarrow> s x = None" by auto

text \<open> Second direction of the correctness proof. We show that for an IMP- program that will
      terminate after at most t steps on any input, if there is a solution in the reduced 
      SAS+ problem, then there is an IMP- state which matches the initial state of the SAS+ problem,
      such that when the IMP- program is run starting from that state, it reaches a terminating 
      state matching the goal state of the SAS+ problem. \<close>

lemma SAS_Plus_to_IMP_Minus_correctness: 
  assumes 
    "dom I \<subseteq> set (IMP_Minus_Max_Constant.all_variables c)"
    "dom G \<subseteq> set (IMP_Minus_Max_Constant.all_variables c)" 
    "Max (ran G) < 2 ^ (t + max_input_bits c I r)" 
    "is_serial_solution_for_problem (IMP_Minus_to_SAS_Plus c I r G t) plan"
    "\<forall>s1. \<exists>s2. \<exists>t' \<le> t. (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2" 
  shows "\<exists>s1 s2 t'. t' \<le> t \<and> I \<subseteq>\<^sub>m Some \<circ> s1 \<and> G \<subseteq>\<^sub>m Some \<circ> s2 \<and> (c, s1)  \<Rightarrow>\<^bsup>t'\<^esup> s2" 
proof -
  let ?guess_range = "max_input_bits c I r"
  let ?n = "t + ?guess_range + 1"
  let ?c' = "IMP_Minus_To_IMP_Minus_Minus c ?n"
  let ?I = "(IMP_Minus_initial_to_IMP_Minus_Minus I ?n ?guess_range) 
    |` (set (enumerate_variables ?c'))"
  let ?G = "(IMP_Minus_State_To_IMP_Minus_Minus_partial G ?n ?n) |` (set (enumerate_variables ?c'))"

  have "finite (ran I)" "finite (ran G)" 
    using \<open>dom I \<subseteq> set (IMP_Minus_Max_Constant.all_variables c)\<close> 
      \<open>dom G \<subseteq> set (IMP_Minus_Max_Constant.all_variables c)\<close>
    finite_set by(auto simp: finite_subset intro!: finite_ran)

  have "?n > 0" by simp 

  obtain plan' where "length plan' \<le> length plan
    \<and> is_serial_solution_for_problem_sas_plus_plus (imp_minus_minus_to_sas_plus ?c' ?I ?G) plan'" 
    using SAS_Plus_To_SAS_Plus_Plus 
      \<open>is_serial_solution_for_problem (IMP_Minus_to_SAS_Plus c I r G t) plan\<close>
    by (metis IMP_Minus_to_SAS_Plus_def imp_minus_minus_to_sas_plus_valid)

  then obtain s1 s2 t' where "(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1"
    "dom s1 = set (enumerate_variables ?c')"
    "(?G|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s2" "t' \<le> length plan'" 
    "(?c', s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)"
    using sas_plus_plus_to_imp_minus_minus by fastforce

  let ?s1' = "IMP_Minus_Minus_State_To_IMP_Minus s1 ?n" 
  let ?s2' = "IMP_Minus_Minus_State_To_IMP_Minus s2 ?n"

  have "s1 v = (IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n |` (set (enumerate_variables ?c'))) v" 
    for v
  proof(cases "v \<in> set (enumerate_variables ?c')")
    case True
    thus ?thesis
    proof (cases "v \<in> dom ?I")
      case True
      hence "s1 v = ?I v" using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close> 
        by(auto simp: map_le_def)
      thus ?thesis using \<open>v \<in> set (enumerate_variables ?c')\<close> 
          apply(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_partial_def  
              IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def var_to_var_bit_eq_Some_iff
              var_to_operand_bit_eq_Some_iff IMP_Minus_initial_to_IMP_Minus_Minus_def
              IMP_Minus_State_To_IMP_Minus_Minus_partial_of_operand_bit_to_var
              IMP_Minus_State_To_IMP_Minus_Minus_def
              nth_bit_of_IMP_Minus_Minus_State_To_IMP_Minus 
              split: option.splits)
        using \<open>v \<in> dom ?I\<close> by(auto simp: map_comp_def IMP_Minus_initial_to_IMP_Minus_Minus_def 
            IMP_Minus_State_To_IMP_Minus_Minus_partial_def
            IMP_Minus_State_To_IMP_Minus_Minus_partial_of_operand_bit_to_var 
            var_bit_to_var_neq_operand_bit_to_var[symmetric]
            dest!: set_mp[OF IMP_Minus_To_IMP_Minus_Minus_variables[OF \<open>?n > 0\<close>, simplified]] 
            split: option.splits char.splits bool.splits)
    next
      case False
      then obtain v' i where "v = var_bit_to_var (v', i) \<and> i < ?guess_range" using \<open>\<not>(v \<in> dom ?I)\<close>
         \<open>v \<in> set (enumerate_variables ?c')\<close>
        set_mp[OF IMP_Minus_To_IMP_Minus_Minus_variables \<open>v \<in> set (enumerate_variables ?c')\<close>]
        apply(auto simp: IMP_Minus_initial_to_IMP_Minus_Minus_def map_comp_def
            IMP_Minus_State_To_IMP_Minus_Minus_partial_def split: option.splits)
        using leI by blast
      thus ?thesis using \<open>v \<in> set (enumerate_variables ?c')\<close> 
          \<open>dom s1 = set (enumerate_variables ?c')\<close>
        by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_def 
            nth_bit_of_IMP_Minus_Minus_State_To_IMP_Minus
            IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def split: option.splits)
    qed
  next
    case False
    thus ?thesis using \<open>dom s1 = set (enumerate_variables ?c')\<close> by auto
  qed
  hence "s1 = IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n |` (set (enumerate_variables ?c'))" by auto

  have "I v = Some y \<Longrightarrow> ?s1' v = y" for v y 
  proof -
    assume "I v = Some y" 
    hence "v \<in> set (IMP_Minus_Max_Constant.all_variables c)" 
      using \<open>dom I \<subseteq> set (IMP_Minus_Max_Constant.all_variables c)\<close> by auto
    hence "\<forall>i < ?n. var_bit_to_var (v, i) \<in> set (enumerate_variables ?c')" 
      by(auto simp: var_bit_in_IMP_Minus_Minus_variables)
    moreover hence "i < ?n \<longrightarrow> s1 (var_bit_to_var (v, i)) = ?I (var_bit_to_var (v, i))" for i
      using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close> \<open>I v = Some y\<close>
      by(auto simp: IMP_Minus_initial_to_IMP_Minus_Minus_def map_le_def
          IMP_Minus_State_To_IMP_Minus_Minus_def dom_def
          IMP_Minus_State_To_IMP_Minus_Minus_partial_def map_comp_def split: option.splits) 
    ultimately show "?s1' v = y" using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close>
       less_le_trans[OF initial_state_element_less_two_to_the_max_input_bits[where ?c=c and ?r=r]]
       \<open>I v = Some y\<close> bit_at_index_geq_max_input_bits_is_zero_in_initial_state \<open>finite (ran I)\<close>
      by(fastforce simp add: IMP_Minus_initial_to_IMP_Minus_Minus_def map_comp_def 
          IMP_Minus_Minus_State_To_IMP_Minus_def power_add 
          algebra_simps nth_append bit_list_to_nat_eq_nat_iff
          IMP_Minus_State_To_IMP_Minus_Minus_partial_def split: if_splits option.splits)
  qed
  hence "I \<subseteq>\<^sub>m Some \<circ> ?s1'" by(auto simp: map_le_def)
  
  hence "t_small_step_fun t' 
  (?c', IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n |` set (enumerate_variables ?c')) = (SKIP, s2)"
    using \<open>(?c', s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP, s2)\<close> 
      \<open>s1 = IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n |` (set (enumerate_variables ?c'))\<close>
    by(auto simp: t_small_step_fun_t_small_step_equivalence)
  moreover have "t_small_step_fun t' 
    (?c', IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n |` set (enumerate_variables ?c')) 
    = (fst (t_small_step_fun t' (?c', IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n)),
       snd  (t_small_step_fun t' (?c', IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n)) 
      |` set (enumerate_variables ?c'))" 
    by (auto simp: t_small_step_fun_restrict_variables)
  ultimately obtain s2' where "t_small_step_fun t' (?c', IMP_Minus_State_To_IMP_Minus_Minus ?s1' ?n)
    = (SKIP, s2')" "s2' |` set (enumerate_variables ?c') = s2" by auto (metis prod.collapse)

  moreover obtain t'' s2'' where "t'' \<le> t" "(c, ?s1') \<Rightarrow>\<^bsup>t''\<^esup> s2''" 
    using \<open>\<forall>s1. \<exists>s2. \<exists>t' \<le> t. (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2\<close> by blast
  moreover have "?guess_range \<le> i \<Longrightarrow> s1 (var_bit_to_var (v, i)) \<noteq> Some One" for i v 
  proof(cases "(var_bit_to_var (v, i)) \<in> set (enumerate_variables ?c')")
    case True
    assume "?guess_range \<le> i"
    hence "?I (var_bit_to_var (v, i)) = Some Zero" 
      using \<open>(var_bit_to_var (v, i)) \<in> set (enumerate_variables ?c')\<close>  
      by(auto simp: IMP_Minus_initial_to_IMP_Minus_Minus_def 
          IMP_Minus_State_To_IMP_Minus_Minus_partial_def 
          dest!: set_mp[OF IMP_Minus_To_IMP_Minus_Minus_variables]
          split: option.splits)
    thus ?thesis using \<open>(?I|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s1\<close> by(auto simp: map_le_def dom_def)
  next
    case False
    then show ?thesis using \<open>dom s1 = set (enumerate_variables ?c')\<close> by auto
  qed
   
  moreover hence "finite (range (IMP_Minus_Minus_State_To_IMP_Minus s1 ?n))" 
    "Max (range (IMP_Minus_Minus_State_To_IMP_Minus s1 ?n)) < 2 ^ ?guess_range" 
    using all_bits_geq_k_Zero_then_IMP_Minus_Minus_State_To_IMP_Minus_range_limited by blast+
  ultimately have "s2' = IMP_Minus_State_To_IMP_Minus_Minus s2'' ?n" 
    using IMP_Minus_Minus_To_IMP_Minus_aux max_constant_less_two_to_the_max_input_bits
    by(auto simp: power_add algebra_simps mult_2 trans_less_add2)

  have "G v = Some y \<Longrightarrow> s2'' v = y" for v y 
  proof -
    assume "G v = Some y" 
    hence "v \<in> set (IMP_Minus_Max_Constant.all_variables c)" 
      using \<open>dom G \<subseteq> set (IMP_Minus_Max_Constant.all_variables c)\<close> by auto
    hence "\<forall>i < ?n. var_bit_to_var (v, i) \<in> set (enumerate_variables ?c')" 
      by(auto simp: var_bit_in_IMP_Minus_Minus_variables)
    moreover hence "i < ?n \<longrightarrow> s2 (var_bit_to_var (v, i)) = ?G (var_bit_to_var (v, i))" for i
      using \<open>(?G|` set (enumerate_variables ?c')) \<subseteq>\<^sub>m s2\<close> \<open>G v = Some y\<close>
      by(auto simp: IMP_Minus_initial_to_IMP_Minus_Minus_def map_le_def
          IMP_Minus_State_To_IMP_Minus_Minus_def dom_def
          IMP_Minus_State_To_IMP_Minus_Minus_partial_def map_comp_def split: option.splits) 
    moreover hence "i < ?n \<longrightarrow> s2' (var_bit_to_var (v, i)) = ?G (var_bit_to_var (v, i))" for i 
      using \<open>s2' |` set (enumerate_variables ?c') = s2\<close> 
        \<open>\<forall>i < ?n. var_bit_to_var (v, i) \<in> set (enumerate_variables ?c')\<close> by auto
    ultimately have "i < ?n \<longrightarrow> map_option (\<lambda>x. nth_bit x i) (G v) = Some (nth_bit (s2'' v) i)" for i 
      using  \<open>s2' = IMP_Minus_State_To_IMP_Minus_Minus s2'' ?n\<close> \<open>G v = Some y\<close>
      by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_def 
          IMP_Minus_State_To_IMP_Minus_Minus_partial_def
          IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)
    thus "s2'' v = y"
      apply - apply(rule all_bits_equal_then_equal[where ?n = "?n"])
      apply(insert IMP_Minus_space_growth[OF \<open>(c, ?s1') \<Rightarrow>\<^bsup>t''\<^esup> s2''\<close> 
          \<open>finite (range (IMP_Minus_Minus_State_To_IMP_Minus s1 ?n))\<close>, where ?k="?guess_range"])
      using \<open>Max (range (IMP_Minus_Minus_State_To_IMP_Minus s1 ?n)) < 2 ^ ?guess_range\<close>
        max_constant_less_two_to_the_max_input_bits \<open>t'' \<le> t\<close>
        apply simp
        apply(rule less_le_trans[where ?y="2 ^ (t + max_input_bits c I r)"])
         apply(auto simp: algebra_simps)
        apply(rule less_le_trans[where ?y="2 ^ (t'' + max_input_bits c I r)"])
      using \<open>G v = Some y\<close>  apply(auto)
      apply(rule less_le_trans[where ?y="2 ^ (t + max_input_bits c I r)"])
       apply (meson ran_def Max_ge \<open>finite (ran G)\<close> \<open>Max (ran G) < 2 ^ (t + max_input_bits c I r)\<close> 
          le_less_trans ranI)
      by simp
  qed
  hence "G \<subseteq>\<^sub>m Some \<circ> s2''" by(auto simp: map_le_def)

  show ?thesis using \<open>t'' \<le> t\<close> \<open>(c, ?s1') \<Rightarrow>\<^bsup>t''\<^esup> s2''\<close> \<open>I \<subseteq>\<^sub>m Some \<circ> ?s1'\<close> \<open>G \<subseteq>\<^sub>m Some \<circ> s2''\<close>
    by auto
qed

end