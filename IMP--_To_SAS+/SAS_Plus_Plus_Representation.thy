(*
  Author: Mohammad Abdulaziz, Fred Kurz, Florian Keßler
*)
theory SAS_Plus_Plus_Representation
imports "Verified_SAT_Based_AI_Planning.SAS_Plus_Representation"
begin

section "SAS++ Representation"

text \<open> We introduce SAS++, an adopted version of SAS+ that allows for partial initial states
      where not all variables need to have a defined value. \<close>

definition "is_valid_problem_sas_plus_plus \<Psi> 
  \<equiv> let ops = operators_of \<Psi>
      ; vs = variables_of \<Psi>
      ; I = initial_of \<Psi>
      ; G = goal_of \<Psi>
      ; D = range_of \<Psi>
    in list_all (\<lambda>v. D v \<noteq> None) vs
    \<and> list_all (is_valid_operator_sas_plus \<Psi>) ops 
    \<and> list_all (\<lambda> v. length (the (D v)) > 0) vs  
    \<and> (\<forall>v. I v \<noteq> None \<longrightarrow> ListMem v vs) 
    \<and> (\<forall>v. I v \<noteq> None \<longrightarrow> ListMem (the (I v)) (the (D v)))
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem v vs)
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem (the (G v)) (the (D v)))" 


(* TODO can be replaced by proof for sublocale? *)
lemma is_valid_problem_sas_plus_plus_then:
  fixes \<Psi>::"('v,'d) sas_plus_problem"
  assumes "is_valid_problem_sas_plus_plus \<Psi>"
  shows "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v" 
proof -
  let ?vs = "sas_plus_problem.variables_of \<Psi>"
    and ?ops = "sas_plus_problem.operators_of \<Psi>"
    and ?I = "sas_plus_problem.initial_of \<Psi>"
    and ?G = "sas_plus_problem.goal_of \<Psi>"
    and ?D = "sas_plus_problem.range_of \<Psi>"
  {
    fix v 
    have "(?D v \<noteq> None \<and> ?D v \<noteq> Some []) \<longleftrightarrow> ((\<R>\<^sub>+ \<Psi> v) \<noteq> {})"
      by (cases "?D v"; (auto simp: range_of'_def))
  } note nb = this
  have nb\<^sub>1: "\<forall>v \<in> set ?vs. ?D v \<noteq> None"
    and nb\<^sub>4: "\<forall>v \<in> set ?vs. length (the (?D v)) > 0" 
    and "\<forall>op \<in> set ?ops. is_valid_operator_sas_plus \<Psi> op"
    and "\<forall>v. ?I v \<noteq> None \<longrightarrow> v \<in> set ?vs"
    and nb\<^sub>2: "\<forall>v. ?I v \<noteq> None \<longrightarrow> the (?I v) \<in> set (the (?D v))"
    and "\<forall>v. ?G v \<noteq> None \<longrightarrow> v \<in> set ?vs"
    and nb\<^sub>3: "\<forall>v. ?G v \<noteq> None \<longrightarrow> the (?G v) \<in> set (the (?D v))"
    using assms 
    unfolding SAS_Plus_Plus_Representation.is_valid_problem_sas_plus_plus_def Let_def 
      list_all_iff ListMem_iff 
    by argo+
  then have G3: "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and G4: "dom ((\<Psi>)\<^sub>I\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and G5: "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    unfolding variables_of_def operators_of_def
    by auto+
  moreover {
    fix v
    assume "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    then have "?D v \<noteq> None"
      using nb\<^sub>1 
      by force+
  } note G6 = this
  moreover {
    fix v
    assume "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    then have "(\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
      using G6 nb\<^sub>4
      by(auto simp: range_of'_def split: option.splits)
  }
  moreover {
    fix v
    assume "v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+)"
    moreover have "((\<Psi>)\<^sub>I\<^sub>+) v \<noteq> None"
      using calculation
      by blast+
    moreover {
      have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using G4 calculation(1)
        by fast
      then have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
        using range_of_not_empty
        unfolding range_of'_def
        using G6 
        by fast+
      hence "set (the (?D v)) = \<R>\<^sub>+ \<Psi> v" 
        by (simp add: \<open>sas_plus_problem.range_of \<Psi> v \<noteq> None\<close> option.case_eq_if range_of'_def)
    }
    ultimately have "the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
      using nb\<^sub>2
      by force
  }
  moreover {
    fix v
    assume "v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+)"
    then have "((\<Psi>)\<^sub>G\<^sub>+) v \<noteq> None"
      by blast
    moreover {
      have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using G5 calculation(1)
        by fast
      then have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
        using range_of_not_empty
        using G6
        by fast+
      hence "set (the (?D v)) = \<R>\<^sub>+ \<Psi> v" 
        by (simp add: \<open>sas_plus_problem.range_of \<Psi> v \<noteq> None\<close> option.case_eq_if range_of'_def)
    }
    ultimately have "the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
      using nb\<^sub>3
      by auto
  }
  ultimately show "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    by auto
qed

end