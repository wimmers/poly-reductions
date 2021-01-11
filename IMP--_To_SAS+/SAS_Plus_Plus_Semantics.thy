(*
  Author: Mohammad Abdulaziz, Fred Kurz, Florian Keßler
*)
theory SAS_Plus_Plus_Semantics  
  imports "SAS_Plus_Plus_Representation" "Verified_SAT_Based_AI_Planning.SAS_Plus_Semantics"
    "Verified_SAT_Based_AI_Planning.List_Supplement"
    "Verified_SAT_Based_AI_Planning.Map_Supplement"
begin
section "SAS+ Semantics"


subsection "Serial Execution Semantics"

text \<open> Similarly, serial SAS++ solutions are defined like in SAS+, but instead of having a single
      initial state, we assert that there exists one that conforms to the partial initial state,
      and from which a goal state is reachable, using the SAS+ definition of executing a plan. \<close>

definition is_serial_solution_for_problem
  :: "('variable, 'domain) sas_plus_problem \<Rightarrow> ('variable, 'domain) sas_plus_plan \<Rightarrow> bool" 
  where "is_serial_solution_for_problem \<Psi> \<psi>
    \<equiv> let 
        I = sas_plus_problem.initial_of \<Psi>
        ; G = sas_plus_problem.goal_of \<Psi>
        ; ops = sas_plus_problem.operators_of \<Psi>
      in (\<exists>I'. I \<subseteq>\<^sub>m I' \<and> dom I' = set ((\<Psi>)\<^sub>\<V>\<^sub>+)
        \<and> G \<subseteq>\<^sub>m execute_serial_plan_sas_plus I' \<psi> 
        \<and> list_all (\<lambda>op. ListMem op ops) \<psi>)" 

end