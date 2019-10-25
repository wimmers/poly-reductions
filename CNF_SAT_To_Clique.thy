theory CNF_SAT_To_Clique
  imports Main "Three_Sat_To_Set_Cover" HOL.Enum
begin

subsection \<open>Preliminaries\<close>

definition cnf_sat where
  "cnf_sat \<equiv> {F. sat F}"

definition
  "is_clique E C \<equiv> \<forall>u \<in> C. \<forall>v \<in> C. {u, v} \<in> E \<or> v = u"

definition
  "clique \<equiv> {(E, k). \<exists>C. ugraph E \<and> C \<subseteq> \<Union> E \<and> card C \<ge> k \<and> is_clique E C}"

definition
  "cnf_sat_to_clique F \<equiv> (
    {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j}, length F)"



text \<open>Just some tests\<close>

lemma f_not_sat_not_clique: 
  assumes "F \<notin> cnf_sat"
  shows "cnf_sat_to_clique F \<notin> clique"
  sorry

lemma cnf_sat_has_pos: "F \<in> cnf_sat \<and> models \<sigma> F \<and> F \<noteq> []  \<Longrightarrow> \<exists>p. lift \<sigma> p"
  sorry


theorem "F \<in> cnf_sat \<longleftrightarrow> cnf_sat_to_clique F \<in> clique"
   unfolding cnf_sat_to_clique_def clique_def cnf_sat_def sat_def models_def 
      is_clique_def ugraph_def
proof (induction F)
  case Nil
  then show ?case by auto   
next
  case (Cons a F)
  then show ?case sorry
qed

 

theorem is_reduction_cnf_sat_to_clique: 
  "is_reduction cnf_sat_to_clique cnf_sat clique"
  unfolding is_reduction_def
proof safe
  fix F :: "'a lit set list"
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>1 where "\<sigma>1 \<Turnstile> F" 
    unfolding cnf_sat_def sat_def by auto
  obtain E k where "cnf_sat_to_clique F = (E, k)" by force
  show "cnf_sat_to_clique F \<in> clique" sorry
next
  fix F:: "'a lit set list"
  assume 1: "cnf_sat_to_clique F  \<in> clique"
  then show "F \<in> cnf_sat "  using f_not_sat_not_clique by auto
qed



end