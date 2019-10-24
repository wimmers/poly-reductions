theory CNF_SAT_To_Clique
  imports Main "Three_Sat_To_Set_Cover"
begin

subsection \<open>Preliminaries\<close>

definition cnf_sat where
  "cnf_sat \<equiv> {F. sat F}"

definition
  "is_clique E C \<equiv> \<forall>u \<in> C. \<forall>v \<in> C. {u, v} \<in> E \<or> v = u"

definition
  "clique \<equiv> {(E, k). \<exists>C. ugraph E \<and> C \<subseteq> \<Union> E \<and> card C \<ge> k \<and> is_clique E C}"


end