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

lemma cnf_sat_to_clique_ugraph: "F\<in> cnf_sat \<Longrightarrow> ugraph (fst (cnf_sat_to_clique F))"
  sorry

lemma cnf_sat_has_pos: "F \<in> cnf_sat \<and> models \<sigma> F \<and> F \<noteq> []  \<Longrightarrow> \<exists>p. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)

lemma all_clauses_have_pos: "F \<in> cnf_sat \<and> models \<sigma> F  \<Longrightarrow> \<forall>i < (length F). \<exists>p \<in> F!i. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)

lemma clique_in_graph: "F \<in> cnf_sat \<and> C =  {(l1, i) | l1 i . i < length F \<and> l1 \<in> F ! i \<and> lift \<sigma> l1} \<Longrightarrow> C \<subseteq>  \<Union>  (fst (cnf_sat_to_clique F))"  (*\<forall>u \<in> C.
     \<forall>v \<in> C. {u, v} \<in> (fst (cnf_sat_to_clique F)) \<or> u = v"*) 
  sorry

lemma clique_from_model: "models \<sigma> F \<Longrightarrow> is_clique (fst (cnf_sat_to_clique F)) {(l1, i) | l1 i . i < length F \<and> l1 \<in> F ! i \<and> lift \<sigma> l1}"
  apply(auto simp add: is_clique_def models_def cnf_sat_to_clique_def)
  sorry

lemma size_clique: "F \<in> cnf_sat \<Longrightarrow> models \<sigma> F \<Longrightarrow> ((card  {(l1, i) | l1 i . i < length F \<and> l1 \<in> F ! i \<and> lift \<sigma> l1}) \<ge> (length F))"
  sorry

lemma "F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique"
proof -
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>  where "\<sigma> \<Turnstile> F" unfolding cnf_sat_def sat_def by auto
  then have models_sigma: "models \<sigma> F" by auto
  obtain C where "C = {(l1, i) | l1 i . i < length F \<and> l1 \<in> F ! i \<and> lift \<sigma> l1}" by auto
  then have c_def: "C = {(l1, i) | l1 i . i < length F \<and> l1 \<in> F ! i \<and> lift \<sigma> l1}" by auto
  then have is_c: "is_clique (fst (cnf_sat_to_clique F)) C" using f_cnf_sat models_sigma clique_from_model by auto
  then have card_C_length: "card C \<ge> (length F)" using size_clique f_cnf_sat using size_clique f_cnf_sat models_sigma c_def by auto
  then have card_C: "card C \<ge> (snd (cnf_sat_to_clique F))" using cnf_sat_to_clique_def by (simp add: cnf_sat_to_clique_def)
  have clique_contained: "C \<subseteq> \<Union> (fst (cnf_sat_to_clique F))" using clique_in_graph c_def f_cnf_sat by blast
  have ug: "ugraph (fst(cnf_sat_to_clique F))" using  cnf_sat_to_clique_ugraph f_cnf_sat by(auto)
  then have "\<exists> C'. ugraph (fst (cnf_sat_to_clique F)) \<and> C' \<subseteq> \<Union> (fst (cnf_sat_to_clique F)) \<and> card C' \<ge> (snd (cnf_sat_to_clique F)) \<and> is_clique (fst (cnf_sat_to_clique F)) C'"
    using card_C is_c clique_contained by auto
  then have "cnf_sat_to_clique F \<in> {(E, k). \<exists>C. ugraph E \<and> C \<subseteq> \<Union> E \<and> card C \<ge> k \<and> is_clique E C}" by (simp add: case_prod_beta')
  then show ?thesis using clique_def by(auto simp add: clique_def)
qed

lemma  cnf_sat_impl_clique:  "F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique"
proof (induction F)
  case Nil
  then show ?case unfolding cnf_sat_to_clique_def clique_def cnf_sat_def sat_def models_def 
      is_clique_def ugraph_def by auto
next
  case (Cons a F)
  then have a1: "(a#F) \<in> cnf_sat" by simp
  then obtain \<sigma>1 where "\<sigma>1 \<Turnstile> a#F" unfolding cnf_sat_def sat_def by auto
  have "F \<in> cnf_sat" 
    by (metis \<open>\<sigma>1 \<Turnstile> a # F\<close> cnf_sat_def mem_Collect_eq models_def sat_def set_subset_Cons subset_code(1))
  then have "cnf_sat_to_clique F \<in> clique" using Cons.IH by auto
  then have "\<exists>l. l\<in> a \<and> (lift \<sigma>1 l)" unfolding lift_def models_def using \<open>\<sigma>1 \<Turnstile> a # F\<close> all_clauses_have_pos a1 apply(auto split: lit.split) sorry
  then obtain l where "l\<in> a \<and> (lift \<sigma>1 l)" by auto

  (*parameter k*)
  then obtain E k where "cnf_sat_to_clique F = (E, k)" by force
  then have k_length: "k = length F" unfolding cnf_sat_to_clique_def by auto
  obtain E' k' where "cnf_sat_to_clique (a#F) = (E', k')" by force
  then have "k' = length (a#F)" unfolding cnf_sat_to_clique_def by auto 
  then have "k' = k+1" unfolding cnf_sat_to_clique_def  using k_length by auto
  then show ?case sorry

  (*parameter E, (l, i) war vorher nicht drin, jetzt schon und hat verbindungen in die clique*)
(*exists cliqeu, die nur models parameter enthält*)
(*verbindung zu l1*)
(*size ist eins größer*)
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
  show "cnf_sat_to_clique F \<in> clique" by (simp add: cnf_sat_impl_clique f_cnf_sat)
next
  fix F:: "'a lit set list"
  assume 1: "cnf_sat_to_clique F  \<in> clique"
  then show "F \<in> cnf_sat "  using f_not_sat_not_clique by auto
qed



end