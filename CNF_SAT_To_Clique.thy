theory CNF_SAT_To_Clique
  imports Main "Three_Sat_To_Set_Cover" HOL.Enum
begin

subsection \<open>Preliminaries\<close>


definition
  "ugraph_nodes E V \<equiv> ugraph E \<and>  \<Union> E \<subseteq> V"

definition cnf_sat where
  "cnf_sat \<equiv> {F. sat F \<and> (\<forall>c \<in> set F. finite c)}"

definition
  "is_clique E C \<equiv> \<forall>u \<in> C. \<forall>v \<in> C. v=u \<or> {u, v} \<in> E"


definition
  "clique_old \<equiv> {(E, k). \<exists>C. ugraph E \<and> C \<subseteq> \<Union> E \<and> card C \<ge> k \<and> is_clique E C}"

definition
 "clique \<equiv> {(E, V , k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}"

definition
  "cnf_sat_to_clique_old F \<equiv> (
    {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j}, length F)"

definition
  "cnf_sat_to_clique F \<equiv> (
    {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j},
    {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i},
    length F)"



text \<open>Just some tests\<close>

lemma f_not_sat_not_clique: 
  assumes "F \<notin> cnf_sat"
  shows "cnf_sat_to_clique F \<notin> clique"
  sorry

lemma models_smaller: "models \<sigma> (a#F) \<Longrightarrow> models \<sigma> F"
  by(auto simp add: models_def)

text\<open>Similar to the proof in Three_Sat_To_Set_Cover\<close>
lemma cnf_sat_to_clique_ugraph: "F\<in> cnf_sat \<Longrightarrow> ugraph (fst (cnf_sat_to_clique F))"
proof - 
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using prod_cases3 by blast
  assume "F \<in> cnf_sat"
  then have "\<forall>c \<in> set F. finite c" by(auto simp add: cnf_sat_def)
  then have "\<forall>c \<in> set F. \<exists>s. card c \<le> s" by auto
  then obtain s where "s = Max {card c | c. c \<in> set F}" by(auto)
  then have "\<forall>s' \<in> {card c | c. c \<in> set F}. s'\<le> s" by auto
  then have wf: "\<forall>c\<in> set F. card c \<le> s" by(auto)
  from \<open>F \<in> cnf_sat\<close> have fin_1: "finite (\<Union> (set F))" unfolding cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
  let ?S = "((\<Union> (set F)) \<times> {0..<length F}) \<times> ((\<Union> (set F)) \<times> {0..<length F})"
  have "ugraph E"
    using \<open>cnf_sat_to_clique F = (E,V, k)\<close> wf unfolding cnf_sat_to_clique_def is_clique_def ugraph_def
    apply safe
    subgoal
      using fin_1 by (fastforce intro: finite_surj[where A = "?S"])
    by (force simp: card_insert_if)+
  then show ?thesis
    by (simp add: \<open>cnf_sat_to_clique F = (E, V, k)\<close>)
qed

lemma edges_between_nodes:
  assumes "F \<in> cnf_sat" "E  = fst (cnf_sat_to_clique F)" "V  = fst ( snd (cnf_sat_to_clique F))" "X \<in> E"
  shows " X \<subseteq> V"
proof -
  have e_def: "E = {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j} " using cnf_sat_to_clique_def assms 
    by (metis (mono_tags, lifting) fst_eqD)
  have v_def: "V = {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}" using cnf_sat_to_clique_def assms
    by (metis (mono_tags, lifting) fst_conv old.prod.exhaust snd_conv)
  then obtain l1 l2 i j where "X = {(l1, i), (l2, j)}" using e_def assms by(force)
  then have i1: "i < length F" using e_def \<open>X \<in> E \<close> by (smt Pair_inject doubleton_eq_iff mem_Collect_eq)
  then have i2: " l1 \<in> F !i" using e_def \<open>X \<in> E\<close> \<open>X = {(l1, i), (l2, j)}\<close> by (smt Pair_inject doubleton_eq_iff mem_Collect_eq)
  then have j1: "j < length F" using e_def \<open>X \<in> E \<close> \<open>X = {(l1, i), (l2, j)}\<close> by (smt Pair_inject doubleton_eq_iff mem_Collect_eq)
  then have j2: " l2 \<in> F !j" using e_def \<open>X \<in> E\<close> \<open>X = {(l1, i), (l2, j)}\<close> by (smt Pair_inject doubleton_eq_iff mem_Collect_eq)
  have "(l1, i) \<in> V \<and> (l2, j) \<in> V" using i1 i2 j1 j2 v_def by(auto)
  then show ?thesis using assms  \<open>X = {(l1, i), (l2, j)}\<close>
    by blast
qed

lemma cnf_sat_to_clique_ugraph_nodes:
  assumes "F \<in> cnf_sat"
  shows "ugraph_nodes (fst(cnf_sat_to_clique F)) (fst (snd (cnf_sat_to_clique F)))"
  apply(auto simp add: cnf_sat_to_clique_ugraph ugraph_nodes_def assms)
  using edges_between_nodes assms by blast

definition get_some_true where
  "get_some_true F \<sigma> i \<equiv> SOME l. lift \<sigma> l \<and> l \<in> F ! i"

lemma get_some_true_equal: "(get_some_true F \<sigma> i, i) = ( get_some_true F \<sigma> i, i)" 
  unfolding get_some_true_def by(auto)

lemma aux:
  assumes "F \<in> cnf_sat"  "models \<sigma> F" "u\<in>{(get_some_true F \<sigma> i, i) |i. i < length F}" "v\<in>{(get_some_true F \<sigma> i, i) |i. i < length F}"
  shows "{u, v} \<in> fst( cnf_sat_to_clique F) \<or> u = v"
proof (cases "u=v")
  case False
   have select: "(\<sigma>\<up>) (get_some_true F \<sigma> i) \<and> (get_some_true F \<sigma> i) \<in> F ! i" if "i < length F" for i
     using \<open>\<sigma> \<Turnstile> F\<close> that unfolding models_def get_some_true_def by - (rule someI_ex, auto)
   obtain u1 u2 where "u=(u1, u2)" using \<open>u\<in> _\<close> by(auto) 
   obtain v1 v2 where "v=(v1, v2)" using \<open>v\<in> _\<close> by(auto)
   have "u2 < length F"  using \<open>u\<in> _\<close>  \<open>u= (u1, u2)\<close> by(auto)
   have 1:"v2 < length F"  using \<open>v\<in> _\<close>  \<open>v= (v1, v2)\<close> by(auto)
   have 2: "u2 \<noteq> v2" using  get_some_true_equal \<open>u = (u1, u2)\<close> \<open>u \<in> _\<close> \<open>v = (v1, v2)\<close> \<open>v \<in>_\<close> using False by blast
   moreover have l1: "lift \<sigma> u1" using \<open>u = (u1, u2)\<close> assms select  unfolding get_some_true_def by(auto)
   moreover have l2:"lift \<sigma> v1" using  \<open>v = (v1, v2)\<close>  assms select  unfolding get_some_true_def by(auto)
   from l1 l2 have 3: "\<not> conflict u1 v1" unfolding get_some_true_def using conflict_models_ccontr get_some_true_def \<open>u = (u1, u2)\<close> \<open>u \<in> _\<close> \<open>v = (v1, v2)\<close> \<open>v \<in>_\<close> by(auto)
   then have i1:"v1 \<in> F ! v2" using \<open>v = (v1, v2)\<close> \<open>v \<in> _\<close> by (simp add: select) 
   then have i2: "u1 \<in> F ! u2" using \<open>u = (u1, u2)\<close> \<open>u \<in> _\<close> by (simp add: select) 
   then have " {u, v} \<in> {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F \<and> i \<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}" 
     using\<open>u = (u1, u2)\<close> \<open>u \<in> _\<close> \<open>v = (v1, v2)\<close> \<open>v \<in>_\<close> l1 l2 i1 i2 1 2 3 by(auto)
   then have "{u,v} \<in> fst (cnf_sat_to_clique F)" by(auto simp add: cnf_sat_to_clique_def)
  then show ?thesis by(auto)
next
  case True
  then show ?thesis by(auto)
qed

lemma aux2: "fst (cnf_sat_to_clique F) = {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F \<and> i \<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  by(auto simp add: cnf_sat_to_clique_def)
 

lemma is_clique:
  assumes "F \<in> cnf_sat" "models \<sigma> F"
  shows "is_clique (fst (cnf_sat_to_clique F))  {( get_some_true F \<sigma> i, i) | i. i < length F}"
  unfolding is_clique_def using assms aux by(fastforce)

lemma cnf_sat_has_pos: "F \<in> cnf_sat \<and> models \<sigma> F \<and> F \<noteq> []  \<Longrightarrow> \<exists>p. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)

lemma all_clauses_have_pos: "F \<in> cnf_sat \<and> models \<sigma> F  \<Longrightarrow> \<forall>i < (length F). \<exists>p \<in> F!i. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)

lemma card_clique:
  assumes "F \<in> cnf_sat" "models \<sigma> F" "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}"
  shows "card C \<ge> length F"
unfolding assms setcompr_eq_image by (subst card_image) (auto intro: inj_onI)

lemma aux4:
  assumes "F \<in> cnf_sat" "i<length F" "models \<sigma> F"
  shows "get_some_true F \<sigma> i \<in> F!i"
proof-
  obtain v where "v = get_some_true F \<sigma> i" unfolding get_some_true_def by force
  then have "v \<in> F ! i" unfolding get_some_true_def apply(auto) 
    by (metis (lifting) all_clauses_have_pos assms some_eq_ex)
  then show ?thesis using \<open>v=_\<close> by(auto)
qed

lemma aux3:
  assumes "F \<in> cnf_sat" "models \<sigma> F" "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}" " v \<in> C"
  shows "v \<in> fst(snd(cnf_sat_to_clique F))"
proof -
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using cnf_sat_to_clique_def by force
  then have " V = {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}" using cnf_sat_to_clique_def \<open>cnf_sat_to_clique F = (E, V, k)\<close> assms 
    by (metis (mono_tags, lifting) Pair_inject)
  have "\<forall> i < length F. get_some_true F \<sigma> i \<in> F!i" using assms aux4 by(auto)
  then show ?thesis using assms using \<open>V = {(l1, i) |l1 i. i < length F \<and> l1 \<in> F ! i}\<close> \<open>cnf_sat_to_clique F = (E, V, k)\<close> by force
qed

lemma clique_in_graph: 
  assumes  "F \<in> cnf_sat" "models \<sigma> F" "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}"
  shows "C\<subseteq> fst(snd (cnf_sat_to_clique F))"
  using aux3 assms by blast


lemma cnf_sat_impl_clique: "F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique"
proof -
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>  where "\<sigma> \<Turnstile> F" unfolding cnf_sat_def sat_def by auto
  then have models_sigma: "models \<sigma> F" by auto
  obtain C where "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}" 
    using models_sigma f_cnf_sat  by blast
  then have c_def: "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}" by auto
  then have is_c: "is_clique (fst (cnf_sat_to_clique F)) C" using f_cnf_sat models_sigma is_clique  by auto
  then have card_C_length: "card C \<ge> (length F)" using card_clique f_cnf_sat models_sigma c_def by auto
  then have card_C: "card C \<ge> (snd (snd (cnf_sat_to_clique F)))" using cnf_sat_to_clique_def by (simp add: cnf_sat_to_clique_def)
  have clique_contained: "C \<subseteq> fst(snd (cnf_sat_to_clique F))" using c_def f_cnf_sat clique_in_graph models_sigma by blast
  have ug: "ugraph_nodes (fst(cnf_sat_to_clique F)) (fst (snd (cnf_sat_to_clique F)))" using  cnf_sat_to_clique_ugraph_nodes f_cnf_sat by(auto)
  then have "\<exists> C'. ugraph_nodes (fst (cnf_sat_to_clique F)) (fst (snd( cnf_sat_to_clique F))) \<and> C' \<subseteq> fst(snd (cnf_sat_to_clique F)) \<and> card C' \<ge> (snd (snd(cnf_sat_to_clique F))) \<and> is_clique (fst (cnf_sat_to_clique F)) C'"
    using card_C is_c clique_contained ug by(auto)   
  then have "cnf_sat_to_clique F \<in> {(E, V, k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}" by (simp add: case_prod_beta')
  then show ?thesis using clique_def by(auto simp add: clique_def)
qed
 

theorem is_reduction_cnf_sat_to_clique: 
  "is_reduction cnf_sat_to_clique cnf_sat clique"
  unfolding is_reduction_def
proof safe
  fix F :: "'a lit set list"
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>1 where "\<sigma>1 \<Turnstile> F" 
    unfolding cnf_sat_def sat_def by auto
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using cnf_sat_to_clique_def by force
  show "cnf_sat_to_clique F \<in> clique" by (simp add: cnf_sat_impl_clique f_cnf_sat)
next
  fix F:: "'a lit set list"
  assume 1: "cnf_sat_to_clique F  \<in> clique"
  then show "F \<in> cnf_sat "  using f_not_sat_not_clique by auto
qed



end