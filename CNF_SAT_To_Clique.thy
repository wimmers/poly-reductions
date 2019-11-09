theory CNF_SAT_To_Clique
  imports Main "Three_Sat_To_Set_Cover" HOL.Enum
begin

subsection \<open>Preliminaries\<close>


definition
  "ugraph_nodes E V \<equiv> ugraph E \<and>  \<Union> E \<subseteq> V \<and> finite V"

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
         l1 \<in> F ! i \<and> l2 \<in> F ! j},
    {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i},
    length F)"

definition
  "cnf_sat_to_clique F \<equiv> (if finite (\<Union> (set F)) then (
    {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j},
    {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i},
    length F) else ({}, {}, 1))"

subsection \<open>F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique\<close>

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
    using fin_1 by(auto)
  then show ?thesis
    by (simp add: \<open>cnf_sat_to_clique F = (E, V, k)\<close>)
qed

lemma edges_between_nodes:
  assumes "F \<in> cnf_sat" "E  = fst (cnf_sat_to_clique F)" "V  = fst ( snd (cnf_sat_to_clique F))" "X \<in> E"
  shows " X \<subseteq> V"
proof -
  from \<open>F \<in> cnf_sat\<close> have fin_1: "finite (\<Union> (set F))" unfolding cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
  have e_def: "E = {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j} " using cnf_sat_to_clique_def assms fin_1
    by (metis (mono_tags, lifting) fst_eqD)
  have v_def: "V = {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}" using cnf_sat_to_clique_def assms fin_1
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

lemma finite_V:
  assumes "F \<in> cnf_sat"
  shows "finite (fst (snd (cnf_sat_to_clique F)))"
proof -
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using prod_cases3 by blast
  have "\<forall>c \<in> set F. finite c" using assms by(auto simp add: cnf_sat_def)
  then have "\<forall>c \<in> set F. \<exists>s. card c \<le> s" by auto
  then obtain s where "s = Max {card c | c. c \<in> set F}" by(auto)
  then have "\<forall>s' \<in> {card c | c. c \<in> set F}. s'\<le> s" by auto
  then have wf: "\<forall>c\<in> set F. card c \<le> s" by(auto)
  from \<open>F \<in> cnf_sat\<close> have fin_1: "finite (\<Union> (set F))" unfolding cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
  let ?S = "((\<Union> (set F)) \<times> {0..<length F})"
  have "finite V"
    using \<open>cnf_sat_to_clique F = (E,V, k)\<close> wf unfolding cnf_sat_to_clique_def is_clique_def ugraph_def
    using fin_1 by (fastforce intro: finite_surj[where A = "?S"])
  then show ?thesis
    by (simp add: \<open>cnf_sat_to_clique F = (E, V, k)\<close>)
qed

lemma cnf_sat_to_clique_ugraph_nodes:
  assumes "F \<in> cnf_sat"
  shows "ugraph_nodes (fst(cnf_sat_to_clique F)) (fst (snd (cnf_sat_to_clique F)))"
  apply(auto simp add: cnf_sat_to_clique_ugraph ugraph_nodes_def assms finite_V)
  using edges_between_nodes assms  by blast

definition get_some_true where
  "get_some_true F \<sigma> i \<equiv> SOME l. lift \<sigma> l \<and> l \<in> F ! i"

lemma get_some_true_equal: "(get_some_true F \<sigma> i, i) = ( get_some_true F \<sigma> i, i)" 
  unfolding get_some_true_def by(auto)

lemma get_some_true_yields_clique:
  assumes "F \<in> cnf_sat"  "models \<sigma> F" "u\<in>{(get_some_true F \<sigma> i, i) |i. i < length F}" "v\<in>{(get_some_true F \<sigma> i, i) |i. i < length F}"
  shows "{u, v} \<in> fst( cnf_sat_to_clique F) \<or> u = v"
proof (cases "u=v")
  case False
   have select: "(\<sigma>\<up>) (get_some_true F \<sigma> i) \<and> (get_some_true F \<sigma> i) \<in> F ! i" if "i < length F" for i
     using \<open>\<sigma> \<Turnstile> F\<close> that unfolding models_def get_some_true_def by - (rule someI_ex, auto)
   from \<open>F \<in> cnf_sat\<close> have fin_1: "finite (\<Union> (set F))" unfolding cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
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
   then have "{u,v} \<in> fst (cnf_sat_to_clique F)" by(auto simp add: cnf_sat_to_clique_def fin_1)
  then show ?thesis by(auto)
next
  case True
  then show ?thesis by(auto)
qed

lemma aux1: "finite (\<Union> (set F)) \<Longrightarrow> fst (cnf_sat_to_clique F) = {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F \<and> i \<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  by(auto simp add: cnf_sat_to_clique_def)
 

lemma is_clique:
  assumes "F \<in> cnf_sat" "models \<sigma> F"
  shows "is_clique (fst (cnf_sat_to_clique F))  {( get_some_true F \<sigma> i, i) | i. i < length F}"
  unfolding is_clique_def using assms get_some_true_yields_clique by(fastforce)

lemma cnf_sat_has_pos: "F \<in> cnf_sat \<and> models \<sigma> F \<and> F \<noteq> []  \<Longrightarrow> \<exists>p. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)

lemma all_clauses_have_pos: "F \<in> cnf_sat \<and> models \<sigma> F  \<Longrightarrow> \<forall>i < (length F). \<exists>p \<in> F!i. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)

lemma card_clique:
  assumes "F \<in> cnf_sat" "models \<sigma> F" "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}"
  shows "card C \<ge> length F"
unfolding assms setcompr_eq_image by (subst card_image) (auto intro: inj_onI)

lemma aux2:
  assumes "F \<in> cnf_sat" "i<length F" "models \<sigma> F"
  shows "get_some_true F \<sigma> i \<in> F!i"
proof-
  obtain v where "v = get_some_true F \<sigma> i" unfolding get_some_true_def by force
  then have "v \<in> F ! i" unfolding get_some_true_def apply(auto) 
    by (metis (lifting) all_clauses_have_pos assms some_eq_ex)
  then show ?thesis using \<open>v=_\<close> by(auto)
qed

lemma in_clique_implies_in_nodes:
  assumes "F \<in> cnf_sat" "models \<sigma> F" "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}" " v \<in> C"
  shows "v \<in> fst(snd(cnf_sat_to_clique F))"
proof -
  from \<open>F \<in> cnf_sat\<close> have fin_1: "finite (\<Union> (set F))" unfolding cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using prod_cases3 by blast
  then have " V = {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}" using cnf_sat_to_clique_def \<open>cnf_sat_to_clique F = (E, V, k)\<close> assms fin_1
    by (metis (mono_tags, lifting) Pair_inject)
  have "\<forall> i < length F. get_some_true F \<sigma> i \<in> F!i" using assms aux2 by(auto)
  then show ?thesis using assms using \<open>V = {(l1, i) |l1 i. i < length F \<and> l1 \<in> F ! i}\<close> \<open>cnf_sat_to_clique F = (E, V, k)\<close> by force
qed

lemma clique_in_graph: 
  assumes  "F \<in> cnf_sat" "models \<sigma> F" "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}"
  shows "C\<subseteq> fst(snd (cnf_sat_to_clique F))"
  using in_clique_implies_in_nodes assms by blast


lemma cnf_sat_impl_clique: "F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique"
proof -
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>  where "\<sigma> \<Turnstile> F" unfolding cnf_sat_def sat_def by auto
  then have models_sigma: "models \<sigma> F" by auto
  from \<open>F \<in> cnf_sat\<close> have fin_1: "finite (\<Union> (set F))" unfolding cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
  obtain C where "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}" 
    using models_sigma f_cnf_sat  by blast
  then have c_def: "C =  {( get_some_true F \<sigma> i, i) | i. i < length F}" by auto
  then have is_c: "is_clique (fst (cnf_sat_to_clique F)) C" using f_cnf_sat models_sigma is_clique  by auto
  then have card_C_length: "card C \<ge> (length F)" using card_clique f_cnf_sat models_sigma c_def by auto
  then have card_C: "card C \<ge> (snd (snd (cnf_sat_to_clique F)))" using cnf_sat_to_clique_def by (simp add: cnf_sat_to_clique_def fin_1)
  have clique_contained: "C \<subseteq> fst(snd (cnf_sat_to_clique F))" using c_def f_cnf_sat clique_in_graph models_sigma by blast
  have ug: "ugraph_nodes (fst(cnf_sat_to_clique F)) (fst (snd (cnf_sat_to_clique F)))" using  cnf_sat_to_clique_ugraph_nodes f_cnf_sat by(auto)
  then have "\<exists> C'. ugraph_nodes (fst (cnf_sat_to_clique F)) (fst (snd( cnf_sat_to_clique F))) \<and> C' \<subseteq> fst(snd (cnf_sat_to_clique F)) \<and> card C' \<ge> (snd (snd(cnf_sat_to_clique F))) \<and> is_clique (fst (cnf_sat_to_clique F)) C'"
    using card_C is_c clique_contained ug by(auto)   
  then have "cnf_sat_to_clique F \<in> {(E, V, k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}" by (simp add: case_prod_beta')
  then show ?thesis using clique_def by(auto simp add: clique_def)
qed
 
subsection\<open>cnf_sat_to_clique F \<in> clique \<Longrightarrow> F \<in> cnf_sat\<close>


lemma not_finite_implies_not_finite:
  assumes "\<not> (\<forall>c \<in> set F. finite c)" "cnf_sat_to_clique F = (E, V, k)" 
  shows "V = {}"
proof -
  (*have v_def: "V =  {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}" using assms cnf_sat_to_clique_def
    by (meti (mono_tags, lifting) Pair_inject)
  obtain V' where  "V' = {{(l1, i) | l1. l1 \<in> F ! i} | i. i<length F}"  by auto 
  then have v'_v: "\<Union>V' = V" using v_def by(auto)*)
  have "\<exists>c\<in> set F. \<not> finite c" using assms by(auto)
  then have "\<not> finite (\<Union> (set F))" 
    by (meson Sup_upper finite_subset)
  then show ?thesis using assms cnf_sat_to_clique_def 
    by (simp add: cnf_sat_to_clique_def)
  (*then have "\<exists>i < length F. \<not>finite (F!i)" by (metis in_set_conv_nth)
  then obtain i where "i<length F \<and>  \<not>finite (F!i)" by auto
  then have "\<not>finite {l1 | l1. l1 \<in> F!i}" by(auto)
  then have fin_1: "\<not> finite ({l1 | l1. l1 \<in> F!i} \<times> {i})" 
    using finite_cartesian_productD1 by auto
  have "({l1 | l1. l1 \<in> F!i} \<times> {i}) =  {(l1, i) | l1. l1 \<in> F!i}" by(auto)
  then have "\<not>finite {(l1, i) | l1. l1 \<in> F!i}" using fin_1 by simp
  then have "\<exists>v' \<in> V'. \<not> finite v'" using \<open>V' = _\<close> \<open>i<length F \<and>_\<close> by blast
  then have "\<not> finite (\<Union> V')" 
    by (meson PowD finite_subset in_mono subset_Pow_Union)
  then have "\<not> finite V" using v'_v by(auto)
  then show ?thesis by simp*)
qed

lemma else_not_in_clique: "({}, {}, 1) \<notin> clique"
  by(auto simp add: clique_def)

lemma aux_for_finite_F:
  assumes "cnf_sat_to_clique F = (E, V, k)" "(E, V, k) \<in> clique" "X \<in> set F" "infinite X"
  shows "False"
proof -
  from assms have "\<not>(\<forall>c \<in> set F. finite c)" by(auto)
  from assms have "\<not> finite (\<Union> (set F))"by (meson Sup_upper finite_subset)
  then have "(E, V, k) = ({}, {}, 1)" using cnf_sat_to_clique_def assms 
    by (simp add: cnf_sat_to_clique_def)
  then show ?thesis using assms else_not_in_clique by(auto)
qed

lemma 
  assumes "cnf_sat_to_clique F = (E, V, k)" "(E, V, k) \<in> clique" "X \<in> set F"
  shows "finite X"
  using not_finite_implies_not_finite assms aux_for_finite_F 
  by blast 



lemma no_edges_between_clause:
  assumes "{(l1, i), (l2, i)} \<in> fst (cnf_sat_to_clique F)" 
  shows "False"
proof -
  obtain E where "E = fst (cnf_sat_to_clique F)" by auto
  then have "E \<noteq> {}" using assms  by auto
  then have "finite (\<Union> (set F))" using cnf_sat_to_clique_def \<open>E = _\<close> by(auto simp add: cnf_sat_to_clique_def)
  then have "E = {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j}"  using \<open>E = _\<close> by(auto simp add: aux1)
  then have "i \<noteq> i" using assms \<open>E = fst _\<close>  apply(auto)
    by (metis (no_types, lifting) Pair_inject doubleton_eq_iff) 
  then show ?thesis by(auto)
qed

lemma conflict_commutative: "conflict l1 l2 = conflict l2 l1"
  by(auto simp add: conflict_def)

lemma edge_conflict_aux:
  assumes "{(l1, i), (l2, j)} \<in> {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  shows "\<not> conflict l1 l2"
proof (rule ccontr)
  assume "\<not> \<not> conflict l1 l2"
  then have "conflict l1 l2 \<and> conflict l2 l1" by (auto simp add: conflict_commutative) 
  then have "\<not>conflict l1 l2 \<or> \<not> conflict l2 l1" using assms apply(auto)
    by (metis (no_types) doubleton_eq_iff fst_conv)
  then have "\<not> conflict l1 l2" using conflict_commutative by(auto)
  then show False using assms 
    using \<open>\<not> \<not> conflict l1 l2\<close> by auto
qed

lemma aux5: "v\<in> C \<and> u \<in> C \<and> card C \<le> 1 \<and> finite C\<Longrightarrow> u = v"
  apply(auto) sledgehammer
  by (simp add: card_le_Suc0_iff_eq) 

lemma no_conflicts_in_edges_empty_E:
  assumes "is_clique E C" "E=fst (cnf_sat_to_clique F)" "(l1, i) \<in> C" "(l2, j) \<in> C" "conflict l1 l2" "E = {}" "finite C"
  shows "False"
proof -
  have "card C \<le> 1" using assms is_clique_def apply(auto)
    by (metis assms(1) assms(6) card_le_Suc0_iff_eq emptyE is_clique_def)
  then have "(l1, i) = (l2, j)" using \<open>(l1, i) \<in> C\<close> \<open>(l2, j) \<in> C\<close> aux5  assms
    by fastforce
  then have "\<not> conflict l1 l2" by auto
  then show ?thesis using assms by(auto)
qed

lemma no_conflicts_in_edges:
  assumes "is_clique E C" "E=fst (cnf_sat_to_clique F)" "(l1, i) \<in> C" "(l2, j) \<in> C" "conflict l1 l2" "E \<noteq> {}"
  shows "False"
proof -
  from assms have fin_1: "finite (\<Union> (set F))" using else_not_in_clique cnf_sat_to_clique_def apply(auto) 
    by (simp add: cnf_sat_to_clique_def)
  have e_def: "E =  {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j}" using assms  aux1 fin_1 by(auto simp add: fin_1 aux1)
  have in_E: "{(l1, i), (l2, j)} \<in> E" using assms is_clique_def
    by (metis Pair_inject conflict_same)
  then have "\<not> conflict l1 l2" using e_def edge_conflict_aux fin_1
    by (metis (no_types, lifting) assms(2) aux1)
  then show ?thesis using assms by(auto)
qed
  

lemma f_sat:
  assumes"cnf_sat_to_clique F \<in> clique"
  shows "sat F"
proof -
  from assms have fin_1: "finite (\<Union> (set F))" using else_not_in_clique cnf_sat_to_clique_def
    apply(auto simp add: else_not_in_clique) 
    by (smt cnf_sat_to_clique_def else_not_in_clique)
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using prod_cases3 by blast
  then have in_clique: "(E, V, k) \<in> clique" using assms by(auto)
  with \<open>cnf_sat_to_clique F = _\<close> have "length F = k"
      unfolding cnf_sat_to_clique_def else_not_in_clique assms 
      by (metis (no_types, lifting) else_not_in_clique old.prod.inject)
    have e_def: "E = fst (cnf_sat_to_clique F)" using \<open>cnf_sat_to_clique F = _\<close> by(auto)
    have fin_2: "finite V" using in_clique clique_def ugraph_nodes_def  apply(auto) by fastforce
  from in_clique obtain C where C:
      "ugraph_nodes E V" "C \<subseteq> V" "card C \<ge> k" "is_clique E C"
      using cnf_sat_to_clique_def \<open>cnf_sat_to_clique _ = _\<close> in_clique clique_def 
      by (smt case_prodD mem_Collect_eq) 
    define \<sigma> where "\<sigma> \<equiv> \<lambda>x. (\<exists>i. (Pos x, i) \<in> C)"
    have V_inj: "l = l'" if "(l, i) \<in> C" "(l', i) \<in> C" for l l' i
    proof (rule ccontr)
      from that C(2) have "i < length F"
        using \<open>cnf_sat_to_clique _ = _\<close> unfolding cnf_sat_to_clique_def by(auto simp add: fin_1) 
      from that C(2) have "l \<in> F ! i" "l' \<in> F ! i"
        using \<open>cnf_sat_to_clique _ = _\<close> unfolding cnf_sat_to_clique_def by(auto simp add: fin_1)
      assume "l \<noteq> l'"
      with \<open>l \<in> _\<close> \<open>l' \<in> _\<close> \<open>i < _\<close> have "{(l, i), (l', i)} \<notin> E"
        using \<open>cnf_sat_to_clique _ = _\<close> unfolding cnf_sat_to_clique_def 
        by (metis (no_types, lifting) \<open>cnf_sat_to_clique F = (E, V, k)\<close> no_edges_between_clause fst_eqD)
      with C(4) that \<open>l \<noteq> l'\<close> show False
        unfolding is_clique_def by auto
    qed
    have fin_3: "finite C" using C fin_2 using finite_subset by auto
    have 1: "i < length F \<and> l \<in> F ! i" if "(l, i) \<in> C" for l i
      using that C(2) using \<open>cnf_sat_to_clique _ = _\<close> unfolding cnf_sat_to_clique_def by (auto simp add: fin_1)
    then have C_sub: "C \<subseteq> (\<lambda>i. (SOME l. (l, i) \<in> C, i)) ` {0..<length F}"
      by (auto 4 3 intro: someI V_inj)
    have 2: "\<exists>l. (l, i) \<in> C" if "i < length F" for i
    proof (rule ccontr)
      assume "\<nexists>l. (l, i) \<in> C"
      with that C_sub have "C \<subset> (\<lambda>i. (SOME l. (l, i) \<in> C, i)) ` {0..<length F}"
        by fastforce
      then have "card C < length F"
        apply -
        apply (drule psubset_card_mono[rotated])
        using card_image_le[of "{0..<length F}" "\<lambda>i. (SOME l. (l, i) \<in> C, i)"]
        by auto
      with \<open>card C \<ge> _\<close> \<open>length F = _\<close> show False
        by simp
    qed
    have no_conflict: False if "(l, i) \<in> C" "(l', j) \<in> C" "conflict l l'" for l l' i j
      using \<open>cnf_sat_to_clique F = (E,V, k)\<close> that no_conflicts_in_edges C fin_1 cnf_sat_to_clique_def e_def fin_3
      apply(auto simp add: fin_1 no_conflicts_in_edges no_conflicts_in_edges_empty_E)
      using no_conflicts_in_edges_empty_E by fastforce
    have "\<exists>l\<in>cls. (\<sigma>\<up>) l" if "cls \<in> set F" for cls
    proof -
      from that obtain i where "F ! i = cls" "i < length F"
        by (meson in_set_conv_nth)
      then obtain l where "(l, i) \<in> C"
        by (blast dest: 2)
      then have "(\<sigma>\<up>) l"
        unfolding \<sigma>_def lift_def by (cases l) (auto simp: conflict_def dest: no_conflict)
      moreover from \<open>_ \<in> C\<close> have "l \<in> cls"
        using \<open>F ! i = _\<close> by (auto dest: 1)
      ultimately show ?thesis
        by auto
    qed
    then have "\<sigma> \<Turnstile> F"
      unfolding models_def by auto
    then show ?thesis by(auto simp add: sat_def)
  qed

lemma in_clique_implies_in_cnf_sat: 
  assumes "cnf_sat_to_clique F \<in> clique"
  shows "F \<in> cnf_sat"
  using aux_for_finite_F f_sat cnf_sat_def assms 
proof - (*found by sledgehammer*)
  have "\<forall>p Ls. cnf_sat_to_clique (Ls::'a lit set list) \<noteq> p \<or> p \<notin> clique \<or> sat Ls"
    by (simp add: f_sat)
  then have "sat F \<and> (\<forall>L. L \<in> set F \<longrightarrow> finite L)"
    by (metis (no_types) assms aux_for_finite_F old.prod.exhaust)
  then show ?thesis
    using cnf_sat_def by auto
qed



subsection\<open> Main theorem \<close>

theorem is_reduction_cnf_sat_to_clique: 
  "is_reduction cnf_sat_to_clique cnf_sat clique"
  unfolding is_reduction_def
proof safe
  fix F :: "'a lit set list"
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>1 where "\<sigma>1 \<Turnstile> F" 
    unfolding cnf_sat_def sat_def by auto
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)" using prod_cases3 by blast
  show "cnf_sat_to_clique F \<in> clique" by (simp add: cnf_sat_impl_clique f_cnf_sat)
next
  fix F:: "'a lit set list"
  assume 1: "cnf_sat_to_clique F  \<in> clique"
  then show "F \<in> cnf_sat "  using in_clique_implies_in_cnf_sat by auto
qed



end