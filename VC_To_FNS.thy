theory VC_To_FNS
  imports Main "Three_Sat_To_Set_Cover" Graph_Theory.Digraph Graph_Theory.Arc_Walk
  "VC_Set_To_VC_List"
begin

fun del_verts:: "('a, 'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow>('a,'b) pre_digraph" where
"del_verts G [] = G" |
"del_verts G (v#vs) = del_verts (pre_digraph.del_vert G v) vs"

definition
  "is_fns (G::('a,'b) pre_digraph) (R:: 'a list)  \<equiv> \<not>(\<exists>p. pre_digraph.cycle (del_verts G R) p) "

definition
 "fns \<equiv> {(G, k). \<exists>R. wf_digraph G \<and> length R < k \<and> is_fns G R}"

definition "vc_to_fns \<equiv> \<lambda>(E, k).(if ugraph E \<and> k \<le> card (\<Union> E) 
  then (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)
  else (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0))"

lemma else_not_in_fns:
  shows "(\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0) \<notin> fns"
  using fns_def by auto

context
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover"
  fixes G k' assumes G_def: "(G, k') = vc_to_fns (E, k)"
  fixes Cov assumes Cov_def: "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov" 
  fixes R assumes R_def: "R = set_to_list Cov"
begin


lemma k_k':
  shows "k' = k+1"
proof -
  have ugraph: "ugraph E" "k \<le> card (\<Union> E)" using in_vc vertex_cover_def
    by auto
  then have "vc_to_fns (E, k) 
    = (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    by(auto simp add: vc_to_fns_def) 
  then show ?thesis using G_def by simp
qed


lemma G_def_2:
  shows "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd\<rparr>"
proof -
  have ugraph: "ugraph E" "k \<le> card (\<Union> E)" using in_vc vertex_cover_def
    by auto
  then have "vc_to_fns (E, k) 
    = (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    by(auto simp add: vc_to_fns_def) 
  then show ?thesis using G_def by simp
qed

lemma wf_digraph_G: 
  shows "wf_digraph G"
  using G_def_2 by(auto simp add: wf_digraph_def) 

lemma ugraph_E:
  shows "ugraph E"
  using in_vc vertex_cover_def
    by auto

lemma finite_E:
  shows "finite (\<Union> E)"
  using ugraph_vertex_set_finite ugraph_E 
  by auto


lemma finite_Cov: 
  shows "finite Cov"
  using Cov_def finite_E 
  by (meson finite_subset)  


lemma distinct_R:
  shows "distinct R"
  using R_def set_to_list_def 
  using distinct_set_to_list finite_Cov by auto 

lemma card_R_equal:
  shows "length R = card Cov"
  using R_def set_to_list_def distinct_R 
  using distinct_card finite_Cov set_set_to_list by fastforce  


lemma card_R:
  shows "length R < k+1" 
  using card_R_equal Cov_def by simp


lemma e_in_arcs_del_verts_e_in_arcs: 
  assumes "e \<in> arcs (del_verts G' E')"
  shows "e \<in> arcs G'"
  using assms proof(induction E' arbitrary: G')
  case Nil
  then show ?case by auto
next
  case (Cons a E')
  then have "e \<in> arcs ((pre_digraph.del_vert G' a))"
    by fastforce
  then show ?case 
    by (simp add: pre_digraph.arcs_del_vert) 
qed



lemma e_in_arcs_del_verts_impl_not_vertex_in_E: 
  assumes "e \<in> arcs (del_verts G' E')"
  shows "head G' e \<notin> set E' \<and> tail G' e \<notin> set E'"
using assms proof(induction E' arbitrary: G')
  case Nil
  then show ?case by simp
next
  case (Cons a E')
  then obtain G1 where G1_def: "G1 = (pre_digraph.del_vert G' a)"
    by auto
  then have "e \<in> arcs (del_verts G1 E')" 
    using Cons by auto 
  then have 1: "head G' e \<notin> set E' \<and> tail G' e \<notin> set E'"
    using Cons 
    by (metis del_verts.simps(2) pre_digraph.head_del_vert pre_digraph.tail_del_vert)
  have "head G' e \<noteq> a \<and> tail G' e \<noteq> a" proof(rule ccontr)
    assume "\<not> (head G' e \<noteq> a \<and> tail G' e \<noteq> a)"
    then have "head G' e = a \<or> tail G' e = a" by auto
    then have "e \<notin> arcs G1" 
      using G1_def by(auto simp add: pre_digraph.del_vert_def)  
    then have "e \<notin> arcs (del_verts G1 E')" 
      using e_in_arcs_del_verts_e_in_arcs by metis
    then show False using Cons G1_def by simp
  qed
  then show ?case using 1 by simp
qed
 


lemma in_arcs_G_imp_in_set_R: 
  assumes "e \<in> arcs G"
  shows "head G e \<in> set R \<or> tail G e \<in> set R"
proof -
  obtain v u where vu_def: "v = head G e" "u = tail G e"
    by auto
  then obtain e' where e'_def: "e' = {v, u}"
    by auto
  then have "e' \<in> E"
    using G_def_2 assms vu_def 
    by(auto simp add: G_def_2 insert_commute)
  then have "u \<in> Cov \<or> v \<in> Cov"
    using Cov_def is_vertex_cover_def e'_def 
    by fast 
  then show ?thesis using vu_def 
    using R_def finite_Cov set_set_to_list by auto 
qed


lemma arcs_del_g_empty: 
  shows "arcs (del_verts G R) = {}"
  using in_arcs_G_imp_in_set_R e_in_arcs_del_verts_impl_not_vertex_in_E 
    e_in_arcs_del_verts_e_in_arcs by fast  


lemma empty_arcs_impl_no_cycle: 
  assumes "arcs G' = {}"
  shows  "\<not>(\<exists>p. pre_digraph.cycle G' p)"
proof(rule ccontr)
  assume "\<not>\<not>(\<exists>p. pre_digraph.cycle G' p)"
  then obtain p where 1: "pre_digraph.cycle G' p"
    by auto
  then have 0: "p \<noteq> []" 
    using pre_digraph.cycle_def by fastforce
  then have "\<exists>u. pre_digraph.awalk G' u p u"
    using 1 pre_digraph.cycle_def by metis
  then obtain u where 2: "pre_digraph.awalk G' u p u"
    by auto
  then have "set p \<subseteq> arcs G'" 
    using pre_digraph.awalk_def by fast
  then have "p = []" using assms by simp
  then show False using 0 by simp 
qed

lemma is_fns_R:
  shows "is_fns G R"
  using empty_arcs_impl_no_cycle arcs_del_g_empty is_fns_def by metis

lemma in_fns_context:
  shows "vc_to_fns (E, k) \<in> fns"
  using fns_def card_R wf_digraph_G is_fns_R k_k' G_def
  by fastforce   

end

context
  fixes G k' assumes G_def: "(G, k') \<in> fns"
  fixes E k assumes Ek_def: "(G, k') = vc_to_fns (E, k)" 
  fixes R assumes R_def: "is_fns G R" "length R < k'"
  fixes Cov assumes Cov_def: "Cov = set R"
begin

lemma cardE_k:
  shows "k \<le> card (\<Union> E)"
proof(rule ccontr)
  assume "\<not> k \<le> card (\<Union> E)"
  then have "(G, k') = (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0)"
    using Ek_def by(auto simp add: vc_to_fns_def)  
  then show False using else_not_in_fns G_def by auto
qed

lemma ugraphE:
  shows "ugraph E"
proof(rule ccontr)
  assume "\<not> ugraph E"
  then have "(G, k') = (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0)"
    using Ek_def by(auto simp add: vc_to_fns_def)  
  then show False using else_not_in_fns G_def by auto
qed

lemma G_def_3:
  shows "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd\<rparr>" "k' = k+1"
proof -
  have "(G, k') = (if ugraph E \<and> k \<le> card (\<Union> E) 
  then (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)
  else (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0))"
    by(auto simp add: Ek_def vc_to_fns_def)  
  then have "(G, k') = (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    using ugraphE cardE_k by auto
  then show "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd\<rparr>" "k' = k+1"
    by auto
qed

lemma in_vc_context:
  shows "(E, k) \<in> vertex_cover"
  using vertex_cover_def ugraphE cardE_k 
  sorry

end



lemma in_fns: 
  assumes "(E, k) \<in> vertex_cover"
  shows "vc_to_fns (E, k) \<in> fns"
proof -
  obtain G k' where 1: "(G, k') = vc_to_fns (E, k)"
    using assms 
    by (metis surjective_pairing) 
  obtain Cov where 2: "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov"
    using assms by(auto simp add: vertex_cover_def) 
  obtain R where 3: "R = set_to_list Cov"
    by simp
  then show ?thesis using 1 2 3 in_fns_context assms by blast 
qed


lemma in_vc: 
  assumes "vc_to_fns (E ,k) \<in> fns"
  shows "(E, k) \<in> vertex_cover"
proof -
  obtain G k' where 1: "(G, k') = vc_to_fns (E, k)" 
    by (metis surj_pair) 
  then obtain R where 2: "is_fns G R" "length R < k'"
    using assms fns_def by(auto simp add: assms fns_def)
  then obtain Cov where 3: "Cov = set R"
    by auto
  then show ?thesis using in_vc_context 1 2 3 assms by metis
qed


theorem is_reduction_vc_to_fns: 
  "is_reduction vc_to_fns vertex_cover fns"
  unfolding is_reduction_def
  using in_vc in_fns by auto



end