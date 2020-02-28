theory VC_To_FNS
  imports Main "../Three_Sat_To_Set_Cover" Graph_Theory.Digraph Graph_Theory.Arc_Walk
    "../VC_Set_To_VC_List/VC_Set_To_VC_List"
begin

section\<open>VC To FNS\<close>
subsubsection\<open>Preliminaries\<close>

fun del_verts:: "('a, 'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow>('a,'b) pre_digraph" where
  "del_verts G [] = G" |
  "del_verts G (v#vs) = del_verts (pre_digraph.del_vert G v) vs"

definition
  "is_fns (G::('a,'b) pre_digraph) (R:: 'a list)  \<equiv> \<not>(\<exists>p. pre_digraph.cycle (del_verts G R) p) "

definition
  "fns \<equiv> {(G, k). \<exists>R. wf_digraph G \<and> length R < k \<and> is_fns G R \<and> set R \<subseteq> verts G}"

definition "vc_to_fns \<equiv> \<lambda>(E, k).(if ugraph E \<and> k \<le> card (\<Union> E) 
  then (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)
  else (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0))"


lemma else_not_in_fns:
  shows "(\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0) \<notin> fns"
  using fns_def by auto


lemma e_in_arcs_del_verts_e_in_arcs: 
  assumes "e \<in> arcs (del_verts G' E')"
  shows "e \<in> arcs G'"
  using assms
proof(induction E' arbitrary: G')
  case Nil
  then show ?case 
    by auto
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
  using assms 
proof(induction E' arbitrary: G')
  case Nil
  then show ?case 
    by simp
next
  case (Cons a E')
  then obtain G1 where G1_def: "G1 = (pre_digraph.del_vert G' a)"
    by auto
  then have "e \<in> arcs (del_verts G1 E')" 
    using Cons
    by auto 
  then have 1: "head G' e \<notin> set E' \<and> tail G' e \<notin> set E'"
    using Cons 
    by (metis del_verts.simps(2) pre_digraph.head_del_vert pre_digraph.tail_del_vert)
  have "head G' e \<noteq> a \<and> tail G' e \<noteq> a" 
  proof(rule ccontr)
    assume "\<not> (head G' e \<noteq> a \<and> tail G' e \<noteq> a)"
    then have "head G' e = a \<or> tail G' e = a" 
      by auto
    then have "e \<notin> arcs G1" 
      using G1_def 
      by(auto simp add: pre_digraph.del_vert_def)  
    then have "e \<notin> arcs (del_verts G1 E')" 
      using e_in_arcs_del_verts_e_in_arcs 
      by metis
    then show False
      using Cons G1_def 
      by simp
  qed
  then show ?case
    using 1 
    by simp
qed


lemma e_in_arcs_not_in_R:
  assumes "e \<in> arcs G" "head G e \<notin> set E" "tail G e \<notin> set E"
  shows "e \<in> arcs (del_verts G E)"
  using assms 
proof(induction E arbitrary: G)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a E)
  then have "e \<in> arcs (pre_digraph.del_vert G a)" 
    by (simp add: pre_digraph.del_vert_def) 
  then have "e \<in> arcs (del_verts (pre_digraph.del_vert G a) E)"
    using Cons
    by (simp add: pre_digraph.head_del_vert pre_digraph.tail_del_vert) 
  then show ?case 
    by simp
qed


subsection\<open>in VC implies in FNS\<close>

context
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover"
  fixes G k' assumes G_def: "(G, k') = vc_to_fns (E, k)"
  fixes Cov assumes Cov_def: "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov" 
  fixes R assumes R_def: "R = set_to_list Cov"
begin


lemma k_k':
  shows "k' = k+1"
proof -
  have ugraph: "ugraph E" "k \<le> card (\<Union> E)"
    using in_vc vertex_cover_def
    by auto
  then have "vc_to_fns (E, k) 
    = (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    by(auto simp add: vc_to_fns_def) 
  then show ?thesis 
    using G_def 
    by simp
qed


lemma G_def_2:
  shows "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd\<rparr>"
proof -
  have ugraph: "ugraph E" "k \<le> card (\<Union> E)" 
    using in_vc vertex_cover_def
    by auto
  then have "vc_to_fns (E, k) 
    = (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    by(auto simp add: vc_to_fns_def) 
  then show ?thesis 
    using G_def
    by simp
qed


lemma wf_digraph_G: 
  shows "wf_digraph G"
  using G_def_2 
  by(auto simp add: wf_digraph_def) 


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
  using R_def set_to_list_def distinct_set_to_list finite_Cov 
  by auto 


lemma card_R_equal:
  shows "length R = card Cov"
  using R_def set_to_list_def distinct_R 
  using distinct_card finite_Cov set_set_to_list 
  by fastforce  


lemma card_R:
  shows "length R < k+1" 
  using card_R_equal Cov_def 
  by simp



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
  then show ?thesis
    using vu_def R_def finite_Cov set_set_to_list
    by auto 
qed


lemma arcs_del_g_empty: 
  shows "arcs (del_verts G R) = {}"
  using in_arcs_G_imp_in_set_R e_in_arcs_del_verts_impl_not_vertex_in_E 
    e_in_arcs_del_verts_e_in_arcs 
  by fast  


lemma empty_arcs_impl_no_cycle: 
  assumes "arcs G' = {}"
  shows  "\<not>(\<exists>p. pre_digraph.cycle G' p)"
proof(rule ccontr)
  assume "\<not>\<not>(\<exists>p. pre_digraph.cycle G' p)"
  then obtain p where 1: "pre_digraph.cycle G' p"
    by auto
  then have 0: "p \<noteq> []" 
    using pre_digraph.cycle_def 
    by fastforce
  then have "\<exists>u. pre_digraph.awalk G' u p u"
    using 1 pre_digraph.cycle_def
    by metis
  then obtain u where 2: "pre_digraph.awalk G' u p u"
    by auto
  then have "set p \<subseteq> arcs G'" 
    using pre_digraph.awalk_def 
    by fast
  then have "p = []" 
    using assms 
    by simp
  then show False 
    using 0 
    by simp 
qed


lemma is_fns_R:
  shows "is_fns G R"
  using empty_arcs_impl_no_cycle arcs_del_g_empty is_fns_def 
  by metis


lemma R_subset_verts:
  shows "set R \<subseteq> verts G"
proof -
  have "set R = Cov" 
    using R_def set_to_list_def 
    by (simp add: finite_Cov set_set_to_list) 
  then have "set R \<subseteq> \<Union> E" 
    using Cov_def
    by simp
  then show ?thesis 
    using G_def_2
    by auto 
qed


lemma in_fns_context:
  shows "vc_to_fns (E, k) \<in> fns"
  using fns_def card_R wf_digraph_G is_fns_R k_k' G_def R_subset_verts
  by fastforce   

end


subsection\<open>vc_to_fns in FNS implies in HC\<close>

context
  fixes G k' assumes G_def: "(G, k') \<in> fns"
  fixes E k assumes Ek_def: "(G, k') = vc_to_fns (E, k)" 
  fixes R assumes R_def: "is_fns G R" "length R < k'" "set R \<subseteq> verts G"
  fixes Cov assumes Cov_def: "Cov = set R"
begin

lemma cardE_k:
  shows "k \<le> card (\<Union> E)"
proof(rule ccontr)
  assume "\<not> k \<le> card (\<Union> E)"
  then have "(G, k') = (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0)"
    using Ek_def
    by(auto simp add: vc_to_fns_def)  
  then show False 
    using else_not_in_fns G_def 
    by auto
qed


lemma ugraphE:
  shows "ugraph E"
proof(rule ccontr)
  assume "\<not> ugraph E"
  then have "(G, k') = (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0)"
    using Ek_def 
    by(auto simp add: vc_to_fns_def)  
  then show False
    using else_not_in_fns G_def 
    by auto
qed


lemma G_def_3:
  shows "G = \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, 
    tail = fst, head = snd\<rparr>" "k' = k+1"
proof -
  have "(G, k') = (if ugraph E \<and> k \<le> card (\<Union> E) 
  then (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)
  else (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0))"
    by(auto simp add: Ek_def vc_to_fns_def)  
  then have "(G, k') = 
    (\<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k+1)"
    using ugraphE cardE_k 
    by auto
  then show "G = 
    \<lparr>verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd\<rparr>" "k' = k+1"
    by auto
qed


lemma wf_digraph_G_2:
  shows "wf_digraph G"
  using G_def fns_def 
  by auto


lemma e_in_E_e_explicit: 
  assumes "e \<in> E"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v" 
proof -
  have 1: "card e = 2" 
    using ugraphE ugraph_def assms
    by blast 
  then have 2: "finite e" 
    using card_infinite
    by fastforce
  then have "\<exists>u. u \<in> e"
    using all_not_in_conv 1
    by fastforce 
  then obtain u where u_def: "u \<in> e"
    by auto
  then have 3: "card (e -{u}) = 1" 
    using 1 2 
    by simp  
  then have 4: "finite (e -{u})" 
    using 2 
    by simp
  then have "\<exists>v. v \<in> (e -{u})" 
    using all_not_in_conv 3 2
    by (metis card_1_singletonE singletonI) 
  then obtain v where v_def: "v \<in> (e -{u})"
    by auto
  then have 5: "card (e -{u, v}) = 0"
    using 2 3 4 
    by (metis Diff_insert2 card_Diff_singleton_if diff_is_0_eq' le_numeral_extra(4)) 
  then have "finite (e -{u, v})"
    using 4 2 
    by blast
  then have "(e -{u, v}) = {}" 
    using 5 
    by auto
  then have "e = {u, v}"
    using 1 u_def v_def 
    by auto  
  then show ?thesis 
    using u_def v_def 
    by auto 
qed


lemma G_symmetric:
  assumes "(u, v) \<in> arcs G" 
  shows "(v, u) \<in> arcs G" 
  using assms G_def_3 
  by(auto simp add: assms G_def_3 insert_commute)  


lemma pre_digraph_cas_edge:
  assumes  "head G' = snd" "tail G' = fst"
  shows "pre_digraph.cas G' v [(v, u), (u, v)] v"
proof -
  have 1: "pre_digraph.cas G' v [(v, u), (u, v)] v =
     (tail G' (v, u) = v \<and> pre_digraph.cas G' (head G' (v, u)) [(u,v)] v)"
    by (simp add: pre_digraph.cas.simps(2)) 
  then have 2: "... = pre_digraph.cas G' u [(u,v)] v" 
    using assms  
    by simp
  then have 3: "... = (tail G' (u, v) = u \<and> pre_digraph.cas G' (head G' (u, v)) [] v)"
    by (simp add: pre_digraph.cas.simps(2)) 
  then have 4: "... = True" 
    using assms 
    by (simp add: pre_digraph.cas.simps)
  then show ?thesis 
    using 1 2 3 4 
    by simp
qed


lemma edge_cycle:
  assumes "(u, v) \<in> arcs G'" "(v, u) \<in> arcs G'" "u \<noteq> v" "tail G' = fst" "head G' = snd" "wf_digraph G'"
  shows "pre_digraph.cycle G' [(v, u), (u, v)]"
  using pre_digraph.cycle_def 
proof -
  have 1:  "[(v, u), (u, v)] \<noteq> []"
    by auto
  have 2: "pre_digraph.awalk G' v [(v, u), (u, v)] v"
    unfolding pre_digraph.awalk_def
  proof -
    have 1: "v \<in> verts G'" 
      using wf_digraph_def assms 
      by fastforce
    have 2: "set [(v, u), (u, v)] \<subseteq> arcs G'" 
      using assms by simp
    have 3: "pre_digraph.cas G' v [(v, u), (u, v)] v"
      using pre_digraph_cas_edge assms 
      by fast
    then show "v \<in> verts G' \<and> set [(v, u), (u, v)] \<subseteq> arcs G' \<and> pre_digraph.cas G' v [(v, u), (u, v)] v"
      using 1 2 3 
      by auto
  qed
  have 3: "distinct (tl (pre_digraph.awalk_verts G' v [(v, u), (u, v)]))"
  proof -
    have "(pre_digraph.awalk_verts G' v [(v, u), (u, v)]) = [v, u, v]"
      by(auto simp add: pre_digraph.awalk_verts_def assms)
    then show ?thesis 
      using assms
      by auto
  qed     
  then show ?thesis 
    using 1 2 3 pre_digraph.cycle_def 
    by blast
qed


lemma head_tail_del_verts: 
  shows "head (del_verts G' E') = head G'" "tail (del_verts G' E') = tail G'"
  by(induction E' arbitrary: G')(auto simp add: pre_digraph.head_del_vert pre_digraph.tail_del_vert) 


lemma wf_digraph_del_verts:
  assumes "wf_digraph G'"
  shows "wf_digraph (del_verts G' E')"
  using assms 
  by(induction E' arbitrary: G')(auto simp add: wf_digraph.wf_digraph_del_vert) 


lemma cycle_in_R: 
  assumes "pre_digraph.cycle G [(v, u), (u, v)]" "(u, v) \<in> arcs G" "(v, u) \<in> arcs G" "u \<noteq> v"
  shows "u \<in> set R \<or> v \<in> set R"
proof(rule ccontr)
  assume "\<not>(u \<in> set R \<or> v \<in> set R)"
  then have "u \<notin> set R \<and> v \<notin> set R" 
    by auto
  then have 1: "(v, u) \<in> arcs (del_verts G R)"  "(u, v) \<in> arcs (del_verts G R)" "u \<noteq> v"
    using G_def_3 e_in_arcs_not_in_R assms 
    by force+
  have 2: "tail (del_verts G R) = fst" "head (del_verts G R) = snd"
    using G_def_3 
    by(auto simp add: head_tail_del_verts)   
  have "wf_digraph (del_verts G R)" 
    using wf_digraph_G_2 wf_digraph_del_verts
    by auto
  then have "pre_digraph.cycle (del_verts G R) [(v, u), (u, v)]"
    using edge_cycle 1 2 
    by fast 
  then show False 
    using R_def is_fns_def 
    by blast
qed


lemma G_fst_snd:
  shows "tail G = fst" "head G = snd"
  using G_def_3 by auto


lemma in_arcs_one_in_R:
  assumes "e \<in> arcs G" "e = (u, v)" "u \<noteq> v"
  shows "u \<in> set R \<or> v \<in> set R"
proof -
  have 1: "(v, u) \<in> arcs G" "(u, v) \<in> arcs G"
    using assms G_symmetric 
    by blast+
  then have "pre_digraph.cycle G [(v, u), (u, v)]"
    using edge_cycle assms wf_digraph_G_2 G_fst_snd 
    by fast
  then show "u \<in> set R \<or> v \<in> set R" 
    using cycle_in_R 1 assms
    by blast
qed


lemma Cov_properties:
  shows "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov"
proof -
  have "set R \<subseteq> \<Union> E" 
    using R_def G_def_3
    by auto
  then show "Cov \<subseteq> \<Union> E"
    using Cov_def 
    by simp
next
  have "length R \<le> k"
    using R_def G_def_3 
    by linarith
  then show "card Cov \<le> k" 
    using Cov_def card_length dual_order.trans 
    by blast  
next
  have "\<forall>e\<in>E. \<exists>v\<in>Cov. v \<in> e" 
  proof 
    fix e assume 1: "e \<in> E"
    then obtain u v where 2: "e = {u, v}" "u \<noteq> v"
      using e_in_E_e_explicit by metis 
    then have "(u, v) \<in> arcs G"
      using G_def_3 1 
      by auto
    then have "u \<in> set R \<or> v \<in> set R" 
      using in_arcs_one_in_R 2 
      by simp
    then show "\<exists>v\<in> Cov. v\<in> e"
      using Cov_def 2 
      by auto
  qed
  then show "is_vertex_cover E Cov"
    using is_vertex_cover_def 
    by auto
qed


lemma in_vc_context:
  shows "(E, k) \<in> vertex_cover"
  using vertex_cover_def ugraphE cardE_k Cov_properties 
  by blast

end


subsection\<open>Main theorem\<close>

lemma in_fns: 
  assumes "(E, k) \<in> vertex_cover"
  shows "vc_to_fns (E, k) \<in> fns"
proof -
  obtain G k' where 1: "(G, k') = vc_to_fns (E, k)"
    using assms 
    by (metis surjective_pairing) 
  obtain Cov where 2: "Cov \<subseteq> \<Union> E" "card Cov \<le> k" "is_vertex_cover E Cov"
    using assms 
    by(auto simp add: vertex_cover_def) 
  obtain R where 3: "R = set_to_list Cov"
    by simp
  then show ?thesis 
    using 1 2 3 in_fns_context assms 
    by blast 
qed


lemma in_vc: 
  assumes "vc_to_fns (E ,k) \<in> fns"
  shows "(E, k) \<in> vertex_cover"
proof -
  obtain G k' where 1: "(G, k') = vc_to_fns (E, k)" 
    by (metis surj_pair) 
  then obtain R where 2: "is_fns G R" "length R < k'" "set R \<subseteq> verts G"
    using assms fns_def
    by(auto simp add: assms fns_def)
  then obtain Cov where 3: "Cov = set R"
    by auto
  then show ?thesis
    using in_vc_context 1 2 3 assms
    by metis
qed


theorem is_reduction_vc_to_fns: 
  "is_reduction vc_to_fns vertex_cover fns"
  unfolding is_reduction_def
  using in_vc in_fns 
  by auto


end