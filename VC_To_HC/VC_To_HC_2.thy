theory VC_To_HC_2
imports 
    Definitions "../VC_Set_To_VC_List"
begin

subsection\<open>vc_hc (E, k) f \<in> hc  \<Longrightarrow> (E,k) \<in> VC\<close>
context 
  fixes E k  assumes in_hc: "vc_hc (E, k) \<in> hc"
  fixes G assumes G_def: "G = vc_hc (E, k)" 
  fixes Cycle assumes Cycle_def: "is_hc G Cycle"
  fixes C assumes C_def: "C = {v|v e i j. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}"
begin

subsubsection\<open>Preliminaries\<close>

lemma G_def_2:
  shows "G =  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd \<rparr>" (is "G = ?L")
proof -
  have "G = (if ugraph (set E) \<and>  k \<le> card (\<Union> (set E)) \<and> distinct E
        then  ?L
        else \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>)"
    by(auto simp add: vc_hc_def G_def) 
  then have G_or: "G = ?L \<or> G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by argo
  then show "G = ?L" using else_not_in_hc in_hc G_def 
    by fast 
qed

subsubsection\<open>Lemmas for E\<close>

lemma ugraph:
  shows "ugraph (set E)" 
proof (rule ccontr)
  assume "\<not> (ugraph (set E))"
  then have "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by(auto simp add: vc_hc_def G_def) 
  then have "G \<notin> hc" 
    by (auto simp add: else_not_in_hc) 
  then show False 
    by (auto simp add: in_hc G_def)
qed

lemma k_smaller_number_vertices:
  shows "k \<le> card (\<Union> (set E))"
proof (rule ccontr)
  assume "\<not> k \<le> card (\<Union> (set E))"
  then have "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by(auto simp add: vc_hc_def G_def) 
  then have "G \<notin> hc" 
    by (auto simp add: else_not_in_hc) 
  then show False 
    by (auto simp add: in_hc G_def)
qed

lemma distinct_E:
  shows "distinct E" 
proof (rule ccontr)
  assume "\<not> (distinct E)"
  then have "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by(auto simp add: vc_hc_def G_def) 
  then have "G \<notin> hc" 
    by (auto simp add: else_not_in_hc) 
  then show False 
    by (auto simp add: in_hc G_def)
qed

lemma verts_of_Cycle_in_G:
  shows "set Cycle \<subseteq> verts G" 
  using Cycle_def is_hc_def by metis

lemma Edges_in_Cycle: 
  assumes "Edge u e i \<in> set Cycle" 
  shows "u \<in> e" "e \<in> set E" "i\<le>1" 
  using assms verts_of_Cycle_in_G G_def_2 by auto  

lemma covers_in_Cycle:
  assumes "Cover i \<in> set Cycle"
  shows "i < k" 
  using assms verts_of_Cycle_in_G G_def_2 by auto 


subsubsection\<open>Lemmas for V\<close>

lemma C_subset_Nodes:
  shows "C \<subseteq>  \<Union> (set E)"
proof 
  fix x assume "x \<in> C" 
  then have "\<exists>e i j. (Edge x e i, Cover j) \<in> set ( vwalk_arcs Cycle)" 
    using C_def by auto 
  then have "\<exists>e i. Edge x e i \<in> set Cycle" 
    using in_set_vwalk_arcsE by metis
  then obtain e i where "Edge x e i \<in> set Cycle"
    by auto
  then have "e \<in> set E" "x\<in> e" 
    using Edges_in_Cycle
    by simp+
  then show "x\<in> \<Union> (set E)" 
    by blast
qed

lemma finite_C:
  shows "finite C" 
  using C_subset_Nodes ugraph ugraph_vertex_set_finite finite_subset 
  by metis

lemma 
  assumes "Ci = {v|v e i. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}" 
  shows "card Ci \<le> 1" 
  sorry


lemma card_C:
  shows "card C \<le> k"
proof -
  have card_Cover_G: "card {i |i. Cover i \<in> verts G} \<le> k" "finite {i |i. Cover i \<in> verts G}" 
    using G_def_2 by auto  
  have "{i |i. Cover i \<in> set Cycle} \<subseteq> {i |i. Cover i \<in> verts G}"  
    using Cycle_def is_hc_def G_def_2 
    by fast 
  then have "card {i |i. Cover i \<in> set Cycle} \<le> k" using card_Cover_G  
    by (meson card_mono order_trans)
  show ?thesis sorry
qed

lemma is_vc_C:
  shows "is_vertex_cover (set E) C" 
  sorry

lemma C_properties: 
  shows "C \<subseteq> \<Union> (set E) \<and> card C \<le> k \<and> is_vertex_cover (set E) C \<and> finite C"
  using is_vc_C card_C finite_C C_subset_Nodes by simp




lemma Cover_exists:
  shows "(\<exists>V. set V \<subseteq> \<Union> (set E) \<and> length V = k \<and> is_vertex_cover_list E V \<and> distinct V)"
proof -
  have "finite C" using C_properties 
    by auto
  obtain k' where k'_def: "k' = k - (card C)" by simp
  then obtain leftNodes where leftNodes_def: "leftNodes = ((\<Union> (set E)) - C)"  by simp
  then have "leftNodes \<subseteq> \<Union> (set E)" by simp
  then obtain setV where setV_def: "setV= C \<union> get_elements k' leftNodes" by simp
  have 1: "k' \<le> card leftNodes"  
      using C_properties leftNodes_def k'_def k_smaller_number_vertices card_Diff_subset 
      by fastforce 
  then have 2: "setV \<subseteq> \<Union> (set E)"  
    using \<open>leftNodes \<subseteq> \<Union> (set E)\<close> get_elements_subset setV_def C_properties by blast
  then have 4: "finite setV" 
    using 2 C_properties ugraph_def 
    by (meson finite_subset ugraph ugraph_vertex_set_finite) 
  have 3: "card setV = k" proof -
    have "card (get_elements k' leftNodes) = k'" 
      by (simp add: "1" card_get_elements) 
    have a: "(get_elements k' leftNodes) \<subseteq> leftNodes" 
      by (simp add: "1" get_elements_subset)  
    have "leftNodes \<inter> C = {}" using leftNodes_def by auto
    then have "C \<inter> (get_elements k' leftNodes) = {}" using a by auto
    then have "card setV = card C + card (get_elements k' leftNodes)" 
      using setV_def 4 
      by (simp add: card_Un_disjoint)   
    then show ?thesis using k'_def setV_def C_properties 
      using \<open>card (get_elements k' leftNodes) = k'\<close> distinct_size by force 
  qed
  have "\<exists>L. set L = setV \<and> distinct L" 
    using 4
    by (simp add: finite_distinct_list)  
  then obtain L where L_def: "set L = setV" "distinct L" 
    by auto
  then have "is_vertex_cover (set E) (set L)" 
    using C_properties setV_def is_vertex_cover_super_set 
    by fastforce 
  then have vc_list: "is_vertex_cover_list E L" 
    using is_vertex_cover_def
    is_vertex_cover_list_def by metis
  have length_L: "length L = k" using L_def 3 distinct_card 
    by fastforce   
  then show ?thesis 
    using L_def vc_list 2 by auto
qed


subsubsection\<open>Conclusion\<close>

lemma hc_impl_vc_context:
  shows "(E, k) \<in> vertex_cover_list"
proof -
  have 1: "distinct E" 
    using distinct_E by auto
  have 2: "k \<le> card (\<Union> (set E))"
    using k_smaller_number_vertices by auto
  have 3: "ugraph (set E)" 
    using ugraph by auto
  have 4: "(\<exists>V. set V \<subseteq> \<Union> (set E) \<and> length V = k \<and> is_vertex_cover_list E V \<and> distinct V)"
    using Cover_exists by auto
  then show ?thesis 
    using vertex_cover_list_def 1 2 3 4 by(auto)
qed

end

end