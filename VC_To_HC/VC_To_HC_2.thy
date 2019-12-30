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
 

lemma 
  assumes "S = {v|v e i. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}"
  shows "card S \<le> 1"
proof (cases "card S \<le> 1")
  case True
  then show ?thesis using assms by auto
next
  case False
  have distinct: "distinct (tl Cycle)" 
    using Cycle_def is_hc_def 
    by blast
  have "card S > 1" 
    using False by auto
  then have "\<exists>v1 v2. v1 \<in> S \<and> v2 \<in> S \<and> v1 \<noteq> v2" 
    using card_greater_1_contains_two_elements by fast 
  then obtain v1 v2 where "v1 \<in> S \<and> v2 \<in> S \<and> v1 \<noteq> v2"  
    by auto
  then have "\<exists>e1 i1 e2 i2. (Edge v1 e1 i1, Cover j) \<in> set (vwalk_arcs Cycle) \<and>
    (Edge v2 e2 i2, Cover j) \<in> set (vwalk_arcs Cycle) \<and> Edge v1 e1 i1 \<noteq> Edge v2 e2 i2"
    using assms by fast
  then obtain e1 i1 e2 i2 where edges_def: "(Edge v1 e1 i1, Cover j) \<in> set (vwalk_arcs Cycle) \<and>
    (Edge v2 e2 i2, Cover j) \<in> set (vwalk_arcs Cycle) \<and> Edge v1 e1 i1 \<noteq> Edge v2 e2 i2" 
    by auto
  then have "\<exists>p1 p2. p1@ [Edge v1 e1 i1, Cover j]@p2 = Cycle" 
    using sublist_for_edges 
    by fast   
  then obtain p11 p21 where p1_def: "p11@ [Edge v1 e1 i1, Cover j]@p21 = Cycle" 
    by auto
  then have "\<exists>p1 p2. p1@ [Edge v2 e2 i2, Cover j]@p2 = Cycle" 
    using sublist_for_edges edges_def
    by fast   
  then obtain p12 p22 where p2_def: "p12@ [Edge v2 e2 i2, Cover j]@p22 = Cycle" 
    by auto
  then have "p11 \<noteq> p12" using edges_def 
    using p1_def by auto 

  then have "Edge v2 e2 i2 \<in> set Cycle" 
    using p2_def by auto 
  then have "Edge v2 e2 i2 \<in> set (p11 @ [Edge v1 e1 i1, Cover j] @ p21)" 
    using p1_def by simp
  then have "Edge v2 e2 i2 \<in> set (p11) \<or>
    Edge v2 e2 i2 \<in> set ([Edge v1 e1 i1, Cover j]) \<or>
    Edge v2 e2 i2 \<in> set (p21)" by auto
  then have edge2: "Edge v2 e2 i2 \<in> set p11 \<or> Edge v2 e2 i2 \<in> set p21" 
    using edges_def p1_def 
    by auto 

  have "Edge v2 e2 i2 \<noteq> last p11" using distinct p1_def sorry
  then have "Cover j \<in> set p11 \<or> Cover j \<in> set p21" using p2_def edge2 sorry
  

  then have "Cover j \<in> (set p11 \<union> set p21)" by auto
  then have "\<not> distinct (tl Cycle)" sorry
    
  then have "False" using distinct by auto
  then show ?thesis by auto
qed


(*lemma
  shows "card {Cover i|i. i<i'} \<le> i'"
proof (induction i')
  case 0
  then show ?case by auto
next
  case (Suc i')
  have fin1: "finite  {Cover i |i. i < i'}" by simp
  have fin2: "finite {Cover i'}" by simp
  have union: "{Cover i |i. i < Suc i'} = {Cover i |i. i < i'} \<union> {Cover i'}" 
    by auto
  then have "{Cover i |i. i < i'} \<union> {Cover i'} = insert (Cover i') {Cover i |i. i < i'}" 
    by simp
  then have fin3: "finite {Cover i |i. i < Suc i'}" by simp
  have "card ({Cover i |i. i < i'} \<union> {Cover i'}) \<le> card {Cover i |i. i < i'} + card {Cover i'}"
    using fin1 fin2 try0 sledgehammer 
  then have "card {Cover i |i. i < Suc i'} \<le> card {Cover i |i. i < i'} + card {Cover i'}"
    using union fin1 fin2 fin3 sorry 
  then show ?case sorry
qed *)

lemma Cover_equal:
"Cover i = Cover j \<longleftrightarrow> i = j" 
  by simp


lemma 
  shows "card {x|x j. (x, Cover j) \<in> set (vwalk_arcs Cycle)} \<le> k" "finite {x|x j. (x, Cover j) \<in> set (vwalk_arcs Cycle)}"
  sorry



lemma inCycle_inVerts: 
  assumes "x \<in> set Cycle"
  shows "x\<in> verts G"
  using Cycle_def is_hc_def assms by fast  

lemma 
  shows "card C \<le> k"
proof (rule ccontr)
  have 1: "card {i |i. Cover i \<in> verts G} \<le> k" "finite {i |i. Cover i \<in> verts G}" 
    using G_def_2 by auto
  assume "\<not> card C \<le> k"
  then have "card C > k" 
    by linarith
  then have "\<exists>j. \<exists>v1 v2 e1 e2 i1 i2. (Edge v1 e1 i1, Cover j) \<in> set (vwalk_arcs Cycle) \<and>
  (Edge v2 e2 i2, Cover j) \<in> set (vwalk_arcs Cycle) \<and> v1 \<noteq> v2" using 1 inCycle_inVerts
    sorry

  then show False 
    sorry
qed


(*fun i_to_Cover:: "nat \<Rightarrow> ('a, 'b) hc_node" where
"i_to_Cover i = Cover i"

fun Cover_to_i::"('a, 'b) hc_node \<Rightarrow> nat" where
"Cover_to_i (Cover i) = i" 

lemma iCover: "i_to_Cover (Cover_to_i (Cover i)) = Cover i" 
  by simp 

lemma inj: "inj i_to_Cover" 
  by (simp add: linorder_injI) 

lemma "card {i_to_Cover i|i. i \<in> S} \<le> card S"
  using inj inj_def *) 



(*Evtl zeigen, dass es für jeden Cover-Knoten in G maximal eine Kante im Cycle gibt. Damit
hat das set für diesen Knoten maximal ein Element. Dann zeigen, dass G maximal
k Coverknoten hat und damit auch maximal k Cover-knoten im Cycle sind. Dann C als 
Union von diesem set schreiben und hoffentlich fertig*)


lemma card_C:
  shows "card C \<le> k"
proof -
  have 1: "card {i|i. Cover i \<in> verts G} = k"
    using G_def_2 by simp 

  obtain Cover_is where Cover_is_def: "Cover_is = {i. Cover i \<in> verts G}" by auto
  obtain S where S_def: "S =  \<Union>{{v|v e i . (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}|j. j \<in> Cover_is}" by auto
  have eq: "C = S"
  proof
    show "C \<subseteq> S" proof 
      fix x assume "x \<in> C"
      then have "\<exists>e i j. (Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
        using C_def by fast
      then have "\<exists>j. \<exists>e i.(Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" by blast
      then obtain j where j_def: " \<exists>e i.(Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)"
        by auto
      then have "Cover j \<in> verts G" 
        by (meson inCycle_inVerts in_set_vwalk_arcsE) 
      then have "j \<in> Cover_is" 
        using Cover_is_def by simp
      then show "x \<in> S" 
        using S_def j_def by blast 
    qed   
  next
    show "S \<subseteq> C"  proof 
      fix x assume "x \<in> S" 
      then have "\<exists>j. \<exists>e i.(Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
        using S_def by blast 
      then have "\<exists>e i j. (Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
        by auto
      then show "x \<in> C" 
        using C_def by blast
    qed
  qed
 
  have 3: "finite Cover_is" using Cover_is_def 1 proof (cases "k = 0")
    case True
    then have "{i. Cover i \<in> verts G} = {}" 
      using G_def_2 by auto 
    then show ?thesis 
      using Cover_is_def by simp 
  next
    case False
    then show ?thesis 
      using Cover_is_def 1 
      by (meson card_infinite) 
  qed  
  (*have finS: "finite S" sorry*) 
  have 2: "card S \<le> card Cover_is" using S_def 3 sorry 
  (*have "\<forall>j \<in> Cover_is. card {v|v e i . (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)} \<le> 1"  sorry*)
  have "card C = card S" using eq by simp  
  then show "card C \<le> k" 
    using 1 2 Cover_is_def by simp 
qed



  (*fix x assume "x \<in> {x|x j. (x, Cover j) \<in> set (vwalk_arcs Cycle)}" 
  then have "(\<exists>v e i. x = Edge v e i) \<or> (\<exists>i. x = Cover i)" 
    by (meson hc_node.exhaust) 

  fix v assume v_def: "v \<in> C"
  then have "\<exists>e i j. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
    using C_def by simp
  then obtain e i where "\<exists>j. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
    by auto
  then have "Edge v e i \<in> {x|x j. (x, Cover j) \<in> set (vwalk_arcs Cycle)}" 
    by auto
  then have "card C \<le> card {x|x j. (x, Cover j) \<in> set (vwalk_arcs Cycle)}" 
    using v_def C_def apply(auto) sorry 

  have card_Cover_G: "card {i |i. Cover i \<in> verts G} \<le> k" "finite {i |i. Cover i \<in> verts G}" 
    using G_def_2 by auto  
  have subset: "{i |i. Cover i \<in> set Cycle} \<subseteq> {i |i. Cover i \<in> verts G}"  
    using Cycle_def is_hc_def G_def_2 
    by fast 
  then have "card {i |i. Cover i \<in> set Cycle} \<le> k" "finite {i |i. Cover i \<in> set Cycle}" using card_Cover_G  
    apply (meson card_mono order_trans) 
    using subset rev_finite_subset card_Cover_G by auto 

  have 1: "{x |i x. x \<in> set Cycle \<and> x = Cover i} \<subseteq> set Cycle" 
    by auto
  (*then have "card {x |i x. x \<in> set Cycle \<and> x = Cover i} \<le> k" proof -
    have "{Cover i|i. Cover i \<in> set Cycle} \<subseteq> {Cover i |i. i<k}" 
      using covers_in_Cycle by fast
    have "card {Cover i |i. i<k} \<le> k" oops
      oops*)

  have "C = \<Union>{{v|v e i. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}|j. j \<in> \<nat>}" 
    using C_def  sorry  
   
     
  show "card C \<le> k" sorry
qed *)

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