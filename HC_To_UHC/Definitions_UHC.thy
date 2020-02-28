theory Definitions_UHC
  imports Main "../Three_Sat_To_Set_Cover" Graph_Theory.Digraph  Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    "../Auxiliaries/List_Auxiliaries" "../Auxiliaries/Set_Auxiliaries"
    "../VC_To_HC/Definitions" "../Auxiliaries/Graph_auxiliaries" "../Graph_Extensions/Vwalk_Cycle"
begin


subsection\<open>Preliminaries\<close>

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_uhc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    ((vwalk_cycle G c \<and> (\<forall>x\<in> verts G. x \<in> set c)\<and> distinct (tl c))\<or> card (verts G) \<le> 1)\<and> set c \<subseteq> verts G"

definition
  "uhc \<equiv> {G. \<exists>c. wf_digraph G \<and> symmetric G \<and> is_uhc G c \<and>((tail G = fst \<and> head G = snd) \<or> arcs G = {}) \<and> finite (verts G)}"

fun to_cycle_hc where
"to_cycle_hc ((a, b)#vs) = (if b = 1 then a#(to_cycle_hc vs) else to_cycle_hc vs)" |
"to_cycle_hc [] = []"

(*last two edge sets are not part of the original proof, but are needed for case with only one node*)
(*I'm using the "\<or> arcs = {}" to easily construct a graph that is not in uhc. If arcs are empty, 
head and tail are not important*)
definition "hc_to_uhc \<equiv>
  \<lambda>(G::('a, ('a \<times> 'a)) pre_digraph). (if wf_digraph G \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}) then (if finite (verts G) then (if card (verts G) > 1 then 
    \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v},
    tail = fst, head = snd\<rparr> 
    else \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>) else \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>)
    else (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>))"



lemma not_wf_digraph_not_arcs_empty: 
  assumes "\<not> wf_digraph G" 
  shows "arcs G \<noteq> {}"
proof(rule ccontr)
  assume "\<not> arcs G \<noteq> {}"
  then have "wf_digraph G"
    using wf_digraph_def by blast 
  then show False 
    using assms by simp
qed


lemma verts_empt_arcs_not_not_wf_digraph: 
  assumes "verts G = {}" "arcs G \<noteq> {}"
  shows "\<not> wf_digraph G"
  using assms wf_digraph_def 
  by fast  


lemma else_not_in_uhc_1: 
  assumes "G' = (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)" 
      "\<not> wf_digraph G"
    shows "G' \<notin> uhc"
proof -
  obtain x where x_def: "x = (SOME x. x \<in> arcs G)"
    by simp 
  then have vertsG': "verts G' = {}"
    using assms
    by (meson select_convs(1))
  have "arcs G \<noteq> {}" 
    using not_wf_digraph_not_arcs_empty assms by auto
  then have "arcs G' \<noteq> {}"
    using assms 
    by (metis insert_not_empty select_convs(2)) 
  then have "\<not> wf_digraph G'"
    using verts_empt_arcs_not_not_wf_digraph vertsG' by auto
  then show ?thesis using uhc_def by blast
qed

lemma else_not_in_uhc_2: 
  assumes "G' = (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)" 
      "\<not>((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
    shows "G' \<notin> uhc"
proof -
  have vertsG': "verts G' = {}"
    using assms 
    by (meson select_convs(1)) 
  have "arcs G \<noteq> {}" 
    using assms by auto
  then have "arcs G' \<noteq> {}"
    using assms 
    by (metis insert_not_empty select_convs(2)) 
  then have "\<not> wf_digraph G'"
    using verts_empt_arcs_not_not_wf_digraph vertsG' by auto
  then show ?thesis using uhc_def by blast
qed


lemma else_not_in_uhc_3: 
  assumes "G' = \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>" 
      "\<not> finite (verts G)"
    shows "G' \<notin> uhc"
proof -
  have vertsG': "verts G' = {(v, 0)|v. v \<in> verts G}"
    using assms by auto
  then have "verts G' = (verts G) \<times> {0}" 
    by auto
  then have "\<not> finite (verts G')" 
    using assms finite_cartesian_productD1 by fastforce  
  then show ?thesis using uhc_def by blast
qed


lemma else_not_in_uhc: 
  assumes "G' = (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)" 
      "\<not>(wf_digraph G \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}))"
    shows "G' \<notin> uhc"
  using else_not_in_uhc_1 else_not_in_uhc_2 assms by blast


lemma G_leq_1_vertex_in_uhc: 
  assumes "G \<in> hc" "\<not>card (verts G) >1"
  shows "hc_to_uhc G \<in> uhc"
proof -
  have "hc_to_uhc G = \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>"
    using assms hc_to_uhc_def hc_def 
    by (simp add: hc_def hc_to_uhc_def) 
  then have "wf_digraph (hc_to_uhc G)" "symmetric (hc_to_uhc G)" "finite (verts (hc_to_uhc G))" 
    "arcs (hc_to_uhc G) = {}"  "is_uhc (hc_to_uhc G) []" 
    by(auto simp add: wf_digraph_def symmetric_def arcs_ends_def sym_def is_uhc_def)   
  then show ?thesis using uhc_def by auto
qed 


end