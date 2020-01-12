theory HC_To_UHC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Digraph  Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    "List_Auxiliaries" 
    "VC_To_HC/Definitions" 
begin

subsection\<open>Preliminaries\<close>

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_uhc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    ((pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1)\<and> set c \<subseteq> verts G \<and> distinct (tl c)"

definition
  "uhc \<equiv> {G. \<exists>c. wf_digraph G \<and> symmetric G \<and> is_uhc G c \<and> head G = snd \<and> tail G = fst}"

(*last two edge sets are not part of the original proof, but are needed for case with only one node*)
definition "hc_to_uhc \<equiv>
  \<lambda>(G::('a, ('a \<times> 'a)) pre_digraph). (if wf_digraph G then 
    \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (u, 2))|u. u \<in> verts G}\<union> 
          {((u, 2), (u, 0))|u. u \<in> verts G}, 
    tail = fst, head = snd\<rparr>
    else \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>)"



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


lemma else_not_in_uhc: 
  assumes "G' = \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>" 
      "\<not> wf_digraph G"
    shows "G' \<notin> uhc"
proof -
  have vertsG': "verts G' = {}"
    using assms by auto
  have "arcs G \<noteq> {}" 
    using not_wf_digraph_not_arcs_empty assms by auto
  then have "arcs G' \<noteq> {}"
    using assms by simp
  then have "\<not> wf_digraph G'"
    using verts_empt_arcs_not_not_wf_digraph vertsG' by auto
  then show ?thesis using uhc_def by blast
qed

subsection\<open>G \<in> hc --> hc_to_uhc G \<in> uhc\<close>

fun to_cycle_uhc::"('a, ('a \<times> 'a)) pre_digraph \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
"to_cycle_uhc G [] = []" |
"to_cycle_uhc G (v#vs) = [(v, 0), (v, 1), (v, 2)] @ to_cycle_uhc G vs"

context
  fixes G assumes in_hc: "G \<in> hc"
  fixes Cy assumes Cy_def: "is_hc G Cy"
  fixes G' assumes G'_def: "G' = hc_to_uhc G"
begin

lemma G'_def_2:
  shows "G' = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (u, 2))|u. u \<in> verts G}\<union> 
          {((u, 2), (u, 0))|u. u \<in> verts G}, 
    tail = fst, head = snd\<rparr>"
proof -
  have "wf_digraph G" 
    using in_hc hc_def by auto
  then show ?thesis 
    by(auto simp add:  G'_def hc_to_uhc_def)
qed


lemma wf_digraph_G:
  shows "wf_digraph G"
  using in_hc hc_def by auto

lemma wf_digraph_G': 
  shows "wf_digraph G'"
  using G'_def_2 wf_digraph_def wf_digraph_G by(auto simp add: G'_def_2 wf_digraph_def)





lemma in_uhc: "hc_to_uhc G \<in> uhc"
  sorry
end

subsection\<open>hc_to_uhc G \<in> uhc --> G \<in> hc\<close>

context
  fixes G assumes in_uhc: "hc_to_uhc G \<in> uhc"
  fixes G' assumes G'_def: "hc_to_uhc G = G'" 
begin 


lemma in_hc:
  shows "G \<in> hc"
  sorry

end



subsection\<open> Main theorem \<close>

(*Just some helpt for isabelle, since she was not able to figure that out herself*)
lemma hc_implies_uhc: "G \<in> hc  \<Longrightarrow> hc_to_uhc G \<in> uhc"
  using in_uhc hc_def 
  by blast


lemma in_uhc_implies_in_hc: 
  assumes "hc_to_uhc G \<in> uhc"
  shows "G \<in> hc"
  using in_hc assms 
  sorry

theorem is_reduction_vc: 
  "is_reduction hc_to_uhc hc uhc"
  unfolding is_reduction_def
  using in_uhc_implies_in_hc hc_implies_uhc by auto


end