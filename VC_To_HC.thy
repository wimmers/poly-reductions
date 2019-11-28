theory VC_To_HC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Graph_Theory
begin

subsection\<open>Preliminaries\<close>

datatype ('a, 'b) hc_node = Cover nat | Edge 'a 'b nat

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_hc (G::('a,'b) pre_digraph) (c:: 'b list)  \<equiv> 
    (pre_digraph.cycle G c \<and> (\<forall>x\<in> verts G. x \<in> set (pre_digraph.awalk_verts G x c)))\<or> card (verts G) \<le> 1"

definition
  "hc \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c}"

definition
  "vc_hc \<equiv> \<lambda>f (E, k).
    if ugraph E 
    then (if k \<ge> card (\<Union> E)
        then  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in> E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2. e1 \<in> E\<and> e2\<in> E \<and> v \<in> e1 \<and> v \<in> e2 \<and> \<not> (\<exists>e3 \<in> E. v \<in> e3 \<and> f e1 < f e3 \<and> f e3 < f e2)} \<union>
            {(Edge v e 1, Cover i)| v e i. e \<in> E\<and> v \<in> e \<and> \<not> (\<exists>e2 \<in> E. v \<in> e2 \<and> f e < f e2) \<and> i< k}\<union>
            {(Cover i, Edge v e 0)| v e i. e \<in> E\<and> v \<in> e \<and> \<not> (\<exists>e2 \<in> E. v \<in> e2 \<and> f e2 < f e) \<and> i < k},
          tail = fst, head = snd \<rparr>
        else \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>)
    else \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"


lemma else_not_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<notin> hc"
proof 
  assume "G \<in> hc"
  then have "\<exists> c. pre_digraph.cycle G c \<and> (\<forall>x\<in> verts G. x \<in> set (pre_digraph.awalk_verts G x c))" 
    using assms hc_def 
    by (simp add: hc_def doubleton_eq_iff is_hc_def)
  then obtain c where c_def: "pre_digraph.cycle G c" "(\<forall>x\<in> verts G. x \<in> set (pre_digraph.awalk_verts G x c))" by blast
  with pre_digraph.cycle_def have not_empty: "c \<noteq> []"  by fastforce
  from pre_digraph.cycle_def pre_digraph.awalk_def c_def have subset: "set c \<subseteq> arcs G" by metis
  have "arcs G = {}" using assms by(auto)
  with subset  have "set c = {}" by auto
  then show "False" using not_empty by(auto)
qed

lemma if_else_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<in> hc"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

subsection\<open>(E,k) \<in> vc \<Longrightarrow> vc_hc (E, k) f \<in> hc\<close>

fun construct_cycle::"('a set \<Rightarrow> nat) \<Rightarrow> 'a set set \<Rightarrow> 'a list \<Rightarrow> (('a, 'a set) hc_node \<times> ('a, 'a set) hc_node) list"  where
"construct_cycle f E C = undefined"


context 
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover"
  fixes f assumes f_bij: "bij_betw f E {0..<card E}" (*If I fix f above i get a problem with the type of E*)
  fixes Cover assumes cover:"is_vertex_cover E (set Cover)" "distinct Cover" "size Cover \<le> k"
  fixes G assumes g_def: "G = vc_hc f (E,k)"
  fixes Cycle assumes cycle_def: "Cycle = construct_cycle f E Cover"
begin

lemma "size Cover = card (set Cover)"
  using cover by (simp add: distinct_card)

lemma is_cylce: 
  assumes "card (verts G) > 1"
  shows "pre_digraph.cycle G Cylce"
  sorry

lemma cylce_contains_all_verts:
  assumes "card (verts G) > 1"
  shows "(\<forall>x\<in> verts G. x \<in> set (pre_digraph.awalk_verts G x c))"
  sorry

lemma is_hc_cycle_graph: 
  shows "is_hc G Cycle"
  using cylce_contains_all_verts is_cylce is_hc_def 
  by (metis One_nat_def is_hc_def leI)

lemma is_wf_digraph:
  shows "wf_digraph G"
  sorry





lemma "vc_hc f (E,k) \<in> hc"
  using is_wf_digraph is_hc_cycle_graph g_def hc_def
  by auto

end


subsection\<open>vc_hc (E, k) f \<in> hc  \<Longrightarrow> (E,k) \<in> VC\<close>
context 
  fixes E k f assumes "vc_hc f (E, k) \<in> hc"
begin

end

subsection\<open> Main theorem \<close>

end

