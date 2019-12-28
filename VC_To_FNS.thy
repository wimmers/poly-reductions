theory VC_To_FNS
  imports Main "Three_Sat_To_Set_Cover" Graph_Theory.Digraph Graph_Theory.Arc_Walk
begin

fun del_verts:: "('a, 'b) pre_digraph \<Rightarrow> 'a list \<Rightarrow>('a,'b) pre_digraph" where
"del_verts G [] = G" |
"del_verts G (v#vs) = del_verts (pre_digraph.del_vert G v) vs"

definition
  "is_fns (G::('a,'b) pre_digraph) (R:: 'a list)  \<equiv> \<not>(\<exists>p. pre_digraph.cycle (del_verts G R) p) "

definition
 "fns \<equiv> {(G, k). \<exists>R. wf_digraph G \<and> length R \<le> k \<and> is_fns G R}"

definition "
  vc_to_fns VC aux = (case VC of (E, k) \<Rightarrow> (\<lparr> verts = {v. v \<in> \<Union> E}, arcs = {(u, v)| u v. {u, v} \<in> E}, tail = fst, head = snd \<rparr>, k))"
end