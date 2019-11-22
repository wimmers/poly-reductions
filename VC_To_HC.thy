theory VC_To_HC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Graph_Theory
begin

datatype ('a, 'b) hc_node = Cover nat | Edge 'a 'b nat

(*pre_digraph.cycl already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_hc (G::('a,'b) pre_digraph) (c:: 'b list)  \<equiv> 
    (pre_digraph.cycle G c \<and> (\<forall>x\<in> verts G. x \<in> set (pre_digraph.awalk_verts G x c)))"

definition
 "fns \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c}"


end