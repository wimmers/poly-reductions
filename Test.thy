theory Test
  imports "VC_To_HC/VC_To_HC"
begin

context 
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover_list"
  fixes Cov assumes Cov_def:"is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k"
  fixes G assumes G_def: "G = vc_hc (E,k)"
  fixes Cycle assumes Cycle_def: "Cycle = construct_cycle_1 E Cov 0 (set Cov)"
begin

lemma aux1:
  assumes "\<exists>i. i+1<length Cylce \<and> v1 = Cycle!i \<and> v2 = Cycle ! (i+1)" "k>0"
  shows "(v1, v2) \<in> arcs G" 
 using Cycle_def assms G_def_2 Cov_def in_vc Cov_def G_def Cycle_def  apply(auto) 

end

end