theory Three_SAT_To_HC
  imports Main "Three_Sat_To_Set_Cover" "CNF_SAT_To_Clique" HOL.Enum
begin

definition
  "directed_ugraph_nodes E V \<equiv> finite E \<and>  (\<forall>(a, b) \<in> E. a\<in> V \<and> b \<in> V) \<and> finite V"

definition 
  "is_hc E V C \<equiv> (length C = 1 \<or> 
        ((\<forall>i < (length C) -1. (C!i, C!(i+1)) \<in> E) \<and> (C!(length C -1), C!0) \<in> E))
        \<and> (\<forall>v \<in> V. v \<in> (set C))"

definition
  "hc \<equiv> {(E, V). directed_ugraph_nodes E V \<and> (\<exists>C. is_hc E V C)}"


text\<open>I need an aux variable so that the set of clauses and of vertices have the same shape, need var_list to sort variables\<close>
definition
  "three_sat_to_hc F var_list aux\<equiv> (if (\<forall>cls \<in> set F. card cls = 3) then (
    {((l1, i, 0), (l1, i, 1)) | l1 i. i < length F \<and> l1 \<in>set var_list} \<union> {((l1, i, 1), (l1, i, 0)) | l1 i. i < length F \<and> l1 \<in>set var_list} \<union>
    {((l1, 0, 0), (l2, 0, 0)) | l1 l2 i. i < length F-1 \<and> l1 = var_list ! i \<and> l2 = var_list! (i+1)}\<union> 
     {((l1, 0, 0), (l2, length F-1, 1)) | l1 l2 i. i < length F-1 \<and> l1 = var_list ! i \<and> l2 = var_list! (i+1)} \<union>
     {((l1, length F -1, 1), (l2, 0, 0)) | l1 l2 i. i < length F-1 \<and> l1 = var_list ! i \<and> l2 = var_list! (i+1)} \<union>
    {((l1, length F -1, 1), (l2, length F -1, 1)) | l1 l2 i. i < length F-1 \<and> l1 = var_list ! i \<and> l2 = var_list! (i+1)} \<union>
     {((aux, 0, 3), (var_list !0 , 0, 0)),((aux, 0, 3), (var_list !0 , length F -1, 1)), ((var_list ! (length F -1), length F -1, 1), (aux, 0, 4)), ((var_list ! (length F -1), 0, 0), (aux, 0, 4))},
    {(l1, i, a) | l1 i a. i < length F \<and> a \<in> {0, 1}} \<union> {(aux, i, 2) |i. i < length F} \<union> {(aux, 0, 3), (aux, 0, 4)})
    else ({}, {(l1, i, a) | l1 i a. i < length F \<and> a \<in> {0, 1}}))"
text\<open>TODO: add edges for variables to clauses, check F and var_list, add edge for variable to next clause\<close>

end