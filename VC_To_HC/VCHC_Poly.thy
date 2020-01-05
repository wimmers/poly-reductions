theory VCHC_Poly
  imports VC_To_HC "../TSTSC_Poly"
begin


definition "mop_check_distinct E = SPECT [distinct E \<mapsto> length E]"

definition "mop_verts_G E k = SPECT [{Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e} 
    \<mapsto> k + 2*(2*(length E))]"

definition "mop_arcs_G E k = SPECT [
            {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k}
    \<mapsto> (2*(length E)) + (2*(length E)) + (2*(length E)) + (2*(length E)) + 2*  (length E) * k + k*k]"

(*I can dexide last for every edge in O(n) if I start from the end and keep track of an array, whether last has already been found*)


definition "vc_hc_alg = (\<lambda>(E,k).   
  do {
    b \<leftarrow> mop_check_ugraph (set E);
    d \<leftarrow> mop_check_distinct E;
    V  \<leftarrow> mop_get_vertices (set E);
    cV \<leftarrow> mop_set_card V;
    if b \<and> k \<le> cV \<and> d then
      do {
          verts \<leftarrow> mop_verts_G E k;
          arcs \<leftarrow> mop_arcs_G E k;
          RETURNT (\<lparr>verts = verts, arcs = arcs, tail = fst, head = snd\<rparr>)
      }
    else RETURNT (\<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>)
  } )"

definition "size_hc = (\<lambda>G. card (verts G) + card (arcs G) * 2)"
definition "size_vc = (\<lambda>(E,k). length E)"
definition "vc_to_hc_space n  =undefined"
(*Space for E, verts of G, edges of G, an additional list of length 2*n for last and first*)

(*k \<le> 2*(length E) *)
definition "vc_hc_time n = 1+ n + (2 * n + 1) + 1 + (2*n + 2*(2*(n))) 
    +(2*n) + (2*n) + (2*n) + (2*n) + 2* (n) *  (2*n) + (2*n)*(2*n) "


lemma vc_to_hc_size: "size_hc (vc_hc (E, k)) \<le> vc_to_hc_space (size_vc (E, k))" 
  (*apply(auto simp: size_VC_List_def vc_set_to_vc_list_def vcs_to_vcl_space_def size_VC_def)
  apply(auto simp add: set_to_list_def)
  by (metis (mono_tags, lifting) distinct_size eq_imp_le finite_UnionD finite_distinct_list tfl_some ugraph_vertex_set_finite)*)
sorry


lemma vc_to_hc_reifnes:
  "vc_hc_alg (E, k) \<le> SPEC (\<lambda>y. y = (vc_hc (E, k))) (\<lambda>_. vc_hc_time (size_vc (E, k)))"
  unfolding SPEC_def sorry


lemma cnf_sat_to_clique_ispolyred: "ispolyred vc_hc_alg vertex_cover_list hc size_vc size_hc" 
  unfolding ispolyred_def
  apply(rule exI[where x=vc_hc])
  apply(rule exI[where x=vc_hc_time])
  apply(rule exI[where x=vc_to_hc_space])
  apply(safe)
  subgoal using vc_to_hc_reifnes by blast
  subgoal using vc_to_hc_size by blast  
  subgoal unfolding poly_def vc_hc_time_def apply(rule exI[where x=2]) by auto  
  subgoal unfolding poly_def vc_to_hc_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_vc_to_hc .
  done



end