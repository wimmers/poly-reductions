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

(*I can decide last for every edge in O(n) if I start from the end and keep track of an array, whether last has already been found*)


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

definition "space_verts n = 6 * n"
definition "space_edges n = 6 * n * 6 * n"
(*at most complete Graph*)

definition "size_hc = (\<lambda>G. card (verts G) + card (arcs G))"
definition "size_vc = (\<lambda>(E,k). length E)"
definition "vc_to_hc_space n  = n + space_verts n + space_edges n + n + 2"
(*Space for E, verts of G, edges of G, an additional list of length 2*n for last and first, 2 for case of else*)

(*k \<le> 2*(length E) *)
definition "vc_hc_time n = 1+ n + (2 * n + 1) + 1 + (2*n + 2*(2*(n))) 
    +(2*n) + (2*n) + (2*n) + (2*n) + 2* (n) *  (2*n) + (2*n)*(2*n)"


lemma finite_card_3_sets: 
  assumes "finite A" "finite B" "finite C"
  shows "card (A \<union> B \<union> C) \<le> card A + card B + card C"
  using assms 
  by (metis (no_types, lifting) add.commute card_Un_le le_trans nat_add_left_cancel_le)


lemma card_verts: 
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  shows "card ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}) \<le> 6 * length E"
  sorry

lemma card_arcs: 
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  shows "card ({(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k}) \<le> (6 * length E) * (6 * length E)" (is "card ?A \<le> (6 * length E) * (6 * length E)")
proof -
  have "?A \<subseteq> 
    ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}) 
    \<times> ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})"
    sorry
  then have "card ?A \<le> card ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}) * 
    card ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})" 
    sorry
  then have "card ?A \<le> 6 * length E * 6 * length E" 
    using card_verts assms sorry 
  then show ?thesis by linarith
  qed



lemma aux: 
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  shows "card ({Cover i |i. i < k} \<union> {Edge v e 0 |v e. e \<in> set E \<and> v \<in> e} \<union> {Edge v e (Suc 0) |v e. e \<in> set E \<and> v \<in> e}) +
        card
         ({(Edge v e 0, Edge v e (Suc 0)) |v e. e \<in> set E \<and> v \<in> e} \<union> {(Edge v e 0, Edge u e 0) |u v e. e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
          {(Edge v e (Suc 0), Edge u e (Suc 0)) |u v e. e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
          {(Edge v e1 (Suc 0), Edge v e2 0) |v e1 e2.
           \<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i < j \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j)} \<union>
          {(Edge v e (Suc 0), Cover n) |v e n. \<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> n < k} \<union>
          {(Cover n, Edge v e 0) |v e n. \<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> n < k} \<union>
          {(Cover i, Cover j) |i j. i < k \<and> j < k})
        \<le> Suc (Suc (8 * length E + 36 * length E * length E))"
proof -
  have 1: "card ({Cover i |i. i < k} \<union> {Edge v e 0 |v e. e \<in> set E \<and> v \<in> e} \<union> {Edge v e (Suc 0) |v e. e \<in> set E \<and> v \<in> e}) \<le> 6 * length E" 
    using card_verts assms by auto
  have "card
         ({(Edge v e 0, Edge v e (Suc 0)) |v e. e \<in> set E \<and> v \<in> e} \<union> {(Edge v e 0, Edge u e 0) |u v e. e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
          {(Edge v e (Suc 0), Edge u e (Suc 0)) |u v e. e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
          {(Edge v e1 (Suc 0), Edge v e2 0) |v e1 e2.
           \<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i < j \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j)} \<union>
          {(Edge v e (Suc 0), Cover n) |v e n. \<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> n < k} \<union>
          {(Cover n, Edge v e 0) |v e n. \<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> n < k} \<union>
          {(Cover i, Cover j) |i j. i < k \<and> j < k}) \<le> 6 * length E * 6 * length E" 
    using card_arcs assms 
    by fastforce 
  then show ?thesis using 1 
    by linarith
qed



lemma vc_to_hc_size: "size_hc (vc_hc (E, k)) \<le> vc_to_hc_space (size_vc (E, k))" 
  apply(auto simp: size_vc_def vc_hc_def vc_to_hc_space_def size_hc_def) 
  apply(auto simp add: space_verts_def space_edges_def)
  using aux by blast


lemma ugraph_card_verts_smaller_2_length: 
  assumes "\<forall>e\<in> set E. card e = 2" 
  shows "card (\<Union> (set E)) \<le> 2* (length E)"
  using assms proof(induction E)
  case Nil
  then show ?case by auto
next
  case (Cons a E)
  then have "card a = 2" by auto
  then have 1: "card (a \<union> \<Union> (set E)) \<le> 2 + (card (\<Union> (set E)))"
    by (metis card_Un_le) 
  have 2: "2* (length (a#E)) \<le> 2 + 2* (length E)" 
    by simp
  have 3: "card (\<Union> (set E)) \<le> 2*(length E)"
    using Cons by fastforce
  then show ?case using 1 2 by simp
qed

lemma k_smaller_2_length: 
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))"
  shows "k\<le> 2 * length E"
  using assms proof -
  have "\<forall>e\<in> set E. card e = 2" 
    using ugraph_def assms by blast
  then have "k \<le> 2* (length E)"
    using assms ugraph_card_verts_smaller_2_length assms le_trans 
    by blast
  then show ?thesis 
    using card_length le_trans mult_le_mono by blast 
qed

lemma time_ugraph_to_hc: 
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E" 
  shows "2 * card (set E) + (k + (2 * length E * k + k * k)) \<le> 4 * length E + 8 * (length E * length E)"
proof -
  have 1: "k \<le> 2*(length E)" 
    using assms k_smaller_2_length by blast
  then have 1: "2 * card (set E) + (k + (2 * length E * k + k * k)) \<le> 
    2 * card (set E) + ((2*length E) + (2 * length E * k + k * k))"
    by(auto simp add: 1)  
  then have 2: "... \<le> 2 * length E + ((2*length E) + (2 * length E * k + k * k))"
    by (simp add: card_length) 
  then have 3: "... \<le> 4 * length E + (2 * length E * k + k * k)"
    by auto
  then have 4: "... \<le> 4 * length E + (2 * length E * (2 * length E)+ k * k)"
    using 1 by force
  then have 5: "... \<le> 4 * length E + (4 * length E * length E + (2 * length E) * k)" 
    using 1 by simp
  then have 6: "... \<le> 4 * length E + (4 * length E * length E + 2 * length E * 2 * length E)"
    using 1 by fastforce
  then have 7: "... \<le> 4 * length E + 8 * length E * length E" 
    by simp
  then show ?thesis using 1 2 3 4 5 6 7 by linarith
qed

lemma vc_to_hc_reifnes:
  "vc_hc_alg (E, k) \<le> SPEC (\<lambda>y. y = (vc_hc (E, k))) (\<lambda>_. vc_hc_time (size_vc (E, k)))"
  unfolding SPEC_def
  unfolding vc_hc_alg_def vc_hc_def   
      mop_check_ugraph_def mop_check_distinct_def mop_get_vertices_def mop_set_card_def
      mop_verts_G_def mop_arcs_G_def
  apply(rule T_specifies_I) 
  apply(vcg' \<open>-\<close> rules: T_SPEC )  
  apply(auto simp: vc_hc_time_def one_enat_def size_vc_def time_ugraph_to_hc)
  by (simp add: card_length mult_le_mono trans_le_add1)+ 


lemma cnf_sat_to_clique_ispolyred: "ispolyred vc_hc_alg vertex_cover_list hc size_vc size_hc" 
  unfolding ispolyred_def
  apply(rule exI[where x=vc_hc])
  apply(rule exI[where x=vc_hc_time])
  apply(rule exI[where x=vc_to_hc_space])
  apply(safe)
  subgoal using vc_to_hc_reifnes by blast
  subgoal using vc_to_hc_size by blast  
  subgoal unfolding poly_def vc_hc_time_def apply(rule exI[where x=2]) by auto  
  subgoal unfolding poly_def vc_to_hc_space_def space_verts_def space_edges_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_vc_to_hc .
  done



end