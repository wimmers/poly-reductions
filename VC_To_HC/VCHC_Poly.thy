theory VCHC_Poly
  imports VC_To_HC "../TSTSC_Poly"
begin

lemma e_in_E_e_explicit: 
  assumes "card e = 2" 
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v" 
proof -
  have 1: "card e = 2" 
    using ugraph ugraph_def assms by blast 
  then have 2: "finite e" 
    using card_infinite
    by fastforce
  then have "\<exists>u. u \<in> e"
    using all_not_in_conv 1 by fastforce 
  then obtain u where u_def: "u \<in> e"
    by auto
  then have 3: "card (e -{u}) = 1" 
    using 1 2 by simp  
  then have 4: "finite (e -{u})" 
    using 2 by simp
  then have "\<exists>v. v \<in> (e -{u})" 
    using all_not_in_conv 3 2
    by (metis card_1_singletonE singletonI) 
  then obtain v where v_def: "v \<in> (e -{u})"
    by auto
  then have 5: "card (e -{u, v}) = 0"
    using 2 3 4 
    by (metis Diff_insert2 card_Diff_singleton_if diff_is_0_eq' le_numeral_extra(4)) 
  then have "finite (e -{u, v})" using 4 2 by blast
  then have "(e -{u, v}) = {}" using 5 by auto
  then have "e = {u, v}"
    using 1 u_def v_def 
    by auto  
  then show ?thesis using u_def v_def by auto 
qed


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



lemma is_wf_digraph:
  shows "wf_digraph \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd\<rparr>"
  by(auto simp add: wf_digraph_def) 

lemma arcs_subset_graph: 
  assumes "F = \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd\<rparr>"
  shows "arcs F \<subseteq> (verts F) \<times> (verts F)" 
  using assms is_wf_digraph 
  by fastforce


lemma fin_Cov:
  shows "finite {Cover i|i. i< k}"
proof -
  obtain S where S_def: "S= {i|i. i<k}" 
    by auto
  obtain T where T_def: "T = {{Cover j|j. j = i}|i. i\<in> S}"
    by auto
  have card_S: "card S = k"
    using S_def by simp
  have 1: "{Cover i|i. i< k} = \<Union> T" 
    using S_def T_def by auto
  have 2: "\<forall>i. card {Cover j|j. j = i} = 1" by simp
  then have 3: "\<forall>S' \<in> T. card S' \<le> 1" 
    using T_def by fastforce
  have finS: "finite S" 
    using S_def by simp   
  then have fin: "finite T"
    using fin_dep_on_other_set T_def by simp
  have "card {{Cover j|j. j = i}|i. i\<in> S} \<le> card S"
    using finS card_dep_on_other_set
    by fast
  then have "card {{Cover j|j. j = i}|i. i\<in> S} \<le> k"
    using card_S by blast
  have "card (\<Union> T) \<le> card T"
    using 3 card_union_if_all_subsets_card_1 fin by blast
  then show ?thesis using 1 by simp
qed


fun f where
"f (Edge v e i) (v' ,e') = (v = v' \<and> e = e' \<and> i = 0)" |
"f _ _ = False"

fun f1 where
"f1 (Edge v e i) (v' ,e') = (v = v' \<and> e = e' \<and> i = 1)" |
"f1 _ _ = False"



lemma card_S_Edge: 
  assumes "S= {(v, e)|v e. e\<in> set E \<and> v \<in> e}"  "\<forall>e\<in> set E. card e = 2"
  shows "card S \<le> 2 * length E"
  using assms proof(induction E arbitrary: S)
  case Nil
  then show ?case by auto
next
  case (Cons a E)
  then have 0: "{(v, e) |v e. e \<in> set (a # E) \<and> v \<in> e} = 
    {(v, e) |v e. e \<in> set (E) \<and> v \<in> e} \<union> {(v, e)|v e. e = a \<and> v \<in> e}"
    by auto
  have 1: "card {(v, e) |v e. e \<in> set (E) \<and> v \<in> e} \<le> 2 * length E" 
    using Cons assms by simp
  have "card a = 2" using Cons by simp
  then obtain u v where "a = {u, v}" "u\<noteq> v" 
    using Cons e_in_E_e_explicit by metis
  then have "{(v, e)|v e. e = a \<and> v \<in> e} = {(v, a), (u, a)}" 
    by blast
  then have 2: "card {(v, e)|v e. e = a \<and> v \<in> e} = 2" 
    using \<open>u \<noteq> v\<close> by auto 
  then have "card {(v, e) |v e. e \<in> set (a # E) \<and> v \<in> e} \<le> 
    card {(v, e) |v e. e \<in> set (E) \<and> v \<in> e} + card {(v, e)|v e. e = a \<and> v \<in> e}"
    using 0 
    by (metis (no_types, lifting) card_Un_le) 
  then show ?case using 1 2 Cons 
    by fastforce
qed


lemma fin_S_Edge: 
  assumes "S= {(v, e)|v e. e\<in> set E \<and> v \<in> e}"  "\<forall>e\<in> set E. card e = 2"
  shows "finite S"
  using assms proof(induction E arbitrary: S)
  case Nil
  then show ?case by auto
next
  case (Cons a E)
  then have 0: "{(v, e) |v e. e \<in> set (a # E) \<and> v \<in> e} = 
    {(v, e) |v e. e \<in> set (E) \<and> v \<in> e} \<union> {(v, e)|v e. e = a \<and> v \<in> e}"
    by auto
  have 1: "finite {(v, e) |v e. e \<in> set (E) \<and> v \<in> e}" 
    using Cons assms by simp
  have "card a = 2" using Cons by simp
  then obtain u v where "a = {u, v}" "u\<noteq> v" 
    using Cons e_in_E_e_explicit by metis
  then have "{(v, e)|v e. e = a \<and> v \<in> e} = {(v, a), (u, a)}" 
    by blast
  then have 2: "finite {(v, e)|v e. e = a \<and> v \<in> e}" 
    using \<open>u \<noteq> v\<close> by auto 
  then show ?case using 1 2 0 Cons 
    by simp 
qed


lemma f_inv: 
  assumes "f x (v, e)"
  shows "x= Edge v e 0" 
  using assms f.elims(2) by blast 


lemma set_f: 
  assumes "S' = {u|u. f u (v, e)}"
  shows "S' = {Edge v e 0}"
  using assms f_inv by fastforce 

lemma f1_inv: 
  assumes "f1 x (v, e)"
  shows "x= Edge v e 1" 
  using assms f1.elims(2) by blast 


lemma set_f1: 
  assumes "S' = {u|u. f1 u (v, e)}"
  shows "S' = {Edge v e 1}"
  using assms f1_inv by fastforce 


lemma fin_Edge0:
  assumes "\<forall>e\<in> set E. card e = 2" 
  shows "finite {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}"
proof -
  obtain S where S_def: "S= {(v, e)|v e. e\<in> set E \<and> v \<in> e}" 
    by auto
  obtain T where T_def: "T = {{u|u. f u (v, e)}|v e. (v, e)\<in> S}"
    by auto
  have card_S: "card S \<le> 2*length E"
    using S_def card_S_Edge assms by blast
  have 1: "{Edge v e 0|v e. e\<in> set E \<and> v \<in> e} = \<Union> T" 
  proof
    show "{Edge v e 0 |v e. e \<in> set E \<and> v \<in> e} \<subseteq> \<Union> T" proof 
      have 0: "\<Union> T = {u|u v e. f u (v, e) \<and> (v, e) \<in> S}" using T_def by auto
      fix x assume a1: "x \<in> {Edge v e 0 |v e. e \<in> set E \<and> v \<in> e}"
      then obtain v e where ve_def: "x = Edge v e 0"
        by auto
      then have 1: "f x (v, e)"
        by simp
      have "e \<in> set E" "v \<in> e" using ve_def a1 by simp+
      then have "(v, e) \<in> S" using S_def by simp
      then have "x \<in> {u|u v e. f u (v, e) \<and> (v, e) \<in> S}"
        using 1 by blast
      then show "x \<in> \<Union> T" using 0 by simp
    qed
  next
    show "\<Union> T \<subseteq> {Edge v e 0 |v e. e \<in> set E \<and> v \<in> e}" proof 
      fix x assume a1: "x \<in> \<Union> T"
      have 0: "\<Union> T = {u|u v e. f u (v, e) \<and> (v, e) \<in> S}" using T_def by auto
      then obtain v e  where ve_def: "f x (v, e)" "(v, e) \<in> S" 
        using a1 by auto
      then have 1: "x = Edge v e 0" using f_inv by fastforce 
      have 2: "v \<in> e" "e \<in> set E" 
        using ve_def S_def by blast+
      then show "x \<in> {Edge v e 0 |v e. e \<in> set E \<and> v \<in> e}"
        using 1 2 by simp
    qed
  qed  
  have 3: "\<forall>S' \<in> T. finite S'" 
  proof
    fix S' assume "S' \<in> T" 
    then obtain v e where ve_def: "S' = {u|u. f u (v, e)}" "(v, e)\<in> S"
      using T_def by blast
    then have "S' = {Edge v e 0}" using set_f by metis
    then show "finite S'" by simp
  qed
  have finS: "finite S" 
    using S_def fin_S_Edge assms by auto 
  then have fin: "finite T"
    using fin_dep_on_other_set T_def 
    by fastforce 
  have finT: "finite T"
    using finS fin_dep_on_other_set T_def 
    by fastforce
  have "finite (\<Union> T)"
    using 3 fin by blast
  then have "finite {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}" 
    using 1 by simp 
  then show ?thesis .  
qed


lemma fin_Edge1:
  assumes "\<forall>e\<in> set E. card e = 2" 
  shows "finite {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}"
proof -
  obtain S where S_def: "S= {(v, e)|v e. e\<in> set E \<and> v \<in> e}" 
    by auto
  obtain T where T_def: "T = {{u|u. f1 u (v, e)}|v e. (v, e)\<in> S}"
    by auto
  have card_S: "card S \<le> 2*length E"
    using S_def card_S_Edge assms by blast
  have 1: "{Edge v e 1|v e. e\<in> set E \<and> v \<in> e} = \<Union> T" 
  proof
    show "{Edge v e 1 |v e. e \<in> set E \<and> v \<in> e} \<subseteq> \<Union> T" proof 
      have 0: "\<Union> T = {u|u v e. f1 u (v, e) \<and> (v, e) \<in> S}" using T_def by auto
      fix x assume a1: "x \<in> {Edge v e 1 |v e. e \<in> set E \<and> v \<in> e}"
      then obtain v e where ve_def: "x = Edge v e 1"
        by auto
      then have 1: "f1 x (v, e)"
        by simp
      have "e \<in> set E" "v \<in> e" using ve_def a1 by simp+
      then have "(v, e) \<in> S" using S_def by simp
      then have "x \<in> {u|u v e. f1 u (v, e) \<and> (v, e) \<in> S}"
        using 1 by blast
      then show "x \<in> \<Union> T" using 0 by simp
    qed
  next
    show "\<Union> T \<subseteq> {Edge v e 1 |v e. e \<in> set E \<and> v \<in> e}" proof 
      fix x assume a1: "x \<in> \<Union> T"
      have 0: "\<Union> T = {u|u v e. f1 u (v, e) \<and> (v, e) \<in> S}" using T_def by auto
      then obtain v e  where ve_def: "f1 x (v, e)" "(v, e) \<in> S" 
        using a1 by auto
      then have 1: "x = Edge v e 1" using f1_inv by fastforce 
      have 2: "v \<in> e" "e \<in> set E" 
        using ve_def S_def by blast+
      then show "x \<in> {Edge v e 1 |v e. e \<in> set E \<and> v \<in> e}"
        using 1 2 by simp
    qed
  qed  
  have 3: "\<forall>S' \<in> T. finite S'" 
  proof
    fix S' assume "S' \<in> T" 
    then obtain v e where ve_def: "S' = {u|u. f1 u (v, e)}" "(v, e)\<in> S"
      using T_def by blast
    then have "S' = {Edge v e 1}" using set_f1 by metis
    then show "finite S'" by simp
  qed
  have finS: "finite S" 
    using S_def fin_S_Edge assms by auto 
  then have fin: "finite T"
    using fin_dep_on_other_set T_def 
    by fastforce 
  have finT: "finite T"
    using finS fin_dep_on_other_set T_def 
    by fastforce
  have "finite (\<Union> T)"
    using 3 fin by blast
  then have "finite {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}" 
    using 1 by simp 
  then show ?thesis .  
qed


lemma card_Cov:
  assumes "(M::('a, 'b) hc_node set) = {Cover i|i. i< k}"
  shows "card M \<le> k"
proof -
  obtain S where S_def: "S= {i|i. i<k}" 
    by auto
  obtain T::"('a, 'b) hc_node set set" where T_def: "T = {{Cover j|j. j = i}|i. i\<in> S}"
    by auto
  have card_S: "card S = k"
    using S_def by simp
  have 1: "M = \<Union> T" 
    using S_def T_def assms by auto
  then have 10: "card M = card (\<Union> T)"
    by auto
  have 2: "\<forall>i. card {Cover j|j. j = i} = 1" by simp
  then have 3: "\<forall>S' \<in> T. card S' \<le> 1" 
    using T_def by fastforce
  have finS: "finite S" 
    using S_def by simp   
  then have fin: "finite T"
    using fin_dep_on_other_set T_def by simp
  have "card T \<le> card S"
    using finS card_dep_on_other_set T_def
    by fast
  then have cardT: "card T \<le> k"
    using card_S by blast
  have "card (\<Union> T) \<le> card T"
    using 3 card_union_if_all_subsets_card_1 fin by blast
  then have 4: "card (\<Union> T) \<le> k" 
    using cardT by simp 
  then show ?thesis using 10 
    by metis 
qed



lemma fin_verts: 
   assumes "\<forall>e\<in> set E. card e = 2" 
  shows "finite ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})"
  using fin_Cov fin_Edge0 fin_Edge1 assms 
  by blast  

lemma fin_max_arcs:
  assumes "\<forall>e\<in> set E. card e = 2" 
  shows "finite (({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}) \<times>
({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}))"
  using fin_verts assms
  by blast  



lemma card_verts: 
  assumes "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E"
  shows "card ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}) \<le> 6 * length E"
  sorry

lemma max_card_arcs: 
  assumes "A = ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})"
  shows "card (A \<times> A) = card A * card A"
  using card_cartesian_product using assms by blast


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
  have a1: "\<forall>e\<in> set E. card e = 2" using ugraph_def assms by metis
  obtain B where B_def: "B = ({Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e})"
    by auto
  have fB: "finite B" using fin_verts B_def a1 by fast
  have fBB: "finite (B \<times> B)" using fin_max_arcs B_def a1 by blast
  have "?A \<subseteq> 
    B \<times> B"
    using arcs_subset_graph B_def 
    by (auto)
  then have cardA: "card ?A \<le> card (B \<times> B)" 
    using card_mono fBB by(auto simp add: fin_max_arcs card_mono)  
  have 1: "card B \<le> 6 * length E" using card_verts B_def assms by blast
  then have "card (B \<times> B) = (card B) * (card B)"
    using card_cartesian_product by blast
  then have "card (B \<times> B) \<le>  6 * length E *card B"
    using 1 by(auto)
  then have "card (B \<times> B) \<le>  6 * length E * 6 * length E"
    using 1 order_subst1 by fastforce 
  then have "card ?A \<le> 6 * length E * 6 * length E" 
    using cardA by linarith  
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