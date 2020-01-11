theory VCTFNS_Poly
  imports "NREST.NREST" VC_To_FNS  "Landau_Symbols.Landau_More"
    "NREST.RefineMonadicVCG" "NREST.Refine_Foreach" TSTSC_Poly
begin

definition "size_fns = (\<lambda>(G,k). card (verts G)+ card (arcs G))"
definition "vc_to_fns_space n  = 2*n+2*n"

definition "mop_get_verts_fns E =SPECT [ {v. v \<in> \<Union> E} \<mapsto> 2*(card E)]"
definition "mop_get_arcs_fns E =SPECT [{(u, v)| u v. {u, v} \<in> E} \<mapsto> (2*(card E))]"

definition "vc_to_fns_alg = (\<lambda>(E,k).   
  do {
    b \<leftarrow> mop_check_ugraph E;
    V  \<leftarrow> mop_get_vertices E;
    cV \<leftarrow> mop_set_card V;
    if b \<and> k \<le> cV then
      do {
        v \<leftarrow> mop_get_verts_fns E;
        e \<leftarrow> mop_get_arcs_fns E;
        RETURNT (\<lparr>verts = v, arcs = e, tail = fst, head = snd\<rparr>, k+1)
      }
    else RETURNT (\<lparr>verts = {}, arcs = {}, tail = fst, head = snd \<rparr>, 0)
  } )"

definition "vc_fns_time n = 1+ (2 * n + 1) + 1 + 2 * n + 2 * n"


lemma e_in_E_e_explicit: 
  assumes "e \<in> E" "ugraph E"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v" 
proof -
  have 1: "card e = 2" 
    using assms ugraph_def assms by blast 
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


lemma card_verts_ugraph: 
  assumes "ugraph E"
  shows "card (\<Union> E) \<le> 2 * card E" 
  using assms proof(induction "card E" arbitrary: E)
  case 0
  have "finite E" 
    using ugraph_def 0 
    by blast
  then show ?case using 0 
    by fastforce 
next
  case (Suc x)
  then have 1: "E \<noteq> {}" "finite E"
    apply auto 
    using card_infinite by fastforce 
  then have "\<exists>x. x \<in> E" 
    by auto
  then obtain e where e_def: "e \<in> E" 
    by auto
  then have 2: "card (E - {e}) = card E - 1" 
    using 1 by simp
  then have e_prop: "finite e" "card e \<le> 2" 
    using Suc 1 ugraph_def e_def 
     apply (metis Suc.prems Suc_1 card_eq_0_iff e_def nat.distinct(1) ugraph_def) 
    using Suc.prems e_def ugraph_def by fastforce 
  obtain E' where E'_def: "E' = E - {e}"
    by simp
  then have 3: "card E' = x" 
    using Suc 2 
    by presburger
  have "ugraph E'" 
    using Suc E'_def 
    by (meson DiffD1 finite_Diff ugraph_def) 
  then have 4: "card (\<Union> E') \<le> 2 * card E'"
    using Suc 3 by auto
  have 5: "E = E' \<union> {e}" 
    using e_def E'_def by fast 
  then have "(\<Union> E) = (\<Union> E') \<union> e"
    by auto
  then have "card (\<Union> E) = card ((\<Union> E') \<union> e)"
    by metis 
  then have "card (\<Union> E) \<le> card (\<Union> E') + card e"
    by (simp add: card_Un_le) 
  then have "card (\<Union> E) \<le> 2 * card E' + 2" 
    using e_prop 4 
    by linarith
  then have "card (\<Union> E) \<le> 2 * card E" 
    using 5 3 Suc 
    by linarith  
  then show ?case .
qed


lemma card_verts: 
  assumes "ugraph E" 
  shows "card {v. \<exists>x\<in>E. v \<in> x} \<le> 2 * (card E)"
proof -
  have 1: "{v. \<exists>x\<in>E. v \<in> x} = \<Union> E" by blast
  have "card (\<Union> E) \<le> 2 * card E" 
    using assms card_verts_ugraph by auto
  then show ?thesis 
    using 1 by argo
qed


lemma card_arcs: 
  assumes "ugraph E" 
  shows "card {(u, v). {u, v} \<in> E} \<le> 2 * card E"
  using assms proof(induction "card E" arbitrary: E)
  case 0
  then have "finite E" 
    using ugraph_def by auto
  then have " E = {}"
    using 0 by simp
  then show ?case 
    by simp  
next
  case (Suc x)
  then have 1: "E \<noteq> {}" "finite E"
    apply auto 
    using card_infinite by fastforce 
  then have "\<exists>x. x \<in> E" 
    by auto
  then obtain e where e_def: "e \<in> E" 
    by auto
  then have 2: "card (E - {e}) = card E - 1" 
    using 1 by simp
  then have e_prop: "finite e" "card e \<le> 2" 
    using Suc 1 ugraph_def e_def 
     apply (metis Suc.prems(1) Suc_1 card_eq_0_iff e_def nat.distinct(1) ugraph_def) 
    using Suc.prems e_def ugraph_def by fastforce 
  then obtain u v where uv_def: "e = {u, v}" "u \<noteq> v"
    using e_in_E_e_explicit Suc e_def by metis 
  obtain E' where E'_def: "E' = E - {e}"
    by simp
  then have 3: "card E' = x" 
    using Suc 2 
    by presburger
  have "ugraph E'" 
    using Suc E'_def 
    by (meson DiffD1 finite_Diff ugraph_def) 
  then have 4: "card {(u, v). {u, v} \<in> E'} \<le> 2 * card E'"
    using Suc 3 by auto
  have 5: "E = E' \<union> {e}" 
    using e_def E'_def by fast 
  then have "{(u, v). {u, v} \<in> E} = {(u, v). {u, v} \<in> E'} \<union> {(u, v), (v, u)}"
    using uv_def by auto
  then have "card {(u, v). {u, v} \<in> E} = card ({(u, v). {u, v} \<in> E'} \<union> {(u, v), (v, u)})"
    by metis
  then have "card {(u, v). {u, v} \<in> E} \<le> card {(u, v). {u, v} \<in> E'} + card {(u, v), (v, u)}"
    by (metis card_Un_le) 
  then have "card {(u, v). {u, v} \<in> E} \<le> 2 * card E' + card {(u, v), (v, u)}" 
    using 4 
    by linarith
  then have "card {(u, v). {u, v} \<in> E} \<le> 2 * card E' + 2" 
    using uv_def by auto 
  then show ?case 
    using 5 3 Suc by simp 
qed


lemma card_G: 
  assumes "ugraph E"
  shows "card {v. \<exists>x\<in>E. v \<in> x} + card {(u, v). {u, v} \<in> E} \<le> 4 * card E"
proof -
  have 1: "card {v. \<exists>x\<in>E. v \<in> x} \<le> 2 * card E" 
    using card_verts assms 
    by blast
  have 2: "card {(u, v). {u, v} \<in> E} \<le> 2 * card E" 
    using card_arcs assms by blast 
  then show ?thesis using 1 2 by auto
qed

lemma vc_to_fns_size: "size_fns (vc_to_fns (E, k)) \<le> vc_to_fns_space (size_VC (E, k))" 
  apply(auto simp: size_fns_def vc_set_to_vc_list_def vc_to_fns_space_def size_VC_def)
  by(auto simp add: vc_to_fns_def card_G)


lemma vc_to_fns_reifnes:
  "vc_to_fns_alg (E, k) \<le> SPEC (\<lambda>y. y = (vc_to_fns (E, k))) (\<lambda>_. vc_fns_time (size_VC (E, k)))"
  unfolding SPEC_def
  unfolding vc_to_fns_alg_def vc_to_fns_def   
    mop_check_ugraph_def  mop_get_vertices_def mop_set_card_def
    mop_get_verts_fns_def mop_get_arcs_fns_def
  apply(rule T_specifies_I) 
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by(auto simp: vc_fns_time_def size_VC_def set_set_to_list distinct_set_to_list
      one_enat_def)

lemma cnf_sat_to_clique_ispolyred: "ispolyred vc_to_fns_alg vertex_cover fns size_VC size_fns" 
  unfolding ispolyred_def
  apply(rule exI[where x=vc_to_fns])
  apply(rule exI[where x=vc_fns_time])
  apply(rule exI[where x=vc_to_fns_space])
  apply(safe)
  subgoal using vc_to_fns_reifnes by blast
  subgoal using vc_to_fns_size by blast  
  subgoal unfolding poly_def vc_fns_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def vc_to_fns_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_vc_to_fns .
  done

end