theory HC_To_UHC_Poly
  imports "NREST.NREST" HC_To_UHC  "Landau_Symbols.Landau_More"
    "NREST.RefineMonadicVCG" "NREST.Refine_Foreach" "../TSTSC_Poly"
begin


definition "size_uhc = (\<lambda>G. card (verts G) + card (arcs G))"
definition "size_hc = (\<lambda>G. card (verts G))"
definition "hc_to_uhc_space n  = 3 * n+ 9 * n * n + 2"

definition "mop_check_wf_digraph Gr = SPECT [wf_digraph Gr \<mapsto> 1]"
definition "mop_check_finite Gr = SPECT [finite (verts Gr) \<mapsto> 1]"
definition "mop_check_functions Gr = SPECT [((tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}) \<mapsto> 3]" 

definition "mop_verts_G Gr = SPECT [ {(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr} \<union> {(v, 2)|v. v \<in> verts Gr}
    \<mapsto> 3 * (card (verts Gr))]"

definition "mop_arcs_G Gr = SPECT [
            {((v, 0), (v, 1))|v. v \<in> verts Gr} \<union>{((v, 1), (v, 0))|v. v \<in> verts Gr}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts Gr}\<union>{((v, 2), (v, 1))|v. v \<in> verts Gr}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}
    \<mapsto> 3 * card (verts Gr) * 3 * (card (verts Gr))]"

definition "hc_to_uhc_alg = (\<lambda>G.   
  do {
    bg \<leftarrow> mop_check_wf_digraph G;
    bfu  \<leftarrow> mop_check_functions G;
    bfi \<leftarrow> mop_check_finite G;    
    cVG \<leftarrow> mop_set_card (verts G);
    if bg \<and> bfu then
      do {
        if bfi then 
        do { 
          if cVG > 1 then 
          do {
            V \<leftarrow> mop_verts_G G;
            E  \<leftarrow> mop_arcs_G G;
            RETURNT \<lparr>verts = V, arcs = E, tail = fst, head = snd\<rparr> 
          }
          else RETURNT \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>
        }
        else RETURNT \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>
      }
    else RETURNT (let x = (SOME x. x \<in> arcs G) in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)
  } )"

definition "hc_to_uhc_time n = 6 + 3*n + 3 * n * 3 * n"


lemma wf_digraph_card_arcs: 
  assumes "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}" 
    "finite (verts Gr)" 
  shows "card (arcs Gr) \<le> card (verts Gr) * card (verts Gr)" 
proof -
  have "arcs Gr \<subseteq> (verts Gr)\<times> (verts Gr)" 
    using assms wf_digraph.head_in_verts wf_digraph.tail_in_verts by fastforce 
  then show ?thesis using assms 
    by (metis card_cartesian_product card_mono finite_cartesian_product_iff) 
qed


lemma card_verts_i: 
  assumes "finite (verts Gr)" 
  shows "card {(v, i)|v. v \<in> verts Gr} \<le> card (verts Gr)"
  using assms proof -
  have " {(v, i)|v. v \<in> verts Gr} = (verts Gr) \<times> {i}"
    by auto
  then show ?thesis using assms 
    by auto 
qed


lemma card_verts: 
  assumes "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
  shows "card (verts (hc_to_uhc Gr))
    \<le> 3 * card (verts Gr)" 
proof(cases "finite (verts Gr)")
  case True
  then show ?thesis using assms proof(cases "card (verts Gr) > 1")
    case True
    then have "hc_to_uhc Gr = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr} \<union> {(v, 2)|v. v \<in> verts Gr}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts Gr} \<union>{((v, 1), (v, 0))|v. v \<in> verts Gr}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts Gr}\<union>{((v, 2), (v, 1))|v. v \<in> verts Gr}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v},
    tail = fst, head = snd\<rparr>" 
      using assms by(auto simp add: hc_to_uhc_def)
    then have 1: "card (verts (hc_to_uhc Gr)) = card ({(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr} \<union> {(v, 2)|v. v \<in> verts Gr})" 
      by auto
    have 2: "... \<le> card {(v, (0::nat))|v. v \<in> verts Gr} + card  ({(v, (1::nat))|v. v \<in> verts Gr} \<union> {(v, (2::nat))|v. v \<in> verts Gr})"
      using card_Un_le 
      by (simp add: card_Un_le sup_assoc) 
    have 3: "... \<le> card {(v, (0::nat))|v. v \<in> verts Gr} + card  {(v, (1::nat))|v. v \<in> verts Gr} + card {(v, (2::nat))|v. v \<in> verts Gr}"
      using card_Un_le 
      by (simp add: card_Un_le sup_assoc)
    then have 4: "... \<le> card (verts Gr) + card  {(v, (1::nat))|v. v \<in> verts Gr} + card {(v, (2::nat))|v. v \<in> verts Gr}"
      using card_verts_i True by force
    then have 5: "... \<le> card (verts Gr) +card(verts Gr) + card {(v, (2::nat))|v. v \<in> verts Gr}"
      using card_verts_i True by force
    then have 6: "... \<le> card (verts Gr) + card(verts Gr) + card (verts Gr)"
      using card_verts_i True by force
    then have 7: "... \<le> 3* card (verts Gr)"
      by linarith
    then show ?thesis using 1 2 3 4 5 6 7 
      by linarith  
  next
    case False
    then have "hc_to_uhc Gr = \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>"
      using assms True by(auto simp add: hc_to_uhc_def)
    then show ?thesis 
      by simp 
  qed 
next
  case False
  then have 1: "hc_to_uhc Gr = \<lparr>verts = {(v, 0)|v. v \<in> verts Gr}, arcs = {}, tail = fst, head = snd\<rparr>"
    using assms hc_to_uhc_def by(auto simp add: hc_to_uhc_def) 
  then have "\<not> finite (verts (hc_to_uhc Gr))" 
  proof -
    have "verts (hc_to_uhc Gr) = {(v, 0)|v. v \<in> verts Gr}"
      using 1 by auto
    then have "verts (hc_to_uhc Gr) = (verts Gr) \<times> {0}" 
      using 1 by auto
    then have "\<not> finite (verts (hc_to_uhc Gr))" 
      using False finite_cartesian_productD1 by fastforce 
    then show ?thesis by simp 
  qed
  then show ?thesis 
    by simp 
qed


lemma finite_verts_i: 
  assumes "finite (verts Gr)" 
  shows "finite {(v, i)|v. v \<in> verts Gr}"
  using assms proof -
  have " {(v, i)|v. v \<in> verts Gr} = (verts Gr) \<times> {i}"
    by auto
  then show ?thesis using assms 
    by auto 
qed



lemma card_arcs_helper: 
  assumes "G' = (if card (verts Gr) > 1 then 
    \<lparr>verts = {(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr} \<union> {(v, 2)|v. v \<in> verts Gr}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts Gr} \<union>{((v, 1), (v, 0))|v. v \<in> verts Gr}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts Gr}\<union>{((v, 2), (v, 1))|v. v \<in> verts Gr}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v},
    tail = fst, head = snd\<rparr> 
    else \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>)"
    "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}" "finite (verts Gr)" 
  shows "finite (verts G') \<and> tail G' = fst \<and> head G' = snd \<and> wf_digraph G'"
proof(cases "card (verts Gr) > 1")
  case True
  then have G'_def: "G' = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr} \<union> {(v, 2)|v. v \<in> verts Gr}, 
    arcs = {((v, 0::nat), (v, 1))|v. v \<in> verts Gr} \<union>{((v, 1), (v, 0))|v. v \<in> verts Gr}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts Gr}\<union>{((v, 2), (v, 1))|v. v \<in> verts Gr}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v},
    tail = fst, head = snd\<rparr>" 
    using assms by auto
  then have 1: "wf_digraph G'" using wf_digraph_def assms by(auto simp add: wf_digraph_def) 
  then have 2: "tail G' = fst \<and> head G' = snd" using G'_def by simp
  have 3: "finite (verts G')" 
    using assms G'_def finite_verts_i proof -
    have "finite  {(v, (0::nat))|v. v \<in> verts Gr}" "finite {(v, 1)|v. v \<in> verts Gr}" 
        "finite {(v, 2)|v. v \<in> verts Gr}" using finite_verts_i assms by auto
    then show ?thesis using G'_def  finite_UnI 
      by fastforce  
  qed
  then show ?thesis using 1 2 by simp  
next
  case False
  then have "G' = \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>" 
    using assms by auto
  then show ?thesis using wf_digraph_def 
    by force
qed


lemma card_arcs: 
  assumes "wf_digraph Gr" "(tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
  shows "card(arcs (hc_to_uhc Gr)) \<le> 9 * (card (verts Gr)) * (card (verts Gr))"
  proof(cases "finite (verts Gr)")
    case True
    then have "hc_to_uhc Gr = (if card (verts Gr) > 1 then 
    \<lparr>verts = {(v, (0::nat))|v. v \<in> verts Gr} \<union> {(v, 1)|v. v \<in> verts Gr} \<union> {(v, 2)|v. v \<in> verts Gr}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts Gr} \<union>{((v, 1), (v, 0))|v. v \<in> verts Gr}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts Gr}\<union>{((v, 2), (v, 1))|v. v \<in> verts Gr}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs Gr \<and> v = tail Gr e \<and> u = head Gr e \<and> u \<noteq> v},
    tail = fst, head = snd\<rparr> 
    else \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>)"
      using assms by (auto simp add: hc_to_uhc_def)
    then have 1: "finite (verts (hc_to_uhc Gr))" "tail (hc_to_uhc Gr) = fst \<and> head (hc_to_uhc Gr) = snd"
      "wf_digraph (hc_to_uhc Gr)"
      using card_arcs_helper assms True by blast+
    then have 2: "card (arcs (hc_to_uhc Gr)) \<le> card (verts (hc_to_uhc Gr)) * card (verts (hc_to_uhc Gr))" 
      using wf_digraph_card_arcs by blast
    have "card (verts (hc_to_uhc Gr)) \<le> 3 * card (verts Gr)" 
      using assms card_verts True by auto
    then have "card (arcs (hc_to_uhc Gr)) \<le> 3 * card (verts Gr)* 3 * card (verts Gr)" 
      using 2 
      by (smt le_trans mult.assoc mult_le_mono)   
  then show ?thesis using assms wf_digraph_card_arcs card_verts 
    by linarith   
next
  case False
  then have 1: "hc_to_uhc Gr = \<lparr>verts = {(v, 0)|v. v \<in> verts Gr}, arcs = {}, tail = fst, head = snd\<rparr>"
    using assms hc_to_uhc_def by(auto simp add: hc_to_uhc_def) 
  then show ?thesis 
    by simp 
qed



lemma aux1: 
  assumes "wf_digraph Gr \<and> (tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}"
  shows "card (verts (hc_to_uhc Gr))+
        card(arcs (hc_to_uhc Gr))
        \<le> 3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr)" (is "?A + ?B \<le> ?C")
proof -
  have 1: "?A \<le> 3 * card (verts Gr)" 
    using card_verts assms 
    using not_wf_digraph_not_arcs_empty by auto 
  have "?B \<le> 9 * card (verts Gr) * card (verts Gr)"
    using card_arcs assms 
    using not_wf_digraph_not_arcs_empty by auto 
  then show ?thesis using 1 by simp
qed


lemma arith_helper: 
  shows "3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr) \<le>
         3 * (card (verts Gr) + card (arcs Gr)) + 9 * (card (verts Gr) + card (arcs Gr)) * (card (verts Gr) + card (arcs Gr)) +2"
proof -
  have 1: "3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr) \<le> 3 * (card (verts Gr) + card (arcs Gr)) + 9 * card (verts Gr) * card (verts Gr)"
    by auto 
  then have 2: "... \<le>  3 * (card (verts Gr) + card (arcs Gr)) + 9 * (card (verts Gr) + card (arcs Gr)) * card (verts Gr)"
    by simp
  then have 3: "... \<le> 3 *  (card (verts Gr) + card (arcs Gr)) + 9 * (card (verts Gr) + card (arcs Gr)) * (card (verts Gr) + card (arcs Gr))"
    by auto
  then show ?thesis using 1 2 
    by linarith 
qed


lemma vcs_to_vcl_size: "size_uhc (hc_to_uhc Gr) \<le> hc_to_uhc_space (size_hc Gr)" 
  unfolding size_uhc_def hc_to_uhc_space_def size_hc_def 
proof (cases "wf_digraph Gr \<and> (tail Gr = fst \<and> head Gr = snd) \<or> arcs Gr = {}")
  case True
  then have "card (verts (hc_to_uhc Gr)) + card (arcs (hc_to_uhc Gr)) 
    \<le>3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr)"
    using aux1 by auto 
  then show "card (verts (hc_to_uhc Gr)) + card (arcs (hc_to_uhc Gr)) 
    \<le>  3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr) + 2" 
    using arith_helper le_trans by auto
next
  case False
  then have 1: "hc_to_uhc Gr =(let x = (SOME x. x \<in> arcs Gr) in \<lparr>verts = {}, arcs = {((head Gr x, 0), (head Gr x, 1))}, tail = fst, head = snd\<rparr>)"
    by(auto simp add: hc_to_uhc_def)
  then show "card (verts (hc_to_uhc Gr)) + card (arcs (hc_to_uhc Gr)) 
    \<le>  3 * card (verts Gr) + 9 * card (verts Gr) * card (verts Gr) + 2" 
  proof -
    have "card (verts (hc_to_uhc Gr)) = 0" 
      using 1 
      by (metis card_empty select_convs(1)) 
    have "card (arcs (hc_to_uhc Gr)) = 1" 
      using 1 
      by (metis is_singletonI is_singleton_altdef select_convs(2))
    then show ?thesis 
      using \<open>card (verts (hc_to_uhc Gr)) = 0\<close> by linarith  
  qed
qed


lemma vcs_to_vcl_reifnes:
  "hc_to_uhc_alg Gr \<le> SPEC (\<lambda>y. y = (hc_to_uhc Gr)) (\<lambda>_. hc_to_uhc_time (size_hc Gr))"
  unfolding SPEC_def 
  unfolding hc_to_uhc_alg_def hc_to_uhc_def   
    mop_check_ugraph_def  mop_check_wf_digraph_def mop_check_functions_def mop_check_finite_def    
    mop_arcs_G_def mop_verts_G_def mop_set_card_def
  apply(rule T_specifies_I) 
  apply(vcg' \<open>-\<close> rules: T_SPEC )
     apply(auto simp: hc_to_uhc_time_def one_enat_def size_hc_def)
  by (simp add: numeral_eq_enat)+

lemma cnf_sat_to_clique_ispolyred: "ispolyred hc_to_uhc_alg hc uhc size_hc size_uhc" 
  unfolding ispolyred_def
  apply(rule exI[where x=hc_to_uhc])
  apply(rule exI[where x=hc_to_uhc_time])
  apply(rule exI[where x=hc_to_uhc_space])
  apply(safe)
  subgoal using vcs_to_vcl_reifnes by blast
  subgoal using vcs_to_vcl_size by blast  
  subgoal unfolding poly_def hc_to_uhc_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def hc_to_uhc_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_hc_uhc .
  done

end