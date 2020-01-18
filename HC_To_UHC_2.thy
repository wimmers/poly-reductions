theory HC_To_UHC_2
  imports HC_To_UHC
begin

subsection\<open>hc_to_uhc G \<in> uhc --> G \<in> hc\<close>


lemma is_hc_impl_length_c: 
  assumes "is_hc G c" "card (verts G) > 1"
  shows "length c \<ge> card (verts G)" 
proof -
  have "\<not> card (verts G) \<le> 1" 
    using assms by simp
  then have "\<forall>x \<in> verts G. x \<in> set c"
    using assms is_hc_def by metis
  then have "verts G \<subseteq> set c" 
    by auto
  then show ?thesis 
    using card_length card_subset le_trans by blast 
qed

lemma hc_G_geq_2_verts_impl_arcs: 
  assumes "card (verts G) > 1" "(arcs G = {})"
  shows "G \<notin> hc" 
proof(rule ccontr)
  assume "\<not>G \<notin> hc"
  then have "\<exists>c. is_hc G c"
    using assms hc_def by auto
  then obtain c where c_def: "is_hc G c" by auto
  then have "length c > 1" 
    using is_hc_impl_length_c assms by fastforce
  then have 1: "vwalk_arcs c \<noteq> []"
    by (simp add: length_C_vwalk_arcs_not_empty) 
  have "pre_digraph.cycle G (vwalk_arcs c)" 
    using assms c_def is_hc_def by fastforce
  then have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs c) u"
    using pre_digraph.cycle_def by metis
  then have "set (vwalk_arcs c) \<subseteq> arcs G" 
    using pre_digraph.awalk_def by metis
  then show False using 1 assms by simp
qed
     


fun to_cycle_hc where
"to_cycle_hc ((a, b)#vs) = (if b = 0 then a#(to_cycle_hc vs) else to_cycle_hc vs)" |
"to_cycle_hc [] = []"


context
  fixes G assumes in_uhc: "hc_to_uhc G \<in> uhc"
  fixes G' assumes G'_def: "G' = hc_to_uhc G" 
  fixes Cy1 assumes Cy1_def: "is_uhc G' Cy1"
  fixes Cy2 assumes Cy2_def: "Cy2 = rev Cy1"
  fixes C1 assumes C1_def: "C1 = to_cycle_hc Cy1"
  fixes C2 assumes C2_def: "C2 = to_cycle_hc Cy2" 
begin 


lemma G'_properties:
  shows "symmetric G'" "finite (verts G')" "wf_digraph G'" 
  using G'_def in_uhc uhc_def by(auto)


lemma G_properties: 
  shows "wf_digraph G" "((tail G = fst \<and> head G = snd) \<or> arcs G = {})"  
proof -
  show "wf_digraph G" proof(rule ccontr)
    assume a1: "\<not> wf_digraph G" 
    then have "G' = \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>" 
      using G'_def
      by (simp add: hc_to_uhc_def) 
    then have "G' \<notin> uhc" using a1 else_not_in_uhc_1 by blast 
    then show False using G'_def in_uhc by simp
  qed
next
  show "((tail G = fst \<and> head G = snd) \<or> arcs G = {})" proof(rule ccontr)
    assume a1: "\<not> ((tail G = fst \<and> head G = snd) \<or> arcs G = {})" 
    then have "G' = \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>" 
      using G'_def 
      by (simp add: a1 hc_to_uhc_def) 
    then have "G' \<notin> uhc" using a1 else_not_in_uhc_2 by blast   
    then show False using G'_def in_uhc by simp
  qed
qed


lemma G'_def_3:
  shows "G' = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G}, 
      arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (u, 2))|u. u \<in> verts G}\<union> 
          {((u, 2), (u, 0))|u. u \<in> verts G}, 
      tail = fst, head = snd\<rparr>"
  using G_properties G'_def by(auto simp add: hc_to_uhc_def) 


lemma head_tail_G':
  shows "head G' = snd" "tail G' = fst" 
  using G'_def_3 by simp+


lemma is_uhc_lenght_Cycle_approx: 
  assumes "is_uhc G' Cycle"  "card (verts G') > 1"
  shows "length Cycle \<ge> card (verts G')"
proof -
  have "\<forall>x \<in> verts G'. x \<in> set Cycle" 
    using assms is_uhc_def by force
  then have "card (set Cycle) \<ge> card (verts G')"
    by (simp add: card_subset subsetI) 
  then show ?thesis 
    using card_length le_trans by blast 
qed


lemma hd_pre_digraph_cas: 
  assumes "pre_digraph.cas G' u (p) v" "p\<noteq> []" 
  shows "fst (hd p) = u"
  using assms proof(induction p arbitrary: u)
  case Nil
  then show ?case by simp 
next
  case (Cons a p)
  then have "pre_digraph.cas G' u (a#p)  v = 
      (tail G' a = u \<and> pre_digraph.cas G' (head G' a) p v)"
    by (simp add: pre_digraph.cas.simps(2))
  then have "tail G' a = u" 
    using Cons 
    by simp
  then have "fst a = u" 
    using head_tail_G' assms
    by auto
  then show ?case by simp
qed 


lemma last_pre_digraph_cas: 
  assumes "pre_digraph.cas G' u (p) v" "p\<noteq> []" 
  shows "snd (last p) = v"
  using assms proof(induction p arbitrary: u)
  case Nil
  then show ?case by simp 
next
  case (Cons a p)
  then show ?case proof(cases "p = []")
    case True
    then have 0: "last (a#p) = a" 
      by simp
    then have "pre_digraph.cas G' u (a#p)  v = 
      (tail G' a = u \<and> pre_digraph.cas G' (head G' a) [] v)"
      using True 
      by (simp add: pre_digraph.cas.simps(2)) 
    then have 1: "pre_digraph.cas G' (head G' a) [] v"
      using Cons by auto
    then have 2: "pre_digraph.cas G' (head G' a) [] v = 
      ((head G' a) = v)" 
      using pre_digraph.cas.simps  by fast 
    then have "head G' a = snd a" 
      using head_tail_G' assms 
      by (auto)
    then show ?thesis 
      using 0 1 2 by simp
  next
    case False
    then have 0: "last (a#p) = last p" 
      by simp
    have "pre_digraph.cas G' u (a#p)  v = 
      (tail G' a = u \<and> pre_digraph.cas G' (head G' a) p v)"
      by (simp add: pre_digraph.cas.simps(2)) 
    then have "pre_digraph.cas G' (head G' a) p v"
      using Cons by auto
    then have " snd (last p) = v" 
      using Cons False by simp 
    then show ?thesis 
      using 0 by auto 
  qed
qed 


lemma hd_last_C_G': 
  assumes "is_uhc G' Cycle" 
    "card (verts G') > 1" 
  shows "hd Cycle = last Cycle" 
proof -
  have "vwalk_cycle G' Cycle" 
    using is_uhc_def assms by fastforce
  then show ?thesis using vwalk_cycle_def by auto
qed


lemma is_uhc_impl_is_uhc_rev: 
  assumes "is_uhc G' C"
  shows "is_uhc G' (rev C)" 
  unfolding is_uhc_def 
proof -
  have "set C \<subseteq> verts G'"
    using assms is_uhc_def by fast
  then have 1: "set (rev C) \<subseteq> verts G'"
    by simp
  then show "(vwalk_cycle G' (rev C) \<and> (\<forall>x\<in>verts G'. x \<in> set (rev C)) \<and> distinct (tl (rev C)) \<or> card (verts G') \<le> 1) \<and> set (rev C) \<subseteq> verts G'" 
  proof(cases "card (verts G') \<le> 1")
    case True
    then show ?thesis using 1 by blast
  next
    case False
    then have a1: "card (verts G') > 1" by simp
    then have "hd C = last C" "distinct (tl C)"
      using assms is_uhc_def hd_last_C_G' assms False by auto
    then have 2: "distinct (tl (rev C))"
      using distinct_tl_rev_C by auto
    have "(\<forall>x\<in>verts G'. x \<in> set (C))"
      using assms is_uhc_def False by fast
    then have 3: "(\<forall>x\<in>verts G'. x \<in> set (rev C))" 
      by simp
    have "vwalk_cycle G' C"
      using False is_uhc_def assms by blast
    then have "vwalk_cycle G' (rev C)" 
      by (simp add: G'_properties(1) vwalk_cycle_rev) 
    then show ?thesis using 1 2 3 by blast
  qed 
qed


lemma uhc_Cy2: 
  shows "is_uhc G' Cy2" 
  using is_uhc_impl_is_uhc_rev Cy2_def Cy1_def by simp


lemma verts_G_G': 
  assumes "x \<in> verts G"
  shows "(x, 0) \<in> verts G'"  "(x, 1) \<in> verts G'"  "(x, 2) \<in> verts G'" 
  using G'_def_3 assms by auto 


lemma card_verts_G_G': 
  assumes  "card (verts G) > 1" 
  shows "card (verts G') > 1" 
  using G'_def 
  by (metis (no_types, hide_lams) Cy1_def G'_properties(2) HC_To_UHC_2.verts_G_G'(1) assms card_greater_1_contains_two_elements contains_two_card_greater_1 local.in_uhc prod.inject verts_G_G'(2) zero_neq_one) 


lemma hd_last_Cy1: 
  assumes "card (verts G) > 1" 
  shows "hd Cy1 = last Cy1" 
  using assms card_verts_G_G' Cy1_def hd_last_C_G' by blast 


lemma x_inG_x_i_in_Cy1: 
  assumes "x \<in> verts G"  "card (verts G) > 1" 
  shows "(x, 0) \<in> set Cy1"  "(x, 1) \<in> set Cy1"  "(x, 2) \<in> set Cy1"
proof -
  have 0: "card (verts G') > 1" 
    using assms card_verts_G_G' by auto
  then have 1: "\<forall>x \<in> verts G'. x \<in> set Cy1" 
    using Cy1_def is_uhc_def by fastforce
  have "(x, 0) \<in> verts G'"  "(x, 1) \<in> verts G'"  "(x, 2) \<in> verts G'" 
    using assms verts_G_G' by auto
  then show "(x, 0) \<in> set Cy1"  "(x, 1) \<in> set Cy1"  "(x, 2) \<in> set Cy1" using 1 
    by auto
qed


lemma length_Cy1: 
  assumes "card (verts G) > 1"
  shows "length Cy1 \<ge> 2" "length Cy1 > 1"
  proof -
  have 0: "card (verts G') > 1" 
    using assms card_verts_G_G' by auto
  then have 1: "\<forall>x \<in> verts G'. x \<in> set Cy1" 
    using Cy1_def is_uhc_def by fastforce
  then have "length Cy1 > 1" 
    using 0 
    by (meson Cy1_def is_uhc_lenght_Cycle_approx le_trans less_le_not_le) 
  then show "length Cy1 > 1" "length Cy1 \<ge> 2"
    by auto
qed


lemma arcs_ends_G': 
  shows "arcs_ends G' = arcs G'" 
  by (simp add: Graph_Auxiliaries.arcs_ends_G' local.head_tail_G') 


lemma sublist_Cy1_arcs_G': 
  assumes "sublist [a, b] Cy1" "card (verts G) > 1"
  shows "(a, b) \<in> arcs G'" 
proof -
  have 0: "card (verts G') > 1" 
    using assms card_verts_G_G' by auto
  have 1: "(a, b) \<in> set (vwalk_arcs Cy1)" 
    using assms 
    by (simp add: sublist_imp_in_arcs) 
  have "vwalk_cycle G' Cy1"
    using Cy1_def assms is_uhc_def 0 by force
  then have "vwalk Cy1 G'"
    using vwalk_cycle_def by blast
  then have "set (vwalk_arcs Cy1) \<subseteq> arcs_ends G'"
    by auto
  then have "set (vwalk_arcs Cy1) \<subseteq> arcs G'"
    using arcs_ends_G' by simp
  then show ?thesis using 1 by auto 
qed


lemma pre_1_edge: 
  assumes "sublist [y, (x, 1)] Cy1" "card (verts G) > 1"
  shows "y = (x, 0) \<or> y = (x, 2)" 
proof -
  have "(y, (x, 1)) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by simp
  then show ?thesis using G'_def_3 by(auto) 
qed


lemma pre_0_edges_helper: 
  assumes "((x, 2), (y, 0)) \<in> arcs G'" "card (verts G) > 1"
  shows "(x, y) \<in> arcs G \<or> x = y" 
  using assms G_properties G'_def_3 by(auto)



lemma pre_0_edge: 
  assumes "sublist [y, (x, 0)] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> y = (x, 2) \<or> (\<exists>z. y = (z, 2) \<and> (z, x) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms 
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(1)) 
  then obtain a b where ab_def: "(a, b) = y" 
    using G'_def_3 by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3 
    by force  
  have "(y, (x, 0)) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by auto
  then show ?thesis proof(cases "b = 0" )
    case True
    then have "((a, 0), (x, 0)) \<notin> arcs G'"
      using G'_def_3 by simp  
    then show ?thesis 
      using True \<open>(y, x, 0) \<in> arcs G'\<close> ab_def by auto 
  next
    case False
    then have 2: "b = 1 \<or> b = 2" 
      using 1 by simp
    then show ?thesis proof(cases "b = 1")
      case True
      then have "((a, 1), (x, 0)) \<in> arcs G'"
        using ab_def 
        by (simp add: \<open>(y, x, 0) \<in> arcs G'\<close>) 
      then have "a = x"
        using G'_def_3 by simp
      then show ?thesis using ab_def True by simp 
    next
      case False
      then have 3: "b = 2" using 2 by auto
      then have "((a, 2), (x, 0)) \<in> arcs G'" 
        using ab_def 
        by (simp add: \<open>(y, x, 0) \<in> arcs G'\<close>) 
      then have "a = x \<or> (a, x) \<in> arcs G" 
        using pre_0_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma pre_2_edges_helper: 
  assumes "((x, 0), (y, 2)) \<in> arcs G'" "card (verts G) > 1"
  shows "(y, x) \<in> arcs G \<or> x = y" 
  using assms G_properties G'_def_3 by(auto)



lemma pre_2_edge: 
  assumes "sublist [y, (x, 2)] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> y = (x, 0) \<or> (\<exists>z. y = (z, 0) \<and> (x, z) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms 
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(1)) 
  then obtain a b where ab_def: "(a, b) = y" 
    using G'_def_3 by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3 
    by force  
  have "(y, (x, 2)) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by auto
  then show ?thesis proof(cases "b = 2" )
    case True
    then have "((a, 2), (x, 2)) \<notin> arcs G'"
      using G'_def_3 by simp  
    then show ?thesis 
      using True \<open>(y, x, 2) \<in> arcs G'\<close> ab_def by auto 
  next
    case False
    then have 2: "b = 0 \<or> b = 1" 
      using 1 by simp
    then show ?thesis proof(cases "b = 1")
      case True
      then have "((a, 1), (x, 2)) \<in> arcs G'"
        using ab_def 
        by (simp add: \<open>(y, x, 2) \<in> arcs G'\<close>) 
      then have "a = x"
        using G'_def_3 by simp
      then show ?thesis using ab_def True by simp 
    next
      case False
      then have 3: "b = 0" using 2 by auto
      then have "((a, 0), (x, 2)) \<in> arcs G'" 
        using ab_def 
        by (simp add: \<open>(y, x, 2) \<in> arcs G'\<close>) 
      then have "a = x \<or> (x, a) \<in> arcs G" 
        using pre_2_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma post_0_edge: 
  assumes "sublist [(x, 0), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> y = (x, 2) \<or> (\<exists>z. y = (z, 2) \<and> (z, x) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms 
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(2)) 
  then obtain a b where ab_def: "(a, b) = y" 
    using G'_def_3 by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3 
    by force  
  have in_arcs: "((x, 0), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by auto
  then show ?thesis proof(cases "b = 0" )
    case True
    then have "((x, 0), (a, 0)) \<notin> arcs G'"
      using G'_def_3 by simp  
    then show ?thesis 
      using True \<open>((x, 0), y) \<in> arcs G'\<close> ab_def by auto 
  next
    case False
    then have 2: "b = 1 \<or> b = 2" 
      using 1 by simp
    then show ?thesis proof(cases "b = 1")
      case True
      then have "((x, 0), (a, 1)) \<in> arcs G'"
        using ab_def 
        by (simp add: in_arcs) 
      then have "a = x"
        using G'_def_3 by simp
      then show ?thesis using ab_def True by simp 
    next
      case False
      then have 3: "b = 2" using 2 by auto
      then have "((x, 0), (a, 2)) \<in> arcs G'" 
        using ab_def 
        by (simp add: in_arcs) 
      then have "a = x \<or> (a, x) \<in> arcs G" 
        using pre_2_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma post_2_edge: 
  assumes "sublist [(x, 2), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> y = (x, 0) \<or> (\<exists>z. y = (z, 0) \<and> (x, z) \<in> arcs G)"
proof -
  have y_in: "y \<in> verts G'"
    using assms 
    by (metis G'_properties(3) local.arcs_ends_G' sublist_Cy1_arcs_G' wf_digraph.adj_in_verts(2)) 
  then obtain a b where ab_def: "(a, b) = y" 
    using G'_def_3 by auto
  then have 1: "b = 0 \<or> b = 1 \<or> b = 2"
    using y_in G'_def_3 
    by force  
  have in_arcs: "((x, 2), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by auto
  then show ?thesis proof(cases "b = 2" )
    case True
    then have "((x, 2), (a, 2)) \<notin> arcs G'"
      using G'_def_3 by simp  
    then show ?thesis 
      using True in_arcs ab_def by auto 
  next
    case False
    then have 2: "b = 0 \<or> b = 1" 
      using 1 by simp
    then show ?thesis proof(cases "b = 1")
      case True
      then have "((x, 2), (a, 1)) \<in> arcs G'"
        using ab_def 
        by (simp add: in_arcs) 
      then have "a = x"
        using G'_def_3 by simp
      then show ?thesis using ab_def True by simp 
    next
      case False
      then have 3: "b = 0" using 2 by auto
      then have "((x, 2), (a, 0)) \<in> arcs G'" 
        using ab_def 
        by (simp add: in_arcs) 
      then have "a = x \<or> (x, a) \<in> arcs G" 
        using pre_0_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma post_1_edge: 
  assumes "sublist [(x, 1), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 0) \<or> y = (x, 2)" 
proof -
  have "((x, 1), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by simp
  then show ?thesis using G'_def_3 by(auto) 
qed



lemma pre_1_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "(sublist [(x, 0), (x, 1)] Cy1) \<or> sublist [(x, 2), (x, 1)] Cy1"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1 by auto
  have "(x, 1) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [y, (x, 1)] Cy1"  
    using 0 hd_last_Cy1 assms 
    by (meson List_Auxiliaries.b_in_Cycle_exists_sublist) 
  then obtain y where y_def: "sublist [y, (x, 1)] Cy1"
    by blast
  then show ?thesis using pre_1_edge assms by blast
qed


lemma pre_2_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "(sublist [(x, 0), (x, 2)] Cy1) \<or> sublist [(x, 1), (x, 2)] Cy1 \<or> (\<exists>z. sublist [(z, 0), (x, 2)] Cy1 \<and> (x, z) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1 by auto
  have "(x, 2) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [y, (x, 2)] Cy1"  
    using 0 hd_last_Cy1 assms 
    by (meson List_Auxiliaries.b_in_Cycle_exists_sublist) 
  then obtain y where y_def: "sublist [y, (x, 2)] Cy1"
    by blast
  then show ?thesis using pre_2_edge assms by blast 
qed


lemma pre_0_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "(sublist [(x, 1), (x, 0)] Cy1) \<or> sublist [(x, 2), (x, 0)] Cy1 \<or> (\<exists>z. sublist [(z, 2), (x, 0)] Cy1 \<and> (z, x) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1 by auto
  have "(x, 0) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [y, (x, 0)] Cy1"  
    using 0 hd_last_Cy1 assms 
    by (meson List_Auxiliaries.b_in_Cycle_exists_sublist) 
  then obtain y where y_def: "sublist [y, (x, 0)] Cy1"
    by blast
  then show ?thesis using pre_0_edge assms by blast 
qed


lemma post_2_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "(sublist [(x, 2), (x, 0)] Cy1) \<or> sublist [(x, 2), (x, 1)] Cy1 \<or> (\<exists>z. sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1 by auto
  have "(x, 2) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [(x, 2), y] Cy1"  
    using 0 hd_last_Cy1 assms 
    by (meson List_Auxiliaries.a_in_Cycle_exists_sublist) 
  then obtain y where y_def: "sublist [(x, 2), y] Cy1"
    by blast
  then show ?thesis using post_2_edge assms by blast
qed


lemma post_0_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "(sublist [(x, 0), (x, 2)] Cy1) \<or> sublist [(x, 0), (x, 1)] Cy1 \<or> (\<exists>z. sublist [(x, 0), (z, 2)] Cy1 \<and> (z, x) \<in> arcs G)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1 by auto
  have "(x, 0) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [(x, 0), y] Cy1"  
    using 0 hd_last_Cy1 assms 
    by (meson List_Auxiliaries.a_in_Cycle_exists_sublist) 
  then obtain y where y_def: "sublist [(x, 0), y] Cy1"
    by blast
  then show ?thesis using post_0_edge assms by blast 
qed


lemma post_1_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "(sublist [(x, 1), (x, 2)] Cy1) \<or> sublist [(x, 1), (x, 0)] Cy1"
proof -
  have 0: "length Cy1 \<ge> 2"
    using assms length_Cy1 by auto
  have "(x, 1) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1 by simp
  then have "\<exists>y. sublist [(x, 1), y] Cy1"  
    using 0 hd_last_Cy1 assms 
    by (meson List_Auxiliaries.a_in_Cycle_exists_sublist) 
  then obtain y where y_def: "sublist [(x, 1), y] Cy1"
    by blast
  then show ?thesis using post_1_edge assms by blast 
qed






lemma in_hc:
  shows "G \<in> hc"
  sorry

end

end