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
"to_cycle_hc ((a, b)#vs) = (if b = 1 then a#(to_cycle_hc vs) else to_cycle_hc vs)" |
"to_cycle_hc [] = []"


context
  fixes G assumes in_uhc: "hc_to_uhc G \<in> uhc"
  assumes verts_G: "card (verts G) > 1" 
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
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e},
      tail = fst, head = snd\<rparr>"
  using G_properties G'_def verts_G by(auto simp add: hc_to_uhc_def) 


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
  shows "card (verts G') > 1" 
  by (metis (no_types, hide_lams) G'_properties(2) verts_G card_greater_1_contains_two_elements contains_two_card_greater_1 prod.inject verts_G_G'(2)) 


lemma hd_last_Cy1: 
  shows "hd Cy1 = last Cy1" 
  using verts_G card_verts_G_G' Cy1_def hd_last_C_G' by blast 


lemma distinct_tl_Cy1: 
  shows "distinct (tl Cy1)"
  using verts_G Cy1_def card_verts_G_G' is_uhc_def leD by blast 


lemma x_inG_x_i_in_Cy1: 
  assumes "x \<in> verts G" 
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
  shows "length Cy1 \<ge> 2" "length Cy1 > 1"
  proof -
  have 0: "card (verts G') > 1" 
    using verts_G card_verts_G_G' by auto
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
  assumes "sublist [a, b] Cy1" 
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
  assumes "sublist [y, (x, 1)] Cy1" 
  shows "y = (x, 0) \<or> y = (x, 2)" 
proof -
  have "(y, (x, 1)) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by simp
  then show ?thesis using G'_def_3 by(auto) 
qed


lemma pre_0_edges_helper: 
  assumes "((x, 2), (y, 0)) \<in> arcs G'" "card (verts G) > 1"
  shows "(x, y) \<in> arcs G" 
  using assms G_properties G'_def_3 by(auto)



lemma pre_0_edge: 
  assumes "sublist [y, (x, 0)] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> (\<exists>z. y = (z, 2) \<and> (z, x) \<in> arcs G)"
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
      then have "(a, x) \<in> arcs G" 
        using pre_0_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma pre_2_edges_helper: 
  assumes "((x, 0), (y, 2)) \<in> arcs G'" "card (verts G) > 1"
  shows "(y, x) \<in> arcs G" 
  using assms G_properties G'_def_3 by(auto)



lemma pre_2_edge: 
  assumes "sublist [y, (x, 2)] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> (\<exists>z. y = (z, 0) \<and> (x, z) \<in> arcs G)"
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
      then have "(x, a) \<in> arcs G" 
        using pre_2_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma post_0_edge: 
  assumes "sublist [(x, 0), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or>(\<exists>z. y = (z, 2) \<and> (z, x) \<in> arcs G)"
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
      then have "(a, x) \<in> arcs G" 
        using pre_2_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma post_2_edge: 
  assumes "sublist [(x, 2), y] Cy1" "card (verts G) > 1"
  shows "y = (x, 1) \<or> (\<exists>z. y = (z, 0) \<and> (x, z) \<in> arcs G)"
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
      then have "(x, a) \<in> arcs G" 
        using pre_0_edges_helper assms by blast 
      then show ?thesis using ab_def 3 by(auto)  
    qed
  qed
qed


lemma post_1_edge: 
  assumes "sublist [(x, 1), y] Cy1"
  shows "y = (x, 0) \<or> y = (x, 2)" 
proof -
  have "((x, 1), y) \<in> arcs G'"
    using assms sublist_Cy1_arcs_G' by simp
  then show ?thesis using G'_def_3 by(auto) 
qed



lemma pre_1_cycle: 
  assumes "x \<in> verts G"
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
  shows "sublist [(x, 1), (x, 2)] Cy1 \<or> (\<exists>z. sublist [(z, 0), (x, 2)] Cy1 \<and> (x, z) \<in> arcs G)"
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
  shows "(sublist [(x, 1), (x, 0)] Cy1) \<or> (\<exists>z. sublist [(z, 2), (x, 0)] Cy1 \<and> (z, x) \<in> arcs G)"
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
  assumes "x \<in> verts G"
  shows "sublist [(x, 2), (x, 1)] Cy1 \<or> (\<exists>z. sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G)"
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
  then show ?thesis using post_2_edge assms verts_G by blast
qed


lemma post_0_cycle: 
  assumes "x \<in> verts G" "card (verts G) > 1" 
  shows "sublist [(x, 0), (x, 1)] Cy1 \<or> (\<exists>z. sublist [(x, 0), (z, 2)] Cy1 \<and> (z, x) \<in> arcs G)"
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
  assumes "x \<in> verts G"
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



lemma sublist_Cy1_for_x: 
  assumes "x \<in> verts G" 
  shows "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
         (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
proof -
  have 0: "length Cy1 \<ge> 2"
    using length_Cy1 by auto
  have inCy1: "(x, 1) \<in> set Cy1" "(x, 2) \<in> set Cy1" "(x, 0) \<in> set Cy1"
    using assms x_inG_x_i_in_Cy1 by auto 
  then have 1: "sublist [(x, 0), (x, 1)] Cy1 \<or> sublist [(x, 2), (x, 1)] Cy1" 
    using 0 hd_last_Cy1 assms pre_1_cycle verts_G by blast
  have 2: "sublist [(x, 1), (x, 2)] Cy1 \<or> sublist [(x, 1), (x, 0)] Cy1" 
    using 0 assms post_1_cycle by simp
  show ?thesis proof(cases "sublist [(x, 0), (x, 1)] Cy1")
    case True
    then have s1: "sublist [(x, 0), (x, 1)] Cy1"
      by auto
    then show ?thesis proof(cases "sublist [(x, 1), (x, 0)] Cy1")
      case True
      then have "Cy1 = [(x, 0), (x, 1), (x, 0)] \<or> Cy1 = [(x, 1), (x, 0), (x, 1)]" 
        using distinct_tl_cyclic_sublist_cs_explisit s1 hd_last_Cy1 distinct_tl_Cy1 
        by (simp add: distinct_tl_cyclic_sublist_cs_explisit) 
      then have "(x, 2) \<in> set [(x, (0::nat)), (x, 1), (x, 0)] \<or> (x, 2) \<in> set [(x, (1::nat)), (x, 0), (x, 1)]"
        using assms inCy1 
        by fastforce  
      then show ?thesis by(auto)
    next
      case False
      then have "sublist [(x, 1), (x, 2)] Cy1" 
        using 2 by auto
      then show ?thesis using True by auto
    qed
  next
    case False
    then have 3: "sublist [(x, 2), (x, 1)] Cy1" 
      using 1 by simp
    then show ?thesis proof(cases "sublist [(x, 1), (x, 0)] Cy1")
      case True
      then show ?thesis using 3 by simp
    next
      case False
      then have "sublist [(x, 1), (x, 2)] Cy1" 
        using 2 by auto
      then have "Cy1 = [(x, 2), (x, 1), (x, 2)] \<or> Cy1 = [(x, 1), (x, 2), (x, 1)]" 
        using distinct_tl_cyclic_sublist_cs_explisit 3 hd_last_Cy1 distinct_tl_Cy1 
        by (simp add: distinct_tl_cyclic_sublist_cs_explisit) 
      then have "(x, 0) \<in> set [(x, (2::nat)), (x, 1), (x, 2)] \<or> (x, 0) \<in> set [(x, (1::nat)), (x, 2), (x, 1)]"
        using assms inCy1 
        by fastforce  
      then show ?thesis by(auto)
    qed
  qed
qed


lemma x_1_in_C_x_in_to_cycle_hc: 
  assumes "(x, 1) \<in> set C"
  shows "x \<in> set (to_cycle_hc C)"
  using assms apply(induction C)by(auto)


lemma v_in_set_to_cycle_hc_Cy1: 
  assumes "v \<in> verts G"
  shows "v \<in> set (to_cycle_hc Cy1)"
proof -
  have "(v, 1) \<in> set Cy1" 
    using assms x_inG_x_i_in_Cy1(2) by auto 
  then show ?thesis 
    using x_1_in_C_x_in_to_cycle_hc by metis 
qed


lemma v_in_set_to_cycle_hc_Cy2: 
  assumes "v \<in> verts G"
  shows "v \<in> set (to_cycle_hc Cy2)"
  using assms Cy2_def v_in_set_to_cycle_hc_Cy1 
  using G'_def HC_To_UHC_2.v_in_set_to_cycle_hc_Cy1 local.in_uhc uhc_Cy2 verts_G by fastforce 


lemma hd_to_cycle_hc_if_x_1_hd_C:
  assumes "hd C = (x, 1)" "C \<noteq> []"
  shows "to_cycle_hc C = x # (to_cycle_hc (tl C))"
  using assms apply(induction C) by(auto)


lemma x_not_hd_C1_x_not_hd_Cy1: 
  assumes "x \<noteq> hd C1" "Cy1 \<noteq> []"
  shows "(x, 1) \<noteq> hd Cy1" 
proof (rule ccontr)
  assume "\<not> (x, 1) \<noteq> hd Cy1"
  then have "(x, 1) = hd Cy1" 
    by simp
  then have "to_cycle_hc Cy1 = x # (to_cycle_hc (tl Cy1))"
    using assms hd_to_cycle_hc_if_x_1_hd_C by metis
  then have "x = hd C1" using C1_def by simp
  then show False using assms by simp
qed


lemma longer_sublists_Cy1: 
  assumes "x \<in> verts G" "x \<noteq> hd C1" 
  shows "sublist [(x, 0), (x, 1), (x, 2)] Cy1 \<or> sublist [(x, 2), (x, 1), (x, 0)] Cy1" 
proof -
  have 1: "(sublist [(x, (1::nat)), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
         (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms sublist_Cy1_for_x by(auto)
  have 2: "(x, 1) \<noteq> hd Cy1"
    using assms length_Cy1(2) x_not_hd_C1_x_not_hd_Cy1 by fastforce 
  then show ?thesis proof(cases "(sublist [(x, (1::nat)), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)")
    case True
    then have "sublist [(x, 0), (x, 1), (x, 2)] Cy1"
      using sublist_ab_bc_b_not_head 2 distinct_tl_Cy1 by metis
    then show ?thesis by simp
  next
    case False
    then have "(sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
      using 1 by auto
    then have "sublist [(x, 2), (x, 1), (x, 0)] Cy1"
      using sublist_ab_bc_b_not_head 2 distinct_tl_Cy1 by metis
    then show ?thesis by auto
  qed
qed


lemma x_in_verts_x_in_C1: 
  assumes "x \<in> verts G"
  shows "x \<in> set C1" 
  using assms 
  by (simp add: C1_def v_in_set_to_cycle_hc_Cy1) 


lemma in_to_cycle_hc_in_C: 
  assumes "x \<in> set (to_cycle_hc C)"
  shows "(x, (1::nat))\<in> set C" 
  using assms apply(induction C) by(auto split: if_split_asm)


lemma in_Cy1_in_verts_G': 
  assumes "x \<in> set Cy1"
  shows "x \<in> verts G'"
proof -
  have "is_uhc G' Cy1"
    using Cy1_def by auto
  then have "set Cy1 \<subseteq> verts G'"
    using is_uhc_def by fast
  then show ?thesis using assms by auto
qed


lemma x_in_C1_in_verts_G: 
  assumes "x \<in> set C1"
  shows "x \<in> verts G" 
  using assms proof -
  have "(x, 1) \<in> set Cy1"
    using C1_def assms in_to_cycle_hc_in_C  
    by fastforce
  then have "(x, 1) \<in> verts G'"
    using in_Cy1_in_verts_G' by simp
  then show ?thesis using G'_def_3 by simp
qed


lemma b_1_not_in_C_not_in_cycle_hc: 
  assumes "(b, 1) \<notin> set C"
  shows "b \<notin> set (to_cycle_hc C)"
  using assms apply(induction C) by(auto split: if_split_asm)


lemma distinct_C_distinct_to_cycle_hc_C: 
  assumes "distinct (C)" 
  shows "distinct (to_cycle_hc C)" 
  using assms proof(induction C)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  then obtain b c where bc_def: "a = (b,c)"
    by (meson surj_pair) 
  then have 1: "(b, c) \<notin> set C"
    using Cons by simp
  then show ?case proof(cases "c= 1")
    case True
    then have "(b, 1) \<notin> set C"
      using "1" by auto 
    then have "b \<notin> set (to_cycle_hc C)"
      using b_1_not_in_C_not_in_cycle_hc Cons by fast
    then show ?thesis using Cons 
      by (simp add: bc_def) 
  next
    case False
    then have "to_cycle_hc (a#C)= to_cycle_hc C"
      using bc_def by simp 
    then show ?thesis using Cons by auto
  qed 
qed


lemma last_a_1_last_to_cycle_hc: 
  assumes "last C = (a, 1)" "C \<noteq> []"
  shows "last (to_cycle_hc C) = a" 
  using assms proof(induction C)
  case Nil
  then show ?case by auto
next
  case (Cons c C)
  then have "(a, 1) \<in> set (c#C)" 
    by (metis last_in_set) 
  then have "a \<in> set (to_cycle_hc (c#C))"
    by (simp add: x_1_in_C_x_in_to_cycle_hc) 
  then have "to_cycle_hc (c#C) \<noteq> []" 
    using list.set_cases by auto 
  then show ?case proof(cases "C = []")
    case True
    then have "c = (a, 1)"
      using Cons by simp
    then show ?thesis 
      by (simp add: True) 
  next
    case False
    then have "last (c#C) = last (C)" 
      by simp
    then have 1: "last (to_cycle_hc (C)) = a" 
      using Cons False by auto
    have "(a, 1) \<in> set C" 
      using Cons.prems(1) False last_in_set by force
    then have "to_cycle_hc C \<noteq> []" 
      by (metis list.distinct(1) list.set_cases x_1_in_C_x_in_to_cycle_hc) 
    then have "last (to_cycle_hc (c#C)) = last (to_cycle_hc C)" 
      by (metis \<open>last (to_cycle_hc C) = a\<close> last.simps last_ConsR surj_pair to_cycle_hc.simps(1)) 
    then show ?thesis using 1 by simp 
  qed
qed 


lemma distinct_C1: 
  shows "distinct (tl C1) \<and> hd C1 = last C1 \<or> distinct C1" 
proof -
  have 1: "distinct (to_cycle_hc (tl Cy1))" 
    using distinct_C_distinct_to_cycle_hc_C distinct_tl_Cy1 by auto 
  obtain a b where ab_def: "hd Cy1 = (a, b)" 
    by (meson surj_pair) 
  then show ?thesis proof(cases "b = 1")
    case True
    then have "last Cy1 = (a, 1)" 
      using hd_last_Cy1 ab_def by auto 
    then have 2: "last C1 = a"
      using last_a_1_last_to_cycle_hc 
      using C1_def length_Cy1(2) by fastforce 
    have "Cy1 \<noteq> []" 
      using length_C_vwalk_arcs_not_empty length_Cy1(2) vwalk_arcs.simps(1) by blast 
    then have "to_cycle_hc Cy1 = a # (to_cycle_hc (tl Cy1))"
      using ab_def True
      by (simp add: hd_to_cycle_hc_if_x_1_hd_C) 
    then have "hd C1 = last C1" "distinct (tl C1)" 
      using 1 2 C1_def by auto
    then show ?thesis by simp
  next
    case False
    then have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)"
      using ab_def 
      by (metis Pair_inject length_Cy1(2) list.sel(1) list.sel(3) list.size(3) not_one_less_zero to_cycle_hc.elims) 
    then show ?thesis using 1 C1_def by auto
  qed
qed


lemma in_cy1_in_verts_G: 
  assumes "(x, i) \<in> set Cy1"
  shows "x \<in> verts G"
proof -
  have "(x, i) \<in> verts G'" 
    by (simp add: assms in_Cy1_in_verts_G') 
  then show ?thesis using G'_def_3 by auto
qed


lemma sublist_x_y_z_to_cycle_hc: 
  assumes "sublist [x, y] (to_cycle_hc C)" "sublist [x, z] (to_cycle_hc C)" 
"distinct (tl (to_cycle_hc C)) \<and> hd (to_cycle_hc C) = last (to_cycle_hc C) \<or> distinct (to_cycle_hc C)" 
  shows "y = z" 
proof(cases "distinct (to_cycle_hc C)")
  case True
  then show ?thesis using assms 
    by (meson distinct_C_distinct_to_cycle_hc_C two_sublist_distinct_same_last) 
next
  case False
  then have "distinct (tl (to_cycle_hc C)) \<and> hd (to_cycle_hc C) = last (to_cycle_hc C)" 
    using assms by auto
  then show ?thesis using assms 
    by (meson two_sublist_same_first_distinct_tl) 
qed


lemma distinct_tl_c_to_cycle_hc: 
  assumes "distinct (tl C)" "to_cycle_hc C = to_cycle_hc (tl C)"
  shows "distinct (to_cycle_hc C)"
  using assms 
  by (simp add: distinct_C_distinct_to_cycle_hc_C) 


lemma hd_C_not_eq_1_equal_tl: 
  assumes "hd C = (a, b)" "b \<noteq> 1" "C \<noteq> []"
  shows "to_cycle_hc C = to_cycle_hc (tl C)" 
  using assms 
  by (metis list.collapse to_cycle_hc.simps(1)) 


lemma sublist_2_0_in_C1_helper: 
  assumes "sublist [(x, (1::nat)), (x, 2), (y, 0), (y, 1)] C" 
  shows "sublist [x, y] (to_cycle_hc C)"
  using assms proof(induction C)
  case Nil
  then show ?case by (simp add: sublist_def)
next
  case (Cons a C)
  then have 1: "a = (x, 1) \<or> sublist [(x, 1), (x, 2), (y, 0), (y, 1)] C" 
    using sublist_cons_impl_sublist_list by force 
  have "\<exists>p1 p2. p1 @ [(x, 1), (x, 2), (y, 0), (y, 1)]@ p2 = (a#C)" 
    using sublist_def Cons by blast
  then obtain p1 p2 where p_def: "p1 @ [(x, 1), (x, 2), (y, 0), (y, 1)]@ p2 = (a#C)" 
    by auto
  then show ?case proof(cases "p1 \<noteq> []" )
    case True
    then have "tl p1 @ [(x, 1), (x, 2), (y, 0), (y, 1)]@ p2 = (C)"
      using p_def 
      by (metis list.sel(3) tl_append2) 
    then have "sublist [(x, 1), (x, 2), (y, 0), (y, 1)] C"
      using sublist_def by blast 
    then have "sublist [x, y] (to_cycle_hc C)"
      using Cons by auto
    then show ?thesis 
      by (metis sublist_cons surj_pair to_cycle_hc.simps(1))  
  next
    case False
    then have 2: "p1 = []" by simp
    then have "(x, 1) = a"
      using 1 p_def by simp
    then have "[(x, 1), (x, 2), (y, 0), (y, 1)] @ p2 = (a#C)" 
      using 2 p_def by simp 
    then have "to_cycle_hc (a#C) = x # to_cycle_hc ([(x, (2::nat)), (y, 0), (y, 1)] @ p2)" 
      by fastforce
    then have "... = x # to_cycle_hc ([(y, 0), (y, 1)] @ p2)"
      by(auto) 
    then have "... = x # to_cycle_hc ([(y, 1)] @ p2)"
      by simp
    then have "... = x # y # to_cycle_hc p2"
      by auto
    then have "to_cycle_hc (a#C) = x # y # to_cycle_hc p2"
      by (simp add: \<open>to_cycle_hc (a # C) = x # to_cycle_hc ([(x, 2), (y, 0), (y, 1)] @ p2)\<close>) 
    then have "to_cycle_hc (a#C) = [] @ [x, y] @ (to_cycle_hc p2)" 
      by simp
    then show ?thesis using sublist_def 
      by metis  
  qed
qed 


lemma sublist_2_0_in_C1_helper_2: 
  assumes "sublist [(x, (1::nat)), (x, 0), (y, 2), (y, 1)] C" 
  shows "sublist [x, y] (to_cycle_hc C)"
  using assms proof(induction C)
  case Nil
  then show ?case by (simp add: sublist_def)
next
  case (Cons a C)
  then have 1: "a = (x, 1) \<or> sublist [(x, 1), (x, 0), (y, 2), (y, 1)] C" 
    using sublist_cons_impl_sublist_list by force 
  have "\<exists>p1 p2. p1 @ [(x, 1), (x, 0), (y, 2), (y, 1)]@ p2 = (a#C)" 
    using sublist_def Cons by blast
  then obtain p1 p2 where p_def: "p1 @ [(x, 1), (x, 0), (y, 2), (y, 1)]@ p2 = (a#C)" 
    by auto
  then show ?case proof(cases "p1 \<noteq> []" )
    case True
    then have "tl p1 @ [(x, 1), (x, 0), (y, 2), (y, 1)]@ p2 = (C)"
      using p_def 
      by (metis list.sel(3) tl_append2) 
    then have "sublist [(x, 1), (x, 0), (y, 2), (y, 1)] C"
      using sublist_def by blast 
    then have "sublist [x, y] (to_cycle_hc C)"
      using Cons by auto
    then show ?thesis 
      by (metis sublist_cons surj_pair to_cycle_hc.simps(1))  
  next
    case False
    then have 2: "p1 = []" by simp
    then have "(x, 1) = a"
      using 1 p_def by simp
    then have "[(x, 1), (x, 0), (y, 2), (y, 1)] @ p2 = (a#C)" 
      using 2 p_def by simp 
    then have "to_cycle_hc (a#C) = x # to_cycle_hc ([(x, (0::nat)), (y, 2), (y, 1)] @ p2)" 
      by fastforce
    then have "... = x # to_cycle_hc ([(y, 2), (y, 1)] @ p2)"
      by(auto) 
    then have "... = x # to_cycle_hc ([(y, 1)] @ p2)"
      by simp
    then have "... = x # y # to_cycle_hc p2"
      by auto
    then have "to_cycle_hc (a#C) = x # y # to_cycle_hc p2"
      by (simp add: \<open>to_cycle_hc (a # C) = x # to_cycle_hc ([(x, 0), (y, 2), (y, 1)] @ p2)\<close>) 
    then have "to_cycle_hc (a#C) = [] @ [x, y] @ (to_cycle_hc p2)" 
      by simp
    then show ?thesis using sublist_def 
      by metis  
  qed
qed 


lemma sublist_2_0_in_C1: 
  assumes "sublist [(x, 2), (y, 0)] Cy1"
  shows "sublist [x, y] C1 \<or> y = hd C1"
proof -
  have "(x, 2) \<in> set Cy1"
    using assms 
    by (meson in_sublist_impl_in_list list.set_intros(1)) 
  then have "x \<in> verts G" 
    using assms in_cy1_in_verts_G  by simp  
  then have 1: "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms sublist_Cy1_for_x by simp 
  have "\<not> (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)" 
    using distinct_tl_Cy1 hd_last_Cy1 
    using assms two_sublist_same_first_distinct_tl by fastforce 
  then have sx: "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)" 
    using 1 by auto

  have "(y, 0) \<in> set Cy1"
    using assms 
    by (meson in_sublist_impl_in_list list.set_intros) 
  then have "y \<in> verts G" 
    using assms in_cy1_in_verts_G  by simp  
  then have 1: "(sublist [(y, 1), (y, 2)] Cy1 \<and> sublist [(y, 0), (y, 1)] Cy1) \<or> 
      (sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)"
    using assms sublist_Cy1_for_x by simp 
  have "\<not> (sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)" 
    using distinct_tl_Cy1 hd_last_Cy1 
    using assms 
    using two_sublist_distinct_same_first by fastforce 
  then have sy: "(sublist [(y, 1), (y, 2)] Cy1 \<and> sublist [(y, 0), (y, 1)] Cy1)" 
    using 1 by auto
  then have s1: "sublist [(x, 2), (y, 0), (y, 1)] Cy1 \<or> hd Cy1 = (y, 0)"
    using assms 
    using distinct_tl_Cy1 sublist_ab_bc_b_not_head by fastforce 
  then show ?thesis proof 
    assume a1: "sublist [(x, 2), (y, 0), (y, 1)] Cy1"
    then have "sublist [(x, 1), (x, 2), (y, 0), (y, 1)] Cy1 \<or> hd Cy1 = (x, 2)"
      using distinct_tl_Cy1 sublist_ab_bcs_b_not_head sx by metis
    then show ?thesis proof 
      assume a2: "sublist [(x, 1), (x, 2), (y, 0), (y, 1)] Cy1"
      then show ?thesis using sublist_2_0_in_C1_helper C1_def by fast
    next
      have tltlCy1: "tl (tl Cy1) \<noteq> []" 
        using a1 
        by (metis C1_def Nil_tl \<open>(y, 0) \<in> set Cy1\<close> \<open>x \<in> verts G\<close> distinct.simps(2) distinct_length_2_or_more distinct_singleton hd_Cons_tl hd_last_Cy1 last_ConsL last_tl length_0_conv length_Cy1(1) length_geq_2_tt_not_empty list.distinct(1) set_ConsD to_cycle_hc.simps(1) to_cycle_hc.simps(2) x_in_verts_x_in_C1 zero_neq_one) 
      assume a2: "hd Cy1 = (x, 2)" 
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)" 
        using a1 distinct_tl_Cy1 hd_C_not_eq_1_equal_tl 
        by fastforce 
      then have "hd (tl Cy1) = (y, 0)" 
        using a1 a2 assms distinct_tl_Cy1 hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl by force 
      then have "to_cycle_hc (tl Cy1) = to_cycle_hc (tl (tl Cy1))"
        using hd_C_not_eq_1_equal_tl 
        by (metis list.sel(2) zero_neq_one) 
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))"
        by (simp add: \<open>to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)\<close>) 
      have "hd (tl (tl Cy1)) = (y, 1)" 
        using a2 a1 distinct_tl_Cy1 sublist_hd_tl_equal_b_hd_tl_2 hd_last_Cy1 by fastforce 
      then have "hd (to_cycle_hc (tl (tl Cy1))) = y"
        using hd_to_cycle_hc_if_x_1_hd_C tltlCy1 
        by fastforce  
      then show ?thesis 
        by (simp add: C1_def \<open>to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))\<close>) 
    qed
  next
    assume a1: "hd Cy1 = (y, 0)"
    then have "hd (tl Cy1) = (y, 1)"
      using distinct_tl_Cy1 sy 
      using hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl by force 
    have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)" 
      using a1 distinct_tl_Cy1 
      by (metis hd_Cons_tl less_irrefl_nat less_one list.sel(2) to_cycle_hc.simps(1)) 
    then have "hd (to_cycle_hc Cy1) = y"
      by (metis C1_def \<open>hd (tl Cy1) = (y, 1)\<close> \<open>x \<in> verts G\<close> distinct.simps(2) distinct_singleton hd_to_cycle_hc_if_x_1_hd_C list.distinct(1) list.sel(1) to_cycle_hc.elims x_in_verts_x_in_C1) 
    then show ?thesis 
      using C1_def by simp
  qed
qed


lemma sublist_2_0_in_C1_2: 
  assumes "sublist [(x, 0), (y, 2)] Cy1"
  shows "sublist [x, y] C1 \<or> y = hd C1"
proof -
  have "(x, 0) \<in> set Cy1"
    using assms 
    by (meson in_sublist_impl_in_list list.set_intros(1)) 
  then have "x \<in> verts G" 
    using assms in_cy1_in_verts_G  by simp  
  then have 1: "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using assms sublist_Cy1_for_x by simp 
  have "\<not> (sublist [(x, 2), (x, 0)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)" 
    using distinct_tl_Cy1 hd_last_Cy1 
    using assms two_sublist_same_first_distinct_tl by fastforce 
  then have sx: "(sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)" 
    using 1 
    by (metis Pair_inject assms distinct_tl_Cy1 hd_last_Cy1 two_sublist_distinct_same_first two_sublist_same_first_distinct_tl) 

  have "(y, 2) \<in> set Cy1"
    using assms 
    by (meson in_sublist_impl_in_list list.set_intros) 
  then have "y \<in> verts G" 
    using assms in_cy1_in_verts_G  by simp  
  then have 1: "(sublist [(y, 1), (y, 2)] Cy1 \<and> sublist [(y, 0), (y, 1)] Cy1) \<or> 
      (sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)"
    using assms sublist_Cy1_for_x by simp 
  have "\<not> (sublist [(y, 0), (y, 1)] Cy1 \<and> sublist [(y, 1), (y, 2)] Cy1)" 
    using distinct_tl_Cy1 hd_last_Cy1 
    using assms 
    using two_sublist_distinct_same_first 
    by fastforce  
  then have sy: "(sublist [(y, 1), (y, 0)] Cy1 \<and> sublist [(y, 2), (y, 1)] Cy1)" 
    using 1 by auto
  then have s1: "sublist [(x, 0), (y, 2), (y, 1)] Cy1 \<or> hd Cy1 = (y, 2)"
    using assms 
    using distinct_tl_Cy1 sublist_ab_bc_b_not_head by fastforce 
  then show ?thesis proof 
    assume a1: "sublist [(x, 0), (y, 2), (y, 1)] Cy1"
    then have "sublist [(x, 1), (x, 0), (y, 2), (y, 1)] Cy1 \<or> hd Cy1 = (x, 0)"
      using distinct_tl_Cy1 sublist_ab_bcs_b_not_head sx by metis
    then show ?thesis proof 
      assume a2: "sublist [(x, 1), (x, 0), (y, 2), (y, 1)] Cy1"
      then show ?thesis using sublist_2_0_in_C1_helper_2 C1_def by fast
    next
      have tltlCy1: "tl (tl Cy1) \<noteq> []" 
        using a1 
        by (metis \<open>(x, 0) \<in> set Cy1\<close> assms distinct.simps(2) distinct_singleton hd_Cons_tl hd_last_Cy1 last_ConsL last_tl length_Cy1(1) length_geq_2_tt_not_empty old.prod.inject set_ConsD sublist_hd_tl_equal_b_hd_tl zero_neq_numeral) 
      assume a2: "hd Cy1 = (x, 0)" 
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)" 
        using a1 distinct_tl_Cy1 hd_C_not_eq_1_equal_tl 
        by (metis less_numeral_extra(1) less_numeral_extra(3) list.sel(2)) 
      then have "hd (tl Cy1) = (y, 2)" 
        using a1 a2 assms distinct_tl_Cy1 hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl by force 
      then have "to_cycle_hc (tl Cy1) = to_cycle_hc (tl (tl Cy1))"
        using hd_C_not_eq_1_equal_tl 
        by fastforce 
      then have "to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))"
        by (simp add: \<open>to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)\<close>) 
      have "hd (tl (tl Cy1)) = (y, 1)" 
        using a2 a1 distinct_tl_Cy1 sublist_hd_tl_equal_b_hd_tl_2 hd_last_Cy1 by fastforce 
      then have "hd (to_cycle_hc (tl (tl Cy1))) = y"
        using hd_to_cycle_hc_if_x_1_hd_C tltlCy1 
        by fastforce  
      then show ?thesis 
        by (simp add: C1_def \<open>to_cycle_hc Cy1 = to_cycle_hc (tl (tl Cy1))\<close>) 
    qed
  next
    assume a1: "hd Cy1 = (y, 2)"
    then have "hd (tl Cy1) = (y, 1)"
      using distinct_tl_Cy1 sy 
      using hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl by force 
    have "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)" 
      using a1 distinct_tl_Cy1 
      using hd_C_not_eq_1_equal_tl by fastforce 
    then have "hd (to_cycle_hc Cy1) = y"
      by (metis C1_def \<open>hd (tl Cy1) = (y, 1)\<close> \<open>x \<in> verts G\<close> distinct.simps(2) distinct_singleton hd_to_cycle_hc_if_x_1_hd_C list.distinct(1) list.sel(1) to_cycle_hc.elims x_in_verts_x_in_C1) 
    then show ?thesis 
      using C1_def by simp
  qed
qed


  (*have "\<not> hd Cy1 = (y, 0)" proof(rule ccontr)
    assume a1: "\<not> \<not> hd Cy1 = (y, 0)"
    then have b1: "to_cycle_hc Cy1 = to_cycle_hc (tl Cy1)" 
      by (metis list.sel(1) list.sel(2) list.sel(3) prod.inject to_cycle_hc.elims zero_neq_one)
    then have dCy1: "distinct (to_cycle_hc Cy1)"
      using distinct_tl_Cy1 distinct_tl_c_to_cycle_hc by blast 
    have "hd (tl Cy1) = (y, 1)" 
      using a1 sy 
      using distinct_tl_Cy1 hd_last_Cy1 sublist_hd_tl_equal_b_hd_tl by fastforce 
    then have "hd C1 = y" 
      using C1_def b1  apply(auto) 
      by (metis Nitpick.size_list_simp(2) One_nat_def \<open>(y, 0) \<in> set Cy1\<close> \<open>hd (tl Cy1) = (y, 1)\<close> a1 hd_last_Cy1 length_0_conv length_Cy1(2) less_irrefl_nat list.exhaust_sel list.sel(1) list.sel(3) list.set_cases neq_Nil_conv to_cycle_hc.elims to_cycle_hc.simps(1)) 
    then have "False" using sy  
(*Ziel: von (x, 1) auf (x,2) auf (y, 0) auf (y, 1). Falls
dieser Pfad so nicht vorhanden ist, so ist x der letzte in C1*)
  then show ?thesis sorry
qed*)


lemma sublist_predecessor_helper: 
  assumes "sublist [(x, 2), (z, 0)] Cy1" "z = hd C1"
  shows "z = last C1 \<and> sublist [x, y] C1 \<or> x = last C1"
  sorry

lemma sublist_predecessor_helper_2: 
  assumes "sublist [(x, 0), (z, 2)] Cy1" "z = hd C1"
  shows "z = last C1 \<and> sublist [x, y] C1 \<or> x = last C1"
  sorry


lemma sublists_x_z_noteq: 
  assumes "sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1" "sublist [(x, 2), (z, 0)] Cy1"
  shows "x \<noteq> z" 
  using distinct_tl_Cy1 sorry 


lemma sublists_x_z_noteq_2: 
  assumes "sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1" "sublist [(x, 0), (z, 2)] Cy1"
  shows "x \<noteq> z" 
  using distinct_tl_Cy1 sorry 


lemma sublist_predecessor: 
  assumes "sublist [x, y] C1" "sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1"
  shows "sublist [(x, 2), (y, 0)] Cy1 \<or> sublist [(x, 0), (y, 2)] Cy1"
proof(rule ccontr)
  assume a1: "\<not> (sublist [(x, 2), (y, 0)] Cy1 \<or> sublist [(x, 0), (y, 2)] Cy1)"
  have in_Cy1: "(x, 1) \<in> set Cy1" "(y, 1) \<in> set Cy1" 
    using assms 
    by (metis C1_def in_set_vwalk_arcsE in_to_cycle_hc_in_C sublist_imp_in_arcs)+
  then have "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using List_Auxiliaries.a_in_Cycle_exists_sublist hd_last_Cy1 length_Cy1(1) post_1_edge  
    using C1_def sublist_Cy1_for_x x_1_in_C_x_in_to_cycle_hc x_in_C1_in_verts_G by fastforce
  then have "\<not> sublist [(x, 2), (x, 1)] Cy1" 
    using distinct_tl_Cy1 hd_last_Cy1 assms
    by (metis Pair_inject less_numeral_extra(3) pos2 two_sublist_distinct_same_first) 
  then have "(\<exists>z. sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G)"
    by (metis Cy1_def G'_def HC_To_UHC_2.x_in_C1_in_verts_G in_Cy1(1) local.in_uhc post_2_cycle verts_G x_1_in_C_x_in_to_cycle_hc) 
  then obtain z where z_def: "sublist [(x, 2), (z, 0)] Cy1 \<and> (x, z) \<in> arcs G"
    by auto
  then have zy: "z \<noteq> y" 
    using a1 by blast
  then have sxz: "sublist [x, z] C1 \<or> z = hd C1"
    using sublist_2_0_in_C1 z_def 
    by simp 
  then have xnoteqz: "x \<noteq> z" 
    using sublists_x_z_noteq 
    using \<open>sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1\<close> sublists_x_z_noteq z_def by blast 
  then show False proof(cases "sublist [x, z] C1")
    case True
    then show ?thesis using zy 
      using C1_def assms distinct_C1 sublist_x_y_z_to_cycle_hc by fastforce
  next
    case False
    then have "z = hd C1"
      using sxz by simp
    then have "x = last C1" 
      using sublist_predecessor_helper False 
      using z_def by blast 
    then show ?thesis using assms distinct_C1 xnoteqz 
      using \<open>z = hd C1\<close> distinct_sublist_last_first_of_sublist_false by force 
  qed
qed


lemma sublist_predecessor_2: 
  assumes "sublist [x, y] C1" "sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1"
  shows "sublist [(x, 0), (y, 2)] Cy1"
proof(rule ccontr)
  assume a1: "\<not> (sublist [(x, 0), (y, 2)] Cy1)"
  have in_Cy1: "(x, 1) \<in> set Cy1" "(y, 1) \<in> set Cy1" 
    using assms 
    by (metis C1_def in_set_vwalk_arcsE in_to_cycle_hc_in_C sublist_imp_in_arcs)+
  then have "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
      (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    using List_Auxiliaries.a_in_Cycle_exists_sublist hd_last_Cy1 length_Cy1(1) post_1_edge  
    using C1_def sublist_Cy1_for_x x_1_in_C_x_in_to_cycle_hc x_in_C1_in_verts_G by fastforce
  then have "\<not> sublist [(x, 0), (x, 1)] Cy1" 
    using distinct_tl_Cy1 hd_last_Cy1 assms
    by (metis Pair_inject less_numeral_extra(3) pos2 two_sublist_distinct_same_first) 
  then have "(\<exists>z. sublist [(x, 0), (z, 2)] Cy1 \<and> (z, x) \<in> arcs G)"
    by (metis Cy1_def G'_def HC_To_UHC_2.x_in_C1_in_verts_G in_Cy1(1) local.in_uhc post_0_cycle verts_G x_1_in_C_x_in_to_cycle_hc) 
  then obtain z where z_def: "sublist [(x, 0), (z, 2)] Cy1 \<and> (z, x) \<in> arcs G"
    by auto
  then have zy: "z \<noteq> y" 
    using a1 by blast
  then have sxz: "sublist [x, z] C1 \<or> z = hd C1"
    using sublist_2_0_in_C1_2 z_def 
    by simp 
  then have xnoteqz: "x \<noteq> z" 
    using sublists_x_z_noteq 
    using \<open>sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1\<close> sublists_x_z_noteq_2 z_def by blast 
  then show False proof(cases "sublist [x, z] C1")
    case True
    then show ?thesis using zy 
      using C1_def assms distinct_C1 sublist_x_y_z_to_cycle_hc by fastforce
  next
    case False
    then have "z = hd C1"
      using sxz by simp
    then have "x = last C1" 
      using False z_def 
      using sublist_predecessor_helper_2 by blast 
    then show ?thesis using assms distinct_C1 xnoteqz 
      using \<open>z = hd C1\<close> distinct_sublist_last_first_of_sublist_false by force 
  qed
qed


lemma sublist_forall_1: 
  assumes "y = hd C1" "sublist [(y, 0), (y, 1)] Cy1" "sublist [(y, 1), (y, 2)] Cy1" "x = C1!i" "i < length C1" 
  shows "sublist [(x, 0), (x, 1)] Cy1 \<and>sublist [(x, 1), (x, 2)] Cy1"
  using assms proof(induction i arbitrary: x)
  case 0
  then have "x = hd C1"
    by (simp add: hd_conv_nth) 
  then show ?case using assms by simp
next
  case (Suc i)
  then have 1: "sublist [(C1!i, 0), (C1!i, 1)] Cy1 \<and>sublist [(C1!i, 1), (C1!i, 2)] Cy1"
    by (simp add: Suc.prems(5)) 
  have in_verts: "x \<in> verts G" 
    using x_in_C1_in_verts_G 
    by (simp add: Suc.prems(4) Suc.prems(5)) 
  have "sublist [C1!i, x] C1" 
    using Suc sublist_indixes 
    by blast  
  then have sublists_x_y: "sublist [(C1!i, 2), (x, 0)] Cy1" 
    using sublist_predecessor 
    using "1" distinct_tl_Cy1 hd_last_Cy1 two_sublist_same_first_distinct_tl by fastforce
  then have "sublist [(C1!i, 2), (x, 0)] Cy1" proof(cases "sublist [(C1!i, 2), (x, 0)] Cy1")
    case True
    then show ?thesis by simp
  next
    case False
    then have "sublist [(C1!i, 0), (x, 2)] Cy1"
      using sublists_x_y by simp
    then show ?thesis using 1 distinct_tl_Cy1 hd_last_Cy1 
      using two_sublist_same_first_distinct_tl by fastforce 
  qed
  then have "\<not> sublist [(x, 1), (x, 0)] Cy1"
    using distinct_tl_Cy1 hd_last_Cy1 
    using two_sublist_distinct_same_first by fastforce 
  then show ?case using sublist_Cy1_for_x in_verts 
    by blast 
qed


lemma sublist_forall_2: 
  assumes "y = hd C1" "sublist [(y, 2), (y, 1)] Cy1" "sublist [(y, 1), (y, 0)] Cy1" "x = C1!i" "i < length C1" 
  shows "sublist [(x, 2), (x, 1)] Cy1 \<and>sublist [(x, 1), (x, 0)] Cy1"
  using assms proof(induction i arbitrary: x)
  case 0
  then have "x = hd C1"
    by (simp add: hd_conv_nth) 
  then show ?case using assms by simp
next
  case (Suc i)
  then have 1: "sublist [(C1!i, 2), (C1!i, 1)] Cy1 \<and>sublist [(C1!i, 1), (C1!i, 0)] Cy1"
    by (simp add: Suc.prems(5)) 
  have in_verts: "x \<in> verts G" 
    using x_in_C1_in_verts_G 
    by (simp add: Suc.prems(4) Suc.prems(5)) 
  have "sublist [C1!i, x] C1" 
    using Suc sublist_indixes 
    by blast  
  then have sublists_x_y: "sublist [(C1!i, 2), (x, 0)] Cy1 \<or> sublist [(C1!i, 0), (x, 2)] Cy1" 
    using sublist_predecessor sublist_predecessor_2 1 by simp
  then have "sublist [(C1!i, 0), (x, 2)] Cy1" proof(cases "sublist [(C1!i, 0), (x, 2)] Cy1")
    case True
    then show ?thesis by simp
  next
    case False
    then have "sublist [(C1!i, 2), (x, 0)] Cy1"
      using sublists_x_y by simp
    then show ?thesis using 1 distinct_tl_Cy1 hd_last_Cy1 
      using two_sublist_same_first_distinct_tl by fastforce 
  qed
  then have "\<not> sublist [(x, 1), (x, 2)] Cy1"
    using distinct_tl_Cy1 hd_last_Cy1 
    by (meson old.prod.inject two_sublist_distinct_same_first zero_neq_one) 
  then show ?case using sublist_Cy1_for_x in_verts 
    by blast 
qed


lemma sulbist_forall:
  shows "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or>
          (\<forall>x \<in> verts G. sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
proof -
  have "Cy1 \<noteq> []"
    using length_Cy1(2) by auto 
  then have "C1 \<noteq> []" 
    using verts_G x_in_verts_x_in_C1 by fastforce 
  then obtain x where x_def: "(x) = hd (C1)"
    by simp
  then have "x \<in> verts G" 
    by (simp add: \<open>C1 \<noteq> []\<close> x_in_C1_in_verts_G) 
  then have "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1) \<or> 
         (sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)" 
    using sublist_Cy1_for_x by simp
  then show ?thesis proof
    assume "(sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    then show ?thesis using sublist_forall_1 
      by (metis x_def x_in_implies_exist_index x_in_verts_x_in_C1) 
  next
    assume "(sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
    then show ?thesis using sublist_forall_2
      by (metis x_def x_in_implies_exist_index x_in_verts_x_in_C1)
  qed
qed


lemma sublist_rev_Cy1: 
  assumes "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 0)] Cy1 \<and> sublist [(x, 2), (x, 1)] Cy1)"
  shows "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] (rev Cy1) \<and> sublist [(x, 0), (x, 1)] (rev Cy1))" 
  using assms sublist_rev apply(auto) by fastforce+ 





lemma
  assumes  "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
  shows "vwalk C1 G"
  unfolding vwalk_def apply(auto) 
  apply (simp add: x_in_C1_in_verts_G) sorry

lemma 
  assumes "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    "last C1 = hd C1" 
  shows "vwalk_cycle G C1"
  unfolding vwalk_cycle_def 
  using distinct_C1 assms apply(auto) subgoal sorry subgoal sorry 
  using distinct_tl apply auto[1] 
  sorry


lemma 
  assumes "(\<forall>x \<in> verts G. sublist [(x, 1), (x, 2)] Cy1 \<and> sublist [(x, 0), (x, 1)] Cy1)"
    "last C1 \<noteq> hd C1" 
  shows "vwalk_cycle G (last C1 # C1)"
  sorry


lemma in_hc:
  shows "G \<in> hc"
  sorry

end

end