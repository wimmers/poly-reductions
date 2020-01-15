theory HC_To_UHC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Digraph  Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    "List_Auxiliaries" "Set_Auxiliaries"
    "VC_To_HC/Definitions" "VC_To_HC/VC_To_HC"
begin

subsection\<open>Preliminaries\<close>

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_uhc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    ((pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1)\<and> set c \<subseteq> verts G \<and> distinct (tl c)"

definition
  "uhc \<equiv> {G. \<exists>c. wf_digraph G \<and> symmetric G \<and> is_uhc G c \<and>((tail G = fst \<and> head G = snd) \<or> arcs G = {})}"

(*last two edge sets are not part of the original proof, but are needed for case with only one node*)
(*I'm using the or arcs = {} to easily construct a graph that is not in uhc. If arcs are empty, 
head and tail are not important*)
definition "hc_to_uhc \<equiv>
  \<lambda>(G::('a, ('a \<times> 'a)) pre_digraph). (if wf_digraph G \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}) then 
    \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (u, 2))|u. u \<in> verts G}\<union> 
          {((u, 2), (u, 0))|u. u \<in> verts G}, 
    tail = fst, head = snd\<rparr>
    else \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>)"



lemma not_wf_digraph_not_arcs_empty: 
  assumes "\<not> wf_digraph G" 
  shows "arcs G \<noteq> {}"
proof(rule ccontr)
  assume "\<not> arcs G \<noteq> {}"
  then have "wf_digraph G"
    using wf_digraph_def by blast 
  then show False 
    using assms by simp
qed


lemma verts_empt_arcs_not_not_wf_digraph: 
  assumes "verts G = {}" "arcs G \<noteq> {}"
  shows "\<not> wf_digraph G"
  using assms wf_digraph_def 
  by fast  


lemma else_not_in_uhc_1: 
  assumes "G' = \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>" 
      "\<not> wf_digraph G"
    shows "G' \<notin> uhc"
proof -
  have vertsG': "verts G' = {}"
    using assms by auto
  have "arcs G \<noteq> {}" 
    using not_wf_digraph_not_arcs_empty assms by auto
  then have "arcs G' \<noteq> {}"
    using assms by simp
  then have "\<not> wf_digraph G'"
    using verts_empt_arcs_not_not_wf_digraph vertsG' by auto
  then show ?thesis using uhc_def by blast
qed

lemma else_not_in_uhc_2: 
  assumes "G' = \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>" 
      "\<not>((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
    shows "G' \<notin> uhc"
proof -
  have vertsG': "verts G' = {}"
    using assms by auto
  have "arcs G \<noteq> {}" 
    using assms by auto
  then have "arcs G' \<noteq> {}"
    using assms by auto
  then have "\<not> wf_digraph G'"
    using verts_empt_arcs_not_not_wf_digraph vertsG' by auto
  then show ?thesis using uhc_def by blast
qed

lemma else_not_in_uhc: 
  assumes "G' = \<lparr>verts = {}, arcs = {((head G e, 0), (head G e, 1))|e. e \<in> arcs G}, tail = fst, head = snd\<rparr>" 
      "\<not>(wf_digraph G \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}))"
    shows "G' \<notin> uhc"
  using else_not_in_uhc_1 else_not_in_uhc_2 assms by blast


subsection\<open>G \<in> hc --> hc_to_uhc G \<in> uhc\<close>

fun to_cycle_uhc::"('a, ('a \<times> 'a)) pre_digraph \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list" where
"to_cycle_uhc G [] = []" |
"to_cycle_uhc G (v#vs) = [(v, 0), (v, 1), (v, 2)] @ to_cycle_uhc G vs"

context
  fixes G assumes in_hc: "G \<in> hc"
  fixes Cycle assumes Cycle_def: "is_hc G Cycle"
  fixes G' assumes G'_def: "G' = hc_to_uhc G"
  fixes Cy assumes Cy_def: "Cy = (hd Cycle, 2) # to_cycle_uhc G (tl Cycle)"
begin

lemma G'_def_2:
  shows "G' = \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G}, 
    arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (u, 2))|u. u \<in> verts G}\<union> 
          {((u, 2), (u, 0))|u. u \<in> verts G}, 
    tail = fst, head = snd\<rparr>"
proof -
  have "wf_digraph G" "((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
    using in_hc hc_def by auto
  then show ?thesis 
    by(auto simp add:  G'_def hc_to_uhc_def)
qed


lemma wf_digraph_G:
  shows "wf_digraph G" "((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
  using in_hc hc_def by auto


lemma finite_verts_G:
  shows "finite (verts G)" 
  using in_hc hc_def by auto


lemma wf_digraph_G': 
  shows "wf_digraph G'"
  using G'_def_2 wf_digraph_def wf_digraph_G by(auto simp add: G'_def_2 wf_digraph_def)


lemma arc_to_ends_G': 
  shows "arc_to_ends G' e = e"
  using arc_to_ends_def G'_def_2
  by (simp add: arc_to_ends_def) 

lemma arcs_ends_G': 
  shows "arcs_ends G' = arcs G'"
  using arcs_ends_def arc_to_ends_G'
  by(auto simp add: arcs_ends_def arc_to_ends_G')


lemma sym_arcs_G': 
  shows "sym (arcs G')"
  unfolding G'_def_2 sym_def by(auto)   


lemma symmetric_G': 
  shows "symmetric G'"
  using symmetric_def arcs_ends_G' sym_arcs_G' by fastforce   


lemma head_tail_G': 
  shows "head G' = snd" "tail G' = fst"
  using G'_def_2 by auto 



lemma finite_subset_verts_G':
  shows "finite {(v, i) |v. v \<in> verts G}"
   using finite_verts_G by simp 


lemma distinct_tail_cycle: 
  shows "distinct (tl Cycle)" 
  using Cycle_def is_hc_def by auto


lemma finite_verts_G':
  shows "finite (verts G')" 
  using G'_def_2 finite_verts_G finite_subset_verts_G' 
  by fastforce


lemma vwalk_arcs_Cycle_subseteq_arcs_G:
  assumes "card (verts G) > 1"
  shows "set (vwalk_arcs Cycle) \<subseteq> arcs G" 
proof -
  have "pre_digraph.cycle G (vwalk_arcs Cycle)" 
    using Cycle_def is_hc_def assms 
    by force
  then have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    using pre_digraph.cycle_def 
    by metis
  then obtain u where "pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    by auto
  then show ?thesis 
    using  pre_digraph.awalk_def 
    by fast
qed


lemma no_arcs_impl_at_most_one_vertex: 
  assumes "arcs G = {}"
  shows "card (verts G) \<le> 1" 
proof (rule ccontr)
  assume "\<not> card (verts G) \<le> 1"
  then have a1: "card (verts G) > 1" 
    by auto
  then have "pre_digraph.cycle G (vwalk_arcs Cycle)" 
    using is_hc_def a1 Cycle_def
    by force
  then have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    using pre_digraph.cycle_def 
    by metis
  then obtain u where "pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    by auto
  then have "set (vwalk_arcs Cycle) \<subseteq> arcs G"
    using  pre_digraph.awalk_def 
    by fast
  then have "set (vwalk_arcs Cycle) = {}"
    using assms by simp
  then have "vwalk_arcs Cycle = []"
    by simp
  then have "length Cycle \<le> 1" 
    using vwalk_arcs_empty_length_p by auto 
  then have cy1: "card (set Cycle) \<le> 1" "finite (set Cycle)"
    using card_length dual_order.trans apply(blast) by auto
  then have "card (verts G) \<le> 1"
  proof -
    have 1: "\<forall>x \<in> verts G. x \<in> set Cycle"
      using Cycle_def a1 is_hc_def by force
    then have "finite (verts G)" 
      using cy1 a1 card_eq_0_iff by fastforce  
    then have "card (verts G) = card (set Cycle)" 
      using 1 cy1 
      by (meson a1 card_greater_1_contains_two_elements contains_two_card_greater_1 dual_order.strict_trans1 less_numeral_extra(4)) 
    then show ?thesis using cy1 by simp
  qed
  then show False using a1 by auto
qed




lemma awalk_verts_Cycle_one_node: 
  assumes "a = [((v, 0), (v, 1)), ((v, 1), (v, 2)), ((v, 2), (v, 0))]"
  shows "(pre_digraph.awalk_verts G' (v, 0) a) = [(v, 0), (v, 1), (v, 2), (v, 0)]"
  using assms using G'_def_2 by(auto simp add: pre_digraph.awalk_verts.simps)



lemma cas_verts_Cycle_one_node: 
  shows "pre_digraph.cas G' (v, 0) [((v, 0), v, Suc 0), ((v, Suc 0), v, 2), ((v, 2), v, 0)] (v, 0)"
  using G'_def_2 by(auto simp add: pre_digraph.cas.simps) 


lemma awalk_Cycle_one_node: 
  assumes "a = [((v, 0), (v, 1)), ((v, 1), (v, 2)), ((v, 2), (v, 0))]"  
    "verts G' = {(v, 0), (v, 1), (v, 2)}" "((v, 0), (v, 1)) \<in> arcs G'" "((v, 1), (v, 2)) \<in> arcs G'" "((v, 2), (v, 0))\<in> arcs G'"
  shows "(pre_digraph.awalk G' (v, 0) a (v, 0))"
  unfolding pre_digraph.awalk_def using assms by(simp add: cas_verts_Cycle_one_node)


lemma arcs_G'_subset_verts_verts: 
  shows "arcs G' \<subseteq> (verts G' \<times> verts G')" 
  by (simp add: arcs_ends_G' subrelI wf_digraph.adj_in_verts(1) wf_digraph.adj_in_verts(2) wf_digraph_G') 


lemma single_vertex_arcs_G': 
  assumes "verts G = {v}" "verts G' = {(v, 0), (v, 1), (v, 2)}"
  shows  "((v, 0), (v, 1))\<in> arcs G'" "((v, 1), (v, 2)) \<in> arcs G'"  "((v, 2), (v, 0))\<in> arcs G'"
proof -
  have 2: "arcs G' = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (u, 2))|u. u \<in> verts G}\<union> 
          {((u, 2), (u, 0))|u. u \<in> verts G}"
    using G'_def_2 by simp
  then have 3: "arcs G' = {((v, 0), (v, 1))} \<union>{((v, 1), (v, 0))}\<union>
          {((v, 1), (v, 2))}\<union>{((v, 2), (v, 1))}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((v, 0), (v, 2))}\<union> 
          {((v, 2), (v, 0))}"
    using assms by auto
  then have "arcs G' = {((v, 2), (v, 0)), ((v, 0), (v, 2)),  ((v, 2), (v, 1)), ((v, 1), (v, 2)), ((v, 1), (v, 0)), ((v, 0), (v, 1))} 
    \<union> {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}\<union> 
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e}"
    by(simp)  
  then show "((v, 0), (v, 1))\<in> arcs G'" "((v, 1), (v, 2)) \<in> arcs G'"  "((v, 2), (v, 0))\<in> arcs G'" by blast+
qed


lemma cycleG'_one_vertex_G:
  assumes "card (verts G) = 1" 
  shows "\<exists>Cy. is_uhc G' Cy"
proof -
  have "(\<exists>v. verts G = {v})"
    using assms 
    by (meson card_1_singletonE) 
  then obtain v where v_def: "verts G = {v}"
    by auto 
  then have vG': "verts G' = {(v, 0), (v, 1), (v, 2)}"
    using G'_def_2 by auto
  then have aG': "((v, 0), (v, 1))\<in> arcs G'" "((v, 1), (v, 2)) \<in> arcs G'"  "((v, 2), (v, 0))\<in> arcs G'" 
    using single_vertex_arcs_G' v_def by blast+
  obtain Cy where
    Cy_def: "Cy = [(v, (0::nat)), (v, 1), (v,2), (v, 0)]"
    by auto
  then have "is_uhc G' Cy" proof -
    have 1: "set Cy \<subseteq> verts G'" 
      using Cy_def vG' by simp
    have 2: "distinct (tl Cy)"
      using Cy_def by simp
    have 3: "(\<forall>x\<in>verts G'. x \<in> set Cy)"
      using vG' Cy_def by simp
    have "pre_digraph.cycle G' (vwalk_arcs Cy)"
    proof-
      have arcsCy: "vwalk_arcs Cy = [((v, 0), (v, 1)), ((v, 1), (v, 2)), ((v, 2), (v, 0))]"
        using Cy_def by simp
      obtain a where a_def: "a = vwalk_arcs Cy"
        by auto
      then have a1: "a = [((v, 0), (v, 1)), ((v, 1), (v, 2)), ((v, 2), (v, 0))]"
        using arcsCy by auto
      then have 1: "vwalk_arcs a \<noteq> []"
        by auto
      have "(pre_digraph.awalk_verts G' (v, 0) a) = [(v, 0), (v, 1), (v, 2), (v, 0)]"
        using a1 awalk_verts_Cycle_one_node by simp
      then have 2: "distinct (tl (pre_digraph.awalk_verts G' (v, 0) a))"
        by fastforce
      have 3: "pre_digraph.awalk G' (v, 0) a (v, 0)" 
        using awalk_Cycle_one_node a1 vG' aG' 
        by blast 
      show ?thesis using pre_digraph.cycle_def 1 2 3 a_def  
        by fastforce 
    qed
    then show ?thesis  
      using is_uhc_def 1 2 3 by blast
  qed
  then show ?thesis by blast 
qed


lemma arcsG_empty_exists_cycleG':
  assumes "arcs G = {}" 
  shows "\<exists>Cy. is_uhc G' Cy"
proof -
  have "card (verts G) \<le> 1"
    using no_arcs_impl_at_most_one_vertex assms 
    by simp
  then have "card (verts G) = 1 \<or> card (verts G) = 0"
    by auto
  then show ?thesis proof 
    assume "card (verts G) = 1" 
    then show ?thesis 
      using cycleG'_one_vertex_G by simp  
  next
    assume "card (verts G) = 0" 
    then have a1: "verts G = {}"
      using finite_verts_G by auto
    then have cy: "Cycle = []" 
      using Cycle_def is_hc_def 
      by fastforce
    have vG': "verts G' = {}" 
      using G'_def_2 a1 by simp
    then have 1: "card (verts G') \<le> 1" "finite (verts G')"
      by auto
    then have "set [] \<subseteq> verts G'" "distinct (tl [])" 
      using vG' by auto
    then show ?thesis 
      using is_uhc_def 1 by blast 
  qed
qed


lemma non_empty_arcs_card_verts_G: 
  assumes "arcs G \<noteq> {}"
  shows "card (verts G) \<ge> 1"
proof -
  have "\<exists>u v. (u, v) \<in> arcs G" 
    using assms by auto
  then obtain u v where uv_def:
    "(u, v) \<in> arcs G"
    by auto
  then have "u \<in> verts G" 
    using wf_digraph_G wf_digraph_def 
    by fastforce
  then show ?thesis
    using card_0_eq finite_verts_G by fastforce 
qed


lemma card_verts_G':
  assumes "card (verts G) \<ge> 1"
  shows "card (verts G') \<ge> 1"
proof -
  have "\<exists>v. v \<in> verts G" 
    using assms not_one_le_zero by fastforce 
  then obtain v where "v \<in> verts G"
    by auto
  then have "(v, 0) \<in> verts G'"
    using G'_def_2 by auto
  then show ?thesis
    using finite_verts_G' 
    by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)
qed


lemma not_in_cycle_not_in_uhc_cycle: 
  assumes "a \<notin> set C"
  shows "(a, i) \<notin> set (to_cycle_uhc G C)"
  using assms apply(induction C) by(auto)


lemma distinct_C_distinct_uhc_cycle: 
  assumes "distinct C" 
  shows "distinct (to_cycle_uhc G C)"
  using assms proof(induction C)
  case Nil
  then show ?case by simp
next
  case (Cons a C)
  have "to_cycle_uhc G (a # C) = [(a, (0::nat)), (a, 1), (a, 2)] @ to_cycle_uhc G C"
    by simp
  have 1: "distinct (to_cycle_uhc G C)"
    using Cons by simp
  have 2: "distinct [(a, (0::nat)), (a, 1), (a, 2)]"
    by(auto) 
  have "(a, 0) \<notin> set (to_cycle_uhc G C)" "(a, 1) \<notin> set (to_cycle_uhc G C)" "(a, 2) \<notin> set (to_cycle_uhc G C)"
    using not_in_cycle_not_in_uhc_cycle Cons
    by auto 
  then show ?case 
    using 1 2 by auto
qed



lemma distinct_Cy: 
  shows "distinct (tl Cy)"
proof -
  have "tl Cy = to_cycle_uhc G (tl Cycle)" 
    using Cy_def by auto
  then show ?thesis
    using distinct_tail_cycle distinct_C_distinct_uhc_cycle
    by presburger

qed


lemma is_uhc_Cy_G':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "is_uhc G' Cy"
  unfolding is_uhc_def 
  using distinct_Cy
  sorry


lemma arcsG_non_empty_exists_cycleG':
  assumes "arcs G \<noteq> {}" "card (verts G) > 1"
  shows "\<exists>c.  is_uhc G' c"
  using assms is_uhc_Cy_G' by auto


lemma in_uhc: "hc_to_uhc G \<in> uhc"
proof -
  have 1: "head G' = snd" "tail G' = fst"
    using head_tail_G' by auto
  have 2: "symmetric G'"
    using symmetric_G' by auto
  have 3: "wf_digraph G'" 
    using wf_digraph_G' by auto
  have 4: "\<exists>c.  is_uhc G' c"
  proof(cases "arcs G = {}")
    case True
    then show ?thesis 
      using arcsG_empty_exists_cycleG' 
      by auto
  next
    case False
    then have "card (verts G) \<ge> 1"
      using non_empty_arcs_card_verts_G by auto 
    then have "card (verts G) = 1 \<or>card (verts G) > 1"
      by auto
    then show ?thesis proof 
      assume "card (verts G) = 1" 
      then show ?thesis 
        using cycleG'_one_vertex_G by simp
    next
      assume "1 < card (verts G)" 
      then show ?thesis 
        using arcsG_non_empty_exists_cycleG' False by blast 
    qed
  qed
  show ?thesis 
    using G'_def 1 2 3 4 uhc_def by blast
qed
  
end

subsection\<open>hc_to_uhc G \<in> uhc --> G \<in> hc\<close>

context
  fixes G assumes in_uhc: "hc_to_uhc G \<in> uhc"
  fixes G' assumes G'_def: "hc_to_uhc G = G'" 
begin 


lemma in_hc:
  shows "G \<in> hc"
  sorry

end



subsection\<open> Main theorem \<close>

(*Just some helpt for isabelle, since she was not able to figure that out herself*)
lemma hc_implies_uhc: "G \<in> hc  \<Longrightarrow> hc_to_uhc G \<in> uhc"
  using in_uhc hc_def sorry



lemma in_uhc_implies_in_hc: 
  assumes "hc_to_uhc G \<in> uhc"
  shows "G \<in> hc"
  using in_hc assms 
  sorry

theorem is_reduction_vc: 
  "is_reduction hc_to_uhc hc uhc"
  unfolding is_reduction_def
  using in_uhc_implies_in_hc hc_implies_uhc by auto


end