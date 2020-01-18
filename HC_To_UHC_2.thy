theory HC_To_UHC_2
  imports HC_To_UHC
begin

subsection\<open>hc_to_uhc G \<in> uhc --> G \<in> hc\<close>

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



lemma 
  assumes "pre_digraph.cycle G' (vwalk_arcs C)"
  shows "pre_digraph.cycle G' (vwalk_arcs (rev C))" 
  sorry


lemma
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
      by (simp add: G'_properties(1) vwalk_cycle_rev) sorry
    then show ?thesis using 1 2 3 by blast
  qed 
qed


lemma
  shows "is_uhc G' Cy2" 
  unfolding is_uhc_def sorry



lemma in_hc:
  shows "G \<in> hc"
  sorry

end

end