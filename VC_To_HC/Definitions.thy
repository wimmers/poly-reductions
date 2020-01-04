theory Definitions
  imports Main "../Three_Sat_To_Set_Cover"  "../List_Auxiliaries"
    Graph_Theory.Digraph  Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
begin

subsection\<open>Definitions\<close>

definition
  "is_vertex_cover_list E V \<equiv> \<forall> e \<in> set E. \<exists> v \<in> set V. v \<in> e"

(*If size of V is smaller than k, then there is a problem concerning the cover nodes in the Graph*)
definition
  "vertex_cover_list \<equiv>
  {(E, k). \<exists>V. ugraph (set E) \<and> (set V) \<subseteq> \<Union> (set E) \<and> k \<le> card (\<Union> (set E)) \<and> size V = k \<and> 
    is_vertex_cover_list E V \<and> distinct E \<and> distinct V}"

datatype ('a, 'b) hc_node = Cover nat | Edge 'a 'b nat

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_hc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    ((pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1)\<and> set c \<subseteq> verts G \<and> distinct (tl c)"

definition
  "hc \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c}"

definition
  "vc_hc \<equiv> \<lambda>(E, k).
    if ugraph (set E) \<and>  k \<le> card (\<Union> (set E)) \<and> distinct E
        then  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
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
          tail = fst, head = snd \<rparr>
        else \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"

definition get_second where
  "get_second e \<equiv> SOME v. v \<in> e"

definition next_edge where
  "next_edge v E e1 e2 \<equiv> \<exists>i j. i<length E \<and> j<length E \<and>  e1 = E!i \<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>k < size E. v \<in> E!k \<and> i < k \<and> k < j)"

definition first_edge where
  "first_edge v e E \<equiv> (\<exists>i<length E. e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i))"

definition last_edge where
  "last_edge v e E \<equiv> \<exists>i<length E. e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j)"

subsection\<open>Proof for Definitions\<close>

lemma else_not_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<notin> hc"
proof 
  assume "G \<in> hc"
  then have "\<exists> c. pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c) \<and> set c \<subseteq> verts G \<and> distinct (tl c)" 
    using assms hc_def 
    by (simp add: hc_def doubleton_eq_iff is_hc_def)
  then obtain c where c_def: "pre_digraph.cycle G (vwalk_arcs c)" "(\<forall>x\<in> verts G. x \<in> set c)" by blast
  with pre_digraph.cycle_def have not_empty: "vwalk_arcs c \<noteq> []"  by fastforce
  from pre_digraph.cycle_def pre_digraph.awalk_def c_def have subset: "set (vwalk_arcs c) \<subseteq> arcs G" by metis
  have "arcs G = {}" using assms by(auto)
  with subset  have "set (vwalk_arcs c) = {}" by auto
  then show "False" using not_empty by(auto)
qed

lemma else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma if_else_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<in> hc" 
  apply(auto simp add: hc_def wf_digraph_def is_hc_def assms) 
  using set_replicate_conv_if by fastforce 

lemma if_else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma get_second_in_edge:
  assumes "u = get_second e" "e \<noteq> {}"
  shows "u \<in> e"
  using assms unfolding  get_second_def apply(auto) 
  using some_in_eq by auto


lemma first_not_next: 
  assumes "first_edge v e1 E" "next_edge v E e2 e1" "distinct E" 
  shows False
proof -
  obtain i where 1: "i<length E \<and> e1 = E!i \<and> v \<in> e1 \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i)"
    using assms first_edge_def by metis
  obtain i' j' where 2: "i'<length E \<and> j'<length E \<and>  e2 = E!i' \<and> e1 = E!j' \<and> v \<in> e2 \<and> v \<in> e1 \<and> i'<j' \<and>
              \<not> (\<exists>k < size E. v \<in> E!k \<and> i' < k \<and> k < j')"
    using assms next_edge_def 
    by metis 
  then have "i = j'" using 1 2 
    by (simp add: "1" assms(3) nth_eq_iff_index_eq)  
  then have "i' < i" using 2 by simp
  then show ?thesis using 1 2 by blast 
qed

lemma last_not_next:
  assumes "last_edge v e1 E" "next_edge v E e1 e2" "distinct E"
  shows False
proof -
  obtain i where 1: "i<length E \<and> e1 = E!i\<and> v \<in> e1 \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j)"
    using assms last_edge_def by metis
  obtain i' j' where 2: "i'<length E \<and> j'<length E \<and>  e1 = E!i' \<and> e2 = E!j' \<and> v \<in> e1 \<and> v \<in> e2 \<and> i'<j' \<and>
              \<not> (\<exists>k < size E. v \<in> E!k \<and> i' < k \<and> k < j')"
    using assms next_edge_def 
    by metis
  then have "i = i'" using 1 2 
    by (simp add: "1" assms(3) nth_eq_iff_index_eq)  
  then have "i < j'" using 2 by simp
  then show ?thesis using 1 2 by blast 
qed

subsubsection\<open>Definitions for VC_HC_2\<close>

definition "sublist l ls \<equiv> \<exists>p1 p2. p1@l@p2 = ls"

lemma sublist_transitiv:
  assumes "sublist l1 l2" "sublist l2 l3" 
  shows "sublist l1 l3" 
  using assms sublist_def 
  by (metis append.assoc) 

lemma sublist_append:
  assumes "sublist l1 l2" 
  shows "sublist l1 (l3@l2)" 
proof -
  have "\<exists>p1 p2. p1@l1@p2 = l2" 
    using sublist_def assms by auto
  then obtain p1 p2 where "p1@l1@p2 = l2"
    by auto 
  then have "(l3@p1)@l1@p2 = l3@l2" 
    by simp
  then show ?thesis 
    using sublist_def by blast
qed

lemma sublist_cons:
  assumes "sublist l1 l2" 
  shows "sublist l1 (l#l2)"
  using assms 
  by (metis Cons_eq_appendI sublist_def) 


lemma two_sublist_distinct_same_first: 
  assumes "sublist [x, a] L" "sublist [y, a] L" "distinct (tl L)"
  shows "x = y"
  using assms proof(induction L)
  case Nil
  then show ?case 
    by (simp add: sublist_def) 
next
  case (Cons l L)
  then have distinct: "distinct L"
    by simp
  then have 1: "distinct (tl L)" 
    by (simp add: distinct_tl) 
  then show ?case proof(cases "sublist [x, a] L")
    case True
    then have a1: "sublist [x, a] L"
      by simp
    then show ?thesis proof(cases "sublist [y, a] L")
      case True
      then show ?thesis 
        using a1 1 Cons by simp  
    next
      case False
      then have 2: "\<exists>p1 p2. p1@[y, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[y, a] @ p2 = (L))"
        using sublist_def Cons by blast+
      then have "y = l" 
        using Cons 
        by (meson sublist_append_not_eq)
      then have hd: "a = hd L" 
        by (metis 2 append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) tl_append2)
      have tl: "a \<in> set (tl L)" using a1 sublist_def 
        by (smt append_Cons list.sel(3) list.set_intros(1) self_append_conv2 sublist_implies_in_set(2) tl_append2) 
      then have False using hd tl distinct 
        by (metis distinct.simps(2) distinct_singleton list.collapse list_set_tl)         
      then show ?thesis by simp
    qed
  next
    case False
    then have 2: "\<exists>p1 p2. p1@[x, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[x, a] @ p2 = (L))"
      using sublist_def Cons by blast+
    then have 3: "x = l" 
      using Cons 
      by (meson sublist_append_not_eq)
    then show ?thesis proof(cases "sublist [y, a] L")
      case True
      then have hd: "a = hd L" 
        by (metis 2 append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) tl_append2)
      have tl: "a \<in> set (tl L)" using 3 True sublist_def 
        by (smt append_Cons list.sel(3) list.set_intros(1) self_append_conv2 sublist_implies_in_set(2) tl_append2) 
      then have False using hd tl distinct 
        by (metis distinct.simps(2) distinct_singleton list.collapse list_set_tl)
      then show ?thesis by simp
    next
      case False
      then have 2: "\<exists>p1 p2. p1@[y, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[y, a] @ p2 = (L))"
        using sublist_def Cons by blast+
      then have "y = l" 
        using Cons 
        by (meson sublist_append_not_eq)
      then show ?thesis using 3 by simp
    qed
  qed
qed


lemma sublist_cons_impl_sublist: 
  assumes "sublist [a, b] (c#cs)" "a\<noteq> c"
  shows "sublist [a, b] cs"
proof -
  obtain p1 p2 where p_def: "p1@[a, b] @ p2 = (c#cs)" 
    using sublist_def assms 
    by blast
  then have 1: "p1 \<noteq> []" 
    using assms 
    by fastforce
  then have "c = hd p1" 
    using p_def 
    by (metis hd_append2 list.sel(1))
  then have "tl p1 @ [a, b] @ p2 = cs"
    using 1 p_def 
    by (metis list.sel(3) tl_append2) 
  then show ?thesis using sublist_def 
    by blast
qed


lemma sublist_not_cyclic_for_distinct: 
  assumes "sublist [a, b] Cy" "sublist [b, a] Cy" "distinct Cy"
  shows False
  using assms proof (induction Cy)
  case Nil
  then show ?case 
    using sublist_def 
    by fast  
next
  case (Cons c Cy)
  then show ?case proof(cases "a = c")
    case a: True
    then have b_hd: "b = hd Cy" 
      using sublist_def Cons 
      by (metis list.sel(1) list.sel(3) sublist_v1_hd_v2_hd_tl)  
    then show ?thesis proof(cases "b = c")
      case b: True
      then have "b = a" using a by simp
      then have "sublist [a, a] (c#Cy)" 
        using Cons by auto
      then have "\<not> distinct Cy" 
        using sublist_def Cons sublist_implies_in_set_a by metis 
      then show ?thesis 
        using Cons by auto
    next
      case b: False
      then have "b \<noteq> a" 
        using a by simp
      have "sublist [b, a] Cy" 
        using b Cons sublist_cons_impl_sublist
        by metis
      then have "a \<in> set Cy"
        by (simp add: sublist_def sublist_implies_in_set) 
      then show ?thesis 
        using a Cons by simp
    qed
  next
    case a: False
    then show ?thesis proof(cases "b = c")
      case True
      then have "b \<noteq> a" 
        using a by simp
      have "sublist [a, b] Cy" 
        using a Cons sublist_cons_impl_sublist
        by metis
      then have "b \<in> set Cy"
        by (simp add: sublist_def sublist_implies_in_set) 
      then show ?thesis 
        using True Cons by simp
    next
      case False
      then have "sublist [a, b] Cy" "sublist [b, a] Cy"
        using a sublist_cons_impl_sublist Cons
        by metis+  
      then show ?thesis 
        using Cons by auto 
    qed
  qed
qed


lemma distinct_sublist_last_first_of_sublist_false: 
  assumes "distinct cs" "sublist [a, b] cs" "a = last cs" 
  shows False
  using assms proof(induction cs)
  case Nil
  then  have "[] \<noteq>  []" 
    by (simp add: sublist_def)  
  then show ?thesis by auto
next
  case (Cons c cs)
  then show ?thesis proof(cases "a = c")
    case True
    then have "hd (a#cs) = last (a#cs)" 
      using Cons by auto 
    then have "(a#cs) = [a]" 
      using Cons 
      by (metis True distinct.simps(2) last.simps last_in_set) 
    then show ?thesis using Cons 
      by (simp add: sublist_def) 
  next
    case False
    then have 1: "sublist [a,b] cs" 
      using Cons 
      by (meson sublist_cons_impl_sublist) 
    then have "cs \<noteq> []"
      using Cons.prems False by auto 
    then have 2: "last (c#cs) = last cs" by simp
    then show ?thesis using Cons 1  2 by simp
  qed
qed


lemma sublist_hd_tl_equal_b_hd_tl: 
  assumes "sublist [a, b] cs" "a = hd cs" "distinct (tl cs)" 
    "a = last cs"
  shows "b = hd (tl cs)" 
proof -
  obtain p1 p2 where p_def: "p1 @ [a, b] @ p2 = cs"
    using sublist_def assms by blast
  show ?thesis proof(cases "p1 =[]")
    case True
    then show ?thesis 
      using p_def by auto  
  next
    case False
    then have 1: "sublist [a, b](tl cs)" 
      using assms 
      by (metis p_def sublist_def tl_append2) 
    then have "tl cs \<noteq> []"
      using sublist_def by fastforce
    then have "last cs = last (tl cs)"
      by (simp add: last_tl)  
    then show ?thesis 
      using 1 assms p_def distinct_sublist_last_first_of_sublist_false 
      by metis 
  qed
qed


lemma sublist_hd_last_only_2_elems: 
  assumes "sublist [a,b] cs" "a = hd cs" "b = last cs" "distinct cs"
  shows "cs = [a, b]" 
  using assms proof(induction cs)
  case Nil
  then show ?case 
    by (simp add: sublist_def) 
next
  case (Cons c cs)
  then have 0: "a = c" 
    using Cons by auto
  then have 1: "b = hd (cs)" 
    using Cons 
    by (metis list.sel(3) sublist_def sublist_v1_hd_v2_hd_tl) 
  then have "hd cs = last cs" 
    using Cons 
    by (metis \<open>a = c\<close> distinct_sublist_last_first_of_sublist_false last_ConsL last_ConsR) 
  then have "cs = [b]" using 1 Cons 
    by (metis \<open>a = c\<close> append_Nil2 distinct_tl hd_in_set last.simps list.sel(3) sublist_not_cyclic_for_distinct sublist_set_last_ls1_2)
  then have "c#cs = [a, b]" 
    using 0 by simp
  then show ?case by auto
qed


lemma two_sublist_distinct_same_last: 
  assumes "sublist [x, a] L" "sublist [x, b] L" "distinct (L)"
  shows "a = b"
  using assms proof(induction L)
  case Nil
  then show ?case by (simp add: sublist_def)
next
  case (Cons c L)
  then show ?case proof(cases "x = c")
    case True
    then have "a = hd L" "b = hd L"
      using Cons 
      by (metis list.sel(1) list.sel(3) sublist_def sublist_v1_hd_v2_hd_tl)+
    then show ?thesis by simp
  next
    case False
    then have "sublist [x, a] L" "sublist [x, b] L"
      using Cons 
      by (meson sublist_cons_impl_sublist)+
    then show ?thesis using Cons by auto
  qed
qed 


lemma sublist_append_not_in_first: 
  assumes "sublist [v1, v2] (l1 @ l2)" "v1 \<notin> set l1"
  shows "sublist [v1, v2] l2" 
using assms proof(induction l1)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case 
    by (simp add: Cons sublist_cons_impl_sublist) 
qed 

subsection\<open>Auxiliary lemmas\<close>

lemma card_greater_1_contains_two_elements:
  assumes "card S > 1"
  shows "\<exists>u v. v\<in> S \<and> u\<in> S \<and> u \<noteq> v"
proof -
  have "S \<noteq> {}"
    using assms by(auto)
  then have "\<exists>v. v \<in> S" by(auto)
  then obtain v where "v \<in> S" by auto 
  have "(S-{v}) \<noteq> {}" 
    using assms
    by (metis Diff_empty Diff_idemp Diff_insert0 \<open>S \<noteq> {}\<close> card.insert_remove card_empty finite.emptyI insert_Diff less_Suc0 less_numeral_extra(4) less_one)
  then have "\<exists>u. u \<in> S-{v}" 
    by(auto)
  then obtain u where "u\<in> S-{v}"
    by auto
  then have "u\<in> S" by(auto)
  then have "u \<noteq> v" using \<open>u\<in>S-{v}\<close> by(auto)
  then show ?thesis using \<open>u\<in> S\<close> \<open>v \<in> S\<close> by auto
qed

lemma contains_two_card_greater_1:
  assumes "v \<in> S" "u \<in> S" "u \<noteq> v" "finite S"
  shows "1 < card S"
  using assms apply(auto) 
  by (meson card_le_Suc0_iff_eq not_le_imp_less) 

lemma ugraph_implies_smaller_set_ugraph:
  assumes "ugraph (insert a (set E'))"
  shows "ugraph (set E')"
  using assms by (simp add: ugraph_def)

lemma edge_contains_minus_one_not_empty: 
  assumes "e \<in> set E'" "ugraph (set E')" "u \<in> e"
  shows "e-{u} \<noteq> {}"
  using subset_singletonD assms ugraph_def by fastforce

lemma if_edge_then_cycle_length_geq_2:
  assumes "(u, v) \<in> set (vwalk_arcs C)" 
  shows "length C \<ge> 2"
proof(rule ccontr)
  assume "\<not> 2 \<le> length C"
  then have length_C: "length C = 1 \<or> length C = 0" 
    by linarith
  then show False proof(cases "length C = 1")
    case True
    then have "vwalk_arcs C = []" 
      by (metis One_nat_def Suc_length_conv length_0_conv vwalk_arcs.simps(2))
    then show ?thesis using assms by auto
  next
    case False
    then have "length C = 0" using length_C by auto
    then have "vwalk_arcs C = []" by auto
    then show ?thesis using assms by auto
  qed
qed

lemma sublist_for_edges: 
  assumes "(u, v) \<in> set (vwalk_arcs C)"
  shows "\<exists>p1 p2. p1 @ [u, v] @ p2 = C"
  using assms proof(induction C)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  then have length_C: "length C \<ge> 1" 
    using if_edge_then_cycle_length_geq_2 by fastforce
  then show ?case proof(cases "u = a \<and> v = hd C")
    case True
    then have "[]@[u,v] @ (tl C) = (a#C)" 
      by (metis Cons.prems append_Cons append_self_conv2 list.collapse list.distinct(1) list.set_cases vwalk_arcs.simps(2))
    then show ?thesis by blast
  next
    case False
    then have "(u,v) \<in> set (vwalk_arcs C)" 
      using Cons 
      by (metis prod.inject set_ConsD vwalk_arcs.simps(1) vwalk_arcs.simps(2) vwalk_arcs_Cons) 
    then have "\<exists>p1 p2. p1 @ [u, v] @ p2 = C" using Cons by auto
    then obtain p1 p2 where p_def: "p1 @ [u, v] @ p2 = C" by blast
    then obtain p1' where "p1' = a # p1" by auto
    then have "p1' @ [u, v] @ p2 = (a#C)" using p_def by auto
    then show ?thesis using Cons by blast
  qed
qed

lemma if_sublist_then_edge: 
  assumes "\<exists>p1 p2. p1 @ [u, v] @ p2 = C"
  shows "(u, v) \<in> set (vwalk_arcs C)"
  using assms in_set_vwalk_arcs_append1 by force 


lemma vwalk_arcs_empty_length_p: 
  assumes "vwalk_arcs p = []"
  shows "length p \<le> 1" 
  using assms apply(induction p) apply(auto)
  using vwalk_arcs_Cons by fastforce  

lemma in_sublist_impl_in_list:
  assumes "sublist a b" "x \<in> set a"
  shows "x \<in> set b"
  using assms 
  by (metis append_Cons append_assoc in_set_conv_decomp sublist_def) 


end