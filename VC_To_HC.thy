theory VC_To_HC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Graph_Theory
begin

subsection\<open>Preliminaries\<close>

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
    (pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1"

definition
  "hc \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c}"

definition
  "vc_hc \<equiv> \<lambda>(E, k).
    if ugraph (set E) \<and>  k \<le> card (\<Union> (set E))
        then  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!i \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd \<rparr>
        else \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"


lemma else_not_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<notin> hc"
proof 
  assume "G \<in> hc"
  then have "\<exists> c. pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c)" 
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
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma if_else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

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

subsection\<open>(E,k) \<in> vc \<Longrightarrow> vc_hc (E, k) f \<in> hc\<close>

definition get_second where
  "get_second e \<equiv> SOME v. v \<in> e"

lemma edge_contains_minus_one_not_empty: 
  assumes "e \<in> set E'" "ugraph (set E')" "u \<in> e"
  shows "e-{u} \<noteq> {}"
  using subset_singletonD assms ugraph_def by fastforce

lemma ugraph_implies_smaller_set_ugraph:
  assumes "ugraph (insert a (set E'))"
  shows "ugraph (set E')"
  using assms by (simp add: ugraph_def)

lemma get_second_in_edge:
  assumes "u = get_second e" "e \<noteq> {}"
  shows "u \<in> e"
  using assms unfolding  get_second_def apply(auto) 
  using some_in_eq by auto

fun construct_cycle_add_edge_nodes:: "('a set list) \<Rightarrow> 'a \<Rightarrow> ('a set) \<Rightarrow>  (('a, 'a set) hc_node) list"
  where 
    "construct_cycle_add_edge_nodes [] v C = []" |
    "construct_cycle_add_edge_nodes (e#es) v C = (if v \<in> e then 
    (let u = (get_second (e-{v})) in 
      (if u\<in> C then [(Edge v e 0), (Edge v e 1)] 
      else [(Edge v e 0), (Edge u e 0), (Edge u e 1), (Edge v e 1)])) @ construct_cycle_add_edge_nodes es v C 
    else construct_cycle_add_edge_nodes es v C)"

fun construct_cycle_1::"'a set list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> (('a, 'a set) hc_node) list"  where
  "construct_cycle_1 E (x#Cs) n C =(Cover n) # (construct_cycle_add_edge_nodes E x C) @ 
    (construct_cycle_1 E Cs (n+1) C)"|
  "construct_cycle_1 E [] n C = [(Cover 0)]"

fun construct_cycle:: "'a set list \<Rightarrow> 'a list \<Rightarrow> (('a, 'a set) hc_node \<times> ('a, 'a set) hc_node) list" where
  "construct_cycle E C = vwalk_arcs (construct_cycle_1 E C 0 (set C))"


context 
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover_list"
  fixes Cov assumes Cov_def:"is_vertex_cover_list E Cov" "distinct Cov" "length Cov = k"
  fixes G assumes G_def: "G = vc_hc (E,k)"
  fixes Cycle assumes Cycle_def: "Cycle = construct_cycle_1 E Cov 0 (set Cov)"
begin

lemma card_dedges: 
  assumes "e \<in> set E"
  shows "card e = 2"
  using in_vc ugraph_def assms vertex_cover_list_def
  by fast

lemma "size Cov = card (set Cov)"
  using Cov_def by (simp add: distinct_card)

lemma in_vc_k_smaller:
  assumes "(E, k) \<in> vertex_cover_list" "\<not> k \<le> card (\<Union> (set E))"
  shows "False"
  using vertex_cover_list_def assms by(auto simp add: vertex_cover_list_def assms)

lemma G_def_2:
  shows "G =  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!i \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd \<rparr>" 
  using in_vc vertex_cover_list_def G_def apply(auto simp add: vc_hc_def) 
  using in_vc_k_smaller by blast+ 

lemma is_wf_digraph:
  shows "wf_digraph G"
  by(auto simp add: G_def_2 wf_digraph_def) 

lemma function_of_edge_nodes: 
  assumes "v \<in> set (construct_cycle_1 E (CS) n C)" "\<forall>k'. v \<noteq> Cover k'"
  shows "\<exists> x. v \<in> set (construct_cycle_add_edge_nodes E x C)"
  using assms apply(induction CS arbitrary: n)
  by(auto) 

lemma edge_0_with_many_prems:
  assumes "ugraph (insert a (set Ea))" "v \<in> set (let u = get_second (a - {x}) in if u \<in> C then [Edge x a 0, Edge x a 1] else [Edge x a 0, Edge u a 0, Edge u a 1, Edge x a 1])"
    "x \<in> a" "\<forall>e u. u \<in> e \<longrightarrow> v = Edge u e (Suc 0) \<longrightarrow> e \<noteq> a \<and> e \<notin> set Ea"
  shows "\<exists>e u. v = Edge u e 0 \<and> u \<in> e \<and> (e = a \<or> e \<in> set Ea)"
proof -
  have not_empty: "(a - {x}) \<noteq> {}" 
    using edge_contains_minus_one_not_empty assms 
    by (metis list.set_intros(1) list.simps(15))
  then obtain u where u_def: "u = get_second (a-{x})" by(auto)
  then have "u \<in> a" 
    using not_empty get_second_in_edge by fast
  then show ?thesis using u_def assms apply(auto)
    by (smt One_nat_def empty_set insert_iff set_ConsD singleton_iff)
qed


lemma no_Cover_in_edge_function: 
  assumes "v \<in> set (construct_cycle_add_edge_nodes E x C)" "ugraph (set E)"
  shows "(\<exists> e u. v = Edge u e 0 \<and> u \<in> e \<and> e \<in> set E) \<or> (\<exists> e u. v = Edge u e 1 \<and> u \<in> e \<and> e \<in> set E)"
  using assms apply(induction E arbitrary: ) apply(auto split: if_split_asm simp add: ugraph_implies_smaller_set_ugraph) 
  by(auto simp add: edge_0_with_many_prems)


lemma cover_in_construct_cycle:
  assumes "i<length Cs +n" "i \<ge> n \<or> i = 0"
  shows "Cover i \<in> set (construct_cycle_1 E Cs n Cs')"
  using assms by(induction Cs arbitrary: n Cs') (auto) 

lemma Edge_nodes_in_construct_edge:
  assumes "v \<in> e" "e \<in> set E'"
  shows "Edge v e 0 \<in> set (construct_cycle_add_edge_nodes E' v Cs')" "Edge v e 1 \<in> set (construct_cycle_add_edge_nodes E' v Cs')"
  using assms apply(induction E') apply(auto) 
   apply(smt list.set_intros(1))
  by (smt One_nat_def list.set_intros(1) list.set_intros(2)) 

lemma edge_nodes_in_construct_cycle_both_in_Cover:
  assumes "e \<in> set E" "u\<in> e" "v\<in> e" "u \<in> set Cs" "v \<in> Cs'" "u\<in> Cs'"
  shows "(Edge u e 0) \<in> set  (construct_cycle_1 E Cs n Cs')" "(Edge u e 1) \<in> set  (construct_cycle_1 E Cs n Cs')"
  using assms apply(induction Cs arbitrary: n) using Edge_nodes_in_construct_edge by(auto simp add: Edge_nodes_in_construct_edge)

lemma edge_nodes_construct_edges_expanded:
  assumes "u \<in> e" "u \<notin> Cs'"  "v \<in> e"  "card e = 2" "u \<noteq> v"
  shows "Edge u e 0 \<in> set (let u' = get_second (e - {v}) in if u' \<in> Cs' then [Edge v e 0, Edge v e 1] else [Edge v e 0, Edge u' e 0, Edge u' e 1, Edge v e 1])
   \<and>Edge u e 1 \<in> set (let u' = get_second (e - {v}) in if u' \<in> Cs' then [Edge v e 0, Edge v e 1] else [Edge v e 0, Edge u' e 0, Edge u' e 1, Edge v e 1])"
proof -
  have "card (e - {v}) = 1" 
    using assms apply(auto)
    by (metis Diff_empty card_Diff_insert card_infinite diff_Suc_1 insert_absorb insert_not_empty numeral_2_eq_2 zero_neq_numeral) 
  then have "(e - {v}) = {u}" 
    using assms 
    by (metis card_1_singletonE empty_iff insertE insert_Diff)
  then have "get_second (e - {v}) = u" 
    using get_second_in_edge
    by (metis insert_not_empty singletonD)
  then show ?thesis using assms by(auto)
qed

lemma edge_nodes_in_construct_edgess:
  assumes "v \<in> e" "u \<in> e" "e \<in> set E'" "u \<notin> Cs'" "card e = 2" "v \<noteq> u"
  shows "Edge u e 0 \<in> set (construct_cycle_add_edge_nodes E' v Cs') \<and> Edge u e 1 \<in> set (construct_cycle_add_edge_nodes E' v Cs')"
  using assms apply(induction E') using ugraph_def edge_nodes_construct_edges_expanded apply(auto) 
  by fast+

lemma edge_nodes_in_construct_cycle_one_in_Cover:
  assumes "e \<in> set E" "u\<in> e" "v\<in> e" "u \<in> set Cs" "u \<in> Cs'" "v \<notin> Cs'"
  shows "(Edge v e 0) \<in> set  (construct_cycle_1 E Cs n Cs') \<and> (Edge v e 1) \<in> set  (construct_cycle_1 E Cs n Cs')"
  using assms apply(induction Cs arbitrary: n) using Edge_nodes_in_construct_edge edge_nodes_in_construct_edgess card_dedges  apply(auto) 
  by (smt assms(3) assms(6) edge_nodes_in_construct_edgess card_dedges numeral_1_eq_Suc_0 numeral_2_eq_2 numerals(1))+   

lemma edge_nodes_in_cycle:
  assumes "e \<in> set E" "v \<in> e"
  shows "Edge v e 0 \<in> set (Cycle) \<and> Edge v e 1 \<in> set (Cycle)"
proof (cases "v\<in> set Cov")
  case True
  then show ?thesis 
    using assms edge_nodes_in_construct_cycle_one_in_Cover edge_nodes_in_construct_cycle_both_in_Cover Cycle_def by(auto)
next
  case False
  then have "\<exists>u. u \<in> e \<and> u \<in> set Cov" using assms Cov_def is_vertex_cover_list_def by fast 
  then obtain u where "u\<in> e" "u \<in> set Cov" by auto
  then show ?thesis using False assms edge_nodes_in_construct_cycle_one_in_Cover  Cycle_def by(auto)
qed

lemma cycle_contains_all_verts:
  assumes "card (verts G) > 1"
  shows "(\<forall>x\<in> verts G. x \<in> set Cycle)" 
  apply(auto simp add: G_def Cycle_def vc_hc_def) 
      apply (simp add: Cov_def(3) cover_in_construct_cycle) 
  using edge_nodes_in_cycle apply (simp add: Cycle_def)
  using edge_nodes_in_cycle apply(simp add: Cycle_def)
  using in_vc vertex_cover_list_def apply blast
  using in_vc in_vc_k_smaller apply blast
  done


lemma length_cycle:
  assumes "card (verts G) > 1" 
  shows "1 < length Cycle" 
proof -
  obtain u v where "u\<in> verts G" "v \<in> verts G" "u \<noteq> v" using card_greater_1_contains_two_elements assms by blast
  then have "u\<in> set Cycle" "v\<in> set Cycle" using cycle_contains_all_verts assms by blast+ 
  then have "card (set Cycle) > 1" using \<open>u\<noteq>v\<close> contains_two_card_greater_1 by fastforce 
  then show ?thesis 
    by (metis \<open>u \<in> set Cycle\<close> card_length leD length_pos_if_in_set less_numeral_extra(3) less_one linorder_neqE_nat)
qed 


lemma only_small_Cover_nodes_in_Cycle:
  assumes "length Cs +n \<le> k'" "0<k'"
  shows "Cover k' \<notin> set (construct_cycle_1 E (Cs) n C)"
  using assms 
  apply(induction Cs arbitrary: n) 
   apply(auto) 
  using no_Cover_in_edge_function in_vc vertex_cover_list_def by(blast) 

lemma function_of_cover_nodes:
  assumes "k\<le>k'" "0<k"
  shows "Cover k' \<notin> set (construct_cycle_1 E (Cov) 0 C)"
  using Cov_def assms by(auto simp add: only_small_Cover_nodes_in_Cycle) 


lemma nodes_of_cycle:
  assumes "v\<in> set Cycle" "k>0"
  shows "(\<exists>k'. v = Cover k' \<and> k' <k) \<or> (\<exists>e u. v = Edge u e 0 \<and> e \<in> set E \<and> u \<in> e) \<or> (\<exists>e u. v = Edge u e 1\<and> e \<in> set E \<and> u \<in> e)"
  using assms no_Cover_in_edge_function Cycle_def function_of_edge_nodes function_of_cover_nodes in_vc vertex_cover_list_def 
  by (metis (no_types, lifting) case_prodD le_eq_less_or_eq linorder_neqE_nat mem_Collect_eq)

lemma Cover_in_G:
  assumes "k' < k" "v = Cover k'"
  shows "v \<in> verts G"
  using G_def_2 assms by(auto)

lemma Edge0_in_G:
  assumes "e \<in> set E" "u\<in> e" "v = Edge u e 0"
  shows "v \<in> verts G"
  using G_def_2 assms by(auto)

lemma Edge1_in_G:
  assumes "e \<in> set E" "u \<in> e" "v = Edge u e 1"
  shows "v \<in> verts G"
  using G_def_2 assms by auto


lemma in_cycle_in_verts: 
  assumes "v \<in> set Cycle" "k>0"
  shows "v\<in> verts G" 
  using assms nodes_of_cycle Edge0_in_G Edge1_in_G Cover_in_G by blast


lemma 
  assumes "card S > 0"
  shows "\<exists>v. v\<in> S"
proof -
  have "S \<noteq> {}"
    using assms by(auto)
  then have "\<exists>v. v \<in> S" by(auto)
  then show ?thesis by auto
qed

lemma many_verts_impl_k_greater_0:
  assumes "card (verts G) > 1"
  shows "k>0"
proof (rule ccontr)
  assume "\<not> 0 < k" 
  then have "0 = k" by(auto)
  then have "Cov = []" using Cov_def by(auto)
  then have "Cycle = [(Cover 0)]" using Cycle_def by(auto)
  then have "set Cycle = {(Cover 0)}" by auto
  then have "verts G = {(Cover 0)}" using cycle_contains_all_verts assms apply(auto) 
    using card_greater_1_contains_two_elements by fastforce
  then show False using assms by(auto)
qed

lemma head_cycle_in_verts: 
  assumes "v = (hd Cycle)" "card (verts G) > 1" "Cycle \<noteq> []"
  shows "v \<in> (verts G)" 
  using in_cycle_in_verts assms many_verts_impl_k_greater_0 by(auto) 

lemma cycle_arcs_not_empty: 
  assumes "1 < size Cycle" 
  shows "vwalk_arcs Cycle \<noteq> []"
proof - (*Faster than sledgehammer generated*)
  obtain x y cs where "Cycle = x#y#cs" using assms 
    by (metis One_nat_def length_0_conv length_Cons less_numeral_extra(4) not_one_less_zero vwalk_arcs.cases)
  then have "vwalk_arcs Cycle = (x,y)#(vwalk_arcs (y#cs))" by simp
  then have "vwalk_arcs Cycle \<noteq> []" by auto
  then show ?thesis .
qed

lemma Cover_not_in_sublists:
  assumes " u = get_second (aa - {a})" 
      "Cover i
        \<in> set (if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
  shows "False"
  using assms by(auto split: if_split_asm)

lemma Cover_not_in_edge_nodes:
  assumes "Cover i \<in> set (construct_cycle_add_edge_nodes E' a C')"
  shows False
  using assms apply(induction E') apply(auto simp add: Cover_not_in_sublists split: if_split_asm) 
  using Cover_not_in_sublists by (metis (mono_tags, lifting)) 

lemma constraints_for_Cover_nodes: 
  assumes "Cover i \<in> set (construct_cycle_1 E C n C')"
  shows "(i<length C +n \<and> i\<ge> n)  \<or> i = 0"
  using assms apply(induction C arbitrary: n) apply(auto simp add: Cover_not_in_edge_nodes) using Cover_not_in_edge_nodes 
  by fastforce+

subsection\<open>Cycle is distince\<close>
lemma distinct_edges:
  shows "distinct E"
  using in_vc vertex_cover_list_def by(auto)

lemma distinct_cover:
  shows "distinct Cov"
  using Cov_def by simp

lemma distinct_edge_lists:
  assumes "u = get_second (aa - {a})" "ugraph (insert aa (set E'))" 
  shows "distinct (if u \<in> C' then [Edge a aa 0, Edge a aa 1] 
      else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
proof -
  have "card aa = 2" 
    using assms 
    by (simp add: ugraph_def) 
  then have "u \<in> (aa - {a})" 
    using assms  
    by (metis Diff_empty Diff_insert0 add_diff_cancel_right' card_Diff_singleton finite.emptyI get_second_in_edge infinite_remove insert_Diff_if is_singletonI is_singleton_altdef less_diff_conv not_add_less2 numeral_less_iff odd_card_imp_not_empty odd_one one_add_one semiring_norm(76) singletonI) 
  then have "u \<noteq> a" 
    using assms by blast
  then show ?thesis by(auto)
qed

lemma edge_in_list_construction_contains_given_e:
  assumes 
      "Edge u e i
        \<in> set (if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
    shows "aa = e"
  using assms by(auto split: if_split_asm)

lemma edge_in_list_construction_contains_given_e2:
  assumes "Edge u e i
        \<in> set (let u = get_second (aa - {a}) in if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
  shows "e = aa"
  using assms edge_in_list_construction_contains_given_e 
  by (smt empty_set hc_node.inject(2) list.simps(15) set_ConsD singleton_iff)


lemma only_previous_edges_in_new_edges:
  assumes "e \<notin> set E'" "\<exists>u i. Edge u e i \<in> set (construct_cycle_add_edge_nodes E' a C')"
  shows False
  using assms apply(induction E') apply(auto split: if_split_asm)
  using edge_in_list_construction_contains_given_e2 by fastforce+

lemma distinct_construct_edge_nodes:
  assumes "distinct E'" "ugraph (set E')"
  shows "distinct (construct_cycle_add_edge_nodes E' a C')"
  using assms apply(induction E') apply(auto)
  using distinct_edge_lists apply smt
    apply (auto simp add: ugraph_implies_smaller_set_ugraph) 
  using only_previous_edges_in_new_edges 
  by (smt empty_set list.simps(15) set_ConsD singleton_iff)

lemma card_3_element_set:
  assumes "v\<in> e" "u\<in> e" "x\<in> e" "v \<noteq> u" "x \<noteq> u" "v \<noteq> x" "finite e"
  shows "card e \<ge> 3"
proof -
  have 1: "{x, u, v} \<subseteq> e" using assms by simp
  have "finite {x, u, v}" by simp
  then have "card {x, u, v} = 3" using assms by(auto)
  then show ?thesis 
    using 1 assms by (metis card_mono)
qed

lemma elements_of_edges_helper:
  assumes "v\<in> e" "u\<in> e" "card e = 2" "v \<noteq> u" "finite e"
  shows "e = {v, u}"
  using assms apply(auto) apply(rule ccontr) using card_3_element_set 
  by (metis add_le_cancel_right numeral_le_one_iff numeral_plus_one one_add_one semiring_norm(5) semiring_norm(69))

lemma node_of_node_of_edge_construction:
  assumes "Edge v e i \<in> set (construct_cycle_add_edge_nodes E' a C')"
  shows "v = a \<or> v \<notin> C'"
  using assms apply(induction E') apply(auto split: if_split_asm) 
  by (smt empty_set hc_node.inject(2) insertCI set_ConsD singleton_iff)

lemma node_of_edge_construction_contains_a: 
  assumes "Edge v e i \<in> set (construct_cycle_add_edge_nodes E' a C')"
  shows "a \<in> e"
  using assms apply(induction E') apply(auto split: if_split_asm) 
  using edge_in_list_construction_contains_given_e2 by fastforce

lemma vertex_in_dege_of_node_helper2:
  assumes "Edge v e i
        \<in> set (if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
      "u = get_second (aa - {a})"
    shows "v = a \<or> v = u"
  using assms by(auto split: if_split_asm)

lemma vertex_in_edge_of_node_helper2: 
  assumes "Edge v e i
        \<in> set (if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
      "u = get_second (aa - {a})" "a \<in> aa" "card e \<ge> 2"
    shows "v \<in> e"
proof -
  have 2: "e = aa" using assms by(auto split: if_split_asm)
  have 1: "v = a \<or> v = u" 
    using vertex_in_dege_of_node_helper2 assms by fast
  have "u \<in> aa" using assms 
    by (metis Suc_1 \<open>e = aa\<close> card_empty card_insert_le_m1 diff_is_0_eq' get_second_in_edge insert_Diff insert_iff le_numeral_extra(3) le_numeral_extra(4) less_numeral_extra(1) not_less_eq_eq)
  then show ?thesis using 1 2 assms by(auto)
qed

lemma vertex_in_edge_of_node_helpe3:
  assumes "ugraph (insert aa (set E'))" "a \<in> aa" 
      "Edge v e i
        \<in> set (let u = get_second (aa - {a}) in if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
    shows "v \<in> e"
proof -
  have 1: "card aa = 2" 
    using assms by (simp add: ugraph_def)
  then have "e = aa" 
    using edge_in_list_construction_contains_given_e2 assms by fastforce
  then have "card e = 2" 
    using 1 by auto
  then show ?thesis using assms vertex_in_edge_of_node_helper2 
    by (smt Suc_1 Suc_le_mono le_numeral_extra(4))
qed

lemma vertex_in_edge_of_node: 
  assumes "Edge v e i \<in> set (construct_cycle_add_edge_nodes E' a C')" "ugraph (set E')"
  shows "v \<in> e"
  using assms apply(induction E') apply(auto split: if_split_asm) 
  using assms vertex_in_edge_of_node_helpe3 apply fast    
  using ugraph_implies_smaller_set_ugraph by auto
 

lemma edge_of_vertex_contains: 
  assumes "Edge v e i \<in> set (construct_cycle_add_edge_nodes E a C')" "v \<noteq> a" "ugraph (set E)"
  shows "e = {v,a}"
proof -
  have 1: "a\<in> e" 
    using node_of_edge_construction_contains_a assms by fast
  have 2: "v \<in> e" 
    using vertex_in_edge_of_node assms by fast
  have 3: "card e = 2" 
    using assms ugraph_def only_previous_edges_in_new_edges by metis
  then have "finite e" 
    using card_infinite by force 
  then show ?thesis 
    using 1 2 3 assms elements_of_edges_helper by metis 
qed

lemma edge_vertex_not_in_two_lists:
  assumes "x \<in> set (construct_cycle_add_edge_nodes E v C')" "v \<in> C'" "v \<noteq> u"
    "u \<in> C'" "x \<in> set (construct_cycle_add_edge_nodes E u C')" "ugraph (set E)"
  shows  False
proof -
  have "\<exists>w e i. x = Edge w e i" 
    using assms by (metis Cover_not_in_edge_nodes hc_node.exhaust)
  then obtain w e i where "x = Edge w e i" by blast
  then have 1: "w = v \<or> w \<notin> C'" 
    using node_of_node_of_edge_construction assms by simp
  then have 2: "w\<noteq> u" 
    using assms by auto
  show False proof(cases "w = v")
    case True
    then have "x\<notin> set (construct_cycle_add_edge_nodes E u C')" 
      using assms node_of_node_of_edge_construction \<open>x = Edge w e i\<close> by fast
    then show ?thesis 
      using assms by simp
  next
    case False
    then have "w \<notin> C'" 
      using 1 by auto
    then have "e = {w, v}" 
      using False assms edge_of_vertex_contains by (simp add: \<open>x = Edge w e i\<close>)
    then have "u \<notin> e" using assms 2 by simp
    then have "x\<notin> set (construct_cycle_add_edge_nodes E u C')" 
      using node_of_edge_construction_contains_a \<open>x = Edge w e i\<close> by fast
    then show ?thesis 
      using assms by simp
  qed
qed

lemma cover_node_not_in_other_edge:
  assumes "x \<in> set (construct_cycle_add_edge_nodes E a C')"
    "a \<notin> set Cs" "distinct Cs" "a \<in> C'" "set Cs \<subseteq> C'"
  shows "x \<notin> set (construct_cycle_1 E Cs n C')"
  using assms apply(induction Cs arbitrary: n) apply(auto)
  using Cover_not_in_edge_nodes apply fast+
  using edge_vertex_not_in_two_lists assms in_vc vertex_cover_list_def 
  by fast

lemma distinct_n_greater_0:  
  assumes "distinct E" "distinct Cs" "n>0"  "set Cs \<subseteq> C'"
  shows "distinct ((construct_cycle_1 E Cs n C'))"
  using assms apply(induction Cs arbitrary: n) apply(auto simp add: distinct_construct_edge_nodes)
    apply (meson Cover_not_in_edge_nodes)
  using Suc_n_not_le_n constraints_for_Cover_nodes apply blast
  using distinct_construct_edge_nodes in_vc vertex_cover_list_def apply fast
  using cover_node_not_in_other_edge by auto

lemma distinct_nodes: 
  assumes "distinct E" "distinct Cs" "set Cs \<subseteq> C'"
  shows "distinct (tl (construct_cycle_1 E Cs n C'))"
  using assms apply(induction Cs arbitrary: n) 
   apply(auto)
  using vertex_cover_list_def in_vc
  by(auto simp add: distinct_construct_edge_nodes distinct_n_greater_0 cover_node_not_in_other_edge in_vc vertex_cover_list_def)
  

lemma cycle_distinct:
  "distinct (tl Cycle)"
  using Cycle_def distinct_nodes Cycle_def distinct_edges distinct_cover by(auto)

lemma vwalk_arcs_awalk_verts_equal: 
  assumes "length C \<ge> 2"
  shows "C = ((pre_digraph.awalk_verts G u (vwalk_arcs C)))"
  using assms proof(induction C arbitrary: u)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  then have length_C: "length C > 0" 
    by auto
  then obtain v where v_def: "v = hd C" 
    by simp
  then have "vwalk_arcs (a#C) = (a,v)#(vwalk_arcs C)" using Cons length_C by(auto)  
  then have 1: "(pre_digraph.awalk_verts G u (vwalk_arcs (a#C))) = (tail G (a,v)) # (pre_digraph.awalk_verts G (head G (a,v)) (vwalk_arcs C))" 
    by (simp add: pre_digraph.awalk_verts.simps(2))
  then have "tail G (a,v) = a" using G_def_2 by(auto)
  then have 2: "(pre_digraph.awalk_verts G u (vwalk_arcs (a#C))) = a # (pre_digraph.awalk_verts G (head G (a,v)) (vwalk_arcs C))" 
    using 1 by auto
  have "(pre_digraph.awalk_verts G (head G (a,v)) (vwalk_arcs C)) = C" using Cons proof(cases "length C \<ge> 2")
    case True
    then show ?thesis using Cons by(auto)
  next
    case False
    then have "length C = 1" using length_C 
      by linarith 
    then have C_v: "C = [v]" using v_def apply(auto)
      by (metis Suc_length_conv length_0_conv list.sel(1))
    then have "vwalk_arcs C = []" by simp
    then have 3: "(pre_digraph.awalk_verts G (head G (a,v)) (vwalk_arcs C)) = [(head G (a, v))]"
      by (simp add: pre_digraph.awalk_verts_conv)
    have "head G (a, v) = v" using G_def_2 by auto
    then show ?thesis 
      using 3 C_v by simp  
  qed
  then show ?case using Cons 2 by(auto)
qed  


lemma distinct_nodes_implie_distinct_edges:  
  assumes "distinct (tl C)"
  shows "distinct (tl (pre_digraph.awalk_verts G v (vwalk_arcs C)))"
proof(cases "length C \<ge> 2")
  case True
  then have "(pre_digraph.awalk_verts G v (vwalk_arcs C)) = C"  
    using vwalk_arcs_awalk_verts_equal by auto
  then show ?thesis 
    using assms by auto 
next
  case False
  then have "length C = 0 \<or> length C = 1" 
    by linarith
  then have "vwalk_arcs C = []" 
    apply(auto) 
    by (metis One_nat_def cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv less_numeral_extra(3) vwalk_length_def vwalk_length_simp)
  then have "(pre_digraph.awalk_verts G v (vwalk_arcs C)) = [v]" 
    by (simp add: pre_digraph.awalk_verts.simps(1))
  then show ?thesis by simp
qed

lemma distinct_arcs: "distinct (tl (pre_digraph.awalk_verts G v (vwalk_arcs Cycle)))"
  using cycle_distinct distinct_nodes_implie_distinct_edges by(auto)

subsection\<open>Test\<close>
lemma aux22:
  assumes " u = get_second (aa - {a})" "1<i" "Edge u1 e1 i
        \<in> set (if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
  shows "False"
  using assms by(auto split: if_split_asm)

lemma aux21: 
  assumes "Suc 0 < i" "Edge u1 e1 i \<in> set (construct_cycle_add_edge_nodes E' a C')"
  shows "False"
  using assms apply(induction E')
   apply(auto split: if_split_asm) 
  using aux22
  by (smt One_nat_def)

lemma aux20:
  assumes "v1 = Edge u1 e1 i" "v1 \<in> set (construct_cycle_1 E C n C')" "i>1"
  shows "False"
  using assms apply(induction C arbitrary: n) apply(auto simp add: aux21) using aux21 by metis


lemma in_cycle:
  assumes "v \<in> set (construct_cycle_1 E (CS) n C)" "ugraph (set E)"
  shows "(\<exists>i. v = Cover i \<and>  ((i<length CS + n \<and> i \<ge> n)  \<or> i = 0)) 
        \<or> (\<exists> e u. v = Edge u e 0 \<and> u \<in> e \<and> e \<in> set E) \<or> (\<exists> e u. v = Edge u e 1 \<and> u \<in> e \<and> e \<in> set E)"
  using assms apply(induction CS arbitrary: n) apply(auto) 
  apply (metis One_nat_def assms(2) no_Cover_in_edge_function)
  by fastforce

(*lemma aux_3: 
  assumes "i+1<length Cy" "Cy = (construct_cycle_1 E (CS) n C)" "Cy!i = v1" "Cy!(i+1) = v2"
    "v1 = Cover x1"
  shows "((x1<length CS +n \<and>( x1 \<ge> n \<or> x1 = 0)) \<and> 
      ((\<exists>i. v2 = Cover i \<and>  i<length CS +n \<and> (i \<ge> n \<or> i = 0)) \<or> 
        (\<exists>u e. v2 = Edge u e 0 \<and> (\<exists>i<length E. e = E ! i \<and> u \<in> e \<and> (\<forall>j. u \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i)))))"
  sorry

lemma aux_2: 
  assumes "i+1<length Cy" "Cy = (construct_cycle_1 E (CS) n C)" "Cy!i = v1" "Cy!(i+1) = v2"
  shows "v1 = Cover i \<longrightarrow> (((i<length CS +n \<and> i \<ge> n) \<or> i = 0) \<and> 
      ((\<exists>i. v2 = Cover i \<and>  (i<length CS +n \<and> i \<ge> n) \<or> i = 0) \<or> (\<exists> e u. v = Edge u e 0 \<and> u \<in> e \<and> e \<in> set E)))"
      "v1 = Edge u1 e1 0 \<longrightarrow> ( u1 \<in> e1 \<and> e1 \<in> set E) \<and> ((\<exists>u2. v2 = Edge u2 e1 0 \<and> u2 \<in> e1) \<or>
          v2 = Edge u1 e1 1)"
      "v1 = Edge u1 e1 1 \<longrightarrow> ( u1 \<in> e1 \<and> e1 \<in> set E) \<and> ((\<exists>u2. v2 = Edge u2 e1 1 \<and> u2 \<in> e1) \<or>
          (\<exists>e2. v2 = Edge u1 e2 0 \<and> u1 \<in> e2))"
  sorry*)

lemma aux_4: 
  assumes "Suc i<length C" "C!i = x"
  shows "x \<in> set C"
  using assms Suc_lessD nth_mem by blast  

lemma aux_5:
  assumes "(\<exists>i. v2 = Cover i \<and> (i < k \<or> i = 0)) \<or> (\<exists>u e. v2 = Edge u e 0 \<and> (\<exists>i<length E. e = E ! i \<and> u \<in> e \<and> (\<forall>j. u \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i)))"
     "0 < k"
  shows "(\<exists>i. v2 = Cover i \<and> i < k) \<or> (\<exists>u e. v2 = Edge u e 0 \<and> (\<exists>i<length E. e = E ! i \<and> u \<in> e \<and> (\<forall>j. u \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i)))" 
using assms proof (cases "(\<exists>i. v2 = Cover i \<and> (i < k \<or> i = 0))")
  case True
  then obtain i where "(v2 = Cover i \<and> (i < k \<or> i = 0))" by blast
  then have 1: "v2 = Cover i \<and>( i < k \<or> i = 0)" by auto
  then have 2: "i<k" using assms by(auto)
      from 1 have "v2 = Cover i" by auto
  then have 1: "v2 = Cover i \<and> i< k" using \<open>k>0\<close> 
    by (simp add: "2")
  then show ?thesis by auto
next
  case False
  with assms have "(\<exists>u e. v2 = Edge u e 0 \<and> (\<exists>i<length E. e = E ! i \<and> u \<in> e \<and> (\<forall>j. u \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i)))"
    by auto
  then show ?thesis by auto
qed
(*
lemma aux_1:
  assumes "i+1<length Cycle"  "v1 = Cycle!i" "v2 = Cycle ! (i+1)" "k>0"
  shows "(v1, v2) \<in> arcs G" 
 (*using Cycle_def assms G_def_2 Cov_def aux_2 apply(simp)*)
proof (cases v1)
  case (Cover x1)
  then have "Cover x1 \<in> set Cycle" using assms aux_4 by(auto)
  then have "x1 < k" using aux_3 in_cycle assms apply(auto simp add: in_cycle nodes_of_cycle) 
    using Cycle_def function_of_cover_nodes not_le_imp_less by metis
  then have  "((x1<length Cov +0 \<and>( x1 \<ge> 0 \<or> x1 = 0)) \<and> 
      ((\<exists>i. v2 = Cover i \<and>  i<length Cov +0 \<and> (i \<ge> 0 \<or> i = 0)) \<or> 
        (\<exists>u e. v2 = Edge u e 0 \<and> (\<exists>i<length E. e = E ! i \<and> u \<in> e \<and> (\<forall>j. u \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i)))))"
    using aux_3 assms  Cov_def apply(auto simp add:) 
    by (smt Cover Cycle_def add_cancel_right_right) sorry
  then have "((\<exists>i. v2 = Cover i \<and> i < k) \<or>
             (\<exists>u e. v2 = Edge u e 0 \<and> (\<exists>i<length E. e = E ! i \<and> u \<in> e \<and> (\<forall>j. u \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i))))"
    using \<open>0<k\<close> Cov_def by(simp add: aux_5) 
  then show ?thesis using Cover Cov_def assms \<open>x1< _ \<close> aux_5 apply(simp add: assms Cycle_def G_def_2) by blast
next
  case (Edge x21 x22 x23)
  then show ?thesis sorry
qed*)

subsubsection\<open>Edges of Cycle are Edges of Graph\<close>

lemma aux40:
  assumes "Edge v e 0 \<in>  set (construct_cycle_1 E C n C')" 
  shows "v \<in> e" "e \<in> set E"
  using assms in_cycle in_vc vertex_cover_list_def by(blast)+

lemma aux41:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = C"
  shows "v1 \<in> set C" "v2 \<in> set C"
  using assms 
  by auto

lemma aux43: 
  shows "hd (construct_cycle_1 E C n C') = Cover n \<or> hd ((construct_cycle_1 E C n C')) = Cover 0"
  apply(induction C) by(auto) 

lemma aux100: 
  shows "last (construct_cycle_1 E C n C') = Cover 0"
  apply(induction C arbitrary: n) apply(auto) 
  using construct_cycle_1.elims apply blast
  by (metis construct_cycle_1.elims last_append neq_Nil_conv)


lemma aux101:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = l1"
  shows "v2 = hd (ls1 @ ls2)"
  using assms apply(induction L) apply(auto) 
  by (metis assms(1) assms(2) distinct_append hd_append hd_in_set list.sel(1) list.sel(3) not_distinct_conv_prefix self_append_conv2)

lemma aux102_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows "v2 \<in> set ls2"
  using assms proof(induction L arbitrary: ls2 ls1)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "ls1 = []" using assms Cons 
      by (metis (no_types, hide_lams) Nil_is_append_conv append.assoc append_Cons_eq_iff append_self_conv2 distinct.simps(2) in_set_conv_decomp in_set_conv_decomp_first list.distinct(1) split_list)
    then have "a#L = ls2" using Cons by auto
    then have "v2 \<in> set ls2"
      using Cons.prems(3) aux41(2) by force 
    then show ?thesis .
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then show ?thesis using Cons 
      by (metis L_def_2 append_self_conv2 aux41(2) distinct_tl p_def tl_append2)
  qed
qed 

lemma aux102_2:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows "v2 \<in> set ls2"
  using assms aux102_1 
  by (metis Cons_eq_appendI)

lemma aux102_3:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2"
  using assms proof(induction L arbitrary: ls2 ls1)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "ls1 = []" using assms Cons 
      by (metis (no_types, hide_lams) Nil_is_append_conv append.assoc append_Cons_eq_iff append_self_conv2 distinct.simps(2) in_set_conv_decomp in_set_conv_decomp_first list.distinct(1) split_list)
    then have "a#L = ls2" using Cons by auto
    then show ?thesis 
      using Cons by blast
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then show ?thesis using Cons 
      by (metis L_def_2 append_self_conv2 distinct_tl p_def tl_append2)
  qed
qed 

lemma aux102_4:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2" "ls3 = l1#ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2"
proof -
  have 1: "L = ls3 @ ls2" 
    using assms by simp
  then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2" 
    using aux102_3 assms 1  by fast 
  then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 = ls2" by blast
  then show ?thesis by auto
qed

lemma aux102:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows  "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2"
  using assms aux102_4 
  by fast 

lemma aux103_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "v2 \<in> set ls1"
  using assms proof(induction L arbitrary: ls1 ls2 )
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd ls1" 
      using Cons by (metis distinct.simps(2) distinct_singleton hd_append2 list.sel(1))
    with Cons have "v1 \<noteq> last ls1" 
      by auto
    then have "tl ls1 \<noteq> []" 
      by (metis Cons.prems(4) \<open>v1 = hd ls1\<close> distinct.simps(2) distinct_singleton last_ConsL list.collapse)
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" 
      using Cons assms by  argo
    then obtain p1 p2 where "p1@ [v1, v2] @ p2 = (a#L)" by auto
    then have "p1 = []" 
      using Cons \<open>v1 = a\<close> by (metis aux41(1) distinct.simps(2) list.sel(3) tl_append2)
    then have "v2 = hd L" 
      using Cons by (metis Cons_eq_appendI True \<open>p1 @ [v1, v2] @ p2 = a # L\<close> eq_Nil_appendI list.sel(1) list.sel(3))
    then have "v2 = hd (tl ls1)" 
      using Cons \<open>tl ls1 \<noteq> []\<close> by (metis Nil_tl \<open>p1 = []\<close> hd_append2 list.sel(3) tl_append2) 
    then show ?thesis 
      by (simp add: \<open>tl ls1 \<noteq> []\<close> list_set_tl)
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" 
      using False Cons p_def 
      by (metis hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 self_append_conv2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" 
      by auto
    have 2: "distinct L" 
      using Cons by (meson distinct.simps(2))
    have 3: "L = tl ls1 @ ls2" 
      using Cons 
      by (metis distinct.simps(2) distinct_singleton list.sel(3) tl_append2) 
    have 4: "v1 \<in> set (tl ls1)" 
      using Cons False by (metis hd_Cons_tl hd_append2 list.sel(1) set_ConsD tl_Nil)
    have 5: "v1 \<noteq> last (tl ls1)" 
      using Cons 
      by (metis "4" last_tl list.set_cases neq_Nil_conv) 
    then show ?thesis
      using Cons 1 2 3 4 5 list_set_tl 
      by metis   
  qed
qed  

lemma aux103_2:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1" "ls3 = l1#ls1"
  shows "v2 \<in> set ls1"
proof -
  have "L = ls3 @ ls2" 
    using assms by simp
  have "v1 \<in> set ls3" using assms by simp
  then have 1: "v2 \<in> set ls3" using aux103_1 assms 
    by (metis \<open>L = ls3 @ ls2\<close> last.simps list.distinct(1) list.set_cases)
  have "v2 \<noteq> l1" using assms 
    by (metis append_self_conv2 aux41(2) distinct.simps(2) hd_append2 list.sel(1) list.sel(2) list.sel(3) list.set_sel(1) tl_append2)
  then have "v2 \<in> (set ls1)" 
    using 1 assms by simp
  then show ?thesis  .
qed

lemma aux103_3:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "v2 \<in> set ls1"
  using assms aux103_2 
  by fast

lemma aux103_4:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1"
  using assms proof(induction L arbitrary: ls1 ls2 )
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd ls1" 
      using Cons by (metis distinct.simps(2) distinct_singleton hd_append2 list.sel(1))
    with Cons have "v1 \<noteq> last ls1" 
      by auto
    then have "tl ls1 \<noteq> []" 
      by (metis Cons.prems(4) \<open>v1 = hd ls1\<close> distinct.simps(2) distinct_singleton last_ConsL list.collapse)
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" 
      using Cons assms by  argo
    then obtain p1 p2 where "p1@ [v1, v2] @ p2 = (a#L)" by auto
    then have "p1 = []" 
      using Cons \<open>v1 = a\<close> by (metis aux41(1) distinct.simps(2) list.sel(3) tl_append2)
    then have "v2 = hd L" 
      using Cons by (metis Cons_eq_appendI True \<open>p1 @ [v1, v2] @ p2 = a # L\<close> eq_Nil_appendI list.sel(1) list.sel(3))
    then have "v2 = hd (tl ls1)" 
      using Cons \<open>tl ls1 \<noteq> []\<close> by (metis Nil_tl \<open>p1 = []\<close> hd_append2 list.sel(3) tl_append2) 
    then show ?thesis 
      by (metis Cons.prems(4) \<open>p1 = []\<close> \<open>tl ls1 \<noteq> []\<close> \<open>v1 = hd ls1\<close> append_Cons eq_Nil_appendI in_set_replicate list.exhaust_sel replicate_empty)
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" 
      using False Cons p_def 
      by (metis hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 self_append_conv2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" 
      by auto
    have 2: "distinct L" 
      using Cons by (meson distinct.simps(2))
    have 3: "L = tl ls1 @ ls2" 
      using Cons 
      by (metis distinct.simps(2) distinct_singleton list.sel(3) tl_append2) 
    have 4: "v1 \<in> set (tl ls1)" 
      using Cons False by (metis hd_Cons_tl hd_append2 list.sel(1) set_ConsD tl_Nil)
    have 5: "v1 \<noteq> last (tl ls1)" 
      using Cons 
      by (metis "4" last_tl list.set_cases neq_Nil_conv) 
    then have "\<exists>p1 p2. p1@[v1, v2]@p2 = tl(ls1)" 
      using Cons 1 2 3 4 5 by blast
    then obtain p1' p2' where "p1'@[v1, v2]@p2' = tl(ls1)" by auto
    then have "(a#p1')@[v1, v2]@p2' = ls1" 
      using Cons by (simp add: "3")
    then show ?thesis
      by blast 
  qed
qed  

lemma aux103_5:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1" "ls3 = l1#ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1"
proof -
  have 1: "L = ls3 @ ls2" 
    using assms by simp
  have 2: "v1 \<in> set ls3" using assms by simp
  have 3: "v1 \<noteq> last ls3" using assms by auto
  then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls3" 
    using aux103_4 assms 1 2 by fast 
  then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 = ls3" by blast
  have "v2 \<noteq> l1" using assms 
    by (metis append_self_conv2 aux41(2) distinct.simps(2) hd_append2 list.sel(1) list.sel(2) list.sel(3) list.set_sel(1) tl_append2)
  have 1: "v1 \<noteq> l1" 
    using assms by force
  then have 2: "p1@ [v1, v2] @ p2 = (l1 # ls1)" using assms p_def by auto
  then have "hd p1 = l1" using 1 p_def  
    by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
  then have "(tl p1)@[v1, v2] @ p2 = ls1" 
    using 2 1 by (metis hd_append list.sel(1) list.sel(3) tl_append2) 
  then show ?thesis by auto
qed

lemma aux103:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1"
  using assms aux103_5 by fast

lemma aux104_2: 
  assumes "x = hd L" "x = last ls1" "L = ls1 @ ls2" "x \<in> set ls1" "distinct L"
  shows "ls1 = [x]"
  using assms proof(induction L)
  case Nil
  then show ?case by(auto)
next
  case (Cons a L)
  then have "x = a" 
    by (meson list.sel(1))
  then show ?case using Cons 
    by (metis append.assoc append_Cons append_Cons_eq_iff append_Nil append_butlast_last_id distinct.simps(2) distinct_singleton)
qed

lemma aux104_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 = hd ls2"
using assms proof(induction L arbitrary: ls1 ls2)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd (a#L)" 
      by simp  
    then have "ls1 = [a]" using assms Cons aux104_2 True 
      by fast 
    then have "L = ls2" using Cons by auto
    then have "v2 = hd ls2"
      using Cons by (metis (mono_tags, lifting) Cons_eq_appendI True \<open>ls1 = [a]\<close> aux101 list.sel(3)) 
    then show ?thesis .
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def 
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2) 
    then have L_exists: "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    have "ls1 \<noteq> []" using False Cons 
      by (metis Cons_eq_appendI L_def_2 L_exists Nil_is_append_conv append_self_conv append_self_conv2 aux41(2) distinct.simps(2) distinct_length_2_or_more distinct_tl hd_Cons_tl last_snoc list.discI p_def rotate1.simps(2) tl_append2)
    then have "L = tl ls1 @ ls2" using Cons 
      by (metis list.sel(3) tl_append2)
    then show ?thesis using Cons L_exists 
      by (metis False distinct.simps(2) distinct_singleton hd_append2 last_tl list.collapse list.sel(1) set_ConsD)
  qed
qed

lemma aux104_3:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1" "ls3 = l1 # ls1"
  shows "v2 = hd ls2"
proof -
  have L_def_2: "L = ls3 @ ls2" using assms by auto
  then have last: "v1 = last ls3" using assms by auto
  then have "v1 \<in> set ls3" using assms by auto
  then have "v2 = hd ls2" 
    using assms(1) assms(3) last aux104_1 L_def_2 by fast
  then show ?thesis .
qed

lemma aux104:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 = hd ls2"
  using assms aux104_3 by fast


lemma aux110_1:
  assumes "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C' \<Longrightarrow>
        (\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e) \<or>
        (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
        (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
        (\<exists>v e1.
            v1 = Edge v e1 (Suc 0) \<and>
            (\<exists>e2. v2 = Edge v e2 0 \<and>
                  (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! i \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))))"
    "p1 @ v1 # v2 # p2 =
        (if a \<in> aa
         then (let u = get_second (aa - {a}) in if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1]) @
              construct_cycle_add_edge_nodes E' a C'
         else construct_cycle_add_edge_nodes E' a C')"
  shows "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
         (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! i \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))))"
  sorry

lemma aux110_2:
  assumes "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>v e1.
        v1 = Edge v e1 (Suc 0) \<and>
        (\<exists>e2. v2 = Edge v e2 0 \<and>
              (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))))" 
  shows "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set (aa # E') \<and> v \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set (aa # E') \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set (aa # E') \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>v e1.
        v1 = Edge v e1 (Suc 0) \<and>
        (\<exists>e2. v2 = Edge v e2 0 \<and>
              (\<exists>i<length (aa # E').
                  \<exists>j<length (aa # E').
                     e1 = (aa # E') ! i \<and> e2 = (aa # E') ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> (aa # E') ! i' \<longrightarrow> i' < length (aa # E') \<longrightarrow> \<not> i' < j))))"
  using assms proof(cases "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e)")
  case True
  then show ?thesis using assms by auto
next
  case False
  then have 1: "\<nexists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e" by auto
  then show ?thesis proof(cases "(\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e)")
    case True
    then show ?thesis using assms by auto
  next
    case False
    then have 2:  "\<nexists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e" by auto
    then show ?thesis proof(cases "(\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e)")
      case True
      then show ?thesis by auto
    next
      case False
      then have 3: "\<nexists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e" by auto
      then have 4: "(\<exists>v e1.
        v1 = Edge v e1 (Suc 0) \<and>
        (\<exists>e2. v2 = Edge v e2 0 \<and>
              (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))))" 
        using assms 1 2 3 by blast
      then obtain v e1 where " v1 = Edge v e1 (Suc 0)" by blast
      then have 5: "(\<exists>e2. v2 = Edge v e2 0 \<and>
              (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j)))" 
        using 4 by simp
      then obtain e2 where "v2 = Edge v e2 0" by blast
      then have 6: "\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j)"
        using 5 by simp 
      then obtain i j where ij_def: "e1 = E' ! i" "e2 = E' ! j" "v \<in> e1" "v \<in> e2" "(\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j)"  by auto
      then have "e1 = (aa#E') ! (i+1)" "e2 = (aa#E') ! (j+1)" "v \<in> e1" "v \<in> e2"  by auto
      have "(\<forall>i'>(i+1). v \<in> (aa # E') ! i' \<longrightarrow> i' < length (aa#E') \<longrightarrow> \<not> i' < (j+1))" using ij_def sorry
      then show ?thesis sorry 
    qed
  qed
qed


lemma aux110:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C'" 
  shows "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
         (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))))"
using assms proof(induction E')
  case Nil
  then show ?case by auto
next
  case (Cons aa E')
  then have 1: "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = (if a \<in> aa
         then (let u = get_second (aa - {a}) in if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1]) @
              construct_cycle_add_edge_nodes E' a C'
         else construct_cycle_add_edge_nodes E' a C')" by simp
  then show ?case proof(cases "a \<in> aa")
    case True
    then show ?thesis sorry
  next
    case False
    then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C'" 
      using 1 by simp
    then have "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E' \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>v e1.
        v1 = Edge v e1 (Suc 0) \<and>
        (\<exists>e2. v2 = Edge v e2 0 \<and>
              (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))))" 
      using Cons by auto
    then show ?thesis using Cons aux110_2  sorry
  qed
qed
  


lemma aux45:
  assumes "x \<in> e" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (
  let u = get_sceond (e - {x}) in (if u \<in> C then [Edge x e 0, Edge x e 1] else [Edge x e 0, Edge u e 0, Edge u e 1, Edge x e 1]) @
        construct_cycle_add_edge_nodes E' x C)" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 0"
  shows "e1 = e2"
  sorry

lemma aux44: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 0"
  shows "e1 = e2"
  using assms aux45 apply(induction E') apply(auto split: if_split_asm) 
  sorry


lemma aux42:
  assumes "(construct_cycle_1 E C n C') ! i = Edge u1 e1 0" "(construct_cycle_1 E C n C') ! (i+1) = Edge u2 e2 0" "i< length (construct_cycle_1 E C n C')"
  shows "e2 = e1"
(*using assms aux44 apply(induction C arbitrary: n) apply( auto)*)  
using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case using assms by(auto)
next
  case (Cons a C)
  then have "construct_cycle_1 E (a # C) n C' = 
        Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" by auto
  then show ?case proof (cases "i< length (Cover n # construct_cycle_add_edge_nodes E a C')")
    case True
    then have "(Cover n # construct_cycle_add_edge_nodes E a C') !i = Edge u1 e1 0" using Cons apply(auto) sorry
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed 

lemma aux5: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 0"
  shows "e1 = e2" "u1\<in> e1" "u2 \<in> e2" "e1 \<in> set E"
proof -
  have v1_in_set: "v1 \<in> set (construct_cycle_1 E C n C')" 
    using assms aux41 by fastforce
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms aux41 by fastforce
  then show "e1 \<in> set E" "u1 \<in> e1" "u2 \<in> e2" using assms v1_in_set in_cycle aux40 by(auto)
next
  show "e1 = e2" using assms aux42 apply(induction C arbitrary: n) apply(auto) sorry
qed

lemma aux6:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 1"
  shows "e1 = e2" "u1\<in> e1" "u2 = u1" "e1 \<in> set E"
  sorry

lemma aux7:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 1"
  shows "e1 = e2" "u1 \<in> e1" "u2 \<in> e1" "e1 \<in> set E"
  sorry

lemma aux8:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 0"
  shows "u1 = u2" "u1 \<in> e1" "u1 \<in> e2" "e1 \<in> set E" "e2 \<in> set E" 
    "(\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! i \<and> (\<forall>i'>i. u1 \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))"
  sorry

lemma aux9:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Cover i" "v2 = Edge u2 e2 j" "j> 0"
  shows "False"
  sorry

lemma aux10:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Cover n" "v2 = Edge u2 e2 0"
  shows "(\<exists>i<length E. e = E ! i \<and> u2 \<in> e2 \<and> (\<forall>j. u2 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> n < length C)"
  sorry

lemma aux11:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Edge u1 e1 1" "v2 = Cover n"
  shows "(\<exists>i<length E. e1 = E ! i \<and> u1 \<in> e1 \<and> (\<forall>j. u1 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> n < length C)"
  sorry

lemma aux12:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 i" "v2 = Cover j" "i\<noteq>1"
  shows "False"
  using assms apply(induction C arbitrary: n) apply(auto)
  sorry

lemma aux13:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Cover i" "v2 = Cover j" "length C + n > 0"
  shows "i<length C + n" "j<length C + n"
proof -
  have "v1 \<in> set (construct_cycle_1 E C n C')" "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms apply(auto) 
       apply(metis in_set_conv_decomp)
      apply(metis in_set_conv_decomp)
    by (metis append_assoc append_eq_Cons_conv assms(2) assms(3) in_set_conv_decomp self_append_conv2)+
  then  have "i<length C +n" "j<length C + n"
    using constraints_for_Cover_nodes assms by(auto)
  then show "i<length C + n" "j<length C + n" by auto
qed 


lemma aux23:
  assumes "v2 = Edge v e i" "v1 = Cover x1" 
    "\<exists>p1 p2. p1 @ Cover x1 # Edge v e i # p2 = construct_cycle_1 E C 0 (set C)" "length C \<le> k"
  shows  "i = 0 \<and> (\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> x1 < k)"
using assms proof (cases "i = 0")
  case True
  then show ?thesis using aux10 assms apply(auto)
    by (smt le_antisym le_neq_implies_less le_trans less_imp_le_nat) 
next
  case False
  then show ?thesis using assms aux9 apply(auto) by blast 
qed
 

lemma aux14:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Edge u1 e1 i" "v2 = Edge u2 e2 j" "j > 1 \<or> i > 1"
  shows "False"
proof -
  from \<open>\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)\<close> have v1_in:  "v1 \<in> set (construct_cycle_1 E C 0 (set C))" 
    by (metis Cons_eq_appendI in_set_conv_decomp self_append_conv2)
  from \<open>\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)\<close> have v2_in: "v2 \<in> set (construct_cycle_1 E C 0 (set C))" 
    by (metis (no_types, hide_lams) append_eq_Cons_conv append_eq_append_conv2 in_set_conv_decomp self_append_conv2) 
  then show False using assms v1_in v2_in aux20 \<open>j> 1 \<or> i > 1\<close> by meson +
qed

lemma aux16:
  assumes "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 i2""\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C"
  shows " (\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E \<and> v \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e)"
proof (cases)
  assume "i2 = 0 \<or> i2 = 1"
  then show ?thesis 
  proof 
    assume "i2=0"
    then show ?thesis using aux5 assms apply(simp) by metis
  next
    assume "i2 = 1" 
    then show ?thesis using aux6 assms apply(simp) by metis
  qed
next
  assume "\<not> (i2 = 0 \<or> i2 = 1)"
  then have "i2 > 1" by auto
  then show ?thesis 
    using aux14 assms apply(simp) 
    by blast
qed

lemma aux17:
  assumes "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 i2""\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C"
  shows "(\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! i \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))))"
proof (cases)
  assume "i2 = 0 \<or> i2 = 1"
  then show ?thesis 
  proof 
    assume "i2=0"
    then show ?thesis using assms aux8 apply(simp) by blast
  next
    assume "i2 = 1" 
    then show ?thesis using assms aux7 apply(simp) by blast
  qed
next
  assume "\<not> (i2 = 0 \<or> i2 = 1)"
  then have "i2 > 1" by auto
  then show ?thesis 
    using aux14 assms apply(simp) 
    by blast
qed

lemma aux15:
  assumes "v1 = Edge u1 e1 i1" "v2 = Edge u2 e2 i2""\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C"
  shows " (\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E \<and> v \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e) \<or>
    (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! i \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))))"
proof (cases)
  assume "i1 = 0 \<or> i1 = 1"
  then show ?thesis 
  proof 
    assume "i1=0"
    then show ?thesis 
      using assms aux16 by(simp)
  next
    assume "i1 = 1" 
    then show ?thesis 
      using assms aux17 by simp
  qed
next
  assume "\<not> (i1 = 0 \<or> i1 = 1)"
  then have "i1 > 1" by auto
  then show ?thesis 
    using aux14 assms apply(simp) 
    by blast
qed


lemma aux4:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C" (*"distinct C"*) "length  C = k" "k>0"
  shows "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E \<and> v \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e) \<or>
         (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! i \<and> v \<in> e1 \<and> v \<in> e2 \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j)))) \<or>
         (\<exists>v e. v1 = Edge v e (Suc 0) \<and> (\<exists>n. v2 = Cover n \<and> (\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> n < k))) \<or>
         (\<exists>v e n. v1 = Cover n \<and> v2 = Edge v e 0 \<and> (\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> n < k))\<or>
        (\<exists>i. v1 = Cover i \<and> (\<exists>j. v2 = Cover j \<and> i < k \<and> j < k))"
proof (cases)
  assume v1: "\<exists>x1. v1 = Cover x1"
  then obtain x1 where v1_2: "v1 = Cover x1" by blast
  then show ?thesis
  proof (cases)
    assume "\<exists> x2. v2 = Cover x2"
    then show ?thesis 
      using aux13 v1 assms apply simp 
      by fastforce 
  next
    assume  "\<not> (\<exists> x2. v2 = Cover x2)"
    then have "\<exists>v e i. v2 = Edge v e i" 
      by (meson hc_node.exhaust)
    then obtain v e i where "v2 = Edge v e i" by blast
    then show ?thesis
      using aux9 aux10 v1_2 assms by(simp add: aux23)
  qed
next
  assume "\<not> (\<exists>x1. v1 = Cover x1)"
  then have "\<exists>u1 e1 i1. v1 = Edge u1 e1 i1" 
    by (meson hc_node.exhaust) 
  then obtain u1 e1 i1 where "v1 = Edge u1 e1 i1" by blast
  then show ?thesis 
  proof(cases)
    assume "\<exists> x2. v2 = Cover x2"
    then obtain x2 where "v2 = Cover x2" by blast
    then show ?thesis 
      using aux11 aux12 \<open>v1 = _\<close> assms 
    proof(cases "i1 = 1")
      case True
      then show ?thesis using aux11 assms  \<open>v1 = _\<close>  \<open>v2 = _\<close> apply(simp) 
        by fastforce   
    next
      case False
      then show ?thesis 
        using aux12 assms \<open>v1 = _\<close>  \<open>v2 = _\<close>  apply(simp) 
        by blast 
    qed
  next
    assume  "\<not> (\<exists> x2. v2 = Cover x2)"
    then have "\<exists>v e i. v2 = Edge v e i" 
      by (meson hc_node.exhaust)
    then obtain u2 e2 i2 where "v2 = Edge u2 e2 i2" by blast
    then show ?thesis
      using aux15 assms \<open>v1 = _\<close>  \<open>v2 = _\<close> by(auto)  
  qed
qed


lemma aux1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = Cycle" "k>0"
  shows "(v1, v2) \<in> arcs G"
  sorry
  (*using Cycle_def assms G_def_2 Cov_def aux4 by(simp)*)

lemma aux3:
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
    using aux3 by fastforce
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


lemma edges_of_cycle_are_in_Graph:
  assumes "card (verts G) > 1" 
  shows "set (vwalk_arcs Cycle) \<subseteq> arcs G"
proof 
  have k0: "k > 0" 
    using many_verts_impl_k_greater_0 assms
    by auto
  fix x assume x_assm: "x \<in> set (vwalk_arcs Cycle)"
  then have "\<exists>u v. x = (u, v)" by simp
  then obtain u v where uv_def: "x = (u, v)" by blast
  then have "\<exists>p1 p2. p1 @ [u, v] @ p2 = Cycle" using x_assm sublist_for_edges by fast
  then show "x \<in> arcs G" using uv_def aux1 k0 by(auto)
qed

subsection\<open>Cycle is awalk\<close>

lemma hd_construct_cycle_Cover_0:
  shows "(hd (construct_cycle_1 E C 0 C')) = Cover 0"
  apply(induction C) by(auto) 

lemma head_construct_cycle_Cover_n:
  assumes "C \<noteq> []"
  shows "(hd (construct_cycle_1 E C n C')) = Cover n"
  using assms apply(induction C)by(auto) 

lemma last_construct_cycle_Cover_0:
  shows "(last (construct_cycle_1 E C n C')) = Cover 0"
  apply(induction C arbitrary: n) apply(auto)
  using construct_cycle_1.elims apply blast
  by (metis construct_cycle_1.elims last_append neq_Nil_conv)

lemma step_vwalk_arcs_impl_cas:
  assumes "pre_digraph.cas G (hd L) (vwalk_arcs L) (last L)"  "(a, hd L) \<in> arcs G" 
  shows "pre_digraph.cas G a ((a, hd L) # vwalk_arcs L) (last L)"
proof -
  have 3: "pre_digraph.cas G a ((a, hd L) # vwalk_arcs L) (last L) = (tail G (a, hd L) = a \<and> pre_digraph.cas G (head G (a, hd L)) (vwalk_arcs L) (last L))"
    by (simp add: pre_digraph.cas.simps(2)) 
  have 1: "tail G (a, hd L) = a" using G_def_2 by(auto)
  have 2: "head G (a, hd L) = (hd L)" using G_def_2 by(auto)
  with 1 2 3 assms show ?thesis by simp
qed

lemma vwalk_arcs_impl_cas:
  assumes "set (vwalk_arcs L) \<subseteq> arcs G" "L\<noteq> []"
  shows "pre_digraph.cas G (hd L) (vwalk_arcs L) (last L)"
  using assms apply(induction L)
   apply (metis last_ConsL list.distinct(1) list.sel(1) pre_digraph.cas.simps(1) vwalk_arcs.elims)
  apply(auto) 
   apply (simp add: pre_digraph.cas.simps(1))
  using step_vwalk_arcs_impl_cas by simp

lemma general_cas_construct_cycle: 
  assumes "(set (vwalk_arcs (construct_cycle_1 E C n C'))) \<subseteq> arcs G" "C \<noteq> []"
  shows "pre_digraph.cas G (Cover n) (vwalk_arcs (construct_cycle_1 E C n C')) (Cover 0)"
proof -
  have 1: "construct_cycle_1 E C n C' \<noteq> []" 
    apply(induction C arbitrary: n) by(auto)
  have 2: "hd (construct_cycle_1 E C n C') = (Cover n)" 
    using assms by (simp add: head_construct_cycle_Cover_n)
  have 3: "last (construct_cycle_1 E C n C') = Cover 0" 
    using last_construct_cycle_Cover_0 by(auto)
  then show ?thesis 
    using 1 2 3 assms vwalk_arcs_impl_cas by fastforce
qed

lemma is_awalk:
  assumes "card (verts G) > 1" "v \<in> (verts G)" "v =(hd Cycle)" 
  shows "pre_digraph.awalk G v (vwalk_arcs Cycle) v"
  using assms pre_digraph.awalk_def  apply(auto simp add: pre_digraph.awalk_def)
  using assms(1) edges_of_cycle_are_in_Graph apply blast
  using Cycle_def apply(auto simp add: hd_construct_cycle_Cover_0 general_cas_construct_cycle) 
  using general_cas_construct_cycle Cov_def(3) edges_of_cycle_are_in_Graph many_verts_impl_k_greater_0 by auto 


subsection\<open>Is in hc\<close>

lemma is_cylce: 
  assumes "card (verts G) > 1" "v \<in> (verts G)" "v =(hd Cycle)" 
  shows "pre_digraph.cycle G (vwalk_arcs Cycle)"
proof -
  have "1 < size Cycle" 
    using assms length_cycle by auto
  then have not_empty: "vwalk_arcs Cycle \<noteq> []" 
    using assms cycle_arcs_not_empty by auto
  have distinct: "distinct (tl (pre_digraph.awalk_verts G v (vwalk_arcs Cycle)))" 
    using distinct_arcs by(auto)
  have contained: "set (vwalk_arcs Cycle) \<subseteq> arcs G" 
    using assms edges_of_cycle_are_in_Graph by(auto)
  have awalk: "pre_digraph.awalk G v (vwalk_arcs Cycle) v" using assms is_awalk by(auto)
  show ?thesis using not_empty distinct contained awalk pre_digraph.cycle_def pre_digraph.awalk_def by(auto)  
qed

lemma is_hc_cycle_graph: 
  shows "is_hc G Cycle"
  using cycle_contains_all_verts is_cylce is_hc_def head_cycle_in_verts 
  by fastforce


lemma vc_impl_hc_context: "vc_hc (E,k) \<in> hc"
  using is_wf_digraph is_hc_cycle_graph G_def hc_def
  by auto

end


subsection\<open>vc_hc (E, k) f \<in> hc  \<Longrightarrow> (E,k) \<in> VC\<close>
context 
  fixes E k  assumes "vc_hc (E, k) \<in> hc"
begin

end

subsection\<open> Main theorem \<close>

lemma vc_impl_hc: "(E,k) \<in> vertex_cover_list \<Longrightarrow> vc_hc (E,k) \<in> hc"
proof -
  assume in_vc: "(E,k)\<in> vertex_cover_list"
  then obtain Cov where "is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k" 
    using vertex_cover_list_def 
    by (smt case_prodD mem_Collect_eq)
  then show ?thesis 
    using vc_impl_hc_context in_vc by blast
qed

lemma hc_impl_vc: "vc_hc (E,k) \<in> hc \<Longrightarrow> (E,k) \<in> vertex_cover_list"
proof -
  show ?thesis sorry
qed



theorem is_reduction_vc_to_hc:
  "is_reduction vc_hc vertex_cover_list hc"
  unfolding is_reduction_def using vc_impl_hc hc_impl_vc by(auto)


subsection\<open>Need to prove equivalence of Vertex-Cover\<close>

lemma is_vc_list_equal: 
  assumes "distinct E" "distinct V" 
  shows "is_vertex_cover (set E) (set V)\<longleftrightarrow> is_vertex_cover_list E V"
  apply(auto) 
  sorry

lemma "(set E, k) \<in> vertex_cover \<longleftrightarrow> (E, k) \<in> vertex_cover_list"
  using vertex_cover_def vertex_cover_list_def is_vc_list_equal apply(auto)
  sorry



end

