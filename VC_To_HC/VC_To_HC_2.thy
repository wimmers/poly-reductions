theory VC_To_HC_2
imports 
    Definitions "../VC_Set_To_VC_List"
begin

subsection\<open>vc_hc (E, k) f \<in> hc  \<Longrightarrow> (E,k) \<in> VC\<close>
context 
  fixes E k  assumes in_hc: "vc_hc (E, k) \<in> hc"
  fixes G assumes G_def: "G = vc_hc (E, k)" 
  fixes Cycle assumes Cycle_def: "is_hc G Cycle"
  fixes C assumes C_def: "C = {v|v e i j. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}"
begin

subsubsection\<open>Preliminaries\<close>

lemma G_def_2:
  shows "G =  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd \<rparr>" (is "G = ?L")
proof -
  have "G = (if ugraph (set E) \<and>  k \<le> card (\<Union> (set E)) \<and> distinct E
        then  ?L
        else \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>)"
    by(auto simp add: vc_hc_def G_def) 
  then have G_or: "G = ?L \<or> G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by argo
  then show "G = ?L" using else_not_in_hc in_hc G_def 
    by fast 
qed

subsubsection\<open>Lemmas for E\<close>

lemma ugraph:
  shows "ugraph (set E)" 
proof (rule ccontr)
  assume "\<not> (ugraph (set E))"
  then have "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by(auto simp add: vc_hc_def G_def) 
  then have "G \<notin> hc" 
    by (auto simp add: else_not_in_hc) 
  then show False 
    by (auto simp add: in_hc G_def)
qed

lemma k_smaller_number_vertices:
  shows "k \<le> card (\<Union> (set E))"
proof (rule ccontr)
  assume "\<not> k \<le> card (\<Union> (set E))"
  then have "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by(auto simp add: vc_hc_def G_def) 
  then have "G \<notin> hc" 
    by (auto simp add: else_not_in_hc) 
  then show False 
    by (auto simp add: in_hc G_def)
qed

lemma distinct_E:
  shows "distinct E" 
proof (rule ccontr)
  assume "\<not> (distinct E)"
  then have "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>" 
    by(auto simp add: vc_hc_def G_def) 
  then have "G \<notin> hc" 
    by (auto simp add: else_not_in_hc) 
  then show False 
    by (auto simp add: in_hc G_def)
qed

lemma verts_of_Cycle_in_G:
  shows "set Cycle \<subseteq> verts G" 
  using Cycle_def is_hc_def by metis

lemma Edges_in_Cycle: 
  assumes "Edge u e i \<in> set Cycle" 
  shows "u \<in> e" "e \<in> set E" "i\<le>1" 
  using assms verts_of_Cycle_in_G G_def_2 by auto  

lemma covers_in_Cycle:
  assumes "Cover i \<in> set Cycle"
  shows "i < k" 
  using assms verts_of_Cycle_in_G G_def_2 by auto 

subsubsection\<open>Structural Lemmas for Cycle\<close>

lemma inCycle_inVerts: 
  assumes "x \<in> set Cycle"
  shows "x\<in> verts G"
  using Cycle_def is_hc_def assms by fast 


lemma inVerts_inCycle:
  assumes "x \<in> verts G" "card (verts G) > 1"
  shows "x \<in> set Cycle"
  using assms Cycle_def is_hc_def by force 


lemma card_verts_set_Edge_i:
  assumes "\<forall>e \<in> set E. card e = 2"
  shows "finite {Edge v e i|v e. e\<in> set E \<and> v \<in> e}"
  using assms proof(induction E)
  case Nil
  then show ?case by simp
next
  case (Cons a E)
  then have union: "{Edge v e i|v e. e\<in> set (a#E) \<and> v \<in> e} = 
    {Edge v e i|v e. e\<in> set E \<and> v \<in> e} \<union> {Edge v a i|v. v \<in> a}" 
    by auto
  then have 1: "finite {Edge v e i|v e. e\<in> set E \<and> v \<in> e}" 
    using Cons
    by auto
  have card_a: "card a = 2" using Cons by auto
  then have "finite a" 
    using card_infinite 
    by fastforce 
  then have "finite {Edge v a i|v. v \<in> a}" 
    using Cons proof-
    have "\<exists>u v. a = {u, v}" 
      using card_a 
      by (metis card_eq_SucD numeral_2_eq_2) 
    then obtain u v where " a = {u, v}" 
      by auto
    then have "{Edge v a i|v. v \<in> a} = {Edge v a i, Edge u a i}"
      by auto
    then show ?thesis 
      by simp
  qed
  then show ?case 
    using 1 union 
    by auto  
qed 


lemma finite_verts:  
"finite (verts G)"
proof -
  have fin1: "finite {Cover i|i. i< k}" 
    by simp
  have 1: "finite (set E)"
    by simp
  have 2: "\<forall>e \<in> set E. card e = 2" 
    using ugraph ugraph_def by blast
  then have fin2: "finite {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}"
    "finite {Edge v e 1|v e. e\<in> set E \<and> v \<in> e}"
    using 1 2 card_verts_set_Edge_i 
    by blast+
  then show "finite (verts G)" 
    using G_def_2 fin1 fin2 
    by fastforce
qed

lemma length_cycle_number_verts: 
  assumes "length Cycle > 2"
  shows "card (verts G) > 1"
proof -
  have 0: "set (tl Cycle) \<subseteq> verts G" 
    using Cycle_def is_hc_def
    by (simp add: inCycle_inVerts list_set_tl subsetI) 
  have 1: "distinct (tl Cycle)" 
    using Cycle_def is_hc_def by blast
  then have "length (tl Cycle) \<ge> 2"
    using assms by simp
  then have "card (set (tl Cycle)) \<ge> 2"
    using 1 by (simp add: distinct_card) 
  then show ?thesis 
    using Cycle_def is_hc_def 0 finite_verts 
    by (smt card_seteq leI le_neq_implies_less not_numeral_less_one one_less_numeral_iff order.trans semiring_norm(76)) 
qed

lemma last_pre_digraph_cas: 
  assumes "pre_digraph.cas G u (vwalk_arcs p) u" "p\<noteq> []"
  shows "last p = u"
  using assms proof(induction p)
  case Nil
  then show ?case by simp 
next
  case (Cons a p)
  then show ?case sorry
qed 

lemma hd_pre_digraph_cas: 
  assumes "pre_digraph.cas G u (vwalk_arcs p) u" "p \<noteq> []"
  shows "hd p = u"
  using assms G_def_2  
  sorry

lemma hd_last_Cycle:
  assumes "Cycle \<noteq> []" "card (verts G) > 1" 
  shows "hd Cycle = last Cycle" 
proof -
  have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    using Cycle_def is_hc_def pre_digraph.cycle_def assms 
    by (metis antisym less_imp_le_nat nat_neq_iff)
  then obtain u where "pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    by auto
  then have 1: "pre_digraph.cas G u (vwalk_arcs Cycle) u" 
    using pre_digraph.awalk_def by force
  then have 2: "last Cycle = u" 
    using last_pre_digraph_cas assms  by simp
  then have 3: "hd Cycle = u" 
    using hd_pre_digraph_cas 1 assms by simp
  then show ?thesis using 2 3 
    by simp
qed

lemma sublist_length_g_2:
  assumes "sublist [a, b] Cycle" "a\<noteq>b"
  shows "length Cycle > 2"
proof (rule ccontr)
  assume "\<not>length Cycle >2"
  then have length_Cycle: "length Cycle \<le> 2"
    by auto
  then have "\<exists>p1 p2. p1@ [a, b] @p2 = Cycle" 
    using sublist_def assms by blast
  then obtain p1 p2 where p_def: "p1@ [a, b] @p2 = Cycle"
    by auto
  then have "p1 = []" "p2 = []" 
    using length_Cycle by auto
  then have c: "Cycle = [a, b]" 
    using p_def by simp
  then have "Cycle \<noteq> []"
    by auto
  then have 1: "hd Cycle = last Cycle" 
    using hd_last_Cycle c length_cycle_number_verts 
    by (metis assms(2) contains_two_card_greater_1 finite_verts inCycle_inVerts list.set_intros(1) p_def sublist_implies_in_set(2))
  have "hd Cycle = a" "last Cycle = b"
    using c by simp+
  then show False 
    using 1 assms by simp
qed

lemma elem2_sublist_in_edges:
  assumes "sublist [a, b] Cycle" "a \<noteq> b"
  shows "(a, b) \<in> arcs G"
proof - 
  have "length Cycle > 2" 
    using assms sublist_length_g_2 
    by simp 
  then have card_G: "card (verts G) > 1" 
    using length_cycle_number_verts 
    by blast
  have "\<exists>p1 p2. p1 @ [a, b] @ p2 = Cycle" 
    using assms sublist_def by blast
  then have 1: "(a,b) \<in> set (vwalk_arcs Cycle)" 
    by (simp add: if_sublist_then_edge) 
  then have "pre_digraph.cycle G (vwalk_arcs Cycle)" 
    using Cycle_def is_hc_def card_G 
    by fastforce 
  then have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    using pre_digraph.cycle_def by metis
  then obtain u  where "pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    by auto
  then have "set (vwalk_arcs Cycle) \<subseteq> arcs G" 
    using pre_digraph.awalk_def by metis
  then show "(a, b) \<in> arcs G" 
    using 1 by blast 
qed

lemma pre_1_edges:
  assumes "sublist [x, Edge v e 1] Cycle" 
  shows "v \<in> e" "(x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v) \<or> (x = Edge v e 0)"
  sorry

subsubsection\<open>Lemmas for V\<close>

lemma C_subset_Nodes:
  shows "C \<subseteq>  \<Union> (set E)"
proof 
  fix x assume "x \<in> C" 
  then have "\<exists>e i j. (Edge x e i, Cover j) \<in> set ( vwalk_arcs Cycle)" 
    using C_def by auto 
  then have "\<exists>e i. Edge x e i \<in> set Cycle" 
    using in_set_vwalk_arcsE by metis
  then obtain e i where "Edge x e i \<in> set Cycle"
    by auto
  then have "e \<in> set E" "x\<in> e" 
    using Edges_in_Cycle
    by simp+
  then show "x\<in> \<Union> (set E)" 
    by blast
qed

lemma finite_C:
  shows "finite C" 
  using C_subset_Nodes ugraph ugraph_vertex_set_finite finite_subset 
  by metis


lemma Cover_equal:
"Cover i = Cover j \<longleftrightarrow> i = j" 
  by simp

paragraph\<open>Cardinality of Cover\<close>

(*Evtl zeigen, dass es für jeden Cover-Knoten in G maximal eine Kante im Cycle gibt. Damit
hat das set für diesen Knoten maximal ein Element. Dann zeigen, dass G maximal
k Coverknoten hat und damit auch maximal k Cover-knoten im Cycle sind. Dann C als 
Union von diesem set schreiben und hoffentlich fertig*)

lemma card_dep_on_other_set:
  assumes "finite T" 
  shows "card {{u. f u j}|j. j \<in> T} \<le> card T" 
using assms proof (induction "card T" arbitrary: T)
  case 0
  then have "T = {}" 
    using assms 
    by simp
  then have "{{u. f u j}|j. j \<in> T} = {}" 
    using assms 0 
    by auto
  then show ?case 
    by auto
next
  case (Suc x)
  then have "\<exists>x. x \<in> T" 
    by (metis card_eq_SucD insertI1) 
  then obtain t where t_def: "t \<in> T" by auto
  then obtain T' where T'_def: "T' = T - {t}" by auto
  then have card: "x = card T'" 
    using Suc t_def by simp
  have "finite T'" using Suc 
    by (simp add: T'_def) 
  then have 1: "card {{u. f u j}|j. j \<in> T'} \<le> card T'" 
    using Suc card   
    by blast 
  have 2: "T = T' \<union> {t}" using T'_def t_def 
    by auto 
  then have "{{u. f u j}|j. j \<in> T} = {{u. f u j}|j. j \<in> T'} \<union> {{u. f u t}}"
    using T'_def 
    by blast
  then have "card {{u. f u j}|j. j \<in> T} = card ({{u. f u j}|j. j \<in> T'} \<union> {{u. f u t}})"
    by simp
  then have "card {{u. f u j}|j. j \<in> T}  \<le> card {{u. f u j}|j. j \<in> T'} + card {{u. f u t}}"
    by (metis (no_types, lifting) card_Un_le) 
  then have 3: "card {{u. f u j}|j. j \<in> T}  \<le> card T' + 1" 
    using 1 by simp
  have "card T = card T' +1 " 
    using 2 t_def T'_def Suc.hyps(2) card 
    by linarith  
  then have "card {{u. f u j}|j. j \<in> T}  \<le> card T" 
    using 2 3 
    by linarith
  then show ?case 
    using Suc 
    by argo
qed

lemma card_union_if_all_subsets_card_1:
  assumes "\<forall>S' \<in> S. card S' \<le> 1" "finite S"  
  shows "card (\<Union> S) \<le> card S"
proof (cases "finite (\<Union> S)")
  case True
  then show ?thesis using assms proof(induction "card S" arbitrary: S)
    case 0
    then have "S = {}" 
      using assms 0 by simp
    then show ?case 
      by simp
  next
    case (Suc x)
   then have "\<exists>x. x \<in> S" 
    by (metis card_eq_SucD insertI1) 
  then obtain S' where S'_def: "S' \<in> S" by auto
  then obtain T where T_def: "T = S - {S'}" by auto
  then have card_T: "card T = x" 
    using Suc S'_def by auto
  then have "\<forall>S' \<in> T. card S' \<le> 1" "finite T" 
    using Suc T_def by(blast)+
  then have 1: "card (\<Union> T) \<le> card T" 
    using Suc card_T 
    by fastforce
  have card_S': "card S' \<le> 1" 
    using Suc S'_def by fast 
  have fin: "finite S'" using True S'_def 
    using Suc.prems(1) rev_finite_subset by blast  
  then have 2: "card ((\<Union> T) \<union> S') \<le> card T+1" using 1 Suc S'_def card_S' fin proof - 
    have "card ((\<Union> T) \<union> S') \<le> card (\<Union> T) + card S'" 
      by (simp add: card_Un_le) 
    then have "card ((\<Union> T) \<union> S') \<le> card (\<Union> T) + 1" 
      using card_S' 
      by force
    then have "card ((\<Union> T) \<union> S') \<le> card T + 1" 
      using 1 by auto
    then show ?thesis .
  qed
  have 3: "card T +1 = card S" 
    using S'_def T_def 
    using Suc.hyps(2) card_T by linarith 
  have "(\<Union> T) \<union> S' = \<Union>S" 
    using S'_def T_def by auto 
  then show ?case using 2 3 Suc S'_def 
    by argo   
qed
next
  case False
  then have "card (\<Union> S) = 0" by simp
  then show ?thesis by simp
qed



lemma card_forall_for_elements: 
  assumes "\<forall>j \<in> T. card {u. f u j} \<le> 1" "S = {{u. f u j}| j. j \<in> T}"
  shows "\<forall>S' \<in> S. card S' \<le> 1"
proof 
  fix S' assume "S' \<in> S" 
  then have "\<exists>j \<in> T. S' = {u. f u j}" 
    using assms by blast
  then show "card S' \<le> 1" 
    using assms by blast 
qed

lemma two_edges_same_hd_not_distinct: 
  assumes "(v1, x) \<in> set (vwalk_arcs c)" "(v2, x) \<in> set (vwalk_arcs c)" "v1 \<noteq> v2"
  shows "\<not> distinct (tl c)"
  using assms proof(induction c)
  case Nil
  then show ?case by auto
next
  case (Cons a c)
  then have "\<exists>p1 p2. p1@ [v1, x]@p2 = (a#c)" 
    by (meson sublist_for_edges) 
  then obtain p1 p2 where p_def: "p1@ [v1, x]@p2 = (a#c)"
    by auto
  then have "\<exists>p1 p2. p1@ [v2, x]@p2 = (a#c)" 
    using Cons
    by (meson sublist_for_edges) 
  then obtain q1 q2 where q_def: "q1@ [v2, x]@q2 = (a#c)"
    by auto
  then have "p1 \<noteq> q1" 
    using p_def Cons 
    by (metis hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 same_append_eq) 
  then show ?case 
  proof(cases "p1 = []")
    case True
    then have 1: "a#c = v1#x#p2" using p_def by simp
    then have "\<exists>q11 q21. q11 @ [v2, x] @ q21 = x#p2" 
      using Cons q_def 
      by (metis Cons_eq_append_conv True \<open>p1 \<noteq> q1\<close> append_self_conv2 list.sel(3) tl_append2) 
    then have "x\<in> set p2" 
      by (metis True \<open>a # c = v1 # x # p2\<close> append_Cons eq_Nil_appendI list.sel(1) list.sel(3) list.set_intros(1) sublist_implies_in_set(2) tl_append2)
    then have "\<not> distinct c" using 1 by simp 
    then show ?thesis by simp
  next
    case False
    then have p1: "\<exists>p1 p2. p1@ [v1, x]@p2 = c" 
      using p_def 
      by (metis list.sel(3) tl_append2) 
    then have v1_in: "(v1, x) \<in> set (vwalk_arcs c)" 
      using if_sublist_then_edge by fast 
    show ?thesis 
    proof (cases "q1 = []")
      case True
      then have 1: "a#c = v2#x#q2" using q_def by simp
      then have "\<exists>q11 q21. q11 @ [v1, x] @ q21 = x#q2" 
        using Cons q_def 
        by (metis False list.sel(3) p_def tl_append2) 
      then have "x\<in> set q2" 
        by (metis True 1 append_Cons eq_Nil_appendI list.sel(1) list.sel(3) list.set_intros(1) sublist_implies_in_set(2) tl_append2)
      then have "\<not> distinct c" using 1 by simp 
      then show ?thesis by simp
    next
      case False
      then have q1: "\<exists>p1 p2. p1@ [v2, x]@p2 = c" 
        using q_def 
        by (metis list.sel(3) tl_append2)  
      then have v2_in: "(v2, x) \<in> set (vwalk_arcs c)" 
        using if_sublist_then_edge by fast 
      then have "\<not> distinct (tl c)" 
        using Cons v1_in v2_in 
        by blast 
      then show ?thesis 
        using distinct_tl by auto 
    qed
  qed
qed 

lemma card_Ci:
  assumes "S = {v|v e i. (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}" 
  shows "card S \<le> 1"
proof (cases "card S \<le> 1")
  case True
  then show ?thesis using assms by auto
next
  case False
  have distinct: "distinct (tl Cycle)" 
    using Cycle_def is_hc_def 
    by blast
  have "card S > 1" 
    using False by auto
  then have "\<exists>v1 v2. v1 \<in> S \<and> v2 \<in> S \<and> v1 \<noteq> v2" 
    using card_greater_1_contains_two_elements by fast 
  then obtain v1 v2 where "v1 \<in> S \<and> v2 \<in> S \<and> v1 \<noteq> v2"  
    by auto
  then have "\<exists>e1 i1 e2 i2. (Edge v1 e1 i1, Cover j) \<in> set (vwalk_arcs Cycle) \<and>
    (Edge v2 e2 i2, Cover j) \<in> set (vwalk_arcs Cycle) \<and> Edge v1 e1 i1 \<noteq> Edge v2 e2 i2"
    using assms by fast
  then obtain e1 i1 e2 i2 where edges_def: "(Edge v1 e1 i1, Cover j) \<in> set (vwalk_arcs Cycle) \<and>
    (Edge v2 e2 i2, Cover j) \<in> set (vwalk_arcs Cycle) \<and> Edge v1 e1 i1 \<noteq> Edge v2 e2 i2" 
    by auto
  then have "\<not>distinct (tl Cycle)" 
    using two_edges_same_hd_not_distinct by metis
  then show ?thesis using distinct by simp
qed


lemma card_C:
  shows "card C \<le> k"
proof -
  have 1: "card {i|i. Cover i \<in> verts G} = k"
    using G_def_2 by simp 

  obtain Cover_is where Cover_is_def: "Cover_is = {i. Cover i \<in> verts G}" by auto
  obtain S where S_def: "S = {{v|v e i . (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)}|j. j \<in> Cover_is}" by auto
  have eq: "C =  \<Union>S"
  proof
    show "C \<subseteq>  \<Union> S" proof 
      fix x assume "x \<in> C"
      then have "\<exists>e i j. (Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
        using C_def by fast
      then have "\<exists>j. \<exists>e i.(Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" by blast
      then obtain j where j_def: " \<exists>e i.(Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)"
        by auto
      then have "Cover j \<in> verts G" 
        by (meson inCycle_inVerts in_set_vwalk_arcsE) 
      then have "j \<in> Cover_is" 
        using Cover_is_def by simp
      then show "x \<in>  \<Union>S" 
        using S_def j_def by blast 
    qed   
  next
    show " \<Union>S \<subseteq> C"  proof 
      fix x assume "x \<in>  \<Union>S" 
      then have "\<exists>j. \<exists>e i.(Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
        using S_def by blast 
      then have "\<exists>e i j. (Edge x e i, Cover j) \<in> set (vwalk_arcs Cycle)" 
        by auto
      then show "x \<in> C" 
        using C_def by blast
    qed
  qed
 
  have 3: "finite Cover_is" using Cover_is_def 1 proof (cases "k = 0")
    case True
    then have "{i. Cover i \<in> verts G} = {}" 
      using G_def_2 by auto 
    then show ?thesis 
      using Cover_is_def by simp 
  next
    case False
    then show ?thesis 
      using Cover_is_def 1 
      by (meson card_infinite) 
  qed  
  have fin_S: "finite S"
    using finite_C eq 
    using finite_UnionD by auto  
  have 2: "card S \<le> card Cover_is" 
    using S_def 3 card_dep_on_other_set by fastforce 
  have "\<forall>j \<in> Cover_is. card {v|v e i . (Edge v e i, Cover j) \<in> set (vwalk_arcs Cycle)} \<le> 1"  
    using card_Ci by blast 
  then have "\<forall>S'\<in> S. card S' \<le> 1" 
    using S_def card_forall_for_elements 
    by blast   
  then have  "card (\<Union>S) \<le> card S" 
    using S_def card_union_if_all_subsets_card_1 fin_S by blast
  then have 3: "card (\<Union>S) \<le> card Cover_is" 
    using 2 by linarith
  have "card C = card (\<Union>S)" 
    using eq by simp  
  then show "card C \<le> k" 
    using 1 3 Cover_is_def by simp 
qed

paragraph\<open>The Cover fulfills is_verte_cover\<close>


lemma is_vc_C:
  shows "is_vertex_cover (set E) C" 
  sorry

lemma C_properties: 
  shows "C \<subseteq> \<Union> (set E) \<and> card C \<le> k \<and> is_vertex_cover (set E) C \<and> finite C"
  using is_vc_C card_C finite_C C_subset_Nodes by simp




lemma Cover_exists:
  shows "(\<exists>V. set V \<subseteq> \<Union> (set E) \<and> length V = k \<and> is_vertex_cover_list E V \<and> distinct V)"
proof -
  have "finite C" using C_properties 
    by auto
  obtain k' where k'_def: "k' = k - (card C)" by simp
  then obtain leftNodes where leftNodes_def: "leftNodes = ((\<Union> (set E)) - C)"  by simp
  then have "leftNodes \<subseteq> \<Union> (set E)" by simp
  then obtain setV where setV_def: "setV= C \<union> get_elements k' leftNodes" by simp
  have 1: "k' \<le> card leftNodes"  
      using C_properties leftNodes_def k'_def k_smaller_number_vertices card_Diff_subset 
      by fastforce 
  then have 2: "setV \<subseteq> \<Union> (set E)"  
    using \<open>leftNodes \<subseteq> \<Union> (set E)\<close> get_elements_subset setV_def C_properties by blast
  then have 4: "finite setV" 
    using 2 C_properties ugraph_def 
    by (meson finite_subset ugraph ugraph_vertex_set_finite) 
  have 3: "card setV = k" proof -
    have "card (get_elements k' leftNodes) = k'" 
      by (simp add: "1" card_get_elements) 
    have a: "(get_elements k' leftNodes) \<subseteq> leftNodes" 
      by (simp add: "1" get_elements_subset)  
    have "leftNodes \<inter> C = {}" using leftNodes_def by auto
    then have "C \<inter> (get_elements k' leftNodes) = {}" using a by auto
    then have "card setV = card C + card (get_elements k' leftNodes)" 
      using setV_def 4 
      by (simp add: card_Un_disjoint)   
    then show ?thesis using k'_def setV_def C_properties 
      using \<open>card (get_elements k' leftNodes) = k'\<close> distinct_size by force 
  qed
  have "\<exists>L. set L = setV \<and> distinct L" 
    using 4
    by (simp add: finite_distinct_list)  
  then obtain L where L_def: "set L = setV" "distinct L" 
    by auto
  then have "is_vertex_cover (set E) (set L)" 
    using C_properties setV_def is_vertex_cover_super_set 
    by fastforce 
  then have vc_list: "is_vertex_cover_list E L" 
    using is_vertex_cover_def
    is_vertex_cover_list_def by metis
  have length_L: "length L = k" using L_def 3 distinct_card 
    by fastforce   
  then show ?thesis 
    using L_def vc_list 2 by auto
qed


subsubsection\<open>Conclusion\<close>

lemma hc_impl_vc_context:
  shows "(E, k) \<in> vertex_cover_list"
proof -
  have 1: "distinct E" 
    using distinct_E by auto
  have 2: "k \<le> card (\<Union> (set E))"
    using k_smaller_number_vertices by auto
  have 3: "ugraph (set E)" 
    using ugraph by auto
  have 4: "(\<exists>V. set V \<subseteq> \<Union> (set E) \<and> length V = k \<and> is_vertex_cover_list E V \<and> distinct V)"
    using Cover_exists by auto
  then show ?thesis 
    using vertex_cover_list_def 1 2 3 4 by(auto)
qed

end

end