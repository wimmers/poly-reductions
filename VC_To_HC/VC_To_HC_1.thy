theory VC_To_HC_1
  imports  Main "../Three_Sat_To_Set_Cover" 
    Graph_Theory.Digraph  Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    "../List_Auxiliaries"
    Definitions
begin

subsection\<open>(E,k) \<in> vc \<Longrightarrow> vc_hc (E, k) f \<in> hc\<close>

lemma fin_Cov:
  shows "finite {Cover i|i. i< k}"
proof -
  show ?thesis by simp
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
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e  \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd \<rparr>" (is "G = ?L")
proof -
  have 1: "ugraph (set E)" "k \<le> card (\<Union> (set E))" "distinct E" 
    using in_vc vertex_cover_list_def apply auto by force
  have "G = (if ugraph (set E) \<and>  k \<le> card (\<Union> (set E)) \<and> distinct E
        then  ?L
        else \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>)"
    by(auto simp add: vc_hc_def G_def) 
  then show "G = ?L" 
    using 1 by argo 
qed 


lemma ugraph_E:
  shows "ugraph (set E)"
  using in_vc vertex_cover_list_def by auto


lemma is_wf_digraph:
  shows "wf_digraph G"
  by(auto simp add: G_def_2 wf_digraph_def) 


lemma finite_verts_G:
  shows "finite (verts G)" 
  using G_def_2 fin_Cov fin_Edge1 fin_Edge0 ugraph_E ugraph_def 
  by auto 


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
  using in_vc in_vc_k_smaller vertex_cover_list_def apply blast+
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

subsubsection\<open>Cycle is distince\<close>
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

subsubsection\<open>Edges of Cycle are Edges of Graph\<close>

lemma Edgei_not_in_construct_edge_nodes_helper:
  assumes " u = get_second (aa - {a})" "1<i" "Edge u1 e1 i
        \<in> set (if u \<in> C' then [Edge a aa 0, Edge a aa 1] else [Edge a aa 0, Edge u aa 0, Edge u aa 1, Edge a aa 1])"
  shows "False"
  using assms by(auto split: if_split_asm)

lemma Edgei_not_in_construct_edge_nodes: 
  assumes "Suc 0 < i" "Edge u1 e1 i \<in> set (construct_cycle_add_edge_nodes E' a C')"
  shows "False"
  using assms apply(induction E')
   apply(auto split: if_split_asm) 
  using Edgei_not_in_construct_edge_nodes_helper
  by (smt One_nat_def)

lemma Edgei_not_in_construct_cycle:
  assumes "v1 = Edge u1 e1 i" "v1 \<in> set (construct_cycle_1 E C n C')" "i>1"
  shows "False"
  using assms apply(induction C arbitrary: n) apply(auto simp add: Edgei_not_in_construct_edge_nodes) using Edgei_not_in_construct_edge_nodes by metis


lemma in_cycle:
  assumes "v \<in> set (construct_cycle_1 E (CS) n C)" "ugraph (set E)"
  shows "(\<exists>i. v = Cover i \<and>  ((i<length CS + n \<and> i \<ge> n)  \<or> i = 0)) 
        \<or> (\<exists> e u. v = Edge u e 0 \<and> u \<in> e \<and> e \<in> set E) \<or> (\<exists> e u. v = Edge u e 1 \<and> u \<in> e \<and> e \<in> set E)"
  using assms apply(induction CS arbitrary: n) apply(auto) 
   apply (metis One_nat_def assms(2) no_Cover_in_edge_function)
  by fastforce


lemma last_construct_cycle_not_Edge0: 
  assumes "v1 = last (construct_cycle_add_edge_nodes E' a C')" "v1 = Edge v e 0" "construct_cycle_add_edge_nodes E' a C' \<noteq> []"
  shows False
  using assms apply(induction E') apply(auto split: if_split_asm) 
  by (smt append.right_neutral hc_node.inject(2) last_ConsL last_ConsR less_numeral_extra(1) list.discI nat_neq_iff)

lemma hd_construct_cycle_not_Edge1: 
  assumes "v1 = hd (construct_cycle_add_edge_nodes E' a C')" "v1 = Edge v e 1" "construct_cycle_add_edge_nodes E' a C' \<noteq> []"
  shows False
  using assms apply(induction E') apply(auto split: if_split_asm) 
   apply (smt One_nat_def hc_node.inject(2) less_numeral_extra(1) list.sel(1) nat_neq_iff)
  by (smt One_nat_def hc_node.inject(2) hd_append less_Suc_eq_0_disj less_numeral_extra(4) list.sel(1)) 

lemma edge0_in_construct_cycle:
  assumes "Edge v e 0 \<in>  set (construct_cycle_1 E C n C')" 
  shows "v \<in> e" "e \<in> set E"
  using assms in_cycle in_vc vertex_cover_list_def by(blast)+

lemma edge1_in_construct_cycle:
  assumes "Edge v e 1 \<in>  set (construct_cycle_1 E C n C')" 
  shows "v \<in> e" "e \<in> set E"
  using assms in_cycle in_vc vertex_cover_list_def by(blast)+

lemma hd_construct_cycle: 
  shows "hd (construct_cycle_1 E' C n C') = Cover n \<or> hd ((construct_cycle_1 E' C n C')) = Cover 0"
  apply(induction C) by(auto) 

lemma last_construct_cycle: 
  shows "last (construct_cycle_1 E C n C') = Cover 0"
  apply(induction C arbitrary: n) apply(auto) 
  using construct_cycle_1.elims apply blast
  by (metis construct_cycle_1.elims last_append neq_Nil_conv)


lemma helper_for_helper_arcs_explicit_Cover_Edge0_Edge0: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 0"
    "distinct (construct_cycle_add_edge_nodes E' a C)" 
  shows "e1 = e2 \<and> u1 \<noteq> u2"
  using assms proof(induction E')
  case Nil
  then show ?case by simp
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e # E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by simp 
  then show ?case proof (cases "a\<in>e")
    case True
    then have 2: "construct_cycle_add_edge_nodes (e # E') a C = (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then obtain u where u_def: "u = get_second (e-{a})" by auto
    then show ?thesis proof(cases "u\<in>C")
      case True
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C =  [(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C" using 2 u_def by simp
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge a e 0)" using assms by simp
        have "\<exists>p1 p2.  p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes (e#E') a C"  
          using Cons by blast
        then obtain p1 p2 where p1p2_def:  "p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes (e#E') a C" 
          by blast
        have "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C)" 
          using True 4 3 Cons by simp
        then have "v2 = hd (tl (construct_cycle_add_edge_nodes (e#E') a C))" using 3 Cons True 4
          by (metis (mono_tags, lifting) append_Cons sublist3_hd_lists list.sel(3))
        then have "v2 = Edge a e 1" 
          using 3 Cons True by simp
        then show ?thesis using assms 3 by simp
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    next
      case False
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]
         @ construct_cycle_add_edge_nodes E' a C" 
        using 2 u_def \<open>a\<in> e\<close> by smt
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge a e 0) \<or> v1 = Edge u e 0" using assms by simp
        then have 6: "v1 \<noteq> last ([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])" by auto
        have 7: "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C) \<or> v1 = hd (tl(construct_cycle_add_edge_nodes (e#E') a C))"
          using True 4 3 Cons by simp
        then have "v2 = hd (tl (construct_cycle_add_edge_nodes (e#E') a C)) 
              \<or> v2 = hd (tl  (tl(construct_cycle_add_edge_nodes (e#E') a C)))" proof(cases "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C)")
          case True
          then have "v2 = hd (tl (construct_cycle_add_edge_nodes (e#E') a C))" 
            using 3 Cons True 4 sublist_v1_hd_v2_hd_tl by fast
          then show ?thesis ..
        next
          case False
          then have "v1 = hd (tl(construct_cycle_add_edge_nodes (e#E') a C))" using 7 by simp
          then have "v2 = hd (tl (tl(construct_cycle_add_edge_nodes (e#E') a C)))" 
            using 3 Cons True 4 sublist_v1_hd_v2_hd_tl 
            by (metis (no_types, lifting) False distinct_tl hd_append list.discI list.sel(1) tl_append2)  
          then show ?thesis ..
        qed
        then have 8: "v2 = Edge u e 0 \<or> v2 = Edge u e 1" 
          using 3 Cons True by simp
        have 9: "v1 = Edge a e 0" proof (cases "v1 = Edge a e 0")
          case True
          then show ?thesis by auto
        next
          case False
          then have 9: "v1 = Edge u e 0" 
            using 4 by auto
          then have "v2 = Edge u e 1" proof -
            have "v1 = hd (tl(construct_cycle_add_edge_nodes (e#E') a C))" 
              using 9 3 by simp 
            then have "v2 = hd (tl (tl(construct_cycle_add_edge_nodes (e#E') a C)))" 
              using 3 Cons True 4 sublist_v1_hd_v2_hd_tl 
              by (metis (no_types, lifting) False distinct_tl hd_append list.discI list.sel(1) tl_append2)  
            then show ?thesis 
              using 9 Cons.prems(1) Cons.prems(4) 8 sublist_implies_in_set_a by fastforce 
          qed
          then show ?thesis using Cons by auto
        qed
        then have "v2 = Edge u e 0" proof -
          have "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C)" 
            using 9 3 by simp
          then have "v2 = hd (tl ((construct_cycle_add_edge_nodes (e#E') a C)))" 
            using 3 Cons True 4 sublist_v1_hd_v2_hd_tl 
            by metis  
          then show ?thesis 
            using 8 assms(3) by auto 
        qed
        then show ?thesis using 9 
          using assms sublist_implies_in_set_a by fastforce 
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    qed
  next
    case False
    then have "construct_cycle_add_edge_nodes (e # E') a C = construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then show ?thesis using Cons by simp
  qed
qed

lemma helper_for_helper_arcs_explicit_Cover_Edge0_Edge1: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 1"
    "distinct (construct_cycle_add_edge_nodes E' a C)" 
  shows "e1 = e2 \<and> u1 = u2"
  using assms proof(induction E')
  case Nil
  then show ?case by simp
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e # E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by simp 
  then show ?case proof (cases "a\<in>e")
    case True
    then have 2: "construct_cycle_add_edge_nodes (e # E') a C = (let u = (get_second (e-{a})) in 
    (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then obtain u where u_def: "u = get_second (e-{a})" by auto
    then show ?thesis proof(cases "u\<in>C")
      case True
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C =  [(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C" using 2 u_def by simp
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge a e 0)" using assms by simp
        have "\<exists>p1 p2.  p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes (e#E') a C"  
          using Cons by blast
        then obtain p1 p2 where p1p2_def:  "p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes (e#E') a C" 
          by blast
        have "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C)" 
          using True 4 3 Cons by simp
        then have "v2 = hd (tl (construct_cycle_add_edge_nodes (e#E') a C))" using 3 Cons True 4
          by (metis (mono_tags, lifting) append_Cons sublist3_hd_lists list.sel(3))
        then have "v2 = Edge a e 1" 
          using 3 Cons True by simp
        then show ?thesis using assms 3 4 by simp
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    next
      case False
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]
         @ construct_cycle_add_edge_nodes E' a C" 
        using 2 u_def \<open>a\<in> e\<close> by smt
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge a e 0) \<or> v1 = Edge u e 0" using assms by simp
        then have 6: "v1 \<noteq> last ([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])" by auto
        have 7: "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C) \<or> v1 = hd (tl(construct_cycle_add_edge_nodes (e#E') a C))"
          using True 4 3 Cons by simp
        then show ?thesis using assms 3 4 proof(cases "v1 = hd (construct_cycle_add_edge_nodes (e#E') a C)")
          case True
          then have "v2 = hd (tl (construct_cycle_add_edge_nodes (e#E') a C))" 
            using 3 Cons True 4 sublist_v1_hd_v2_hd_tl by fast
          then have "v2 = Edge u e 0" 
            using 3 by simp 
          then show ?thesis 
            using Cons by auto
        next
          case False
          then have 5: "v1 = hd (tl(construct_cycle_add_edge_nodes (e#E') a C))" using 7 by simp
          then have 6: "v1 = Edge u e 0" using 3 by simp
          then have "v2 = hd (tl (tl(construct_cycle_add_edge_nodes (e#E') a C)))" 
            using 3 Cons True 4 sublist_v1_hd_v2_hd_tl 5
            by (metis (no_types, lifting) False distinct_tl hd_append list.discI list.sel(1) tl_append2)  
          then have "v2 = Edge u e 1" using 3 by simp
          then show ?thesis 
            using 6 Cons by fast
        qed 
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    qed
  next
    case False
    then have "construct_cycle_add_edge_nodes (e # E') a C = construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then show ?thesis using Cons by simp
  qed
qed

lemma helper_for_helper_arcs_explicit_Cover_Edge1_Edge1: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 1"
    "distinct (construct_cycle_add_edge_nodes E' a C)" 
  shows "e1 = e2 \<and> u1 \<noteq> u2"
  using assms proof(induction E')
  case Nil
  then show ?case by simp
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e # E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by simp 
  then show ?case proof (cases "a\<in>e")
    case True
    then have 2: "construct_cycle_add_edge_nodes (e # E') a C = (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then obtain u where u_def: "u = get_second (e-{a})" by auto
    then show ?thesis proof(cases "u\<in>C")
      case True
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C =  [(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C" using 2 u_def by simp
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge a e 1)" using assms by simp
        then have 7: "v1 = last [(Edge a e 0), (Edge a e 1)]" "v1 \<in> set [(Edge a e 0), (Edge a e 1)]" by simp+
        then have 5: "v2 = hd (construct_cycle_add_edge_nodes E' a C)" using 3 4
          by (metis (mono_tags, lifting) Cons.prems(1) Cons.prems(4) Cons_eq_appendI sublist_set_last_ls1 last_ConsL list.set_intros(1))
        then have 6: "v2 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using Cons True sublist_set_last_ls1_1_1 3 4 7
          by fast 
        then show ?thesis proof (cases "(construct_cycle_add_edge_nodes E' a C) = []")
          case True
          then show ?thesis using 6 by simp
        next
          case False
          then show ?thesis using hd_construct_cycle_not_Edge1 5 Cons 
            by metis 
        qed
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    next
      case False
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]
         @ construct_cycle_add_edge_nodes E' a C" 
        using 2 u_def \<open>a\<in> e\<close> by smt
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge u e 1) \<or> v1 = Edge a e 1" using assms by simp
        then show ?thesis proof 
          assume v1_def: "v1 = (Edge u e 1)"
          then have "v1 = hd (tl (tl ([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])))" by simp
          then have "v1 \<noteq> last [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" using v1_def  
            using "3" Cons.prems(4) by auto
          then have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]"  
            using 3 Cons sublist_set_ls1_4 
            by (metis (no_types, hide_lams) True hc_node.inject(2) v1_def) 
          then have 5: "v2 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" 
            using sublist_implies_in_set(2) by force          
          then have v2_def: "v2 = Edge a e 1" "a \<noteq> u" proof -
            have "v2 = Edge u e 1 \<or> v2 = Edge a e 1" 
              using 5 Cons by simp
            then show "v2 = Edge a e 1" "a \<noteq> u"
              using Cons v1_def sublist_implies_in_set_a
              by metis+
          qed
          then show "e1 = e2 \<and> u1 \<noteq> u2" 
            using v1_def Cons by fastforce 
        next
          assume "v1 = Edge a e 1"
          then have 7: "v1 = last [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" 
            "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" by simp+
          then have 5: "v2 = hd (construct_cycle_add_edge_nodes E' a C)"
            using 3 4 Cons sublist_set_last_ls1_1 by fast 
          then have 6: "v2 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
            using Cons True sublist_set_last_ls1_1_1 3 4 7 by fast
          then show ?thesis proof (cases "(construct_cycle_add_edge_nodes E' a C) = []")
            case True
            then show ?thesis using 6 by simp
          next
            case False
            then show ?thesis using hd_construct_cycle_not_Edge1 5 Cons 
              by metis 
          qed
        qed
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    qed
  next
    case False
    then have "construct_cycle_add_edge_nodes (e # E') a C = construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then show ?thesis using Cons by simp
  qed
qed

lemma helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0:
  assumes "(construct_cycle_add_edge_nodes E' a C) \<noteq> []"
  shows "\<exists>e. hd (construct_cycle_add_edge_nodes E' a C) = Edge a e 0"
  using assms apply(induction E')apply(auto) 
   apply (smt list.sel(1)) 
  by (smt hd_append2 list.discI list.sel(1))  

lemma helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0b:
  assumes "(construct_cycle_add_edge_nodes E' a C) \<noteq> []"
  shows "\<exists>e. last (construct_cycle_add_edge_nodes E' a C) = Edge a e 1"
  using assms apply(induction E')apply(auto)
  by (smt One_nat_def append.right_neutral last_ConsL last_ConsR last_appendR list.discI)  

lemma helper6_for_helper_arcs_explicit_Cover_Edge0_Edge0:
  assumes "\<exists>p1 p2. p1 @ v1 # v2 # p2 = L"
  shows "\<exists>i. L!i = v1 \<and> L!(i+1) = v2 \<and> (i+1) < length L"
  using assms apply(induction L) apply(auto) 
  by (metis Suc_lessD append_self_conv2 length_Cons less_Suc_eq_0_disj list.sel(3) nth_Cons_0 nth_tl tl_append2) 

lemma helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1:
  assumes "e \<in> set E'" "a\<in> e"
  shows "Edge a e 1 \<in> set (construct_cycle_add_edge_nodes E' a C)"
  using assms Edge_nodes_in_construct_edge(2) by fast

lemma helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1b:
  assumes "e \<in> set E'" "a\<in> e"
  shows "Edge a e 0 \<in> set (construct_cycle_add_edge_nodes E' a C)"
  using assms Edge_nodes_in_construct_edge(1) by fast




lemma helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0:
  assumes "e1 = E'!i" "e2 = E'!j" "i<j" "a\<in> e1" "a\<in> e2" "i<length E'" "j<length E'" 
  shows "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 1 \<and> i1< j1
  \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)"  
  using assms proof(induction E' arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e # E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by simp 
  then show ?case proof (cases "a\<in>e")
    case True (*a\<in> e*)
    then have 2: "construct_cycle_add_edge_nodes (e # E') a C = (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then obtain u where u_def: "u = get_second (e-{a})" by auto
    then show ?thesis proof(cases "u\<in>C")
      case True
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C =  [(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C" using 2 u_def by simp
      then show ?thesis proof(cases "Edge a e1 1 \<in> set [(Edge a e 0), (Edge a e 1)]")
        case True
        then have 4: "e1 = e" using assms by simp
        then obtain i1 where i1_def: "i1 = (1::nat)" by auto
        then have i1_Edge: "(construct_cycle_add_edge_nodes (e#E') a C)! i1 = Edge a e1 1" using 3 4 by simp
        have "e2 \<in> set E'" using Cons indices_length_set_ls2_only_append by auto 
        then have e2_set_1: "Edge a e2 1 \<in> set (construct_cycle_add_edge_nodes (E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 by fast
        then have "Edge a e2 1 \<in> set (construct_cycle_add_edge_nodes (e#E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1b by simp
        then have "\<exists>j1. (construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 1 
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" using x_in_implies_exist_index e2_set_1 by metis
        then obtain j1 where "(construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 1 
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" by auto
        then have j1_def: "(construct_cycle_add_edge_nodes (e#E') a C)! (j1+2) = Edge a e2 1 
          \<and> (j1+2) < length (construct_cycle_add_edge_nodes (e#E') a C)" using 3 by simp
        then have "i1<(j1+2)" using i1_def by simp  
        then show ?thesis using i1_def j1_def i1_Edge by fastforce
      next
        case False
        then have 10: "e1 \<noteq> e" by auto
        then have  i_def: "(e#E')!i = e1  \<and> i<length (e#E') "  using Cons by simp
        then have 11: "i> 0" using 10 by auto
        then have i_fin: "(E')!(i-1) = e1  \<and> (i-1)<length (E')" using i_def by auto

        then have j_def: "(e#E')!j = e2  \<and> j<length (e#E') \<and> i<j"  using Cons by auto
        then have "j> 1" using 11 by auto
        then have j_fin: "(E')!(j-1) = e2  \<and> (j-1)<length (E') \<and> i-1 < j-1" using i_def j_def  by auto
        then have "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 1 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" using Cons  i_fin j_fin 
          by blast 
        then obtain i1 j1 where "(construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
        \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 1 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" by auto
        then have "([(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) ! (i1+2) = Edge a e1 1" 
          "([(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) !(j1+2) = Edge a e2 1"
          "(i1+2<j1+2)"
          "j1+2 < length ([(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C)" 
          by auto
        then show ?thesis using 3 by metis
      qed
    next
      case False
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]
         @ construct_cycle_add_edge_nodes E' a C" 
        using 2 u_def \<open>a\<in> e\<close> by smt
      then show ?thesis proof(cases "Edge a e1 1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have 4: "e1 = e" by auto
        then obtain i1 where i1_def: "i1 = (3::nat)" by auto
        then have i1_Edge: "(construct_cycle_add_edge_nodes (e#E') a C)! i1 = Edge a e1 1" using 3 4 by simp
        have "e2 \<in> set E'" using Cons indices_length_set_ls2_only_append by auto 
        then have e2_set_1: "Edge a e2 1 \<in> set (construct_cycle_add_edge_nodes (E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 by fast
        then have "Edge a e2 1 \<in> set (construct_cycle_add_edge_nodes (e#E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 by simp
        then have "\<exists>j1. (construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 1 
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" using x_in_implies_exist_index e2_set_1 by metis
        then obtain j1 where "(construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 1 
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" by auto
        then have j1_def: "(construct_cycle_add_edge_nodes (e#E') a C)! (j1+4) = Edge a e2 1 
          \<and> (j1+4) < length (construct_cycle_add_edge_nodes (e#E') a C)" using 3 by simp
        then have "i1<(j1+4)" using i1_def by simp  
        then show ?thesis using i1_def j1_def i1_Edge by fastforce 
      next
        case False
        then have 10: "e1 \<noteq> e" by auto
        then have  i_def: "(e#E')!i = e1  \<and> i<length (e#E') "  using Cons by simp
        then have 11: "i> 0" using 10 by auto
        then have i_fin: "(E')!(i-1) = e1  \<and> (i-1)<length (E')" using i_def by auto

        then have j_def: "(e#E')!j = e2  \<and> j<length (e#E') \<and> i<j"  using Cons by auto
        then have "j> 1" using 11 by auto
        then have j_fin: "(E')!(j-1) = e2  \<and> (j-1)<length (E') \<and> i-1 < j-1" using i_def j_def  by auto
        then have "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
          \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 1 \<and> i1< j1
          \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" using Cons  i_fin j_fin 
          by blast 
        then obtain i1 j1 where "(construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
        \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 1 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" by auto
        then have "([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) ! (i1+4) = Edge a e1 1" 
          "([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) !(j1+4) = Edge a e2 1"
          "(i1+4<j1+4)"
          "j1+4 < length ([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C)" 
          by auto 
        then show ?thesis using 3 by metis
      qed
    qed
  next
    case False
    then have 3: "construct_cycle_add_edge_nodes (e # E') a C = construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    have 10: "e \<noteq> e1" using Cons False by blast 
    then have  i_def: "(e#E')!i = e1  \<and> i<length (e#E') "  using Cons by simp
    then have 11: "i> 0" using 10 by auto 
    then have i_fin: "(E')!(i-1) = e1  \<and> (i-1)<length (E')" using i_def by auto

    then have j_def: "(e#E')!j = e2  \<and> j<length (e#E') \<and> i<j"  using Cons by auto
    then have "j> 1" using 11 by auto
    then have j_fin: "(E')!(j-1) = e2  \<and> (j-1)<length (E') \<and> i-1 < j-1" using i_def j_def  by auto
    then have "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 1 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" using Cons  i_fin j_fin 
      by blast 
    then show ?thesis using Cons  
      using 3 by auto  
  qed
qed


lemma helper4_for_helper_arcs_explicit_Cover_Edge0_Edge0:
  assumes "e1 = E'!i" "e2 = E'!j" "i<j" "a\<in> e1" "a\<in> e2" "i<length E'" "j<length E'"
  shows "\<exists>i1 j1. (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1
    \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" 
  using assms proof(induction E' arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e # E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by simp 
  then show ?case proof (cases "a\<in>e")
    case True (*a\<in> e*)
    then have 2: "construct_cycle_add_edge_nodes (e # E') a C = (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then obtain u where u_def: "u = get_second (e-{a})" by auto
    then show ?thesis proof(cases "u\<in>C")
      case True
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C =  [(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C" using 2 u_def by simp
      then show ?thesis proof(cases "Edge a e1 1 \<in> set [(Edge a e 0), (Edge a e 1)]")
        case True
        then have 4: "e1 = e" using assms by simp
        then obtain i1 where i1_def: "i1 = (1::nat)" by auto
        then have i1_Edge: "(construct_cycle_add_edge_nodes (e#E') a C)! i1 = Edge a e1 1" using 3 4 by simp
        have "e2 \<in> set E'" using Cons indices_length_set_ls2_only_append by auto 
        then have e2_set_1: "Edge a e2 0 \<in> set (construct_cycle_add_edge_nodes (E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1b by metis
        then have "Edge a e2 0 \<in> set (construct_cycle_add_edge_nodes (e#E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 by simp
        then have "\<exists>j1. (construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 0 
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" using x_in_implies_exist_index e2_set_1 by metis
        then obtain j1 where "(construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 0
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" by auto
        then have j1_def: "(construct_cycle_add_edge_nodes (e#E') a C)! (j1+2) = Edge a e2 0 
          \<and> (j1+2) < length (construct_cycle_add_edge_nodes (e#E') a C)" using 3 by simp
        then have "i1<(j1+2)" using i1_def by simp  
        then show ?thesis using i1_def j1_def i1_Edge by fastforce
      next
        case False
        then have 10: "e1 \<noteq> e" by auto
        then have  i_def: "(e#E')!i = e1  \<and> i<length (e#E') "  using Cons by simp
        then have 11: "i> 0" using 10 by auto
        then have i_fin: "(E')!(i-1) = e1  \<and> (i-1)<length (E')" using i_def by auto

        then have j_def: "(e#E')!j = e2  \<and> j<length (e#E') \<and> i<j"  using Cons by auto
        then have "j> 1" using 11 by auto
        then have j_fin: "(E')!(j-1) = e2  \<and> (j-1)<length (E') \<and> i-1 < j-1" using i_def j_def  by auto
        then have "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
          \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1
          \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" using Cons  i_fin j_fin 
          by blast 
        then obtain i1 j1 where "(construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
        \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" by auto
        then have "([(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) ! (i1+2) = Edge a e1 1" 
          "([(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) !(j1+2) = Edge a e2 0"
          "(i1+2<j1+2)"
          "j1+2 < length ([(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C)" 
          by auto
        then show ?thesis using 3 by metis
      qed
    next
      case False
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]
         @ construct_cycle_add_edge_nodes E' a C" 
        using 2 u_def \<open>a\<in> e\<close> by smt
      then show ?thesis proof(cases "Edge a e1 1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have 4: "e1 = e" by auto
        then obtain i1 where i1_def: "i1 = (3::nat)" by auto
        then have i1_Edge: "(construct_cycle_add_edge_nodes (e#E') a C)! i1 = Edge a e1 1" using 3 4 by simp
        have "e2 \<in> set E'" using Cons indices_length_set_ls2_only_append by auto 
        then have e2_set_1: "Edge a e2 0 \<in> set (construct_cycle_add_edge_nodes (E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1b by metis
        then have "Edge a e2 0 \<in> set (construct_cycle_add_edge_nodes (e#E') a C)" using Cons helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 by simp
        then have "\<exists>j1. (construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 0
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" using x_in_implies_exist_index e2_set_1 by metis
        then obtain j1 where "(construct_cycle_add_edge_nodes (E') a C)! j1 = Edge a e2 0
          \<and> j1 < length (construct_cycle_add_edge_nodes (E') a C)" by auto
        then have j1_def: "(construct_cycle_add_edge_nodes (e#E') a C)! (j1+4) = Edge a e2 0 
          \<and> (j1+4) < length (construct_cycle_add_edge_nodes (e#E') a C)" using 3 by simp
        then have "i1<(j1+4)" using i1_def by simp  
        then show ?thesis using i1_def j1_def i1_Edge by fastforce 
      next
        case False
        then have 10: "e1 \<noteq> e" by auto
        then have  i_def: "(e#E')!i = e1  \<and> i<length (e#E') "  using Cons by simp
        then have 11: "i> 0" using 10 by auto
        then have i_fin: "(E')!(i-1) = e1  \<and> (i-1)<length (E')" using i_def by auto

        then have j_def: "(e#E')!j = e2  \<and> j<length (e#E') \<and> i<j"  using Cons by auto
        then have "j> 1" using 11 by auto
        then have j_fin: "(E')!(j-1) = e2  \<and> (j-1)<length (E') \<and> i-1 < j-1" using i_def j_def  by auto
        then have "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
          \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1
          \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" using Cons  i_fin j_fin 
          by blast 
        then obtain i1 j1 where "(construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
        \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" by auto
        then have "([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) ! (i1+4) = Edge a e1 1" 
          "([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C) !(j1+4) = Edge a e2 0"
          "(i1+4<j1+4)"
          "j1+4 < length ([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C)" 
          by auto 
        then show ?thesis using 3 by metis
      qed
    qed
  next
    case False
    then have 3: "construct_cycle_add_edge_nodes (e # E') a C = construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    have 10: "e \<noteq> e1" using Cons False by blast 
    then have  i_def: "(e#E')!i = e1  \<and> i<length (e#E') "  using Cons by simp
    then have 11: "i> 0" using 10 by auto 
    then have i_fin: "(E')!(i-1) = e1  \<and> (i-1)<length (E')" using i_def by auto

    then have j_def: "(e#E')!j = e2  \<and> j<length (e#E') \<and> i<j"  using Cons by auto
    then have "j> 1" using 11 by auto
    then have j_fin: "(E')!(j-1) = e2  \<and> (j-1)<length (E') \<and> i-1 < j-1" using i_def j_def  by auto
    then have "\<exists>i1 j1 . (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
      \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1
        \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" using Cons  i_fin j_fin 
      by blast 
    then show ?thesis using Cons  
      using 3 by auto  
  qed
qed

lemma helper3_for_helper_arcs_explicit_Cover_Edge0_Edge0:
  assumes "v1 = Edge a (E' ! i) 1" "v2 = Edge a (E' ! j) 0" "distinct (construct_cycle_add_edge_nodes E' a C)" "j < length E'"
    "\<exists>p1 p2. p1 @ v1 # v2 # p2 = construct_cycle_add_edge_nodes E' a C" 
    "i < i'" "a \<in> E' ! i'"
    "i' < j"
  shows False
proof -
  obtain e1 where e1_def: "e1 = (E' ! i)" by auto
  obtain e2 where e2_def: "e2 = (E'!j)" by auto
  obtain e3 where e3_def: "e3 = (E'!i')" by auto
  have "\<exists>i. (construct_cycle_add_edge_nodes E' a C)!i = v1 \<and> (construct_cycle_add_edge_nodes E' a C)!(i+1) = v2 \<and> (i+1)< length (construct_cycle_add_edge_nodes E' a C)" 
    using helper6_for_helper_arcs_explicit_Cover_Edge0_Edge0 assms by fast
  then obtain i where i_def: "(construct_cycle_add_edge_nodes E' a C)!i = v1 
    \<and> (construct_cycle_add_edge_nodes E' a C)!(i+1) = v2 \<and> (i+1)< length (construct_cycle_add_edge_nodes E' a C)"
    by auto
  have "a\<in> e1" using e1_def assms 
    by (metis (full_types) in_set_conv_decomp node_of_edge_construction_contains_a) 
  then have "\<exists>i1 j1. (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e3 1 
    \<and> i1< j1 \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)"
    using helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0 assms e1_def e2_def e3_def 
    by force  
  then obtain i1 i'1 where i'1:  
    "(construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e1 1 
    \<and> (construct_cycle_add_edge_nodes E' a C)! i'1 = Edge a e3 1 
    \<and> i1< i'1 \<and> i'1 < length (construct_cycle_add_edge_nodes E' a C)"
    by auto
  have "v2 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
    using assms i_def nth_mem by blast   
  then have "a\<in> e2" using e2_def assms node_of_edge_construction_contains_a 
    by fast 
  then have "\<exists>i1 j1. (construct_cycle_add_edge_nodes E' a C)! i1 = Edge a e3 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i1< j1\<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" 
    using helper4_for_helper_arcs_explicit_Cover_Edge0_Edge0 assms e1_def e2_def e3_def by force
  then obtain i'2 j1 where i'2: 
    "(construct_cycle_add_edge_nodes E' a C)! i'2 = Edge a e3 1 \<and> (construct_cycle_add_edge_nodes E' a C)! j1 = Edge a e2 0 \<and> i'2< j1\<and>
         j1 < length (construct_cycle_add_edge_nodes E' a C)"
    by auto
  then have "(construct_cycle_add_edge_nodes E' a C)! i'2 = (construct_cycle_add_edge_nodes E' a C)! i'1" 
    using i'1 by simp  
  then have "i'1 = i'2" 
    using assms i'1 i'2 distinct_same_indices by fastforce   
  then have "i1<i'1" "i'1<j1" using i'1 i'2 by simp+
  then have con: "i1<j1+1" by simp
  have 1: "Edge a e1 1 = construct_cycle_add_edge_nodes E' a C ! i1" 
    by (simp add: i'1) 
  have "Edge a e1 1 = construct_cycle_add_edge_nodes E' a C ! i" 
    using i_def assms e1_def by simp
  then have 3: "i1 = i" 
    using 1 assms distinct_same_indices i'1 i_def
    by fastforce  
  have 2: "Edge a e2 0 = construct_cycle_add_edge_nodes E' a C ! j1" 
    by (simp add: i'2) 
  have "Edge a e2 0 = construct_cycle_add_edge_nodes E' a C ! (i+1)" 
    using i_def assms e2_def by simp
  then have 4: "j1 = (i+1)" 
    using 1 assms distinct_same_indices i'2 i_def
    by fastforce 
  then show ?thesis 
    using i_def 3 4 \<open>i'1 < j1\<close> \<open>i1 < i'1\<close> by linarith
qed


lemma helper2_for_helper_arcs_explicit_Cover_Edge0_Edge0_1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge a e1 1" "v2 = Edge a e2 0"
    "distinct (construct_cycle_add_edge_nodes E' a C)" "E'!i = e1" "E' ! j = e2" "i<length E'" "j<length E'" "distinct E'"
  shows "i<j"
  using assms proof(induction E' arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e#E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by auto
  then show ?case proof(cases "a \<in> e")
    case True
    then have 1: "construct_cycle_add_edge_nodes (e#E') a C = 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C"
      by simp
    obtain u where u_def: "u = get_second (e -{a})"
      by simp
    then show ?thesis proof(cases "u \<in> C")
      case True
      then have 1: "construct_cycle_add_edge_nodes (e#E') a C = 
         [(Edge a e 0), (Edge a e 1)] @ construct_cycle_add_edge_nodes E' a C"
        using 1 u_def by simp
      then have "v1 = Edge a e 1 \<or> v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" using Cons 
        by (metis helper5_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 node_of_edge_construction_contains_a nth_mem set_ConsD sublist_implies_in_set(1)) 
      then show ?thesis proof
        assume "v1 = Edge a e 1" 
        then have 2: "v1 = last [Edge a e 0, Edge a e 1]" by simp
        then have "v2 = hd (construct_cycle_add_edge_nodes E' a C)"
          by (metis "1" Cons.prems(1) Cons.prems(4) \<open>v1 = Edge a e 1\<close> append_Cons last.simps list.set_intros(1) sublist_set_last_ls1_3)
        have "e1 = e" using 2 Cons by simp
        then have "i = 0" using 2 Cons 
          by (metis length_greater_0_conv list.discI nth_Cons_0 nth_eq_iff_index_eq)
        have "i \<noteq> j" using Cons 
          by (metis "1" "2" Cons_eq_appendI \<open>e1 = e\<close> \<open>i = 0\<close> \<open>v1 = Edge a e 1\<close> \<open>v2 = hd (construct_cycle_add_edge_nodes E' a C)\<close> distinct.simps(2) distinct_length_2_or_more distinct_sublist_last_first_of_sublist_false eq_Nil_appendI hd_in_set sublist_def) 
        then show "i < j" 
          by (simp add: \<open>i = 0\<close>) 
      next
        assume "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)"
        then have 2: "v1 \<notin> set [Edge a e 0, Edge a e 1]" using 1 Cons
          by (metis distinct.simps(2) distinct_singleton only_previous_edges_in_new_edges set_ConsD)  
        then have e1: "e1 \<noteq> e"
          by (simp add: assms(2)) 
        have e2: "e2 \<noteq> e" 
          by (smt "1" Cons.prems(1) Cons.prems(4) \<open>v1 \<in> set (construct_cycle_add_edge_nodes E' a C)\<close> append_Cons append_self_conv2 assms(3) distinct.simps(2) sublist_set_ls2_2) 
        then have 4: "E'!(i-1) = e1" "E'!(j-1) = e2" 
           apply (metis Cons.prems(5) e1 nth_non_equal_first_eq) 
          by (metis Cons.prems(6) e2 nth_non_equal_first_eq)   
        have 6: "(i-1) < length E'" "j-1 < length E'"
          using Cons e1 proof -
          have "i < length (e#E')"  "j < length (e#E')" using Cons by auto
          then have "length E' = length (e#E') -1" by simp
          have "j >0" using e2 Cons 
            by (metis nth_non_equal_first_eq)
          have "i > 0" using e1 Cons 
            by (metis nth_non_equal_first_eq) 
          then show "(i-1) < length E'" "(j-1) < length E'"
            using Cons.prems(7) \<open>length E' = length (e # E') - 1\<close> apply(linarith) 
            using Cons.prems(8) \<open>0 < j\<close> by auto  
        qed
        have 5: "distinct (construct_cycle_add_edge_nodes E' a C)" using Cons 1 by simp
        have "sublist [v1, v2] (construct_cycle_add_edge_nodes (e#E') a C)" using sublist_def Cons by metis
        then have "sublist [v1, v2] (construct_cycle_add_edge_nodes E' a C)"
          using sublist_append_not_in_first 1 2 by metis 
        then have "(i-1) < (j-1)" using Cons 2 4 5 6 
          by (meson distinct.simps(2) sublist_def) 
        then show ?thesis using Cons 2 
          by linarith
      qed
    next
      case False
      then have 1: "construct_cycle_add_edge_nodes (e#E') a C = 
         [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] @ construct_cycle_add_edge_nodes E' a C"
        using u_def 1 
        by smt 
      then have or: "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] \<or> v1 \<in> set (construct_cycle_add_edge_nodes E' a C)"
        using Cons.prems(1) sublist_v1_in_subsets by fastforce 
      show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have "v1 = Edge a e 1" proof -
          have "v1 = Edge u e 1 \<or> v1 = Edge a e 1" 
            using Cons True by auto
          then show ?thesis 
            using assms(2) by blast
        qed
        then have "i = 0" 
          by (metis Cons.prems(5) Cons.prems(7) Cons.prems(9) assms(2) hc_node.inject(2) length_greater_0_conv list.distinct(1) nth_Cons_0 nth_eq_iff_index_eq) 
        have "v1 = last [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" 
          using \<open>v1 = Edge a e 1\<close> by auto 
        then have "v2 = hd (construct_cycle_add_edge_nodes E' a C)"
          using Cons 
          by (metis "1" True sublist_set_last_ls1_1) 
        have "i \<noteq> j" using Cons 
          by (metis "1" \<open>i = 0\<close> \<open>v1 = Edge a e 1\<close> \<open>v1 = last [Edge a e 0, Edge u e 0, Edge u e 1, Edge a e 1]\<close> \<open>v2 = hd (construct_cycle_add_edge_nodes E' a C)\<close> append_Nil2 distinct.simps(2) distinct_sublist_last_first_of_sublist_false hd_in_set nth_Cons_0 only_previous_edges_in_new_edges sublist_def) 
        then show ?thesis 
          by (simp add: \<open>i = 0\<close>) 
      next
        case False
        then have v1_in: "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)"
          using or by simp
        then have e1: "e1 \<noteq> e" using False
          by (simp add: assms(2)) 
        have e2: "e2 \<noteq> e" 
          by (metis "1" Cons.prems(1) Cons.prems(4) Cons.prems(9) assms(3) distinct.simps(2) only_previous_edges_in_new_edges sublist_set_ls2_1 v1_in) 
        then have 4: "E'!(i-1) = e1" "E'!(j-1) = e2" 
           apply (metis Cons.prems(5) e1 nth_non_equal_first_eq) 
          by (metis Cons.prems(6) e2 nth_non_equal_first_eq)   
        have 6: "(i-1) < length E'" "j-1 < length E'"
          using Cons e1 proof -
          have "i < length (e#E')"  "j < length (e#E')" using Cons by auto
          then have "length E' = length (e#E') -1" by simp
          have "j >0" using e2 Cons 
            by (metis nth_non_equal_first_eq)
          have "i > 0" using e1 Cons 
            by (metis nth_non_equal_first_eq) 
          then show "(i-1) < length E'" "(j-1) < length E'"
            using Cons.prems(7) \<open>length E' = length (e # E') - 1\<close> apply(linarith) 
            using Cons.prems(8) \<open>0 < j\<close> by auto  
        qed
        have 5: "distinct (construct_cycle_add_edge_nodes E' a C)" using Cons 1 by simp
        have "sublist [v1, v2] (construct_cycle_add_edge_nodes (e#E') a C)" using sublist_def Cons by metis
        then have "sublist [v1, v2] (construct_cycle_add_edge_nodes E' a C)"
          using sublist_append_not_in_first 1 
          by (metis False)  
        then have "(i-1) < (j-1)" using Cons False 4 5 6 
          by (meson distinct.simps(2) sublist_def) 
        then show ?thesis using Cons 
          by linarith
      qed
    qed
  next
    case False
    then have 2: "construct_cycle_add_edge_nodes (e#E') a C 
      = (construct_cycle_add_edge_nodes E' a C)" 
      by auto
    then have e: "e \<noteq> e1" "e\<noteq> e2"
      using Cons.prems False assms node_of_edge_construction_contains_a sublist_implies_in_set apply fastforce
      using Cons.prems(1) False assms(3) node_of_edge_construction_contains_a sublist_implies_in_set(2) by fastforce 
    then have 4: "E'!(i-1) = e1" "E'!(j-1) = e2"
       apply(metis Cons.prems(5) nth_non_equal_first_eq)
      using e by(metis Cons.prems(6) nth_non_equal_first_eq)
    have 6: "(i-1) < length E'" "j-1 < length E'"
      using Cons 
      by (metis "2" One_nat_def Suc_length_conv Suc_pred construct_cycle_add_edge_nodes.simps(1) length_greater_0_conv less_diff_conv less_imp_diff_less linorder_neqE_nat list.distinct(1) list.set_cases n_not_Suc_n not_add_less1 not_less_eq sublist_implies_in_set(1))+ 
    have 3: "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
      using Cons 2 by metis
    have 5: "distinct (construct_cycle_add_edge_nodes E' a C)" using Cons 2 by argo
    then have "(i-1) < (j-1)" using Cons 2 3 4 5 6 by(auto) 
    then show ?thesis using Cons 2 
      by linarith
  qed
qed




lemma helper2_for_helper_arcs_explicit_Cover_Edge0_Edge0:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge a e1 1" "v2 = Edge a e2 0"
    "distinct (construct_cycle_add_edge_nodes E' a C)" "E'!i = e1" "E' ! j = e2" "i<length E'" "j<length E'" "distinct E'"
  shows "(\<forall>i'>i. a \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j)" "i<j" 
  using assms apply(auto)[1] using helper3_for_helper_arcs_explicit_Cover_Edge0_Edge0 assms  
  apply metis using helper2_for_helper_arcs_explicit_Cover_Edge0_Edge0_1 assms 
  by metis 

lemma helper8_for_helper_arcs_explicit_Cover_Edge0_Edge0: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 0"
    "distinct (construct_cycle_add_edge_nodes E' a C)" 
  shows "u1 = u2 \<and> u1 =a"
  using assms proof(induction E')
  case Nil
  then show ?case by simp
next
  case (Cons e E')
  have 1: "construct_cycle_add_edge_nodes (e # E') a C = (if a \<in> e then 
    (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C 
    else construct_cycle_add_edge_nodes E' a C)" by simp 
  then show ?case proof (cases "a\<in>e")
    case True
    then have 2: "construct_cycle_add_edge_nodes (e # E') a C = (let u = (get_second (e-{a})) in 
      (if u\<in> C then [(Edge a e 0), (Edge a e 1)] 
      else [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])) @ construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then obtain u where u_def: "u = get_second (e-{a})" by auto
    then show ?thesis proof(cases "u\<in>C")
      case True
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C =  [(Edge a e 0), (Edge a e 1)] 
           @ construct_cycle_add_edge_nodes E' a C" using 2 u_def by simp
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge a e 1)" using assms by simp
        then have 7: "v1 = last [(Edge a e 0), (Edge a e 1)]" "v1 \<in> set [(Edge a e 0), (Edge a e 1)]" by simp+
        then have 5: "v2 = hd (construct_cycle_add_edge_nodes E' a C)" using 3 4
          by (metis (mono_tags, lifting) Cons.prems(1) Cons.prems(4) Cons_eq_appendI sublist_set_last_ls1 last_ConsL list.set_intros(1))
        then have 6: "v2 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using Cons True sublist_set_last_ls1_1_1 3 4 7
          by fast 
        then show ?thesis 
          by (metis "4" "5" assms(2) assms(3) helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0 distinct.simps(2) distinct_singleton hc_node.inject(2)) 
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    next
      case False
      then have 3: "construct_cycle_add_edge_nodes (e # E') a C = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]
         @ construct_cycle_add_edge_nodes E' a C" 
        using 2 u_def \<open>a\<in> e\<close> by smt
      then show ?thesis proof(cases "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]")
        case True
        then have 4: "v1 = (Edge u e 1) \<or> v1 = Edge a e 1" using assms by simp
        then show ?thesis proof 
          assume v1_def: "v1 = (Edge u e 1)"
          then have "v1 = hd (tl (tl ([(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)])))" by simp
          then have "v1 \<noteq> last [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" using v1_def  
            using "3" Cons.prems(4) by auto
          then have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]"  
            using 3 Cons sublist_set_ls1_4 
            by (metis (no_types, hide_lams) True hc_node.inject(2) v1_def) 
          then obtain p1 p2 where  p1p2_def: "p1@ [v1, v2] @ p2 = [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" 
            by auto
          then have  a: "[(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)] = [(Edge a e 0), (Edge u e 0)] @[v1] @ [Edge a e 1]"
            using v1_def by simp
          have "distinct [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" 
            using \<open>v1 \<noteq> last [Edge a e 0, Edge u e 0, Edge u e 1, Edge a e 1]\<close> v1_def by auto 
          then have "p1 = [(Edge a e 0), (Edge u e 0)]" 
            using p1p2_def a 
            by (simp add: append_eq_Cons_conv sublist_set_last_ls1_3 v1_def)  
          then have "v2 = Edge a e 1" 
            using a p1p2_def by simp 
          then show ?thesis  using Cons by auto
        next
          assume "v1 = Edge a e 1"
          then have 7: "v1 = last [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" 
            "v1 \<in> set [(Edge a e 0), (Edge u e 0), (Edge u e 1), (Edge a e 1)]" by simp+
          then have 5: "v2 = hd (construct_cycle_add_edge_nodes E' a C)"
            using 3 4 Cons sublist_set_last_ls1_1 by fast 
          then have 6: "v2 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
            using Cons True sublist_set_last_ls1_1_1 3 4 7 by fast
          then show ?thesis using 5 
            by (metis \<open>v1 = Edge a e 1\<close> assms(2) assms(3) helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0 distinct.simps(2) distinct_singleton hc_node.inject(2)) 
        qed
      next
        case False
        then have "v1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
          using 3 Cons sublist_v1_in_subsets by fast
        then have "\<exists>p1 p2. p1 @ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" 
          using 3 Cons sublist_set_ls2_3 by fast  
        then show ?thesis 
          using Cons 3 by auto 
      qed
    qed
  next
    case False
    then have "construct_cycle_add_edge_nodes (e # E') a C = construct_cycle_add_edge_nodes E' a C" 
      using 1 by simp
    then show ?thesis using Cons by auto
  qed
qed

lemma helper_for_helper_arcs_explicit_Cover_Edge1_Edge0: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E' a C" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 0"
    "distinct (construct_cycle_add_edge_nodes E' a C)" "distinct E'"
  shows "u1 = u2 \<and> (\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> i<j \<and> (\<forall>i'>i. u1 \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))"
proof -
  have 1: "u1 = u2" using assms helper8_for_helper_arcs_explicit_Cover_Edge0_Edge0 by fastforce
  have 2: "u1 = a" using assms helper8_for_helper_arcs_explicit_Cover_Edge0_Edge0 by fastforce
  then have 3: "u2 = a" using 1 by simp
  have i_def: "\<exists>i<length (E'). (E')!i = e1" using assms 
    by (metis "2" sublist_implies_in_set(1) in_set_conv_nth only_previous_edges_in_new_edges) 
  have "v2 \<in> set (construct_cycle_add_edge_nodes (E') a C)" using assms 
    by (simp add: sublist_implies_in_set(2)) 
  then have j_def: "\<exists>j<length (E'). (E')!j = e2" using assms 
    by (meson in_set_conv_nth only_previous_edges_in_new_edges)
  then have "(\<exists>i<length E'. \<exists>j<length E'. e1 = E' ! i \<and> e2 = E' ! j \<and> i<j \<and> (\<forall>i'>i. u1 \<in> E' ! i' \<longrightarrow> i' < length E' \<longrightarrow> \<not> i' < j))" 
    using i_def assms helper2_for_helper_arcs_explicit_Cover_Edge0_Edge0 1 3 
    by (metis)
  then show ?thesis using 1 by simp
qed

lemma helper_arcs_explicit_Cover_Edge0_Edge0_1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 0" "distinct (tl (construct_cycle_1 E C n C'))"
  shows "e1 = e2 \<and> u1 \<noteq> u2"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have 11: "tl (construct_cycle_1 E (a#C) n C') 
    = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have "v1 \<in> set (construct_cycle_1 E (a#C) n C')" 
    using Cons sublist_implies_in_set by fast 
  then have "v1 \<in> set (Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
    using 1 by simp
  then have "v1 = Cover n \<or> v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')"
    by simp
  then have 2: "v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
    using assms by simp
  then show ?case proof(cases "v1 \<in> set (construct_cycle_add_edge_nodes E a C')")
    case True
    then have 3: "v1 \<in> set (construct_cycle_add_edge_nodes E a C')" by simp
    then have 4: "(construct_cycle_add_edge_nodes E a C') \<noteq> []" by auto
    then show ?thesis proof (cases "v1 = last (construct_cycle_add_edge_nodes E a C')")
      case True
      then show ?thesis 
        using last_construct_cycle_not_Edge0 Cons 4 by fast
    next
      case False
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
        using sublist_append_not_eq Cons
        by (metis "1" Cover_not_in_edge_nodes True list.sel(3))
      then have 4: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C'" 
        using Cons sublist_set_ls1_4 1 3 11 False by metis
      have "distinct (construct_cycle_add_edge_nodes E a C')" using Cons by simp
      then show ?thesis 
        using Cons helper_for_helper_arcs_explicit_Cover_Edge0_Edge0 4  by metis
    qed
  next
    case False
    have 5: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
      using sublist_append_not_eq Cons
      by (metis "1" hc_node.distinct(1) list.sel(3)) 
    then have "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using 2 False by simp
    then have 6: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using Cons sublist_set_ls2_3 11 5 by fast  
    have "distinct (construct_cycle_1 E C (Suc n) C')" 
      using Cons 11 by simp
    then have "distinct (tl (construct_cycle_1 E C (Suc n) C'))" 
      by (simp add: distinct_tl)
    then show ?thesis 
      using Cons 6  by simp
  qed
qed

lemma helper_arcs_explicit_Cover_Edge0_Edge0: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 0"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "e1 = e2" "u1\<in> e1" "u2 \<in> e2" "e1 \<in> set E" "u1 \<noteq> u2"
proof -
  have v1_in_set: "v1 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fastforce
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fastforce
  then show "e1 \<in> set E" "u1 \<in> e1" "u2 \<in> e2" using assms v1_in_set in_cycle edge0_in_construct_cycle by(auto)
next
  show "e1 = e2" "u1 \<noteq> u2"
    using assms helper_arcs_explicit_Cover_Edge0_Edge0_1 by(auto)  
qed

lemma helper_arcs_explicit_Cover_Edge0_Edge1_1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 1" 
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "e1 = e2 \<and> u1 = u2"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have 11: "tl (construct_cycle_1 E (a#C) n C') 
    = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have "v1 \<in> set (construct_cycle_1 E (a#C) n C')" 
    using Cons sublist_implies_in_set by fast 
  then have "v1 \<in> set (Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
    using 1 by simp
  then have "v1 = Cover n \<or> v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')"
    by simp
  then have 2: "v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
    using assms by simp
  then show ?case proof(cases "v1 \<in> set (construct_cycle_add_edge_nodes E a C')")
    case True
    then have 3: "v1 \<in> set (construct_cycle_add_edge_nodes E a C')" by simp
    then have 4: "(construct_cycle_add_edge_nodes E a C') \<noteq> []" by auto
    then show ?thesis proof (cases "v1 = last (construct_cycle_add_edge_nodes E a C')")
      case True
      then show ?thesis 
        using last_construct_cycle_not_Edge0 Cons 4 by fast
    next
      case False
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
        using sublist_append_not_eq Cons
        by (metis "1" Cover_not_in_edge_nodes True list.sel(3))
      then have 4: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C'" 
        using Cons sublist_set_ls1_4 1 3 11 False by metis
      have "distinct (construct_cycle_add_edge_nodes E a C')" using Cons by simp
      then show ?thesis 
        using Cons helper_for_helper_arcs_explicit_Cover_Edge0_Edge1 4 by metis 
    qed
  next
    case False
    have 5: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
      using sublist_append_not_eq Cons
      by (metis "1" hc_node.distinct(1) list.sel(3)) 
    then have "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using 2 False by simp
    then have 6: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using Cons sublist_set_ls2_3 11 5 by fast  
    have "distinct (construct_cycle_1 E C (Suc n) C')" 
      using Cons 11 by simp
    then have "distinct (tl (construct_cycle_1 E C (Suc n) C'))" 
      by (simp add: distinct_tl)
    then show ?thesis 
      using Cons 6  by simp
  qed
qed

lemma helper_arcs_explicit_Cover_Edge0_Edge1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 1"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "e1 = e2" "u1\<in> e1" "u2 = u1" "e1 \<in> set E"
proof -
  have v1_in_set: "v1 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast 
  then show "e1 \<in> set E" "u1 \<in> e1" using assms v1_in_set in_cycle edge0_in_construct_cycle by(auto)
next
  show "e1 = e2" "u2 = u1" using helper_arcs_explicit_Cover_Edge0_Edge1_1 assms by blast+
qed

lemma helper_arcs_explicit_Cover_Edge1_Edge1_1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 1" 
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "e1 = e2 \<and> u1 \<noteq> u2"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have 11: "tl (construct_cycle_1 E (a#C) n C') 
    = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have "v1 \<in> set (construct_cycle_1 E (a#C) n C')" 
    using Cons sublist_implies_in_set by fast 
  then have "v1 \<in> set (Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
    using 1 by simp
  then have "v1 = Cover n \<or> v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')"
    by simp
  then have 2: "v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
    using assms by simp
  then show ?case proof(cases "v1 \<in> set (construct_cycle_add_edge_nodes E a C')")
    case True
    then have 3: "v1 \<in> set (construct_cycle_add_edge_nodes E a C')" by simp
    then have 4: "(construct_cycle_add_edge_nodes E a C') \<noteq> []" by auto
    then show ?thesis proof (cases "v1 = last (construct_cycle_add_edge_nodes E a C')")
      case True
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
        using Cons 
        by (metis "1" "11" "3" Cover_not_in_edge_nodes append_self_conv2 hd_append list.distinct(1) list.sel(1) tl_append2) 
      then have "v2 = hd (construct_cycle_1 E C (Suc n) C')" using Cons sublist_set_last_ls1_1 1 3 11 True 
        by fast  
      then show ?thesis 
        using Cons by (metis hd_construct_cycle hc_node.distinct(1)) 
    next
      case False
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
        using sublist_append_not_eq Cons
        by (metis "1" Cover_not_in_edge_nodes True list.sel(3))
      then have 4: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C'" 
        using Cons sublist_set_ls1_4 1 3 11 False by metis
      have "distinct (construct_cycle_add_edge_nodes E a C')" using Cons by simp
      then show ?thesis 
        using Cons helper_for_helper_arcs_explicit_Cover_Edge1_Edge1 4 by metis 
    qed
  next
    case False
    have 5: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
      using sublist_append_not_eq Cons
      by (metis "1" hc_node.distinct(1) list.sel(3)) 
    then have "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using 2 False by simp
    then have 6: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using Cons sublist_set_ls2_3 11 5 by fast  
    have "distinct (construct_cycle_1 E C (Suc n) C')" 
      using Cons 11 by simp
    then have "distinct (tl (construct_cycle_1 E C (Suc n) C'))" 
      by (simp add: distinct_tl)
    then show ?thesis 
      using Cons 6  by simp
  qed
qed

lemma helper_arcs_explicit_Cover_Edge1_Edge1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 1"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "e1 = e2" "u1 \<in> e1" "u2 \<in> e1" "e1 \<in> set E" "u1 \<noteq> u2"
proof -
  have v1_in_set: "v1 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  then show "e1 \<in> set E" "u1 \<in> e1" using assms v1_in_set in_cycle edge1_in_construct_cycle by(auto)
next
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  then have u2_in_e2: "u2 \<in> e2"  
    using assms in_cycle edge1_in_construct_cycle by(auto)
  then have "e1 = e2 \<and> u1 \<noteq> u2"
    using helper_arcs_explicit_Cover_Edge1_Edge1_1 assms by simp
  then show "e1 = e2" "u2 \<in> e1" "u1 \<noteq> u2"
    using u2_in_e2 by auto
qed

lemma helper_arcs_explicit_Cover_Edge1_Edge0_1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 0" 
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "u1 = u2 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> i<j \<and> (\<forall>i'>i. u1 \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have 11: "tl (construct_cycle_1 E (a#C) n C') 
    = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  have "v1 \<in> set (construct_cycle_1 E (a#C) n C')" 
    using Cons sublist_implies_in_set by fast 
  then have "v1 \<in> set (Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
    using 1 by simp
  then have "v1 = Cover n \<or> v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')"
    by simp
  then have 2: "v1 \<in> set (construct_cycle_add_edge_nodes E a C') \<or> v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
    using assms by simp
  then show ?case proof(cases "v1 \<in> set (construct_cycle_add_edge_nodes E a C')")
    case True
    then have 3: "v1 \<in> set (construct_cycle_add_edge_nodes E a C')" by simp
    then have 4: "(construct_cycle_add_edge_nodes E a C') \<noteq> []" by auto
    then show ?thesis proof (cases "v1 = last (construct_cycle_add_edge_nodes E a C')")
      case True
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
        using Cons 
        by (metis "1" "11" "3" Cover_not_in_edge_nodes append_self_conv2 hd_append list.distinct(1) list.sel(1) tl_append2) 
      then have "v2 = hd (construct_cycle_1 E C (Suc n) C')" using Cons sublist_set_last_ls1_1 1 3 11 True 
        by fast  
      then show ?thesis 
        using Cons by (metis hd_construct_cycle hc_node.distinct(1)) 
    next
      case False
      have 5: "distinct E" using in_vc vertex_cover_list_def by blast
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
        using sublist_append_not_eq Cons
        by (metis "1" Cover_not_in_edge_nodes True list.sel(3))
      then have 4: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C'" 
        using Cons sublist_set_ls1_4 1 3 11 False by metis
      have "distinct (construct_cycle_add_edge_nodes E a C')" using Cons by simp
      then show ?thesis 
        using Cons helper_for_helper_arcs_explicit_Cover_Edge1_Edge0 4 5 by metis 
    qed
  next
    case False
    have 5: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = tl (construct_cycle_1 E (a#C) n C')" 
      using sublist_append_not_eq Cons
      by (metis "1" hc_node.distinct(1) list.sel(3)) 
    then have "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using 2 False by simp
    then have 6: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using Cons sublist_set_ls2_3 11 5 by fast  
    have "distinct (construct_cycle_1 E C (Suc n) C')" 
      using Cons 11 by simp
    then have "distinct (tl (construct_cycle_1 E C (Suc n) C'))" 
      by (simp add: distinct_tl)
    then show ?thesis 
      using Cons 6  by simp
  qed
qed


lemma helper_arcs_explicit_Cover_Edge1_Edge0:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 0"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "u1 = u2" "u1 \<in> e1" "u1 \<in> e2" "e1 \<in> set E" "e2 \<in> set E" 
    "(\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> i<j \<and> (\<forall>i'>i. u1 \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))"
proof -
  have v1_in_set: "v1 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  then show "e1 \<in> set E" "u1 \<in> e1" "e2 \<in> set E" using assms v1_in_set in_cycle edge1_in_construct_cycle edge0_in_construct_cycle by(auto)
next
  have "v2 \<in> set (construct_cycle_1 E C n C')" 
    using assms sublist_implies_in_set by fast
  then have u2_in_e2: "u2 \<in> e2"  
    using assms in_cycle edge0_in_construct_cycle by auto
  then have "u1 = u2 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> i<j \<and> (\<forall>i'>i. u1 \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))"
    using helper_arcs_explicit_Cover_Edge1_Edge0_1 assms  by simp  
  then show "u1 = u2" "u1 \<in> e2" 
    "(\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> i<j \<and> (\<forall>i'>i. u1 \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))"
    using u2_in_e2 by auto
qed



lemma helper_arcs_explicit_Cover_Edge_g0:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Cover i" "v2 = Edge u2 e2 j" "j> 0"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "False"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by(auto)
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  then show ?case proof(cases)
    assume "v1 = Cover n"
    then show False proof(cases "v2 = hd (construct_cycle_add_edge_nodes E a C')")
      case True
      then have 2: "v2 = hd (construct_cycle_add_edge_nodes E a C')" .
      then show ?thesis proof (cases "(construct_cycle_add_edge_nodes E a C') = []")
        case True
        have "v2 \<in> set ( construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
          using 1 Cons 
          using sublist_implies_in_set(2) by fastforce 
        then have "v2 \<in> set (construct_cycle_1 E C (Suc n) C')" 
          using True by simp
        have "v2 = Cover (n+1) \<or> v2 = Cover 0" using 2 hd_construct_cycle  
          by (metis (no_types, lifting) "1" Cons.IH Cons.prems(1) Cons.prems(5) True add.commute append_self_conv2 assms(2) assms(3) assms(4) distinct_tl hd_append2 list.collapse list.discI list.inject plus_1_eq_Suc tl_append2)  
        then show ?thesis using Cons by auto
      next
        case False
        then show ?thesis 
          using 2 assms helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0 by force 
      qed
    next
      case False
      then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
        using Cons 
        by (metis (mono_tags, lifting) "1" \<open>v1 = Cover n\<close> sublist3_hd_lists hd_construct_cycle distinct.simps(2) hc_node.distinct(1) hd_append list.sel(3)) 
      then have "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" using Cons 1 by auto
      then have 3: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
        using Cons 1 sublist_set_v2_noteq_hd_lists False 
        by (metis (no_types, lifting) hd_construct_cycle hc_node.distinct(1) hd_append)  
      then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
        using Cons 1 
        using append_Cons sublist_implies_in_set(1) list.inject by fastforce 
      then have 4: "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
        using Cover_not_in_edge_nodes assms by fastforce  
      have 5: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
        using Cons by simp
      then have 6: "distinct (construct_cycle_1 E C (Suc n) C')" by simp
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
        using 4 3 5 sublist_set_ls2_3 by fast
      then show ?thesis using Cons 3 6 distinct_tl
        by blast   
    qed
  next
    assume 2: "v1 \<noteq> Cover n"
    then have 3: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
      using Cons 1 sublist_set_noteq_l1 
      by fast  
    then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons 1 
      using append_Cons sublist_implies_in_set(1) list.inject by fastforce 
    then have 4: "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using Cover_not_in_edge_nodes assms by fastforce  
    have 5: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons by simp
    then have 6: "distinct (construct_cycle_1 E C (Suc n) C')" by simp
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using 4 3 5 sublist_set_ls2_3 by fast
    then show False using Cons 3 6  
      using distinct_tl by blast 
  qed
qed


lemma helper_arcs_explicit_Cover_Edge_0__1:
  assumes "Edge v e 0 = hd (construct_cycle_add_edge_nodes E' a C)" "distinct (construct_cycle_add_edge_nodes E' a C)"
    "ugraph (set E')" "construct_cycle_add_edge_nodes E' a C \<noteq> []" "distinct E'"
  shows "\<exists>i<length E'. e = E' ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E' ! j \<longrightarrow> j < length E' \<longrightarrow> \<not> j < i)"
proof -
  have 1: "Edge v e 0 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
    using assms by simp
  then have 2: "v \<in> e" using assms
    by (meson vertex_in_edge_of_node) 
  have "\<exists>i<length E'. e = E' ! i" using assms 1  
    by (metis in_set_conv_nth only_previous_edges_in_new_edges)
  then obtain i where i_def: "i<length E' \<and> e = E' ! i" by auto
  have va: "v = a" using assms  
    using helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0 by fastforce 
  have " (\<forall>j. v \<in> E' ! j \<longrightarrow> j < length E' \<longrightarrow> \<not> j < i)" proof (rule ccontr)
    assume "\<not>(\<forall>j. v \<in> E' ! j \<longrightarrow> j < length E' \<longrightarrow> \<not> j < i)" 
    then have "\<exists>j. v \<in> E' ! j \<and>  j < length E' \<and> j < i" 
      by simp 
    then obtain j where j_def: "v \<in> E' ! j \<and>  j < length E' \<and> j < i" by auto
    then obtain e1 where e1_def: "e1 = E'!j" by simp
    then obtain e2 where e2_def: "e2 = E'!i" by simp
    have ji: "j<i" "i<length E'" "j<length E'" using i_def j_def by auto
    have a_edges: "a \<in>e1" "a \<in> e2" using i_def j_def va 2 e1_def e2_def  by simp+
    then have "\<exists>i1 j1.
       construct_cycle_add_edge_nodes E' a C ! i1 = Edge a e1 1 \<and>
       construct_cycle_add_edge_nodes E' a C ! j1 = Edge a e2 0 \<and> i1 < j1 \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" 
      using helper4_for_helper_arcs_explicit_Cover_Edge0_Edge0 i_def j_def e1_def e2_def ji  a_edges 
      by metis
    then obtain i1 j1 where i1j1_def: "construct_cycle_add_edge_nodes E' a C ! i1 = Edge a e1 1 \<and>
       construct_cycle_add_edge_nodes E' a C ! j1 = Edge a e2 0 \<and> i1 < j1 \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" by blast
    then have "construct_cycle_add_edge_nodes E' a C ! j1 = Edge v e 0" 
      using 1 assms e2_def va i_def by fast    
    then have "j1 = 0" using assms 
      using i1j1_def  hd_conv_nth nth_eq_iff_index_eq by fastforce 
    then show False using i1j1_def by simp
  qed
  then show ?thesis 
    using "2" i_def by blast 
qed

lemma helper_arcs_explicit_Cover_Edge_0:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Cover c" "v2 = Edge u2 e2 0"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "(\<exists>i<length E. e2 = E ! i \<and> u2 \<in> e2 \<and> (\<forall>j. u2 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> c < length C+n)"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  then show ?case proof(cases "v1 = Cover n")
    case True
    then show ?thesis proof(cases "v2 = hd (construct_cycle_add_edge_nodes E a C'@ construct_cycle_1 E C (Suc n) C')")
      case True
      then have 2: "v2 = hd (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" .
      then show ?thesis proof (cases "(construct_cycle_add_edge_nodes E a C') = []")
        case True
        have "v2 \<in> set ( construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
          using 1 Cons 
          using sublist_implies_in_set(2) by fastforce 
        then have "v2 \<in> set (construct_cycle_1 E C (Suc n) C')" 
          using True by simp
        have "v2 = Cover (n+1) \<or> v2 = Cover 0" using 2 True  hd_construct_cycle
          by auto
        then show ?thesis using Cons by auto
      next
        case False
        have distinct: "distinct E" using in_vc vertex_cover_list_def by auto
        have ugraph: "ugraph (set E)" using in_vc vertex_cover_list_def by auto 
        then have "v2 = hd (construct_cycle_add_edge_nodes E a C')" using 2 False by simp
        then have "\<exists>i<length E. e2 = E! i \<and> u2 \<in> e2 \<and> (\<forall>j. u2 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i)" 
          using Cons False helper_arcs_explicit_Cover_Edge_0__1 ugraph distinct
          by (simp add: Cons.IH \<open>v2 = Edge u2 e2 0\<close> helper_arcs_explicit_Cover_Edge_0__1) 
        then show ?thesis 
          using Cons False 
          by (metis sublist_implies_in_set(1) constraints_for_Cover_nodes length_greater_0_conv list.discI trans_less_add1) 
      qed
    next
      case False
      then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
        using Cons 
        by (metis (mono_tags, lifting) "1" \<open>v1 = Cover n\<close> sublist3_hd_lists distinct.simps(2) list.sel(3)) 
      then have "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" using Cons 1 by auto
      then have 3: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
        using Cons 1 sublist_set_v2_noteq_hd_lists False 
        by (metis (no_types, lifting))  
      then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
        using Cons 1 
        using append_Cons sublist_implies_in_set(1) list.inject by fastforce 
      then have 4: "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
        using Cover_not_in_edge_nodes assms by fastforce  
      have 5: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
        using Cons by simp
      then have 6: "distinct (construct_cycle_1 E C (Suc n) C')" by simp
      have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
        using 4 3 5 sublist_set_ls2_3 by fast
      then show ?thesis using Cons 3 6 
        by (metis "4" Nat.add_0_right Suc_n_not_le_n True constraints_for_Cover_nodes distinct_tl gr0I hc_node.inject(1) length_0_conv list.discI)  
    qed
  next
    case False
    then have 3: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
      using Cons 1 sublist_set_noteq_l1 
      by fast  
    then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons 1 
      using append_Cons sublist_implies_in_set(1) list.inject by fastforce 
    then have 4: "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using Cover_not_in_edge_nodes assms by fastforce  
    have 5: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons by simp
    then have 6: "distinct (construct_cycle_1 E C (Suc n) C')" by simp
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using 4 3 5 sublist_set_ls2_3 by fast
    then show ?thesis  using Cons 3 6  
      by (metis False add_is_0 sublist_implies_in_set(1) constraints_for_Cover_nodes distinct_tl gr0I)  
  qed
qed

lemma helper_arcs_explicit_Edge_1_Cover__1:
  assumes "Edge v e 1 = last (construct_cycle_add_edge_nodes E' a C)" "distinct (construct_cycle_add_edge_nodes E' a C)"
    "ugraph (set E')" "construct_cycle_add_edge_nodes E' a C \<noteq> []" "distinct E'"
  shows "\<exists>i<length E'. e = E' ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E' ! j \<longrightarrow> j < length E' \<longrightarrow> \<not> i < j)"
proof -
  have 1: "Edge v e 1 \<in> set (construct_cycle_add_edge_nodes E' a C)" 
    using assms by simp
  then have 2: "v \<in> e" using assms
    by (meson vertex_in_edge_of_node) 
  have "\<exists>i<length E'. e = E' ! i" using assms 1  
    by (metis in_set_conv_nth only_previous_edges_in_new_edges)
  then obtain i where i_def: "i<length E' \<and> e = E' ! i" by auto
  have va: "v = a" using assms  
    using helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0b by fastforce 
  have "(\<forall>j. v \<in> E' ! j \<longrightarrow> j < length E' \<longrightarrow> \<not> i < j)" proof (rule ccontr)
    assume "\<not>(\<forall>j. v \<in> E' ! j \<longrightarrow> j < length E' \<longrightarrow> \<not> i < j)" 
    then have "\<exists>j. v \<in> E' ! j \<and>  j < length E' \<and> i < j" 
      by simp 
    then obtain j where j_def: "v \<in> E' ! j \<and>  j < length E' \<and> i < j" by auto
    then obtain e1 where e1_def: "e1 = E'!i" by simp
    then obtain e2 where e2_def: "e2 = E'!j" by simp
    have ji: "i<j" "i<length E'" "j<length E'" using i_def j_def by auto
    have a_edges: "a \<in>e1" "a \<in> e2" using i_def j_def va 2 e1_def e2_def  by simp+
    then have "\<exists>i1 j1.
       construct_cycle_add_edge_nodes E' a C ! i1 = Edge a e1 1 \<and>
       construct_cycle_add_edge_nodes E' a C ! j1 = Edge a e2 0 \<and> i1 < j1 \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" 
      using helper4_for_helper_arcs_explicit_Cover_Edge0_Edge0 i_def j_def e1_def e2_def ji  a_edges 
      by metis
    then obtain i1 j1 where i1j1_def: "construct_cycle_add_edge_nodes E' a C ! i1 = Edge a e1 1 \<and>
       construct_cycle_add_edge_nodes E' a C ! j1 = Edge a e2 0 \<and> i1 < j1 \<and> j1 < length (construct_cycle_add_edge_nodes E' a C)" by blast
    then have "construct_cycle_add_edge_nodes E' a C ! i1 = Edge v e 1" 
      using 1 assms e1_def va i_def by fast    
    then have "i1 = length (construct_cycle_add_edge_nodes E' a C) -1" using assms 
      using i1j1_def  hd_conv_nth nth_eq_iff_index_eq last_conv_nth by fastforce 
    then show False using i1j1_def by linarith
  qed
  then show ?thesis 
    using 2 i_def 
    by auto 
qed

lemma helper_arcs_explicit_Edge_1_Cover:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 1" "v2 = Cover c"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "(\<exists>i<length E. e1 = E ! i \<and> u1 \<in> e1 \<and> (\<forall>j. u1 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> c < length C + n)"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  then show ?case proof(cases)
    assume a1: "v1 \<in> set (construct_cycle_add_edge_nodes E a C')"
    then have not_empty: "construct_cycle_add_edge_nodes E a C' \<noteq> []" by auto
    have distinct: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons 1 by auto  
    show ?case proof(cases "v1 = last (construct_cycle_add_edge_nodes E a C')")
      case True
      have distinct: "distinct E" using in_vc vertex_cover_list_def by auto
      have ugraph: "ugraph (set E)" using in_vc vertex_cover_list_def by auto 
      then have "(\<exists>i<length E. e1 = E ! i \<and> u1 \<in> e1 \<and> (\<forall>j. u1 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j))" 
        using Cons helper_arcs_explicit_Edge_1_Cover__1 distinct ugraph  
        by (metis True distinct_construct_edge_nodes not_empty) 
      then show ?thesis using Cons constraints_for_Cover_nodes 
        by (metis add_strict_increasing sublist_implies_in_set(2) le_add1 le_add_same_cancel1 length_greater_0_conv list.discI)  
    next
      case False
      then have "v2 \<in> set (construct_cycle_add_edge_nodes E a C')" using Cons a1 
        by (metis "1" Cover_not_in_edge_nodes append_Cons sublist_set_ls1_1 list.inject list.sel(3) self_append_conv2 tl_append2)
      then show ?thesis 
        using assms Cover_not_in_edge_nodes 
        by fast 
    qed
  next
    assume 2: "v1 \<notin> set (construct_cycle_add_edge_nodes E a C')"
    then have 3: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
      using Cons 1 sublist_set_noteq_l1 
      by fast  
    then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons 1 
      using append_Cons sublist_implies_in_set(1) list.inject by fastforce 
    then have 4: "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using assms 2 by fastforce  
    have 5: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons by simp
    then have 6: "distinct (construct_cycle_1 E C (Suc n) C')" by simp
    then have 7: "distinct (tl (construct_cycle_1 E C (Suc n) C'))" using distinct_tl by auto 
    have 8: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using 4 3 5 sublist_set_ls2_3 by fast
    then have "\<exists>i<length E. e1 = E ! i \<and> u1 \<in> e1 \<and> (\<forall>j. u1 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> c < length C + (Suc n)" 
      using Cons 8 7 
      by blast  
    then show ?case by auto 
  qed
qed

lemma helper_arcs_explicit_Edge_Cover:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C n C'" "v1 = Edge u1 e1 i" "v2 = Cover j" "i\<noteq>1"
    "distinct (tl (construct_cycle_1 E C n C'))"
  shows "False"
  using assms proof(induction C arbitrary: n)
  case Nil
  then show ?case by(auto)
next
  case (Cons a C)
  have 1: "construct_cycle_1 E (a#C) n C' 
    = Cover n # construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
    by simp
  then show ?case proof(cases)
    assume a1: "v1 \<in> set (construct_cycle_add_edge_nodes E a C')"
    then have not_empty: "construct_cycle_add_edge_nodes E a C' \<noteq> []" by auto
    have distinct: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons 1 by auto  
    show False proof(cases "v1 = last (construct_cycle_add_edge_nodes E a C')")
      case True
      then have "v2 = hd (construct_cycle_1 E C (Suc n) C')" using assms distinct Cons a1 not_empty 
        by (metis (full_types) One_nat_def last_construct_cycle_not_Edge0 Edgei_not_in_construct_edge_nodes less_one linorder_neqE_nat)
      show ?thesis 
        using helper7_for_helper_arcs_explicit_Cover_Edge0_Edge0b True not_empty assms 
        by fastforce 
    next
      case False
      then have "v2 \<in> set (construct_cycle_add_edge_nodes E a C')" using Cons a1 
        by (metis "1" Cover_not_in_edge_nodes append_Cons sublist_set_ls1_1 list.inject list.sel(3) self_append_conv2 tl_append2)
      then show ?thesis 
        using assms Cover_not_in_edge_nodes 
        by fast 
    qed
  next
    assume 2: "v1 \<notin> set (construct_cycle_add_edge_nodes E a C')"
    then have 3: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C'" 
      using Cons 1 sublist_set_noteq_l1 
      by fast  
    then have "v1 \<in> set (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons 1 
      using append_Cons sublist_implies_in_set(1) list.inject by fastforce 
    then have 4: "v1 \<in> set (construct_cycle_1 E C (Suc n) C')" 
      using assms 2 by fastforce  
    have 5: "distinct (construct_cycle_add_edge_nodes E a C' @ construct_cycle_1 E C (Suc n) C')" 
      using Cons by simp
    then have 6: "distinct (construct_cycle_1 E C (Suc n) C')" by simp
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C (Suc n) C'" 
      using 4 3 5 sublist_set_ls2_3 by fast
    then show False using Cons 3 6  
      using distinct_tl by blast 
  qed
qed


lemma helper_arcs_explicit_Cover_Cover:
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


lemma helper_arcs_explicit_Cover_Nodes:
  assumes "v2 = Edge v e i" "v1 = Cover x1" 
    "\<exists>p1 p2. p1 @ [v1, v2]@ p2 = construct_cycle_1 E C 0 (set C)" "length C \<le> k"
    "distinct (tl (construct_cycle_1 E C 0 (set C)))"
  shows  "i = 0 \<and> (\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> x1 < k)"
  using assms proof (cases "i = 0")
  case True
  then have "(\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> x1 < k)" 
    using helper_arcs_explicit_Cover_Edge_0 assms 
    by fastforce 
  then show ?thesis using True by(auto) 
next
  case False
  then show ?thesis using assms helper_arcs_explicit_Cover_Edge_g0 apply(auto) by blast 
qed


lemma helper_arcs_explicit_Edge_Nodes_greater_1:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "v1 = Edge u1 e1 i" "v2 = Edge u2 e2 j" "j > 1 \<or> i > 1"
  shows "False"
proof -
  from \<open>\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)\<close> have v1_in:  "v1 \<in> set (construct_cycle_1 E C 0 (set C))" 
    by (metis Cons_eq_appendI in_set_conv_decomp self_append_conv2)
  from \<open>\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)\<close> have v2_in: "v2 \<in> set (construct_cycle_1 E C 0 (set C))" 
    by (metis (no_types, hide_lams) append_eq_Cons_conv append_eq_append_conv2 in_set_conv_decomp self_append_conv2) 
  then show False using assms v1_in v2_in Edgei_not_in_construct_cycle \<open>j> 1 \<or> i > 1\<close> by meson +
qed

lemma helper_arcs_explicit_Edge_Nodes_0:
  assumes "v1 = Edge u1 e1 0" "v2 = Edge u2 e2 i2""\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C"
    "distinct (tl (construct_cycle_1 E C 0 (set C)))"
  shows " (\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E \<and> v \<in> e) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v)"
proof (cases)
  assume "i2 = 0 \<or> i2 = 1"
  then show ?thesis 
  proof 
    assume "i2=0"
    then show ?thesis using helper_arcs_explicit_Cover_Edge0_Edge0 assms apply(simp) by metis
  next
    assume "i2 = 1" 
    then show ?thesis using helper_arcs_explicit_Cover_Edge0_Edge1 assms apply(simp) by metis
  qed
next
  assume "\<not> (i2 = 0 \<or> i2 = 1)"
  then have "i2 > 1" by auto
  then show ?thesis 
    using helper_arcs_explicit_Edge_Nodes_greater_1 assms apply(simp) 
    by blast
qed

lemma helper_arcs_explicit_Edge_Nodes_1:
  assumes "v1 = Edge u1 e1 1" "v2 = Edge u2 e2 i2""\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C"
    "distinct (tl (construct_cycle_1 E C 0 (set C)))"
  shows "(\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v) \<or>
    (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))))"
proof (cases)
  assume "i2 = 0 \<or> i2 = 1"
  then show ?thesis 
  proof 
    assume "i2=0"
    then show ?thesis using assms helper_arcs_explicit_Cover_Edge1_Edge0 apply(simp) by blast
  next
    assume "i2 = 1" 
    then show ?thesis using assms helper_arcs_explicit_Cover_Edge1_Edge1 
      by (metis One_nat_def) 
  qed
next
  assume "\<not> (i2 = 0 \<or> i2 = 1)"
  then have "i2 > 1" by auto
  then show ?thesis 
    using helper_arcs_explicit_Edge_Nodes_greater_1 assms apply(simp) 
    by blast
qed

lemma helper_arcs_explicit_Edge_Nodes:
  assumes "v1 = Edge u1 e1 i1" "v2 = Edge u2 e2 i2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C"
    "distinct (tl (construct_cycle_1 E C 0 (set C)))"
  shows " (\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E \<and> v \<in> e ) \<or>
    (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e  \<and> u \<noteq> v) \<or>
    (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v) \<or>
    (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j))))"
proof (cases)
  assume "i1 = 0 \<or> i1 = 1"
  then show ?thesis 
  proof 
    assume "i1=0"
    then show ?thesis 
      using assms helper_arcs_explicit_Edge_Nodes_0 by(simp)
  next
    assume "i1 = 1" 
    then show ?thesis 
      using assms helper_arcs_explicit_Edge_Nodes_1 by simp
  qed
next
  assume "\<not> (i1 = 0 \<or> i1 = 1)"
  then have "i1 > 1" by auto
  then show ?thesis 
    using helper_arcs_explicit_Edge_Nodes_greater_1 assms apply(simp) 
    by blast
qed


lemma helper_arcs_explicit:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = construct_cycle_1 E C 0 (set C)" "is_vertex_cover_list E C" "distinct C" "length  C = k" "k>0"
  shows "(\<exists>v e. v1 = Edge v e 0 \<and> v2 = Edge v e (Suc 0) \<and> e \<in> set E \<and> v \<in> e) \<or>
         (\<exists>u v e. v1 = Edge v e 0 \<and> v2 = Edge u e 0 \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e  \<and> u \<noteq> v) \<or>
         (\<exists>u v e. v1 = Edge v e (Suc 0) \<and> v2 = Edge u e (Suc 0) \<and> e \<in> set E \<and> v \<in> e \<and> u \<in> e  \<and> u \<noteq> v) \<or>
         (\<exists>v e1. v1 = Edge v e1 (Suc 0) \<and> (\<exists>e2. v2 = Edge v e2 0 \<and> (\<exists>i<length E. \<exists>j<length E. e1 = E ! i \<and> e2 = E ! j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and> (\<forall>i'>i. v \<in> E ! i' \<longrightarrow> i' < length E \<longrightarrow> \<not> i' < j)))) \<or>
         (\<exists>v e. v1 = Edge v e (Suc 0) \<and> (\<exists>n. v2 = Cover n \<and> (\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> n < k))) \<or>
         (\<exists>v e n. v1 = Cover n \<and> v2 = Edge v e 0 \<and> (\<exists>i<length E. e = E ! i \<and> v \<in> e \<and> (\<forall>j. v \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> j < i) \<and> n < k))\<or>
        (\<exists>i. v1 = Cover i \<and> (\<exists>j. v2 = Cover j \<and> i < k \<and> j < k))"
proof (cases)
  assume v1: "\<exists>x1. v1 = Cover x1"
  then obtain x1 where v1_2: "v1 = Cover x1" by blast
  have distinct_tl: "distinct (tl (construct_cycle_1 E C 0 (set C)))"
    using assms distinct_edges distinct_nodes by blast
  then show ?thesis
  proof (cases)
    assume "\<exists> x2. v2 = Cover x2"
    then show ?thesis 
      using helper_arcs_explicit_Cover_Cover v1 assms apply simp 
      by fastforce 
  next
    assume  "\<not> (\<exists> x2. v2 = Cover x2)"
    then have "\<exists>v e i. v2 = Edge v e i" 
      by (meson hc_node.exhaust)
    then obtain v e i where vei_def: "v2 = Edge v e i" by blast
    then show ?thesis
      using helper_arcs_explicit_Cover_Edge_g0 helper_arcs_explicit_Cover_Edge_0 v1_2 assms vei_def distinct_tl by(simp add: helper_arcs_explicit_Cover_Nodes)
  qed
next  
  have distinct_tl: "distinct (tl (construct_cycle_1 E C 0 (set C)))"
    using assms distinct_edges distinct_nodes by blast
  assume "\<not> (\<exists>x1. v1 = Cover x1)"
  then have "\<exists>u1 e1 i1. v1 = Edge u1 e1 i1" 
    by (meson hc_node.exhaust) 
  then obtain u1 e1 i1 where "v1 = Edge u1 e1 i1" by blast
  then show ?thesis 
  proof(cases)
    assume "\<exists> x2. v2 = Cover x2"
    then obtain x2 where "v2 = Cover x2" by blast
    then show ?thesis 
      using helper_arcs_explicit_Edge_1_Cover helper_arcs_explicit_Edge_Cover \<open>v1 = _\<close> assms 
    proof(cases "i1 = 1")
      case True
      then have "\<exists>i<length E. e1 = E ! i \<and> u1 \<in> e1 \<and> (\<forall>j. u1 \<in> E ! j \<longrightarrow> j < length E \<longrightarrow> \<not> i < j) \<and> x2 < length C + 0" 
        using helper_arcs_explicit_Edge_1_Cover assms \<open>v1 = _\<close>  \<open>v2 = _\<close>  distinct_tl by blast
      then show ?thesis using helper_arcs_explicit_Edge_1_Cover assms  \<open>v1 = _\<close>  \<open>v2 = _\<close>  distinct_tl True 
        by simp 
    next
      case False
      then show ?thesis 
        using helper_arcs_explicit_Edge_Cover assms \<open>v1 = _\<close>  \<open>v2 = _\<close> distinct_tl apply(simp) 
        by blast 
    qed
  next
    assume  "\<not> (\<exists> x2. v2 = Cover x2)"
    then have "\<exists>v e i. v2 = Edge v e i" 
      by (meson hc_node.exhaust)
    then obtain u2 e2 i2 where "v2 = Edge u2 e2 i2" by blast
    then show ?thesis
      using helper_arcs_explicit_Edge_Nodes assms \<open>v1 = _\<close>  \<open>v2 = _\<close> distinct_tl by simp  
  qed
qed


lemma sublist_of_cycle_is_arc:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = Cycle" "k>0"
  shows "(v1, v2) \<in> arcs G"
  using Cycle_def assms G_def_2 Cov_def helper_arcs_explicit by(simp)




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
  then show "x \<in> arcs G" using uv_def sublist_of_cycle_is_arc k0 by(auto)
qed

subsection\<open>Cycle is awalk\<close>

lemma hd_construct_cycle_Cover_0:
  shows "(hd (construct_cycle_1 E C 0 C')) = Cover 0"
  apply(induction C) by(auto) 

lemma head_construct_cycle_Cover_n:
  assumes "C \<noteq> []"
  shows "(hd (construct_cycle_1 E C n C')) = Cover n"
  using assms apply(induction C)by(auto) 

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
    using last_construct_cycle by(auto)
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

subsubsection\<open>All vertices are vertices of Graph\<close>

lemma verts_of_graph:
  assumes "k>0"
  shows "set Cycle \<subseteq> verts G" 
  using assms 
  by (simp add: in_cycle_in_verts subsetI) 


subsection\<open>Is in HC\<close>

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
  assumes "k> 0"
  shows "is_hc G Cycle"
  using cycle_contains_all_verts is_cylce is_hc_def head_cycle_in_verts verts_of_graph assms 
    cycle_distinct
  by fastforce


lemma vc_impl_hc_context: 
  shows "vc_hc (E,k) \<in> hc"
proof(cases "k=0")
  case True
  then have "Cov = []" 
    using Cov_def by simp
  then have empty_E: "E = []" using Cov_def 
    by (simp add: is_vertex_cover_list_def) 
  then have no_verts: "verts G = {}" 
    using True G_def_2 by simp
  then have is_hc: "is_hc G []" 
    using is_hc_def G_def by fastforce
  then have arcsG: "arcs G = {}" using empty_E G_def_2 True by simp
  have head_tail_G: "head G = snd" "tail G = fst" 
    using G_def_2 by simp+
  have "finite (verts G)"
    using finite_verts_G by auto
  then show ?thesis 
    using hc_def is_hc wf_digraph_def G_def arcsG head_tail_G by auto
next
  case False
  have "head G = snd" "tail G = fst" 
    using G_def_2 by simp+
  then show ?thesis using is_wf_digraph is_hc_cycle_graph G_def hc_def finite_verts_G False
    by auto
qed

end

end