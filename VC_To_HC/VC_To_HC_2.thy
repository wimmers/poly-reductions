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
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
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


lemma in_arcs_next_edge_1_0: 
  assumes "(Edge v e1 1, Edge v e2 0) \<in> arcs G"
  shows "next_edge v E e1 e2" 
proof -
  have "(Edge v e1 1, Edge v e2 0) \<in> arcs G" 
    using assms
    by auto
  then have "\<exists> i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)"
    using G_def_2 
    by fastforce
  then have "next_edge v E e1 e2" 
    using next_edge_def 
    by metis
  then show ?thesis .
qed


lemma in_arcs_last_edge: 
  assumes "(Edge v e 1, Cover n) \<in> arcs G"
  shows "last_edge v e E" 
proof -
  have "\<exists>i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k"
    using G_def_2 assms by auto
  then have "last_edge v e E" 
    using last_edge_def by metis
  then show ?thesis .
qed

lemma in_arcs_first_edge: 
  assumes "(Cover n, Edge v e 0) \<in> arcs G"
  shows "first_edge v e E" 
proof -
  have "\<exists>i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k"
    using G_def_2 assms by auto
  then have "first_edge v e E" 
    using first_edge_def by metis
  then show ?thesis .
qed

lemma Edge_v_e_in_G:
  assumes "e \<in> set E" "v \<in> e" 
  shows "Edge v e 1 \<in> verts G" "Edge v e 0 \<in> verts G"
  using G_def_2 assms by force+ 

lemma Cover_in_G:
  assumes "i<k"
  shows "Cover i \<in> verts G"
  using G_def_2 assms by simp

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

lemma e_in_E_e_explicit: 
  assumes "e \<in> set E"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v" 
proof -
  have 1: "card e = 2" 
    using ugraph ugraph_def assms by blast 
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

subsubsection\<open>Structural Lemmas for Cycle\<close>

lemma distinct_tl_Cycle:
  shows "distinct (tl Cycle)"
  using is_hc_def Cycle_def by blast

lemma inCycle_inVerts: 
  assumes "x \<in> set Cycle"
  shows "x\<in> verts G"
  using Cycle_def is_hc_def assms by fast 


lemma inVerts_inCycle:
  assumes "x \<in> verts G" "card (verts G) > 1"
  shows "x \<in> set Cycle"
  using assms Cycle_def is_hc_def by force 

lemma Edge_v_e_in_Cycle:
  assumes "e \<in> set E" "v \<in> e" "card (verts G) > 1"
  shows "Edge v e 1 \<in> set Cycle" "Edge v e 0 \<in> set Cycle"
  using Edge_v_e_in_G assms inVerts_inCycle 
  by auto 

lemma Cover_in_Cycle:
  assumes "i<k" "card (verts G) > 1"
  shows "Cover i \<in> set Cycle"
  using Cover_in_G assms inVerts_inCycle 
  by auto 

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
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []"
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
    then have "pre_digraph.cas G u (a#p)  v = 
      (tail G a = u \<and> pre_digraph.cas G (head G a) [] v)"
      using True 
      by (simp add: pre_digraph.cas.simps(2)) 
    then have 1: "pre_digraph.cas G (head G a) [] v"
      using Cons by auto
    then have 2: "pre_digraph.cas G (head G a) [] v = 
      ((head G a) = v)" 
      using pre_digraph.cas.simps  by fast 
    then have "head G a = snd a" 
      by (auto simp add: G_def_2)
    then show ?thesis 
      using 0 1 2 by simp
  next
    case False
    then have 0: "last (a#p) = last p" 
      by simp
    have "pre_digraph.cas G u (a#p)  v = 
      (tail G a = u \<and> pre_digraph.cas G (head G a) p v)"
      by (simp add: pre_digraph.cas.simps(2)) 
    then have "pre_digraph.cas G (head G a) p v"
      using Cons by auto
    then have " snd (last p) = v" 
      using Cons False by simp 
    then show ?thesis 
      using 0 by auto 
  qed
qed 


lemma last_vwalk_arcs_last_p:
  assumes "snd (last (vwalk_arcs p)) = v" "(vwalk_arcs p) \<noteq> []"
  shows "last p = v"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case proof(cases "p = []")
    case True
    then have "vwalk_arcs (a#p) = []" by simp
    then show ?thesis 
      using Cons by auto
  next
    case False
    then have 1: "p\<noteq> []" by simp
    then have 2: "vwalk_arcs (a#p) = (a, hd p)#vwalk_arcs p"
      using vwalk_arcs_Cons by auto
    then have "vwalk_arcs (a#p) \<noteq> []" by auto
    then show ?thesis proof(cases "vwalk_arcs p = []")
      case True
      then have 3: "(last (vwalk_arcs (a#p))) = (a, hd p)"
        using 2 by simp 
      have "last p = hd p" using True 1 
        by (metis hd_rev list.distinct(1) list.exhaust rev_singleton_conv vwalk_arcs_Cons) 
      then show ?thesis 
        using 3 Cons False by auto 
    next
      case False
      then have "snd (last (vwalk_arcs (a#p))) = snd (last (vwalk_arcs p))"
        by (simp add: 2) 
      then have "snd (last (vwalk_arcs p)) = v" 
        using Cons by simp
      then have 3: "last p = v" 
        using Cons False by simp 
      have "p \<noteq> []" 
        by (simp add: 1)
      then have "last (a#p) = last p" 
        by auto
      then show ?thesis using 3 by simp 
    qed
  qed
qed


lemma hd_pre_digraph_cas: 
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []"
  shows "fst (hd p) = u"
  using assms proof(induction p arbitrary: u)
  case Nil
  then show ?case by simp 
next
  case (Cons a p)
  then have "pre_digraph.cas G u (a#p)  v = 
      (tail G a = u \<and> pre_digraph.cas G (head G a) p v)"
    by (simp add: pre_digraph.cas.simps(2))
  then have "tail G a = u" 
    using Cons 
    by simp
  then have "fst a = u" 
    using G_def_2 
    by force
  then show ?case by simp
qed 


lemma hd_vwalk_arcs_last_p:
  assumes "fst (hd (vwalk_arcs p)) = v" "(vwalk_arcs p) \<noteq> []"
  shows "hd p = v"
  using assms
proof(induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case proof(cases "p = []")
    case True
    then have "vwalk_arcs (a#p) = []" by simp
    then show ?thesis 
      using Cons by auto
  next
    case False
    then have 1: "p\<noteq> []" by simp
    then have 2: "vwalk_arcs (a#p) = (a, hd p)#vwalk_arcs p"
      using vwalk_arcs_Cons by auto
    then have "fst (hd (vwalk_arcs (a#p))) = a"
      by simp
    then show ?thesis 
      using Cons by simp 
  qed
qed


lemma hd_last_Cycle:
  assumes "Cycle \<noteq> []" "card (verts G) > 1" 
  shows "hd Cycle = last Cycle" 
proof (cases "length Cycle = 1")
  case True
  then show ?thesis 
    by (metis List.finite_set assms(1) card_length contains_two_card_greater_1 last_in_set leD list.set_sel(1))  
next
  case False
  then have "length Cycle \<noteq> 1" "length Cycle \<noteq> 0" 
    using assms by(auto)
  then have "length Cycle \<ge> 2" 
    by linarith  
  then have arcs_not_epmty: "(vwalk_arcs Cycle) \<noteq> []" 
    using vwalk_arcs_empty_length_p by force
  have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    using Cycle_def is_hc_def pre_digraph.cycle_def assms 
    by (metis antisym less_imp_le_nat nat_neq_iff)
  then obtain u where u_def: "pre_digraph.awalk G u (vwalk_arcs Cycle) u" 
    by auto
  then have 1: "pre_digraph.cas G u (vwalk_arcs Cycle) u" 
    using pre_digraph.awalk_def by force
  then have "snd (last (vwalk_arcs Cycle)) = u" 
    using arcs_not_epmty last_pre_digraph_cas 
    by auto 
  then have 2: "last Cycle = u" 
    using assms last_vwalk_arcs_last_p arcs_not_epmty 
    by simp
  have "fst (hd (vwalk_arcs Cycle)) = u" 
    using arcs_not_epmty hd_pre_digraph_cas 1    
    by auto
  then have 3: "hd Cycle = u" 
    using hd_vwalk_arcs_last_p assms arcs_not_epmty 
    by simp
  then show ?thesis using 2 3 
    by simp
qed

lemma hd_last_Cycle_dep_length:
  assumes "Cycle \<noteq> []" "length Cycle \<ge>2" 
  shows "hd Cycle = last Cycle"
proof(cases "length Cycle = 2")
  case True
  then have lc: "length Cycle = 2" by auto
  then show ?thesis proof(cases "hd Cycle = last Cycle")
    case True
    then show ?thesis by auto
  next
    case False
    then have 1: "last Cycle \<in> verts G" 
      using inCycle_inVerts assms by simp
    have 2: "hd Cycle \<in> verts G" 
      using inCycle_inVerts assms by simp
    have "card (verts G) > 1" 
      using 1 2 False
      by (meson contains_two_card_greater_1 finite_verts) 
    then show ?thesis using assms hd_last_Cycle by simp
  qed
next
  case False
  then have "length Cycle > 2" 
    using assms by simp
  then show ?thesis 
    using hd_last_Cycle assms length_cycle_number_verts by blast 
qed


lemma number_verts_length_cycle: 
  assumes "card (verts G) > 1"
  shows "length Cycle > 2" 
proof (rule ccontr)
  assume "\<not> 2 < length Cycle"
  then have "2 \<ge> length Cycle"
    by auto
  then have "length Cycle = 2 \<or> length Cycle = 1 \<or> length Cycle = 0" 
    by linarith
  then show False proof
    assume "length Cycle = 1 \<or> length Cycle = 0"
    then show False using inVerts_inCycle assms
      by (metis (mono_tags, lifting) card_length dual_order.strict_trans le_antisym less_imp_le_nat less_numeral_extra(1) nat_neq_iff subsetI subset_antisym verts_of_Cycle_in_G)
  next
    assume a: "length Cycle = 2"
    then have equal: "hd Cycle = last Cycle" 
      using assms hd_last_Cycle 
      by fastforce
    have "Cycle = [hd Cycle, last Cycle]" 
      using a length_2_hd_last by auto
    then have "set Cycle = {hd Cycle, last Cycle}"
      by (metis empty_set list.simps(15)) 
    then have "card (set Cycle) = 1"
      using equal by simp 
    then show False  
      using inVerts_inCycle assms subsetI verts_of_Cycle_in_G by force 
  qed
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


lemma pre_1_edges_G:
  assumes "(x, Edge v e 1) \<in> arcs G"
  shows "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 0)"
proof -
  have "(\<forall>e. e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and> (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G)"
    using G_def in_hc hc_def wf_digraph_def 
    by fast  
  then have 1: "tail G (x, Edge v e 1) \<in> verts G" 
    using assms by auto
  have "tail G (x, Edge v e 1) = x" 
    using G_def_2 by simp
  then have x_in_verts: "x \<in> verts G" 
    using 1 by auto  
  then have 2: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1) \<or> (\<exists>i. x = Cover i)"
    using G_def_2  
    by auto 
  then show ?thesis proof (cases "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)")
    case True
    then have 3: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)"
      by auto
    show ?thesis proof(cases "\<exists>a b. x = Edge a b 0")
      case True
      then obtain a b where ab_def: "x = Edge a b 0" 
        by auto
      then have 4: "(Edge a b 0, Edge v e 1) \<in> arcs G" 
        using assms by simp
      then have "b = e" "a = v" 
        using G_def_2 by auto
      then show ?thesis 
        using ab_def by simp
    next
      case False
      then have "\<exists>a b. x = Edge a b 1"
        using 3 by simp
      then obtain a b where ab_def: "x = Edge a b 1"
        by auto
      then have 4: "(Edge a b 1, Edge v e 1) \<in> arcs G" 
        using assms by simp
      then have 1: "b = e" 
        using G_def_2 by simp
      have 2: "a \<noteq> v" 
        using 4 G_def_2 by force 
      have "a \<in> e" 
        using 1 x_in_verts ab_def G_def_2 
        by simp
      then show ?thesis using 1 2 ab_def by(auto)   
    qed
  next
    case False
    then have "\<exists>i. x = Cover i"
      using 2 by simp
    then obtain i where "x = Cover i"
      by auto
    then have "(Cover i, Edge v e 1) \<in> arcs G" 
      using assms by simp
    then show ?thesis 
      using G_def_2 by auto
  qed
qed


lemma pre_1_edges:
  assumes "sublist [x, Edge v e 1] Cycle" "card (verts G) > 1"
  shows "v \<in> e" "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 0)"
proof -
  have "Edge v e 1 \<in> set Cycle" 
    using assms in_sublist_impl_in_list 
    by fastforce 
  then show "v \<in> e" 
    using Edges_in_Cycle by auto 
next
  have "(x, Edge v e 1) \<in> set (vwalk_arcs Cycle)"
    using assms 
    by (simp add: sublist_def if_sublist_then_edge)
  then have "(x, Edge v e 1) \<in> arcs G" 
    using vwalk_arcs_Cycle_subseteq_arcs_G assms 
    by blast  
  then show "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 0)" 
    using pre_1_edges_G by auto
qed


lemma post_0_edges_G:
  assumes "(Edge v e 0, x) \<in> arcs G"
  shows "(\<exists>u. (x = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 1)"
proof -
  have "(\<forall>e. e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and> (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G)"
    using G_def in_hc hc_def wf_digraph_def 
    by fast  
  then have 1: "head G (Edge v e 0, x) \<in> verts G" 
    using assms by auto
  have "head G (Edge v e 0, x) = x" 
    using G_def_2 by simp
  then have x_in_verts: "x \<in> verts G" 
    using 1 by auto  
  then have 2: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1) \<or> (\<exists>i. x = Cover i)"
    using G_def_2  
    by auto 
  then show ?thesis proof (cases "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)")
    case True
    then have 3: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)"
      by auto
    show ?thesis proof(cases "\<exists>a b. x = Edge a b 0")
      case True
      then obtain a b where ab_def: "x = Edge a b 0" 
        by auto
      then have 4: "(Edge v e 0, Edge a b 0) \<in> arcs G" 
        using assms by simp
      then have 1: "b = e"  
        using G_def_2 by auto
      have 2: "a \<noteq> v" 
        using 4 G_def_2 by force 
      have "a \<in> e" 
        using 1 x_in_verts ab_def G_def_2 
        by simp
      then show ?thesis 
        using 1 2 ab_def by simp
    next
      case False
      then have "\<exists>a b. x = Edge a b 1"
        using 3 by simp
      then obtain a b where ab_def: "x = Edge a b 1"
        by auto
      then have 4: "(Edge v e 0, Edge a b 1) \<in> arcs G" 
        using assms by simp
      then have 1: "b = e" "a = v"
        using G_def_2 by simp+
      then show ?thesis 
        using 1 ab_def by(auto)   
    qed
  next
    case False
    then have "\<exists>i. x = Cover i"
      using 2 by simp
    then obtain i where "x = Cover i"
      by auto
    then have "(Edge v e 0, Cover i) \<in> arcs G" 
      using assms by simp
    then show ?thesis 
      using G_def_2 by auto
  qed
qed


lemma post_0_edges:
  assumes "sublist [Edge v e 0, x] Cycle" "card (verts G) > 1"
  shows "v \<in> e" "(\<exists>u. (x = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 1)"
proof -
  have "Edge v e 0 \<in> set Cycle" 
    using assms in_sublist_impl_in_list 
    by fastforce 
  then show "v \<in> e" 
    using Edges_in_Cycle by auto 
next
  have "(Edge v e 0, x) \<in> set (vwalk_arcs Cycle)"
    using assms 
    by (simp add: sublist_def if_sublist_then_edge)
  then have "(Edge v e 0, x) \<in> arcs G" 
    using vwalk_arcs_Cycle_subseteq_arcs_G assms 
    by blast
  then show "(\<exists>u. (x = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 1)" 
    using post_0_edges_G by auto
qed


lemma post_1_edges_G:
  assumes "(Edge v e 1, x) \<in> arcs G"
  shows "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (\<exists>i. x = Cover i \<and> last_edge v e E) 
    \<or> (\<exists>e1. x = Edge v e1 0 \<and> next_edge v E e e1)"
proof -
  have "(\<forall>e. e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and> (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G)"
    using G_def in_hc hc_def wf_digraph_def 
    by fast  
  then have 1: "head G (Edge v e 1, x) \<in> verts G" 
    using assms by auto
  have "head G (Edge v e 1, x) = x" 
    using G_def_2 by simp
  then have x_in_verts: "x \<in> verts G" 
    using 1 by auto  
  then have 2: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1) \<or> (\<exists>i. x = Cover i)"
    using G_def_2  
    by auto 
  then show ?thesis proof (cases "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)")
    case True
    then have 3: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)"
      by auto
    show ?thesis proof(cases "\<exists>a b. x = Edge a b 0")
      case True
      then obtain a b where ab_def: "x = Edge a b 0" 
        by auto
      then have 4: "(Edge v e 1, Edge a b 0) \<in> arcs G" 
        using assms by simp
      then have 1: "a = v"  
        using G_def_2 by auto
      then have 2: "next_edge v E e b" 
        using 4 G_def_2 in_arcs_next_edge_1_0 
        by blast 
      then show ?thesis 
        using 1 2 ab_def by simp
    next
      case False
      then have "\<exists>a b. x = Edge a b 1"
        using 3 by simp
      then obtain a b where ab_def: "x = Edge a b 1"
        by auto
      then have 4: "(Edge v e 1, Edge a b 1) \<in> arcs G" 
        using assms by simp
      then have 1: "b = e" 
        using G_def_2 by simp
      have 2: "a \<noteq> v" 
        using 4 G_def_2 by force 
      have "a \<in> e" 
        using 1 x_in_verts ab_def G_def_2 
        by simp
      then show ?thesis 
        using 1 2 ab_def by(auto)   
    qed
  next
    case False
    then have 1: "\<exists>i. x = Cover i"
      using 2 by simp
    then obtain i where "x = Cover i"
      by auto
    then have "(Edge v e 1, Cover i) \<in> arcs G" 
      using assms by simp
    then have "last_edge v e E" 
      using in_arcs_last_edge
      by simp
    then show ?thesis 
      using G_def_2 1 
      by blast
  qed
qed


lemma post_1_edges:
  assumes "sublist [Edge v e 1, x] Cycle" "card (verts G) > 1"
  shows "v \<in> e" "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (\<exists>i. x = Cover i \<and> last_edge v e E) 
    \<or> (\<exists>e1. x = Edge v e1 0 \<and> next_edge v E e e1)"
proof -
  have "Edge v e 1 \<in> set Cycle" 
    using assms in_sublist_impl_in_list 
    by fastforce 
  then show "v \<in> e" 
    using Edges_in_Cycle by auto 
next
  have "(Edge v e 1, x) \<in> set (vwalk_arcs Cycle)"
    using assms 
    by (simp add: sublist_def if_sublist_then_edge)
  then have "(Edge v e 1, x) \<in> arcs G" 
    using vwalk_arcs_Cycle_subseteq_arcs_G assms 
    by blast
  then show "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (\<exists>i. x = Cover i \<and> last_edge v e E) 
    \<or> (\<exists>e1. x = Edge v e1 0 \<and> next_edge v E e e1)"
    using post_1_edges_G by auto
qed


lemma pre_0_edges_G:
  assumes "(x, Edge v e 0) \<in> arcs G"
  shows "(\<exists>u. (x = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (\<exists>i. x = Cover i \<and> first_edge v e E) 
    \<or> (\<exists>e1. x = Edge v e1 1 \<and> next_edge v E e1 e)"
proof -
  have "(\<forall>e. e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and> (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G)"
    using G_def in_hc hc_def wf_digraph_def 
    by fast  
  then have 1: "tail G (x, Edge v e 0) \<in> verts G" 
    using assms by auto
  have "tail G (x, Edge v e 0) = x" 
    using G_def_2 by simp
  then have x_in_verts: "x \<in> verts G" 
    using 1 by auto  
  then have 2: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1) \<or> (\<exists>i. x = Cover i)"
    using G_def_2  
    by auto 
  then show ?thesis proof (cases "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)")
    case True
    then have 3: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)"
      by auto
    show ?thesis proof(cases "\<exists>a b. x = Edge a b 0")
      case True
      then obtain a b where ab_def: "x = Edge a b 0" 
        by auto
      then have 4: "(Edge a b 0, Edge v e 0) \<in> arcs G" 
        using assms by simp
      then have 3: "b = e"  
        using G_def_2 by auto
      have 2: "a \<noteq> v" 
        using 4 G_def_2 by force 
      have "a \<in> e" 
        using 4 x_in_verts ab_def G_def_2 
        by simp
      then show ?thesis 
        using ab_def 2 3 4 by simp
    next
      case False
      then have "\<exists>a b. x = Edge a b 1"
        using 3 by simp
      then obtain a b where ab_def: "x = Edge a b 1"
        by auto
      then have 4: "(Edge a b 1, Edge v e 0) \<in> arcs G" 
        using assms by simp
      then have 1: "a = v" 
        using G_def_2 by simp
      then have "next_edge v E b e"
        using 4 in_arcs_next_edge_1_0 by auto 
      then show ?thesis using 1 2 ab_def by(auto)   
    qed
  next
    case False
    then have 1: "\<exists>i. x = Cover i"
      using 2 by simp
    then obtain i where "x = Cover i"
      by auto
    then have "(Cover i, Edge v e 0) \<in> arcs G" 
      using assms by simp
    then show ?thesis 
      using in_arcs_first_edge 1 by blast
  qed
qed


lemma pre_0_edges:
  assumes "sublist [x, Edge v e 0] Cycle" "card (verts G) > 1"
  shows "v \<in> e" "(\<exists>u. (x = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (\<exists>i. x = Cover i \<and> first_edge v e E) 
    \<or> (\<exists>e1. x = Edge v e1 1 \<and> next_edge v E e1 e)"
proof -
  have "Edge v e 0 \<in> set Cycle" 
    using assms in_sublist_impl_in_list 
    by fastforce 
  then show "v \<in> e" 
    using Edges_in_Cycle by auto 
next
  have "(x, Edge v e 0) \<in> set (vwalk_arcs Cycle)"
    using assms 
    by (simp add: sublist_def if_sublist_then_edge)
  then have "(x, Edge v e 0) \<in> arcs G" 
    using vwalk_arcs_Cycle_subseteq_arcs_G assms 
    by blast  
  then show "(\<exists>u. (x = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (\<exists>i. x = Cover i \<and> first_edge v e E) 
    \<or> (\<exists>e1. x = Edge v e1 1 \<and> next_edge v E e1 e)" 
    using pre_0_edges_G by auto
qed


lemma pre_Cover_G:
  assumes "(x, Cover i) \<in> arcs G"
  shows "(\<exists>j. x = Cover j \<and> j < k) \<or> (\<exists>u e. x = Edge u e 1 \<and> last_edge u e E)" 
proof -
  have "(\<forall>e. e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and> (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G)"
    using G_def in_hc hc_def wf_digraph_def 
    by fast  
  then have 1: "tail G (x, Cover i) \<in> verts G" 
    using assms by auto
  have "tail G (x, Cover i) = x" 
    using G_def_2 by simp
  then have x_in_verts: "x \<in> verts G" 
    using 1 by auto  
  then have 2: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1) \<or> (\<exists>i. x = Cover i)"
    using G_def_2  
    by auto 
  then show ?thesis proof (cases "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)")
    case True
    then have 3: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)"
      by auto
    show ?thesis proof(cases "\<exists>a b. x = Edge a b 0")
      case True
      then obtain a b where ab_def: "x = Edge a b 0" 
        by auto
      then have 4: "(Edge a b 0, Cover i) \<in> arcs G" 
        using assms by simp
      then show ?thesis 
        using ab_def post_0_edges_G by auto 
    next
      case False
      then have "\<exists>a b. x = Edge a b 1"
        using 3 by simp
      then obtain a b where ab_def: "x = Edge a b 1"
        by auto
      then have 4: "(Edge a b 1, Cover i) \<in> arcs G" 
        using assms by simp
      then have "last_edge a b E"
        by (simp add: in_arcs_last_edge) 
      then show ?thesis using ab_def by simp   
    qed
  next
    case False
    then have 1: "\<exists>i. x = Cover i"
      using 2 by simp
    then obtain j where j_def: "x = Cover j"
      by auto
    then have 2: "(Cover j, Cover i) \<in> arcs G" 
      using assms by simp
    then have "Cover j \<in> verts G" 
      using j_def x_in_verts by auto 
    then have "j < k" 
      using G_def_2       
      by simp
    then show ?thesis 
      using 1 2 j_def by simp
  qed
qed


lemma pre_Cover:
  assumes "sublist [x, Cover i] Cycle" "card (verts G) > 1" 
  shows "i<k" "(\<exists>j. x = Cover j \<and> j < k) \<or> (\<exists>u e. x = Edge u e 1 \<and> last_edge u e E)"
proof -
  have "Cover i \<in> set Cycle" 
    using assms in_sublist_impl_in_list 
    by fastforce 
  then show "i<k" 
    using covers_in_Cycle by auto 
next
  have "(x, Cover i) \<in> set (vwalk_arcs Cycle)"
    using assms 
    by (simp add: sublist_def if_sublist_then_edge)
  then have "(x, Cover i) \<in> arcs G" 
    using vwalk_arcs_Cycle_subseteq_arcs_G assms 
    by blast  
  then show "(\<exists>j. x = Cover j \<and> j < k) \<or> (\<exists>u e. x = Edge u e 1 \<and> last_edge u e E)"
    using pre_Cover_G by auto
qed


lemma post_Cover_G:
  assumes "(Cover i, x) \<in> arcs G"
  shows "(\<exists>j. x = Cover j \<and> j < k) \<or> (\<exists>u e. x = Edge u e 0 \<and> first_edge u e E)" 
proof -
  have "(\<forall>e. e \<in> arcs G \<longrightarrow> tail G e \<in> verts G) \<and> (\<forall>e. e \<in> arcs G \<longrightarrow> head G e \<in> verts G)"
    using G_def in_hc hc_def wf_digraph_def 
    by fast  
  then have 1: "head G (Cover i, x) \<in> verts G" 
    using assms by auto
  have "head G (Cover i, x) = x" 
    using G_def_2 by simp
  then have x_in_verts: "x \<in> verts G" 
    using 1 by auto  
  then have 2: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1) \<or> (\<exists>i. x = Cover i)"
    using G_def_2  
    by auto 
  then show ?thesis proof (cases "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)")
    case True
    then have 3: "(\<exists>a b. x = Edge a b 0) \<or> (\<exists>a b. x = Edge a b 1)"
      by auto
    show ?thesis proof(cases "\<exists>a b. x = Edge a b 0")
      case True
      then obtain a b where ab_def: "x = Edge a b 0" 
        by auto
      then have 4: "(Cover i, Edge a b 0) \<in> arcs G" 
        using assms by simp
      then show ?thesis 
        using ab_def in_arcs_first_edge by auto 
    next
      case False
      then have "\<exists>a b. x = Edge a b 1"
        using 3 by simp
      then obtain a b where ab_def: "x = Edge a b 1"
        by auto
      then have 4: "(Cover i, Edge a b 1) \<in> arcs G" 
        using assms by simp
      then show ?thesis 
        using pre_1_edges_G by auto   
    qed
  next
    case False
    then have 1: "\<exists>i. x = Cover i"
      using 2 by simp
    then obtain j where j_def: "x = Cover j"
      by auto
    then have 2: "(Cover i, Cover j) \<in> arcs G" 
      using assms by simp
    then have "Cover j \<in> verts G" 
      using j_def x_in_verts by auto 
    then have "j < k" 
      using G_def_2       
      by simp
    then show ?thesis 
      using 1 2 j_def by simp
  qed
qed


lemma post_Cover:
  assumes "sublist [Cover i, x] Cycle" "card (verts G) > 1" 
  shows "i<k" "(\<exists>j. x = Cover j \<and> j<k) \<or> (\<exists>u e. x = Edge u e 0 \<and> first_edge u e E)"
proof -
  have "Cover i \<in> set Cycle" 
    using assms in_sublist_impl_in_list 
    by fastforce 
  then show "i<k" 
    using covers_in_Cycle by auto 
next
  have "(Cover i, x) \<in> set (vwalk_arcs Cycle)"
    using assms 
    by (simp add: sublist_def if_sublist_then_edge)
  then have "(Cover i, x) \<in> arcs G" 
    using vwalk_arcs_Cycle_subseteq_arcs_G assms 
    by blast  
  then show "(\<exists>j. x = Cover j \<and> j<k) \<or> (\<exists>u e. x = Edge u e 0 \<and> first_edge u e E)"
    using post_Cover_G by auto
qed


lemma b_in_set_cy_exists_sublist: 
  assumes "b \<in> set Cy" "b \<in> set (tl Cy)" "length Cy \<ge> 2"
  shows "\<exists>a. sublist [a, b] Cy"
  using assms proof(induction Cy)
  case Nil
  then show ?case by auto
next
  case (Cons c Cy)
  then have 1: "b \<in> set Cy" 
    by simp
  then show ?case proof(cases "b = hd Cy")
    case True
    then have "(c#Cy) = c#b#tl Cy" 
      by (metis 1 hd_Cons_tl list.distinct(1) list.set_cases) 
    then have "[]@[c,b]@tl Cy = c#Cy" 
      by simp
    then have "sublist [c, b] (c#Cy)" 
      using Cons sublist_def by blast 
    then show ?thesis 
      by auto 
  next
    case False
    have 2: "length Cy \<ge> 2"
    proof (rule ccontr)
      assume "\<not> 2 \<le> length Cy"
      then have "2 > length Cy" 
        by auto
      then have "length Cy = 0 \<or> length Cy = 1" 
        by linarith
      then show False proof 
        assume "length Cy = 0" 
        then have "Cy = []" by simp
        then show False using 1 by simp
      next 
        assume "length Cy = 1" 
        then have "Cy = [b]" 
          using 1 length_1_set_L 
          by metis 
        then have "hd Cy = b" by simp
        then show False using False by simp
      qed
    qed
    then have 3: "b \<in> set (tl Cy)" 
      using False 
      by (metis "1" list.sel(1) list.sel(3) list.set_cases) 
    then have "\<exists>a. sublist [a, b] Cy" 
      using Cons 1 2 3 False by blast
    then show ?thesis using 2 sublist_cons 
      by fast
  qed
qed


lemma a_in_set_cy_exists_sublist: 
  assumes "a \<in> set Cy" "a\<noteq> last Cy" "length Cy \<ge> 2"
  shows "\<exists>b. sublist [a, b] Cy"
  using assms proof(induction Cy)
  case Nil
  then show ?case by auto
next
  case (Cons c Cy)
  then have not_empty: "Cy \<noteq> []"
    using in_set_insert by auto  
  then show ?case proof(cases "a = c")
    case True
    then have "[]@ [a, hd Cy] @ (tl Cy) = (c#Cy)"
      using not_empty by simp 
    then show ?thesis using sublist_def 
      by blast
  next
    case False
    then have in_Cy: "a \<in> set Cy" 
      using Cons by simp
    have not_last: "a\<noteq> last Cy" 
      using Cons not_empty by force  
    then show ?thesis proof(cases "length Cy \<ge> 2")
      case True
      then show ?thesis 
        using Cons not_last in_Cy sublist_cons 
        by fast  
    next
      case False
      then have "length Cy = 1 \<or> length Cy = 0" 
        by linarith 
      then have "length Cy = 1" 
        using not_empty by simp
      then have "Cy = [a]" 
        using in_Cy 
        by (simp add: length_1_set_L) 
      then have "a = last Cy"
        by simp
      then show ?thesis using not_last by simp
    qed
  qed
qed


lemma b_in_Cycle_exists_sublist:
  assumes "b \<in> set Cycle" "length Cycle \<ge> 2" 
  shows "\<exists>a. sublist [a, b] Cycle"
  using assms proof(cases "b = hd Cycle")
  case True
  then have "b = last Cycle"
    by (metis assms(1) assms(2) contains_two_card_greater_1 finite_verts hd_last_Cycle inCycle_inVerts last_in_set list.size(3) not_numeral_le_zero) 
  then have "b \<in> set (tl Cycle)" 
    using assms last_in_set_tl
    by fast 
  then show ?thesis 
    using b_in_set_cy_exists_sublist assms  by metis 
next
  case False
  then have "b \<in> set (tl Cycle)" 
    using assms 
    by (metis hd_Cons_tl list.sel(2) set_ConsD)   
  then show ?thesis 
    using b_in_set_cy_exists_sublist assms by metis
qed


lemma a_in_Cycle_exists_sublist:
  assumes "a \<in> set Cycle" "length Cycle \<ge> 2" 
  shows "\<exists>b. sublist [a, b] Cycle"
  using assms proof(cases "a = last Cycle")
  case True
  then have 1: "a = hd Cycle"
    using assms hd_last_Cycle_dep_length 
    by fastforce
  then obtain b where "b = hd (tl Cycle)" 
    by simp
  then have 2: "a # tl Cycle = Cycle" 
    using 1 
    by (metis assms(1) hd_Cons_tl list.discI list.set_cases) 
  have "tl Cycle \<noteq> []"
    using last_in_set_tl assms  by fastforce 
  then have "[]@[a, b] @ (tl (tl Cycle)) = Cycle"
    using 2 
    by (simp add: \<open>b = hd (tl Cycle)\<close>) 
  then have "sublist [a, b] Cycle" 
    using sublist_def by blast 
  then show ?thesis 
    by auto 
next
  case False   
  then show ?thesis 
    using a_in_set_cy_exists_sublist assms by metis
qed

lemma exists_edge_implies_length_cycle_at_least_4: 
  assumes "e \<in> set E" 
  shows "length Cycle \<ge> 4" 
proof -
  obtain u v where uv_def: "e = {u, v}" "u \<noteq> v" 
    using assms in_hc e_in_E_e_explicit 
    by metis
  then have "u\<in> e" "v\<in> e" 
    by simp+
  then have "Edge v e 0 \<in> verts G" "Edge v e 1 \<in> verts G"
    "Edge u e 0 \<in> verts G" "Edge u e 1 \<in> verts G"
    using assms Edge_v_e_in_G by auto 
  then have in_Cycle: "Edge v e 0 \<in> set Cycle" "Edge v e 1 \<in> set Cycle"
    "Edge u e 0 \<in> set Cycle" "Edge u e 1 \<in> set Cycle"
    by (meson contains_two_card_greater_1 finite_verts hc_node.inject(2) inVerts_inCycle zero_neq_one)+
  show ?thesis proof (rule ccontr) 
    assume "\<not> 4 \<le> length Cycle"
    then have 0: "length Cycle \<le> 3" by simp
    have 1: "{Edge v e 0, Edge v e 1, Edge u e 0, Edge u e 1} \<subseteq> set Cycle" 
      using in_Cycle by fast
    have 2: "card {Edge v e 0, Edge v e 1, Edge u e 0, Edge u e 1} > 3"
      using uv_def 
      by auto
    then have "card {Edge v e 0, Edge v e 1, Edge u e 0, Edge u e 1} \<le> card (set Cycle)" 
      using card_subset 1 by blast
    then have "card (set Cycle) > 3" 
      using 1 2 by linarith 
    then show False using 0 
      by (meson card_length leD le_trans)  
  qed
qed


lemma exists_edge_implies_at_least_on_vertex: 
  assumes "e \<in> set E" 
  shows "1 < card (verts G)" 
proof -
  obtain u v where uv_def: "e = {u, v}" "u \<noteq> v" 
    using assms in_hc e_in_E_e_explicit 
    by metis
  then have "u\<in> e" "v\<in> e" 
    by simp+
  then have in_G: "Edge v e 0 \<in> verts G" "Edge v e 1 \<in> verts G"
    "Edge u e 0 \<in> verts G" "Edge u e 1 \<in> verts G"
    using assms Edge_v_e_in_G by auto 
  show ?thesis proof (rule ccontr) 
    assume "\<not> 1 < card (verts G)"
    then have "card (verts G) = 0 \<or> card (verts G) = 1" 
      by linarith
    then show False proof
      assume "card (verts G) = 0" 
      then have "verts G = {}" 
        using finite_verts by auto 
      then show False using in_G by auto
    next
      assume "card (verts G) = 1" 
      then show False 
        using in_G contains_two_card_greater_1 finite_verts
        by fastforce  
    qed
  qed
qed


lemma sublist_ab_ba_length_geq_4_False: 
  assumes "sublist [a, b] Cycle" "sublist [b, a] Cycle" "length Cycle \<ge> 4" "a \<noteq> b"
  shows "False"
proof -
  have distinct: "distinct (tl Cycle)"
    by (simp add: distinct_tl_Cycle) 
  have not_empty: "Cycle \<noteq> []" 
    using assms sublist_def by auto 
  have card_G: "1 < card (verts G)" 
    using length_cycle_number_verts assms by simp
  then have 1: "hd Cycle = last Cycle" 
    using hd_last_Cycle not_empty by simp
  show ?thesis proof (cases "a = hd Cycle")
    case True
    then have b_hd: "b = hd (tl Cycle)" 
      using assms sublist_hd_tl_equal_b_hd_tl 
      by (simp add: sublist_hd_tl_equal_b_hd_tl "1" distinct_tl_Cycle) 
    then have "sublist [b, a] (tl Cycle)" 
      using assms True
      by (metis hd_Cons_tl not_empty sublist_cons_impl_sublist) 
    have "a = last Cycle" 
      by (simp add: "1" True) 
    then have "tl Cycle = [b, a]"
      using distinct sublist_hd_last_only_2_elems b_hd 
      by (metis \<open>sublist [b, a] (tl Cycle)\<close> assms(1) assms(2) distinct_singleton hd_Cons_tl last_tl sublist_not_cyclic_for_distinct)  
    then have "length (tl Cycle) = 2" 
      by simp
    then have "length Cycle = 3"
      by auto  
    then show ?thesis using assms by auto
  next
    case a: False
    then show ?thesis proof(cases "b = hd Cycle")
      case True
      then have a_hd: "a = hd (tl Cycle)" 
        using assms sublist_hd_tl_equal_b_hd_tl 
        by (simp add: sublist_hd_tl_equal_b_hd_tl "1" distinct_tl_Cycle)  
      then have "sublist [a, b] (tl Cycle)" 
        using assms True
        by (metis hd_Cons_tl not_empty sublist_cons_impl_sublist) 
      have "b = last Cycle" 
        by (simp add: "1" True) 
      then have "tl Cycle = [a, b]"
        using sublist_hd_last_only_2_elems 
        by (metis \<open>sublist [a, b] (tl Cycle)\<close> a_hd assms(1) assms(2) distinct_singleton distinct_tl_Cycle hd_Cons_tl last_tl sublist_not_cyclic_for_distinct)
      then have "length (tl Cycle) = 2" 
        by simp
      then have "length Cycle = 3"
        by auto  
      then show ?thesis using assms by auto
    next
      case b: False
      then have "sublist [a, b] (tl Cycle)" "sublist [b, a] (tl Cycle)"
        using a assms 
        by (metis hd_Cons_tl not_empty sublist_cons_impl_sublist)+ 
      then show ?thesis using distinct 
        by (meson sublist_not_cyclic_for_distinct) 
    qed
  qed
qed





lemma subpath_for_edge: 
  assumes "e \<in> set E" "v \<in> e" "u \<in> e" "u \<noteq> v"
  shows "(sublist [Edge v e 0, Edge v e 1] Cycle \<and> sublist [Edge u e 0, Edge u e 1] Cycle) \<or>
    (sublist [Edge v e 0, Edge v e 1] Cycle \<and> sublist [Edge u e 0, Edge v e 0] Cycle \<and> sublist [Edge v e 1, Edge u e 1] Cycle) \<or>
    (sublist [Edge u e 0, Edge u e 1] Cycle \<and> sublist [Edge v e 0, Edge u e 0] Cycle \<and> sublist [Edge u e 1, Edge v e 1] Cycle)"
proof -
  have length_Cy: "length Cycle \<ge> 4" 
    using assms exists_edge_implies_length_cycle_at_least_4 by simp
  have card_G: "card (verts G) > 1" 
    using assms exists_edge_implies_at_least_on_vertex by simp
  have e_def: "e = {u, v}"  
    using assms e_in_E_e_explicit by auto 
  have "Edge v e 1 \<in> set Cycle" 
    using assms 
    by (meson Edge_v_e_in_Cycle(1) Edge_v_e_in_G(1) contains_two_card_greater_1 finite_verts hc_node.inject(2))
  then have "\<exists>b. sublist [b, Edge v e 1] Cycle" using b_in_Cycle_exists_sublist length_Cy 
    by auto
  then obtain x where x_def: "\<exists>b. sublist [x, Edge v e 1] Cycle"
    by auto
  then have "(\<exists>u. (x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v)) \<or> (x = Edge v e 0)"
    using pre_1_edges card_G by auto  
  then show ?thesis 
  proof 
    assume a1: "\<exists>u. x = Edge u e 1 \<and> u \<in> e \<and> u \<noteq> v"
    then obtain u' where u'_def: "x = Edge u' e 1 \<and> u' \<in> e \<and> u' \<noteq> v"
      by auto
    then have "u' = u" using e_def by blast
    then have sub1: "sublist [Edge u e 1, Edge v e 1] Cycle"
      using a1 u'_def x_def by simp

    have "Edge u e 1 \<in> set Cycle" 
      by (meson sub1 in_sublist_impl_in_list list.set_intros(1))
    then have "\<exists>b. sublist [b, Edge u e 1] Cycle"
      using b_in_Cycle_exists_sublist length_Cy 
      by auto
    then obtain x2 where x2_def: "sublist [x2, Edge u e 1] Cycle" 
      by auto
    then have "(\<exists>v. (x2 = Edge v e 1 \<and> v \<in> e \<and> v \<noteq> u)) \<or> (x2 = Edge u e 0)"  
      using pre_1_edges card_G by auto
    then show ?thesis proof 
      assume "\<exists>v. (x2 = Edge v e 1 \<and> v \<in> e \<and> v \<noteq> u)" 
      then obtain v' where v'_def: "(x2 = Edge v' e 1 \<and> v' \<in> e \<and> v' \<noteq> u)"
        by auto
      then have "v' = v"
        using e_def by blast
      then have "sublist [Edge v e 1, Edge u e 1] Cycle" 
        using x2_def v'_def by simp
      then have "False" 
        using sub1 sublist_ab_ba_length_geq_4_False length_Cy assms by blast
      then show ?thesis by simp
    next
      assume "(x2 = Edge u e 0)"
      then have sub2: "sublist [Edge u e 0, Edge u e 1] Cycle"
        using x2_def by simp

      then have "Edge u e 0 \<in> set Cycle" 
        by (simp add: in_sublist_impl_in_list) 
      have "Edge v e 0 \<in> set Cycle" 
        using assms card_G Edge_v_e_in_Cycle by auto 
      then have "\<exists>b. sublist [Edge v e 0, b] Cycle" 
        using a_in_Cycle_exists_sublist length_Cy by simp
      then obtain x3 where x3_def: 
        "sublist [Edge v e 0, x3] Cycle"
        by auto
      then have "(\<exists>u. x3 = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v) \<or> x3 = Edge v e 1" 
        using post_0_edges card_G 
        by presburger
      then show ?thesis proof
        assume "\<exists>u. x3 = Edge u e 0 \<and> u \<in> e \<and> u \<noteq> v"
        then obtain u' where u'_def: "x3 = Edge u' e 0 \<and> u' \<in> e \<and> u' \<noteq> v"
          by auto
        then have "u' = u" 
          using e_def by auto
        then have sub3: "sublist [Edge v e 0, Edge u e 0] Cycle" 
          using x3_def u'_def 
          by auto  
        show ?thesis using sub1 sub2 sub3 by simp
      next
        assume "x3 = Edge v e 1"
        then have "sublist [Edge v e 0, Edge v e 1] Cycle"
          using x3_def by simp
        then have "Edge v e 0 = Edge u e 1" 
          using sub1 two_sublist_distinct_same_first distinct_tl_Cycle by metis 
        then show ?thesis by simp
      qed
    qed
  next
    assume "x = Edge v e 0"
    then have sub1: "sublist [Edge v e 0, Edge v e 1] Cycle" 
      using x_def by simp

    have "Edge u e 1 \<in> set Cycle"
      using card_G Edge_v_e_in_Cycle assms by blast
    then have "\<exists>b. sublist [b, Edge u e 1] Cycle" 
      using b_in_Cycle_exists_sublist length_Cy 
      by fastforce
    then obtain x2 where x2_def: "sublist [x2, Edge u e 1] Cycle"
      by auto
    then have "(\<exists>v. (x2 = Edge v e 1 \<and> v \<in> e \<and> v \<noteq> u)) \<or> (x2 = Edge u e 0)"
      using pre_1_edges card_G 
      by presburger
    then show ?thesis proof
      assume "\<exists>v. x2 = Edge v e 1 \<and> v \<in> e \<and> v \<noteq> u"
      then obtain v' where v'_def: "x2 = Edge v' e 1 \<and> v' \<in> e \<and> v' \<noteq> u"
        by auto
      then have "v = v'" using e_def by auto
      then have sub2: "sublist [Edge v e 1, Edge u e 1] Cycle" 
        using x2_def v'_def by simp

      have "Edge u e 0 \<in> set Cycle" 
        using card_G Edge_v_e_in_Cycle assms by blast
      then have "\<exists>b. sublist [Edge u e 0, b] Cycle" 
        using a_in_Cycle_exists_sublist length_Cy
        by auto 
      then obtain x3 where x3_def: "sublist [Edge u e 0, x3] Cycle"
        by auto
      then have " (\<exists>v. x3 = Edge v e 0 \<and> v \<in> e \<and> v \<noteq> u) \<or> x3 = Edge u e 1" 
        using post_0_edges card_G by blast
      then show ?thesis proof
        assume "(\<exists>v. x3 = Edge v e 0 \<and> v \<in> e \<and> v \<noteq> u)"
        then obtain v' where v'_def: "x3 = Edge v' e 0 \<and> v' \<in> e \<and> v' \<noteq> u"
          by auto
        then have "v' = v" 
          using e_def by auto
        then have "sublist [Edge u e 0, Edge v e 0] Cycle" 
          using x3_def v'_def by simp
        then show ?thesis using sub1 sub2 by simp
      next
        assume "x3 = Edge u e 1"
        then have "sublist [Edge u e 0, Edge u e 1] Cycle"
          using x3_def by simp
        then have "Edge v e 1 = Edge u e 0" 
          using sub2 two_sublist_distinct_same_first distinct_tl_Cycle 
          by metis
        then show ?thesis by simp
      qed
    next
      assume "x2 = Edge u e 0"
      then have "sublist [Edge u e 0, Edge u e 1] Cycle" 
        using x2_def by simp
      then show ?thesis using sub1 by simp
    qed
  qed
qed



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