theory Vwalk_Cycle
  imports "../Auxiliaries/List_Auxiliaries" "../Auxiliaries/Graph_Auxiliaries" 
begin

definition vwalk_cycle where 
  "vwalk_cycle G p \<equiv> distinct (tl p) \<and> vwalk p G \<and> hd p = last p \<and> length p \<ge> 2"


lemma vwalk_cycle_rev: 
  assumes "symmetric G" "vwalk_cycle G p" 
  shows "vwalk_cycle G (rev p)" 
proof -
  have 1: "hd p = last p" "distinct (tl p)" "vwalk p G" "length p \<ge> 2" 
    using vwalk_cycle_def assms 
    by blast+
  then have 2: "distinct (tl (rev p))"
    using distinct_tl_rev_C 
    by blast
  then have 3: "vwalk (rev p) G"
    using assms 1
    by (simp add: vwalk_rev_ex) 
  have 4: "hd (rev p) = last (rev p)" 
    using 1 hd_rev last_rev 
    by fastforce 
  have 5: "length (rev p) \<ge> 2"
    using 1 
    by simp
  then show ?thesis 
    using 1 2 3 4 vwalk_cycle_def 
    by blast 
qed


lemma vwalk_cycle_not_empty: 
  assumes "vwalk_cycle G p"
  shows "p \<noteq> []" 
  using vwalk_cycle_def assms vwalk_def 
  by auto


lemma vwalk_cycle_vwalk_arcs: 
  assumes "vwalk_cycle G p"
  shows "vwalk_arcs p \<noteq> []"
  using assms vwalk_cycle_def vwalk_arcs_empty_length_p 
  by (metis add_leD2 le_antisym nat_1_add_1 nat_le_iff_add num.distinct(1) one_eq_numeral_iff) 


lemma distinct_awalk_verts_vwalk_arcs: 
  assumes "head G = snd" "tail G = fst" "distinct (tl p)" "length p \<ge> 2"
  shows "distinct (tl (pre_digraph.awalk_verts G u (vwalk_arcs p)))"
  using assms at_least_to_nodes_vwalk_arcs_awalk_verts 
  by (metis leD le_antisym less_one nat_neq_iff num.distinct(1) one_eq_numeral_iff one_le_numeral zero_less_numeral)


lemma awalk_empty_list: 
  assumes "u \<in> verts G" 
  shows "pre_digraph.awalk G u [] u"
proof -
  have 1: "u \<in> verts G" 
    using assms 
    by auto
  have 2: "set [] \<subseteq> arcs G" 
    by simp
  have 3: "pre_digraph.cas G u [] u"
    by (simp add: pre_digraph.cas.simps(1)) 
  then show ?thesis 
    using 1 2 pre_digraph.awalk_def 
    by metis
qed


lemma cas_vwalk_length_at_least_2: 
  assumes "vwalk p G" "head G = snd" "tail G = fst" "length p \<ge> 2"
  shows "pre_digraph.cas G (hd p) (vwalk_arcs p) (last p)"
  using assms 
proof(induction p)
  case (Base u)
  then show ?case 
    using Base 
    by simp
next
  case (Cons u v es)  
  have "vwalk_arcs (u#v#es) = (u, v) # vwalk_arcs (v#es)"
    by simp
  then have a1: "pre_digraph.cas G (hd (u # v # es)) (vwalk_arcs (u # v # es)) (last (u # v # es)) = 
    pre_digraph.cas G (hd (u # v # es)) ((u, v) # (vwalk_arcs (v # es))) (last (u # v # es))"
    by auto
  then have a2: "... = pre_digraph.cas G u ((u, v) # (vwalk_arcs (v # es))) (last (v # es))"
    by simp
  then have a3: "... =  (tail G (u,v) = u \<and> pre_digraph.cas G (head G (u, v)) (vwalk_arcs (v # es)) (last (v # es)))"
    using Cons
    by(auto simp add: pre_digraph.cas.simps) 
  then have a4: "... = pre_digraph.cas G (head G (u, v)) (vwalk_arcs (v # es)) (last (v # es))"
    using Cons 
    by auto
  then have a5: "... = pre_digraph.cas G v (vwalk_arcs (v # es)) (last (v # es))"
    using Cons 
    by simp
  then have 1: "pre_digraph.cas G (hd (u # v # es)) (vwalk_arcs (u # v # es)) (last (u # v # es)) = 
    pre_digraph.cas G v (vwalk_arcs (v # es)) (last (v # es))"
    using a1 a2 a3 a4 a5 
    by argo
  show ?case 
  proof(cases "length es \<le>1")
    case True
    then show ?thesis 
    proof(cases "length es = 1")
      case True
      then have "\<exists>x. es = [x]"
        by (metis length_0_conv length_greater_0_conv length_tl less_numeral_extra(4) list.sel(3) splice.elims zero_less_diff zero_neq_one) 
      then obtain x where x_def: "es = [x]" 
        by auto
      then have 2: "vwalk_arcs (v#es) = [(v, x)]" "last (v#es) = x"
        by auto
      then have "pre_digraph.cas G v (vwalk_arcs (v # es)) (last (v # es)) = 
        pre_digraph.cas G v [(v, x)] x"
        by argo
      then have "... = True" 
        using Cons 
        by(auto simp add: pre_digraph.cas.simps) 
      then show ?thesis 
        using 1 2 
        by auto
    next
      case False
      then have "length es = 0" 
        using True order.not_eq_order_implies_strict 
        by auto 
      then have "es = []" 
        by simp
      then have "last (v # es) = v" "vwalk_arcs (v#es) = []" 
        by auto
      then show ?thesis 
        using a5 1 
        by (simp add: pre_digraph.cas.simps(1)) 
    qed
  next
    case False
    then have "length (v#es) \<ge> 2" 
      by auto
    then have "pre_digraph.cas G (hd (v # es)) (vwalk_arcs (v # es)) (last (v # es))"
      using Cons 
      by blast
    then have 2: "pre_digraph.cas G v (vwalk_arcs (v # es)) (last (v#es))"
      by auto
    then show ?thesis 
      using 1 
      by blast
  qed
qed


lemma awalk_vwalk_length_at_least_2:
  assumes "vwalk p G" "head G = snd" "tail G = fst" "length p \<ge> 2"
  shows "pre_digraph.awalk G (hd p) (vwalk_arcs p) (last p)"
  unfolding pre_digraph.awalk_def 
proof -
  have 1: "hd p \<in> verts G" "set (vwalk_arcs p)\<subseteq> arcs G"
    using assms vwalk_def
    by fastforce+ 
  have 2: "pre_digraph.cas G (hd p) (vwalk_arcs p) (last p)"
    using assms 
    by (simp add: cas_vwalk_length_at_least_2) 
  with 1 show "hd p \<in> verts G \<and> set (vwalk_arcs p) \<subseteq> arcs G \<and> pre_digraph.cas G (hd p) (vwalk_arcs p) (last p)" 
    by simp 
qed


lemma vwalk_cycle_impl_cycle: 
  assumes "head G = snd" "tail G = fst" "vwalk_cycle G p"
  shows "pre_digraph.cycle G (vwalk_arcs p)" 
  using assms 
  unfolding pre_digraph.cycle_def vwalk_cycle_def
  using assms vwalk_cycle_vwalk_arcs distinct_awalk_verts_vwalk_arcs awalk_vwalk_length_at_least_2 
  by metis


lemma last_pre_digraph_cas: 
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []" "head G = snd" "tail G = fst" 
  shows "snd (last p) = v"
  using assms 
proof(induction p arbitrary: u)
  case Nil
  then show ?case 
    by simp 
next
  case (Cons a p)
  then show ?case
  proof(cases "p = []")
    case True
    then have 0: "last (a#p) = a" 
      by simp
    then have "pre_digraph.cas G u (a#p)  v = 
      (tail G a = u \<and> pre_digraph.cas G (head G a) [] v)"
      using True 
      by (simp add: pre_digraph.cas.simps(2)) 
    then have 1: "pre_digraph.cas G (head G a) [] v"
      using Cons 
      by auto
    then have 2: "pre_digraph.cas G (head G a) [] v = 
      ((head G a) = v)" 
      using pre_digraph.cas.simps 
      by fast 
    then have "head G a = snd a" 
      using assms 
      by (auto)
    then show ?thesis 
      using 0 1 2 
      by simp
  next
    case False
    then have 0: "last (a#p) = last p" 
      by simp
    have "pre_digraph.cas G u (a#p)  v = 
      (tail G a = u \<and> pre_digraph.cas G (head G a) p v)"
      by (simp add: pre_digraph.cas.simps(2)) 
    then have "pre_digraph.cas G (head G a) p v"
      using Cons 
      by auto
    then have "snd (last p) = v" 
      using Cons False 
      by simp 
    then show ?thesis 
      using 0 
      by auto 
  qed
qed 

lemma hd_pre_digraph_cas: 
  assumes "pre_digraph.cas G u (p) v" "p\<noteq> []" "head G = snd" "tail G = fst" 
  shows "fst (hd p) = u"
  using assms 
proof(induction p arbitrary: u)
  case Nil
  then show ?case 
    by simp 
next
  case (Cons a p)
  then have "pre_digraph.cas G u (a#p)  v = 
      (tail G a = u \<and> pre_digraph.cas G (head G a) p v)"
    by (simp add: pre_digraph.cas.simps(2))
  then have "tail G a = u" 
    using Cons 
    by simp
  then have "fst a = u" 
    using assms 
    by auto
  then show ?case 
    by simp
qed 


lemma hd_first_edge: 
  assumes "length c \<ge> 2" 
  shows "fst (hd (vwalk_arcs c)) = hd c" 
  using assms 
  by (metis Suc_1 Suc_le_lessD hd_vwalk_arcs_last_p length_C_vwalk_arcs_not_empty) 


lemma tail_last_edge: 
  assumes "length c \<ge> 2" 
  shows "snd (last (vwalk_arcs c))= last c" 
  using assms 
  by (metis Suc_1 last_vwalk_arcs_last_p not_less_eq_eq vwalk_arcs_empty_length_p) 


lemma hd_last_cycle: 
  assumes "length c \<ge> 2" "pre_digraph.cycle G (vwalk_arcs c)" "head G = snd" "tail G = fst"
  shows "hd c = last c" 
proof -
  have 1: "vwalk_arcs c \<noteq> []" 
    using assms pre_digraph.cycle_def 
    by force 
  have "\<exists>u. pre_digraph.awalk G u (vwalk_arcs c) u" 
    using assms pre_digraph.cycle_def 
    by metis
  then obtain u where "pre_digraph.awalk G u (vwalk_arcs c) u" 
    by auto
  then have "pre_digraph.cas G u (vwalk_arcs c) u" 
    using pre_digraph.awalk_def 
    by metis
  then have "fst (hd (vwalk_arcs c)) = u"  "snd (last (vwalk_arcs c)) = u"
    using hd_pre_digraph_cas last_pre_digraph_cas 1 assms 
    by fastforce+
  then have "fst (hd (vwalk_arcs c)) = snd (last (vwalk_arcs c))"
    by simp
  then show ?thesis 
    using hd_first_edge tail_last_edge assms 
    by metis
qed


lemma cycle_implies_vwalk_cycle: 
  assumes "head G = snd" "tail G = fst" "pre_digraph.cycle G (vwalk_arcs c)" 
    "length c \<ge> 2" "wf_digraph G"
  shows "vwalk_cycle G c" 
proof -
  have "\<forall>u. pre_digraph.awalk_verts G u (vwalk_arcs c) = c"
    using assms at_least_to_nodes_vwalk_arcs_awalk_verts 
    by force
  then have 1: "distinct (tl c)" 
    using assms pre_digraph.cycle_def 
    by metis
  have 3: "vwalk c G" 
    using assms 
    by (metis \<open>\<forall>u. pre_digraph.awalk_verts G u (vwalk_arcs c) = c\<close> wf_digraph.awalk_imp_vwalk wf_digraph.cycle_conv) 
  have 4: "hd c = last c"
    using hd_last_cycle assms 
    by metis
  then show ?thesis 
    using 1 3 4 vwalk_cycle_def assms 
    by blast 
qed

end