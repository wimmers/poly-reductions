theory CSTC_Poly
  imports "NREST.NREST" CNF_SAT_to_Clique_2  "Landau_Symbols.Landau_More"
  "NREST.RefineMonadicVCG" "NREST.Refine_Foreach" TSTSC_Poly
begin  

definition "max_size_clauses xs = card (\<Union> (set xs))"
      
definition "add_edges_cstc F S = 
  SPECT [ S \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> \<not> conflict l1 l2 \<and> i \<noteq> j}
       \<mapsto> max_size_clauses F * max_size_clauses F * length F * length F]"

definition "add_nodes_cstc F V =
  SPECT [ V \<union>  {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}
       \<mapsto> max_size_clauses F * length F]"

definition cnf_sat_to_clique_alg :: "'a lit set list \<Rightarrow> (('a lit \<times> nat) set set \<times> ('a lit \<times> nat) set  \<times> nat) nrest" where 
  "cnf_sat_to_clique_alg = (\<lambda>F. do {
      b \<leftarrow> SPECT [ finite (\<Union> (set F)) \<mapsto> 1];
      if b then
        do {
          l \<leftarrow> mop_list_length F; 
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> add_edges_cstc F S;
          V \<leftarrow> mop_set_empty_set;
          V \<leftarrow> add_nodes_cstc F V;
          RETURNT ( S, V, l)
        }
      else RETURNT ( {}, {}, 1 )
    })"

definition "number_clauses_CNF_SAT xs = length xs"
definition "size_CNF_SAT xs = number_clauses_CNF_SAT xs * max_size_clauses xs"
(*with number of clauses time  maximum length of the clauses n*)
definition "cnf_sat_to_clique_time n = 4 + n * n  + n"
definition "size_Clique = (\<lambda>(E,V,k). card E + card V)"
definition "cnf_sat_to_clique_space n  = n * n + n"

lemma upperbounding_card_m: "\<forall>x\<in>X. card x \<le> m \<and> finite x \<Longrightarrow> x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> 
        card {{f l1, g l2} |l1 l2. l1 \<in> x \<and> l2 \<in> y \<and> h l1 l2} \<le> m*m"

      apply(rule order.trans)
       apply(rule card_mono) defer
        apply(rule brr)
       apply(rule order.trans) apply(rule card_Un) 
      subgoal by auto
       apply(rule order.trans) apply(rule sum_image_le)
      subgoal using aaa by auto
        apply simp  apply(rule order.trans)
      apply(rule sum_mono[where g="\<lambda>_. m"]) apply simp 
        apply(rule order.trans) apply(rule card_Un)
      subgoal apply (rule finite_imageI) using aaa by auto
       apply(rule order.trans) apply(rule sum_image_le) 
      subgoal by auto
         apply simp apply simp apply(simp)
      apply(rule finite_Union)
       apply (rule finite_imageI) by auto 

    value "max_size_clauses [{a\<^sub>2, a\<^sub>1}]"

lemma aux0:
  assumes "x \<in> set xs" "finite (\<Union> (set xs))" 
  shows "card x \<le> card (\<Union> (set xs))"
 proof -
   have "x \<subseteq> \<Union> (set xs)" using \<open>x\<in>set xs\<close> by(auto)
  then show ?thesis using assms 
    by (simp add: card_mono)  
qed

lemma card_clauses_samller: "x \<in> set xs \<and> finite (\<Union> (set xs)) \<Longrightarrow> card x \<le> max_size_clauses xs"
  by(auto simp add: max_size_clauses_def aux0)

lemma card_V:
  assumes "finite (\<Union> (set p))"
  shows "card {(l1, i). i < length p \<and> l1 \<in> p ! i} \<le> length p * card (\<Union> (set p))"
proof -
  let ?S = "((\<Union> (set p)) \<times> {0..<length p})"
  let ?V = " {(l1, i). i < length p \<and> l1 \<in> p ! i}"
  have 1: "card ?S \<le> (card (\<Union> (set p))) * length p" 
    by (simp add: card_cartesian_product)
  have "?V \<subseteq> ?S" by(auto)+ 
  then show ?thesis using 1 
    by (metis (no_types, lifting) assms card_mono dual_order.trans finite_SigmaI finite_atLeastLessThan mult.commute) 
qed

lemma aux2: "finite E' \<and> E \<subseteq> E' \<Longrightarrow> card E \<le> card E'"
  by (simp add: card_mono)

lemma card_E:
  assumes "finite (\<Union> (set F))"
  shows "card {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F \<and> i \<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}
            \<le> length F * card (\<Union> (set F)) * (length F * card (\<Union> (set F)))"
proof -
  have 0: "\<forall>x\<in> set F. finite x" using assms 
    by (metis Set.set_insert Un_infinite Union_insert)  
  let ?S = "((\<Union> (set F)) \<times> {0..<length F}) \<times> ((\<Union> (set F)) \<times> {0..<length F})"
  let ?E = "{{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F \<and> i \<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  let ?E' = "{{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  have 1: "?E \<subseteq>?E'" by(auto)
  have fin_E: "finite ?E"
    using assms 
    using assms by (fastforce intro: finite_surj[where A = "?S"])
  have fin_E': "finite ?E'"
    using assms 
      using assms by (fastforce intro: finite_surj[where A = "?S"])
  then have 2: "card ?E \<le> card ?E'" 
    by (simp add: CSTC_Poly.aux2 1) 
  have "card ?E' \<le> 
        length F * card (\<Union> (set F)) * (length F * card (\<Union> (set F)))" using assms card_clauses_samller fin_E'  sorry
  then show ?thesis using 1 2 by(auto) 
qed


lemma cnf_sat_to_clique_size: "size_Clique (cnf_sat_to_clique p) \<le> cnf_sat_to_clique_space (size_CNF_SAT p)" 
  apply(auto simp: size_Clique_def cnf_sat_to_clique_def cnf_sat_to_clique_space_def size_CNF_SAT_def number_clauses_CNF_SAT_def max_size_clauses_def card_clauses_samller)
  apply(rule add_mono)
   apply(auto simp add: card_E)
  apply(auto simp add: card_V)
  done


lemma cnf_sat_to_clique_refines:
  "cnf_sat_to_clique_alg F \<le> SPEC (\<lambda>y. y = cnf_sat_to_clique F) (\<lambda>_. cnf_sat_to_clique_time (size_CNF_SAT F))"
  unfolding SPEC_def
  unfolding cnf_sat_to_clique_alg_def cnf_sat_to_clique_def   
      mop_list_length_def mop_set_empty_set_def add_edges_cstc_def
      add_nodes_cstc_def
  apply(rule T_specifies_I) 
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by(auto simp: cnf_sat_to_clique_time_def number_clauses_CNF_SAT_def max_size_clauses_def one_enat_def size_CNF_SAT_def)

lemma cnf_sat_to_clique_ispolyred: "ispolyred cnf_sat_to_clique_alg cnf_sat clique size_CNF_SAT size_Clique" 
  unfolding ispolyred_def
  apply(rule exI[where x=cnf_sat_to_clique])
  apply(rule exI[where x=cnf_sat_to_clique_time])
  apply(rule exI[where x=cnf_sat_to_clique_space])
  apply(safe)
  subgoal using cnf_sat_to_clique_refines by blast
  subgoal using cnf_sat_to_clique_size  by blast 
  subgoal unfolding poly_def cnf_sat_to_clique_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def cnf_sat_to_clique_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_cnf_sat_to_clique .
  done

end