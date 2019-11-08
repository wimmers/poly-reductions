theory CSTC_Poly
  imports "NREST.NREST" CNF_SAT_to_Clique_2  "Landau_Symbols.Landau_More"
  "NREST.RefineMonadicVCG" "NREST.Refine_Foreach" TSTSC_Poly
begin  

definition "max_size_clauses xs = card (\<Union> (set xs))"
      
definition "add_edges_cstc F S = 
  SPECT [ S \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> \<not> conflict l1 l2 \<and> i \<noteq> j}
       \<mapsto> max_size_clauses F * length F * length F]"

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
definition "cnf_sat_to_clique_space n  = n +n * n"

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


lemma cnf_sat_to_clique_size: "size_Clique (cnf_sat_to_clique p) \<le> cnf_sat_to_clique_space (size_CNF_SAT xs)" 
  (*apply(auto simp: size_Clique_def cnf_sat_to_clique_def cnf_sat_to_clique_space_def size_CNF_SAT_def number_clauses_CNF_SAT_def max_size_clauses_def card_clauses_samller)
  using card_clauses_samller apply(rule order.trans[OF card_Un_le])
  apply(rule add_mono)
  subgoal
    apply(subst paf)
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp
     apply simp
    apply(rule order.trans) apply(rule sum_mono[where g="(\<lambda>_. m*m)"] )
    subgoal for i apply simp
      apply(rule upperbounding_card3) by auto
    apply simp
    done

  subgoal
    apply(subst paf2)
    apply(subst paf)
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp apply simp
    apply(rule order.trans)
     apply(rule sum_mono[where g="\<lambda>_. 9 * length p"])
    subgoal apply simp
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
       apply(rule sum_image_le) apply simp apply simp
      apply(rule order.trans)
       apply(rule sum_mono[where g="\<lambda>_. 9"])
      subgoal
        apply simp apply(rule upperbounding_card3) by auto  
      apply simp done  
    subgoal apply simp done
    done
  done*)
  sorry


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