theory CSTC_Poly
  imports "NREST.NREST" CNF_SAT_to_Clique  "Landau_Symbols.Landau_More"
  "NREST.RefineMonadicVCG" "NREST.Refine_Foreach" TSTSC_Poly
begin  

definition "max_size_clauses xs = card (set xs)"
      
definition "add_edges_cstc F S = 
  SPECT [ S \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> \<not> conflict l1 l2}
       \<mapsto> max_size_clauses F * length F * length F]"

definition "add_nodes_cstc F V =
  SPECT [ V \<union>  {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}
       \<mapsto> max_size_clauses F * length F]"


definition sat_to_is :: "'a lit set list \<Rightarrow> (('a lit \<times> nat) set set \<times> ('a lit \<times> nat) set  \<times> nat) nrest" where 
  "sat_to_is = (\<lambda>F. do {
        do {
          l \<leftarrow> mop_list_length F; 
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> add_edges_cstc F S;
          V \<leftarrow> mop_set_empty_set;
          V \<leftarrow> add_nodes_cstc F V;
          RETURNT ( S, V, l)
        }
    })"


end