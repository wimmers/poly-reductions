theory TSTSC_Poly
  imports "NREST.NREST" Three_Sat_To_Set_Cover  "Landau_Symbols.Landau_More"
  "NREST.RefineMonadicVCG" "NREST.Refine_Foreach"
begin                             



definition poly :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "poly f = (\<exists>e. f \<in> O(\<lambda>n. n^e))" 
 
lemma poly_plus: "poly f \<Longrightarrow> poly g \<Longrightarrow> poly (\<lambda>x. f x + g x)"
  unfolding poly_def sorry

lemma poly_comp: "poly f \<Longrightarrow> poly g \<Longrightarrow> poly (\<lambda>x. f (g x))"
  unfolding poly_def sorry

lemma poly_linear: "poly (\<lambda>a. a)"
  unfolding poly_def apply(rule exI[where x=1]) by auto

(* a program c :: 'a\<Rightarrow>'b nrest
     is a poly_reduction wrt to a reduction red :: 'a\<Rightarrow>'b\<Rightarrow>bool 
    and a measure for the size of the problem  m :: 'a \<Rightarrow> nat

    if there is a time funtion f, such that
  * f polynomial
  * and for any pi, c calculates a correct result in time f (m pi)
    

  *)
definition "ispolyred c A B ma mb = (\<exists>f p ps. \<forall>pi. c pi \<le> SPEC (\<lambda>y. y = f pi) (\<lambda>_. p (ma pi))
                              \<and>  (\<forall>pi. mb (f pi) \<le> ps (ma pi))
                                   \<and> poly p \<and> poly ps \<and> is_reduction f A B )" 

definition "ispolyredd c RI RO A B ma mb = (\<exists>f p ps. \<forall>pi pi'. ((pi',pi):RI \<longrightarrow>  c pi' \<le> \<Down>RO (SPEC (\<lambda>y. y = f pi) (\<lambda>_. p (ma pi))))
                              \<and>  (\<forall>pi. mb (f pi) \<le> ps (ma pi))
                                   \<and> poly p \<and> poly ps \<and> is_reduction f A B )" 

thm SPEC_def
lemma ispolyredd_generalizes_ispolyred:
  "ispolyred c A B ma mb = ispolyredd c Id Id A B ma mb"
  unfolding ispolyred_def ispolyredd_def by auto

lemma ispolyredd_generalizes_ispolyredD:
  "ispolyred c A B ma mb \<Longrightarrow> ispolyredd c Id Id A B ma mb"
  using ispolyredd_generalizes_ispolyred ..
  

thm conc_fun_chain  

lemma ispolyredd_refine:
  assumes 
    1: "ispolyredd c1 RA RB A B ma mb" 
      and 2: "\<And>pi' pi''. (pi'',pi')\<in>RA' \<Longrightarrow>  c' pi'' \<le> \<Down>RB' (c1 pi')"
  shows 
    "ispolyredd c' (RA' O RA) (RB' O RB) A B ma mb"
proof -
  from 1 obtain f1 p1 ps1 where
     spec1: "\<And>pi pi'. (pi',pi)\<in>RA \<Longrightarrow> c1 pi' \<le> \<Down>RB (SPEC (\<lambda>y. y = f1 pi) (\<lambda>_.  (p1 (ma pi))))"
   and size1: "\<And>pi. mb (f1 pi) \<le> ps1 (ma pi)"
    and p1: "poly p1" "poly ps1" and "is_reduction f1 A B" unfolding ispolyredd_def by blast


  show ?thesis
    unfolding ispolyredd_def
    apply(rule exI[where x=f1])
    apply(rule exI[where x=p1])
    apply(rule exI[where x=ps1])
    apply safe
    subgoal  apply(rule order.trans)
       apply(rule 2) apply simp
      apply(rule order.trans)
       apply(rule nrest_Rel_mono) 
      apply(rule spec1) apply simp
      apply(subst conc_fun_chain) by simp
    subgoal by fact
    subgoal by fact
    subgoal by fact
    subgoal by fact
    done
qed

lemma ispolyredd_trans:
  assumes 1: "ispolyredd c1 RA RB A B ma mb"
    and 2: "ispolyredd c2 RB RC B C mb mc"
  shows 
      "ispolyredd (\<lambda>a. bind (c1 a) c2) RA RC A C ma mc"
proof -
  from 1 obtain f1 p1 ps1 where
     spec1: "\<And>pi pi'. (pi',pi)\<in>RA \<Longrightarrow> c1 pi' \<le> \<Down>RB (SPEC (\<lambda>y. y = f1 pi) (\<lambda>_.  (p1 (ma pi))))"
   and size1: "\<And>pi. mb (f1 pi) \<le> ps1 (ma pi)"
    and p1: "poly p1" "poly ps1" and "is_reduction f1 A B" unfolding ispolyredd_def by blast

  from 2 obtain f2 p2 ps2 where
      spec2: "\<And>pi pi'. (pi',pi)\<in>RB \<Longrightarrow> c2 pi' \<le> \<Down>RC (SPEC (\<lambda>y. y = f2 pi) (\<lambda>_. enat (p2 (mb pi))))"
    and size2: "\<And>pi. mc (f2 pi) \<le> ps2 (mb pi)"
     and p2: "poly p2" "poly ps2" "is_reduction f2 B C" unfolding ispolyredd_def by blast

  thm spec1[unfolded SPEC_def ]
  thm spec2[unfolded SPEC_def ]

  then obtain p2' where p2'_ub: "\<And>x. p2 x \<le> p2' x" and p2'_poly: "poly p2'"
    and   p2'_mono: "\<And>i j. i\<le>j \<Longrightarrow> p2' i \<le> p2' j" 
    sorry (* works because p2 is poly *)

  then obtain ps2' where "\<And>x. ps2 x \<le> ps2' x" and ps2'_poly: "poly ps2'"
    and   ps2'_mono: "\<And>i j. i\<le>j \<Longrightarrow> ps2 i \<le> ps2' j" 
    sorry (* works because ps2 is poly *)
 

  show ?thesis
    unfolding ispolyredd_def
    apply(rule exI[where x="f2 o f1"])
    apply(rule exI[where x="\<lambda>n. p1 n + p2' (ps1 n)"])
    apply(rule exI[where x="\<lambda>n. ps2' (ps1 n)"])
    apply safe
    subgoal unfolding SPEC_def
      apply(rule order.trans)
       apply(rule bindT_refine)
      apply (rule spec1) apply simp
       apply (rule spec2) apply simp
      apply(rule nrest_Rel_mono)  
  apply(rule T_specifies_I)  
      apply(vcg' \<open>-\<close> rules: T_SPEC )
      apply (auto split: if_splits)
      subgoal apply(rule order_trans[OF p2'_ub]) using size1 p2'_mono  
        by auto   
      done
    subgoal apply simp  apply(rule order_trans[OF size2])
      apply(rule ps2'_mono) by(rule size1) 
    subgoal
      using p1 p2'_poly by(auto intro!: poly_plus intro: poly_comp  )
    subgoal
      using p1 ps2'_poly by(auto intro!: poly_plus intro: poly_comp)   
    subgoal
      apply(rule is_reduction_trans) by fact+ 
    done
qed


lemma ispolyred_trans:
  "ispolyred c1 A B ma mb \<Longrightarrow> ispolyred c2 B C mb mc
    \<Longrightarrow> ispolyred (\<lambda>a. bind (c1 a) c2) A C ma mc"
  using ispolyredd_generalizes_ispolyred ispolyredd_trans by metis
    

definition "size_IS = (\<lambda>(E,k). card E)"
definition "size_VC = (\<lambda>(E,k). card E)"

section "IS to VC"

subsection \<open>A trivial implementation\<close>

text \<open>Here we assume that we have an operation that returns
      the size of the set of vertices.\<close>

definition "mop_get_vertices_card E = REST [(card (\<Union> E)) \<mapsto> 2 * card E + 2]"

text \<open>Then we can easily give an abstract algorithm for the reduction:\<close>

definition "is_to_vc = (\<lambda>(E,k). 
          do {
            s \<leftarrow> mop_get_vertices_card E;
            if k > s  then
              RETURNT (E,k)
            else
              RETURNT (E, s-k)
          })"

definition "vc_time n = 2 * n + 2" 
definition "vc_space n = n" 


lemma is_to_vc_refines:
  "is_to_vc vc \<le> SPEC (\<lambda>y. y = is_vc vc) (\<lambda>_. vc_time (size_IS vc))"
  unfolding is_to_vc_def is_vc_def SPEC_def mop_get_vertices_card_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close>)
  by (auto simp: size_IS_def size_VC_def vc_time_def vc_space_def) 

lemma is_to_vc_size:
  "size_VC (is_vc a) \<le> vc_space (size_IS a)"
  apply(cases a)
  by (auto simp: is_vc_def size_IS_def size_VC_def vc_time_def vc_space_def) 

thm is_reduction_is_vc


text \<open>And we show that it actually is a polynomial reduction:\<close>

lemma is_to_vc_ispolyred: "ispolyred is_to_vc independent_set vertex_cover size_IS size_VC" 
  unfolding ispolyred_def
  apply(rule exI[where x=is_vc])
  apply(rule exI[where x=vc_time])
  apply(rule exI[where x=vc_space])
  apply(safe)
  subgoal using is_to_vc_refines by blast
  subgoal using is_to_vc_size  by blast 
  subgoal unfolding poly_def vc_time_def apply(rule exI[where x=1]) by auto
  subgoal unfolding poly_def vc_space_def apply(rule exI[where x=1]) by simp
  subgoal using is_reduction_is_vc .
  done



subsection \<open>A more fine grained algorith\<close>

text \<open>now we assume to only have more fine grained basic operations.\<close>

text \<open>This setup is actually unrealistic, it is hard to imagine a datastructure with
  constant insertion and constant cardinality query.
     TODO: make cost of insert linear in size of S\<close>

definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"

definition "mop_set_card S  = REST [card S \<mapsto> 1]"

definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"


text \<open>Now we want to work on lists of tuples to represent the Edge set:\<close>

definition "R_edge_set_tuple_list = {(xs,E) |xs E. ((\<lambda>(a,b). {a,b}) ` (set xs) = E \<and> distinct xs
           \<and> inj_on (\<lambda>(a,b). {a,b}) (set xs)  )}"
text \<open>here the constraint @{term inj_on} means, that the edge list xs
       does not contain any loops ( (a,a) ),
        or both symmetric edges ( (a,b)\<in>set xs \<and> (b,a)\<in>set xs )\<close> 


text \<open>we can restate the specification to get the cardinality of the set of vertices given
      an edge list, and that it refines the operation @{term mop_get_vertices_card}\<close>

definition "mop_get_vertices_card' xs = REST [(card (\<Union> ((\<lambda>(a,b). {a,b}) ` (set xs)))) \<mapsto> 2 * length xs + 2]"

lemma mop_get_vertices_card_data_refine:  
  assumes "(xs,E)\<in>R_edge_set_tuple_list"
  shows "mop_get_vertices_card' xs \<le> mop_get_vertices_card E"
proof -
  from assms have E: "E = (\<lambda>(a,b). {a,b}) ` (set xs)"
     and *: "distinct xs""inj_on (\<lambda>(a,b). {a,b}) (set xs)"
    unfolding R_edge_set_tuple_list_def by auto
  have **: "card E = length xs" 
    by(simp add: card_image distinct_card E *)
  show ?thesis    
    unfolding mop_get_vertices_card'_def mop_get_vertices_card_def
    unfolding ** by(simp add: E)
qed

text \<open>now let's implement getting the cardinality of V with the basic set operations\<close>

definition get_vertices_card :: "('b*'b) list \<Rightarrow> nat nrest" where
  "get_vertices_card es = do {
      S \<leftarrow> mop_set_empty_set;
      S' \<leftarrow> nfoldli es (\<lambda>_. True) 
            (\<lambda>(a,b) S. do {
                  S \<leftarrow> mop_set_insert S a;
                  S \<leftarrow> mop_set_insert S b;
                  RETURNT S }) 

        S;
      n \<leftarrow> mop_set_card S';
      RETURNT n
    }"
 

lemma get_vertices_card_refine:
  "get_vertices_card xs \<le> mop_get_vertices_card' xs"
proof -
  let ?I = "\<lambda>(xs::('b*'b)list) ys (S::'b set).  S = \<Union> ((\<lambda>(a,b). {a,b}) ` (set xs))"

  show ?thesis
  unfolding get_vertices_card_def mop_get_vertices_card'_def
  apply(rule T_specifies_I)
  apply(subst nfoldliIE_def[symmetric, where I="?I" and E=2])
  unfolding mop_set_empty_set_def
  apply(vcg' -) 
  apply(rule nfoldliIE_rule[THEN T_specifies_rev, THEN T_conseq4, where P2="?I xs []" ])
       apply simp
  subgoal 
    apply(rule T_specifies_I)
    unfolding mop_set_insert_def
    apply(vcg' -)
    apply auto unfolding Some_le_emb'_conv
    by auto
     apply simp
    apply simp
  apply (rule order.refl)
  unfolding mop_set_card_def
  apply (vcg' -) apply auto unfolding Some_le_emb'_conv Some_eq_emb'_conv
   apply (auto simp add: one_enat_def)    
  done 
qed

lemma get_vertices_card_data_refine:
  assumes "(xs,E)\<in>R_edge_set_tuple_list"
  shows "get_vertices_card xs \<le>  (mop_get_vertices_card E)"
  apply(rule order.trans) 
  apply(rule   get_vertices_card_refine)
  apply(rule mop_get_vertices_card_data_refine)
  by fact

text \<open>now we can give a refined algorithm, only using the fine grained operations:\<close>

definition "is_to_vc2 = (\<lambda>(xs,k). 
          do {
            s \<leftarrow> get_vertices_card xs;
            if k > s  then
              RETURNT (xs,k)
            else
              RETURNT (xs, s-k)
          })"


lemma R_reintro: "A \<le>   B \<Longrightarrow> A \<le> \<Down>Id B" by simp

term " prod_rel R_edge_set_tuple_list Id"
lemma is_to_vc2_refines:
  "((xs,k),(E,k)) \<in> R_edge_set_tuple_list \<times>\<^sub>r Id
     \<Longrightarrow> is_to_vc2 (xs,k) \<le> \<Down> (R_edge_set_tuple_list \<times>\<^sub>r Id) (is_to_vc (E,k))"
  unfolding is_to_vc_def is_to_vc2_def
  apply (refine_rcg get_vertices_card_data_refine[THEN R_reintro] )
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: RETURNT_refine prod_rel_def_internal)
  subgoal by(auto intro!: RETURNT_refine simp: prod_rel_def_internal)
  done
lemma is_to_vc2_refines':
  "(i',i) \<in> R_edge_set_tuple_list \<times>\<^sub>r Id
     \<Longrightarrow> is_to_vc2 i' \<le> \<Down> (R_edge_set_tuple_list \<times>\<^sub>r Id) (is_to_vc i)"
  unfolding is_to_vc_def is_to_vc2_def
  apply (refine_rcg get_vertices_card_data_refine[THEN R_reintro] )
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: RETURNT_refine prod_rel_def_internal)
  subgoal by(auto intro!: RETURNT_refine simp: prod_rel_def_internal)
  done


thm ispolyredd_refine[OF is_to_vc_ispolyred[THEN ispolyredd_generalizes_ispolyredD] is_to_vc2_refines' ]
    is_to_vc2_refines

text \<open>Finally we can show that the new algorithm also is a polynomial reduction acting on 
      lists of tuples instead of an abstract edge set\<close>

lemma "ispolyredd is_to_vc2
       (R_edge_set_tuple_list \<times>\<^sub>r nat_rel) (R_edge_set_tuple_list \<times>\<^sub>r nat_rel)
        independent_set vertex_cover size_IS size_VC"
  apply(rule ispolyredd_refine[OF is_to_vc_ispolyred[THEN ispolyredd_generalizes_ispolyredD], simplified])
  apply(rule is_to_vc2_refines' ) .




end