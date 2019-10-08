theory TSTSC_Poly
  imports "NREST.NREST" Three_Sat_To_Set_Cover  "Landau_Symbols.Landau_More"
  "NREST.RefineMonadicVCG"
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



lemma ispolyred_trans:
  assumes 1: "ispolyred c1 A B ma mb"
    and 2: "ispolyred c2 B C mb mc"
  shows 
      "ispolyred (\<lambda>a. bind (c1 a) c2) A C ma mc"
proof -
  from 1 obtain f1 p1 ps1 where
     spec1: "\<And>pi. c1 pi \<le> SPEC (\<lambda>y. y = f1 pi) (\<lambda>_.  (p1 (ma pi)))"
   and size1: "\<And>pi. mb (f1 pi) \<le> ps1 (ma pi)"
    and p1: "poly p1" "poly ps1" and "is_reduction f1 A B" unfolding ispolyred_def by blast

  from 2 obtain f2 p2 ps2 where
      spec2: "\<And>pi. c2 pi \<le> SPEC (\<lambda>y. y = f2 pi) (\<lambda>_. enat (p2 (mb pi)))"
    and size2: "\<And>pi. mc (f2 pi) \<le> ps2 (mb pi)"
     and p2: "poly p2" "poly ps2" "is_reduction f2 B C" unfolding ispolyred_def by blast

  thm spec1[unfolded SPEC_def, THEN T_specifies_rev]
  thm spec2[unfolded SPEC_def, THEN T_specifies_rev]

  then obtain p2' where p2'_ub: "\<And>x. p2 x \<le> p2' x" and p2'_poly: "poly p2'"
    and   p2'_mono: "\<And>i j. i\<le>j \<Longrightarrow> p2' i \<le> p2' j" 
    sorry (* works because p2 is poly *)

  then obtain ps2' where "\<And>x. ps2 x \<le> ps2' x" and ps2'_poly: "poly ps2'"
    and   ps2'_mono: "\<And>i j. i\<le>j \<Longrightarrow> ps2 i \<le> ps2' j" 
    sorry (* works because ps2 is poly *)
 

  show ?thesis
    unfolding ispolyred_def
    apply(rule exI[where x="f2 o f1"])
    apply(rule exI[where x="\<lambda>n. p1 n + p2' (ps1 n)"])
    apply(rule exI[where x="\<lambda>n. ps2' (ps1 n)"])
    apply safe
    subgoal unfolding SPEC_def
  apply(rule T_specifies_I)
      apply(vcg' \<open>-\<close> rules: spec1[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
  spec2[unfolded SPEC_def, THEN T_specifies_rev, THEN T_conseq4]
        )
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
  


definition "size_IS = (\<lambda>(E,k). card E)"
definition "size_VC = (\<lambda>(E,k). card E)"

section "IS to VC"

definition "mop_get_vertices_card E = REST [(card (\<Union> E)) \<mapsto> card E]"

definition "is_to_vc = (\<lambda>(E,k). 
          do {
            s \<leftarrow> mop_get_vertices_card E;
            if k > s  then
              RETURNT (E,k)
            else
              RETURNT (E, s-k)
          })"

definition "vc_time n = n" 
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


term vertex_cover
lemma "ispolyred is_to_vc independent_set vertex_cover size_IS size_VC" 
  unfolding ispolyred_def
  apply(rule exI[where x=is_vc])
  apply(rule exI[where x=vc_time])
  apply(rule exI[where x=vc_space])
  apply(safe)
  subgoal using is_to_vc_refines by blast
  subgoal using is_to_vc_size  by blast 
  subgoal unfolding poly_def vc_time_def apply(rule exI[where x=1]) by simp
  subgoal unfolding poly_def vc_space_def apply(rule exI[where x=1]) by simp
  subgoal using is_reduction_is_vc .
  done








end