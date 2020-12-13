theory P imports "../IMP-/Big_StepT"  "../Polynomial_Growth_Functions" begin

type_synonym lang = "nat set"
type_synonym bound_fun = "nat \<Rightarrow> nat"

fun length::"nat \<Rightarrow> nat" where
"length  0 = 0" | 
"length  n = 1 + length (n div 2) "
definition time_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"time_bounded c p \<equiv> (\<forall>s. \<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> p (length (s ''input'')))"

definition poly_time_bounded :: "com \<Rightarrow> bool" where
"poly_time_bounded c \<equiv> \<exists>p. poly p \<and> time_bounded c p"



definition comp :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"comp c x r \<equiv> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = r ))"


definition result_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"result_bounded c p \<equiv> \<forall>x. \<exists>r. comp c x r \<and> length r \<le> p (length x)"

definition poly_result_bounded :: "com \<Rightarrow> bool" where
"poly_result_bounded c \<equiv> \<exists>p. poly p \<and> result_bounded c p"


lemma comp_det: "\<lbrakk>comp c x r ; comp c x r'\<rbrakk> \<Longrightarrow> r= r'"
proof -
  assume asm1:"comp c x r"
  assume asm2:"comp c x r'"
  from asm1 obtain s1 where s1_def: "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> s1" "s1 ''input'' =r" 
    by (metis fun_upd_same comp_def)
  moreover from asm2 obtain s2 where s2_def: "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> s2 " "s2 ''input''=r'" 
    by (metis fun_upd_same fun_upd_upd comp_def)
  ultimately have "s1 = s2"
    by (meson bigstep_det fun_upd_eqD)
  thus "r=r'" using s1_def s2_def by simp
qed

definition decides :: "com \<Rightarrow> lang \<Rightarrow> bool"
  where "decides c L  \<equiv> (\<forall>x. \<exists>r. comp c x r \<and> ( x\<in>L \<longleftrightarrow> r > 0)) "

definition P :: "lang set" where
"P \<equiv> {L. \<exists>c. poly_time_bounded c \<and> decides c L}"


definition verif :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"verif c x z r \<equiv> (\<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                  (\<exists>t s'. (c,s)\<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = r ))"
definition is_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_verif c L  \<equiv> (\<forall>x z. \<exists>r. verif c x z r) \<and> (\<forall>x. (x\<in>L \<longleftrightarrow> (\<exists>z r. verif c x z r \<and> r > 0))) "
  

definition is_poly_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_poly_verif c L \<equiv> is_verif c L \<and> poly_time_bounded c"

definition NP :: "lang set" where
"NP \<equiv> {L. \<exists>c. is_poly_verif c L}"

definition cons_certif :: "com \<Rightarrow> bool" where
"cons_certif c = (\<forall>s t s'. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')"
definition is_reduction :: "com \<Rightarrow> lang \<Rightarrow> lang \<Rightarrow> bool" where
"is_reduction c D D' \<equiv> cons_certif c \<and>( \<forall>x. \<exists>r. comp c x r \<and>( x \<in> D \<longleftrightarrow> r \<in> D'))   "
definition is_polyreduction :: "com \<Rightarrow> lang \<Rightarrow> lang  \<Rightarrow> bool" where
"is_polyreduction c D D' \<equiv> poly_time_bounded c \<and> is_reduction c D D' \<and> poly_result_bounded c "

definition poly_reduces :: "lang \<Rightarrow> lang \<Rightarrow> bool" where
"poly_reduces D D' \<equiv> \<exists>c. is_polyreduction c D D'"

lemma comp_comp:
  assumes "comp f x y" "comp g y z"
  shows "comp (f;;g) x z"
  apply (simp add:comp_def)
  proof 
  fix s
  show "s ''input'' = x \<longrightarrow>(\<exists>t s'. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = z)"
  proof
    assume asmX:"s ''input'' = x"
    from assms(1) obtain s' where s'_def: "\<exists>t1. (f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s'" "s' ''input''= y"
      using comp_def asmX by blast    
    moreover  obtain s'' where s''_def:  "\<exists>t2. (g,s') \<Rightarrow>\<^bsup> t2 \<^esup> s''" "s'' ''input''=z"
      using assms(2) comp_def s'_def(2) by blast
    ultimately have "(\<exists>t. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup>s'')" by auto
    thus "(\<exists>t s'. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = z)" using s''_def(2)  by auto  
  qed
qed

lemma reduction_decision_correct: 
  assumes "is_reduction f D D'" "decides g D'"
  shows "decides (f;;g) D "
  apply ( simp add: is_polyreduction_def decides_def)
proof
  fix x
  obtain y where f_part:"comp f x y" " x \<in> D \<longleftrightarrow> y \<in> D'" using assms(1) is_reduction_def by metis
  obtain z where g_part:"comp g y z" "y \<in> D' \<longleftrightarrow> z > 0" using assms(2) decides_def by meson
  hence "comp (f;;g) x z" using comp_comp f_part(1)_g_part(1) by auto
  moreover have "x \<in>D \<longleftrightarrow> 0 < z" using f_part(2) g_part(2) by blast
  ultimately show "\<exists>r. comp (f;; g) x r \<and> (x \<in> D) = (0 < r)" by auto 
qed


lemma reduction_poly:
  assumes "poly_time_bounded f" "poly_time_bounded g"  "poly_result_bounded f"
  shows "poly_time_bounded (f;;g)"
  apply (simp add:poly_time_bounded_def time_bounded_def)
proof -
  from assms(1) obtain pf where pf_props:"poly pf" "time_bounded f pf" 
    using poly_time_bounded_def by blast
  from assms(2) obtain pg where pg_props:"poly pg" "time_bounded g pg"
    using poly_time_bounded_def by blast
  from assms(3) obtain pd  where pd_props: "poly pd" "\<forall>x. \<exists>r. comp f x r \<and> length r \<le> pd (length x) "
    using poly_result_bounded_def result_bounded_def by auto
  show "\<exists>p. poly p \<and> (\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> p (length (s ''input''))) "
  proof -
    let ?p = "\<lambda>x. pf x + (make_mono pg o pd) x"
    have "poly ?p"
      using poly_add pf_props(1) pg_props(1) poly_compose pd_props(1) poly_make_mono_iff by metis   
    moreover have "\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (length (s ''input''))" 
    proof
      fix s
      show "\<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (length (s ''input''))" 
      proof -
      obtain s1 t1 where stepf:"(f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s1" "t1 \<le> pf (length(s ''input''))"
        using pf_props(2)  by (simp add: time_bounded_def) blast
       obtain s2 t2 where stepg:"(g,s1) \<Rightarrow>\<^bsup> t2 \<^esup> s2" "t2 \<le> pg (length (s1 ''input''))"
         using pg_props(2)  by (simp add: time_bounded_def) blast
       let ?x = "s ''input''"
       obtain r where r_props: "comp f ?x r" "length r \<le> pd (length ?x)" using pd_props(2) by auto
       have "s1 ''input'' = r"
         by (metis (no_types, lifting) bigstepT_the_state fun_upd_same r_props(1) comp_def stepf(1))
       hence "t2 \<le> pg(length  r)" using stepg(2) by simp
       hence "t2 \<le> make_mono pg (length r)" using le_trans by blast
       moreover have "make_mono pg (length r) \<le> make_mono pg (pd (length ?x))"
         using r_props(2) mono_make_mono[of pg] incseq_def  by blast
       ultimately have t2_ineq: "t2 \<le> (make_mono pg o pd)(length ?x)" by fastforce
       hence "(f;;g,s) \<Rightarrow>\<^bsup> t1+t2 \<^esup> s2"  "t1+t2 \<le> pf (length ?x) + (make_mono pg o pd) (length ?x)"
         using stepf(1) stepg (1) apply blast
          using add_mono stepf(2) t2_ineq by blast
      thus "?thesis" by blast 
    qed 
  qed
  ultimately show ?thesis by auto 
qed
qed

lemma p_sanity:
  assumes "D' \<in> P" "poly_reduces D D'"
  shows "D \<in> P"
  using assms apply (auto simp add:P_def poly_reduces_def)
proof 
  fix g f
  assume assms:"is_polyreduction f D D'"
       "poly_time_bounded g" "decides g D'"
  show "poly_time_bounded (f;;g) \<and> decides (f;;g) D "
  proof
    show "poly_time_bounded (f;;g)"
      using assms is_polyreduction_def reduction_poly by auto
  next 
    show "decides (f;;g) D"
      using assms(1) assms(3) reduction_decision_correct is_polyreduction_def by blast 
qed
qed

lemma comp_verif:
  assumes "comp f x y" "verif g y z r" "cons_certif f"
  shows "verif (f;;g) x z r"
  apply(simp add: verif_def comp_def)
proof
  fix s
  show " s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
             (\<exists>t s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)" 
  proof
    assume asm:" s ''input'' = x \<and> s ''certificate'' = z"
    then obtain s' t1 where s'_def:"(f,s)\<Rightarrow>\<^bsup>t1\<^esup> s'" "s' ''input'' = y" "s' ''certificate'' =z" 
      using assms(1) assms(3) comp_def asm cons_certif_def by metis 
    moreover obtain s'' t2 where "(g,s')\<Rightarrow>\<^bsup>t2\<^esup> s''" " s'' ''input'' = r"
        using assms(2) verif_def s'_def  by auto
    ultimately have  "(f;;g,s)\<Rightarrow>\<^bsup> t1+t2 \<^esup>  s'' \<and> s'' ''input''=r " by auto
    thus "(\<exists>t s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r) " by auto
  qed
qed

lemma verif_det:
  assumes "verif f x z r" "verif f x z r'"
  shows "r = r'"
proof -
  obtain s where "s =<''input'':=x,''certificate'':=z>" by simp
  hence s_def: "s ''input'' = x \<and> s ''certificate'' = z" by simp
  obtain s1 where s1_def:  "\<exists>t. (f,s)\<Rightarrow>\<^bsup>t\<^esup>s1" "s1 ''input'' = r" 
    using assms(1) s_def verif_def by blast
   moreover obtain s2 where s2_def:  "\<exists>t. (f,s)\<Rightarrow>\<^bsup>t\<^esup>s2" "s2 ''input'' = r'" 
    using assms(2) s_def verif_def by blast
  ultimately show  "r=r'"  using big_step_t_determ2 by blast   
qed

lemma reduction_verification_correct:

  assumes "is_reduction f D D'" "is_verif g D'"
  shows "is_verif (f;;g) D"         
  apply(simp add:is_verif_def)
proof
  show "\<forall>x z. \<exists>r. verif (f;; g) x z r"
  proof fix x 
    show "\<forall>z. \<exists>r. verif (f;; g) x z r" 
    proof 
      fix z
      from assms(1) obtain y where  "comp f x y " using is_reduction_def by meson
      moreover from assms(2) obtain r where  "verif g y z r" using is_verif_def by meson
      moreover have "cons_certif f" using assms(1) is_reduction_def  by simp
      ultimately show "\<exists>r. verif (f;;g) x z r" using comp_verif by blast
      qed
    qed
next
  show "\<forall>x. (x \<in> D) = (\<exists>z r. verif (f;; g) x z r \<and> 0 < r)"
  proof
    fix x 
    from assms(1) obtain y where y_def:  "comp f x y " " (x\<in>D) = (y\<in>D')" 
      using is_reduction_def by meson
    moreover from assms(2) have "(y\<in>D')  = (\<exists>z r. verif g y z r \<and> r > 0)" 
      using is_verif_def by simp 
    ultimately have "(x \<in> D) = (\<exists>z r. verif g y z r \<and> r > 0) " by simp
    moreover have "cons_certif f" using assms(1) is_reduction_def  by simp
    ultimately show "(x \<in> D) = (\<exists>z r. verif (f;; g) x z r \<and> 0 < r)" using y_def(1) comp_verif
      by (metis (full_types) assms(2) is_verif_def verif_det) 
  qed
qed

lemma np_sanity:
  assumes "poly_reduces D D'" "D' \<in> NP"
  shows "D \<in> NP"
proof -
  from assms(1) obtain f
    where f_def: "is_reduction f D D'" "poly_time_bounded f" "poly_result_bounded f"
    using is_polyreduction_def poly_reduces_def by auto
  from assms(2) obtain g
    where g_def: "is_verif g D'" "poly_time_bounded g" 
    using NP_def is_poly_verif_def by force
  from f_def(1) g_def(1) have "is_verif (f;;g) D" using reduction_verification_correct by simp
  moreover from f_def(2) f_def(3) g_def(2) have "poly_time_bounded (f;;g)"
    using reduction_poly by blast
  ultimately show  ?thesis using NP_def is_poly_verif_def  by auto
qed

lemma "poly_reduces D D"
  apply(simp add:poly_reduces_def is_polyreduction_def)
proof
  let ?c=SKIP
  show "poly_time_bounded ?c \<and> is_reduction ?c D D \<and> poly_result_bounded ?c" 
    apply (auto)
    apply(auto simp add:poly_time_bounded_def)
    subgoal
    proof
      let ?p = "(\<lambda>x. 1)"
      have "poly ?p" by simp 
      moreover have "time_bounded SKIP ?p"
        using time_bounded_def by auto 
      ultimately show "poly ?p \<and> time_bounded SKIP ?p" by simp
    qed
     apply (auto simp add: is_reduction_def cons_certif_def comp_def poly_result_bounded_def)
    subgoal for x
    proof
      show "(\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (SKIP, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = x)) \<and> (x \<in> D) = (x \<in> D)"
        by auto
    qed
  proof
    let ?p= "(\<lambda>a .a)"
    show "poly ?p \<and> result_bounded SKIP ?p" 
      apply(auto simp add:poly_linear result_bounded_def)
      subgoal for x 
      proof
        show " P.comp SKIP x x \<and> P.length x \<le> P.length x "
          by (auto simp add: comp_def)
      qed
      done
  qed
qed

lemma "poly_reduces_trans":
  assumes "poly_reduces D D'"  "poly_reduces D' D''" 
  shows "poly_reduces D D''"
proof -
  from assms obtain f g where fg_def: "is_polyreduction f D D'" "is_polyreduction g D' D''" 
    by (auto simp add:poly_reduces_def)
  let ?c= "f;;g"
  have  "is_polyreduction ?c D D''" 
    apply (auto simp add:is_polyreduction_def  reduction_poly)
    using fg_def apply (simp add: is_polyreduction_def reduction_poly)
    apply(auto simp add:is_reduction_def)
    using fg_def apply (simp add:cons_certif_def is_polyreduction_def is_reduction_def) 
      apply fastforce 
    subgoal for x
    proof - 
      obtain y z where "comp f x y" "comp g y z" "(x\<in>D) =(y\<in>D')" "(y\<in>D') = (z \<in> D'')" 
        using fg_def is_polyreduction_def poly_result_bounded_def result_bounded_def
        by (metis (full_types) is_reduction_def) 
      hence  "comp (f;; g) x z \<and> (x \<in> D) = (z \<in> D'')" using comp_comp by blast
      thus ?thesis by blast
    qed
    apply(auto simp add:poly_result_bounded_def)
  proof -
    obtain pf pg where pf_pg_def: "poly pf" "poly pg " "result_bounded f pf" "result_bounded g pg" 
      using fg_def(1) fg_def(2) is_polyreduction_def poly_result_bounded_def by auto
    have "poly (make_mono pg o pf) \<and> result_bounded (f;;g) (make_mono pg o pf)" 
      apply auto
      apply (simp add: pf_pg_def(1) pf_pg_def(2) poly_compose poly_make_mono_iff)
      apply(simp add:result_bounded_def)
      subgoal
      proof
        fix x
        obtain y z
          where yz_def:"comp f x y" "comp g y z" "length y \<le> pf (length x)" "length z \<le> pg(length y)"
          using pf_pg_def(3) pf_pg_def(4) result_bounded_def by blast
        have "length z \<le> make_mono pg (length y)" using yz_def(4) le_trans by blast 
        hence  " length z \<le> make_mono pg (pf (length x))"
          using yz_def mono_make_mono  le_trans monoD by blast
        moreover have "comp (f;;g) x z" 
          using yz_def comp_comp by blast
        ultimately show "\<exists>r. P.comp (f;; g) x r \<and> P.length r \<le> make_mono pg (pf (P.length x))" 
          by auto
      qed
      done
      then show  "\<exists>p. poly p \<and> result_bounded (f;; g) p " by blast
  qed
  thus "poly_reduces D D''" by (auto simp add:poly_reduces_def)
qed
lemma "poly_time_bounded c \<Longrightarrow> poly_result_bounded c" oops

definition NP_hard :: "lang set" where 
"NP_hard \<equiv> {L'. \<forall>L\<in>NP. poly_reduces L L'}"

definition NP_complete :: "lang set" where
"NP_complete \<equiv> NP_hard \<inter> NP"
  
