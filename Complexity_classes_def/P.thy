theory P imports "../IMP-/Big_StepT" begin

type_synonym lang = "nat set"
type_synonym bound_fun = "nat \<Rightarrow> nat"
definition poly :: "(nat \<Rightarrow> nat) \<Rightarrow> bool"
  where "poly== undefined"

lemma poly_add: "\<lbrakk>poly p ; poly q \<rbrakk> \<Longrightarrow> poly (\<lambda>x. p x + q x) "
  sorry

lemma poly_mul: "poly p  \<Longrightarrow> poly (\<lambda>x. a * p x + b ) "
  sorry
lemma poly_comp : "\<lbrakk>poly p; poly q \<rbrakk> \<Longrightarrow> poly (\<lambda>x. p (q x))"
  sorry
lemma poly_monotonic : "\<lbrakk>poly p; poly q ; x \<le> p y; y \<le> q z \<rbrakk> \<Longrightarrow> x \<le> p (q z) "
  sorry
definition time_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"time_bounded c p \<equiv> (\<forall>s. \<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> p (s ''input''))"

definition poly_time_bounded :: "com \<Rightarrow> bool" where
"poly_time_bounded c \<equiv> \<exists>p. poly p \<and> time_bounded c p"



definition comp :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"comp c x r \<equiv> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s (''input'':= r) ))"


definition result_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"result_bounded c p \<equiv> \<forall>x. \<exists>r. comp c x r \<and> r \<le> p x"

definition poly_result_bounded :: "com \<Rightarrow> bool" where
"poly_result_bounded c \<equiv> \<exists>p. poly p \<and> result_bounded c p"


lemma comp_det: "\<lbrakk>comp c x r ; comp c x r'\<rbrakk> \<Longrightarrow> r= r'"
proof -
  assume asm1:"comp c x r"
  assume asm2:"comp c x r'"
  from asm1 have "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> <''input'':=r>" apply (simp add:comp_def)
    by (metis fun_upd_same fun_upd_upd)
  moreover from asm2 have "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> <''input'':=r'>" apply (simp add:comp_def)
    by (metis fun_upd_same fun_upd_upd)
  ultimately show "r=r'"
    by (meson bigstep_det fun_upd_eqD)  
qed

definition decides :: "com \<Rightarrow> lang \<Rightarrow> bool"
  where "decides c L  \<equiv> (\<forall>x. \<exists>r. comp c x r \<and> ( x\<in>L \<longleftrightarrow> r > 0)) "

definition P :: "lang set" where
"P \<equiv> {L. \<exists>c. poly_time_bounded c \<and> decides c L}"


definition verif :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"verif c x z r \<equiv> (\<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>(\<exists>t. (c,s)\<Rightarrow>\<^bsup>t\<^esup> s(''input'':=r)))"
definition is_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_verif c L  \<equiv> (\<forall>x z. \<exists>r. verif c x z r) \<and> (\<forall>x. (x\<in>L \<longleftrightarrow> (\<exists>z r. verif c x z r \<and> r > 0))) "
  

definition is_poly_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_poly_verif c L \<equiv> is_verif c L \<and> poly_time_bounded c"

definition NP :: "lang set" where
"NP \<equiv> {L. \<exists>c. is_poly_verif c L}"

definition is_reduction :: "com \<Rightarrow> lang \<Rightarrow> lang \<Rightarrow> bool" where
" is_reduction c D D' \<equiv> \<forall>x. \<exists>r. comp c x r \<and>( x \<in> D \<longleftrightarrow> r \<in> D') "
definition is_polyreduction :: "com \<Rightarrow> lang \<Rightarrow> lang  \<Rightarrow> bool" where
"is_polyreduction c D D' \<equiv> poly_time_bounded c \<and> is_reduction c D D' \<and> poly_result_bounded c "

definition reduces :: "lang \<Rightarrow> lang \<Rightarrow> bool" where
"reduces D D' \<equiv> \<exists>c. is_polyreduction c D D'"

lemma comp_comp:
  assumes "comp f x y" "comp g y z"
  shows "comp (f;;g) x z"
  apply (simp add:comp_def)
  proof 
  fix s
  show "s ''input'' = x \<longrightarrow>(\<exists>t. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s(''input'' := z))"
  proof
    let ?s' = " s(''input'':=y)"
    assume asmX:"s ''input'' = x"
    from assms(1) have "\<exists>t1. (f,s) \<Rightarrow>\<^bsup> t1 \<^esup> ?s'"   by (simp add:asmX comp_def)
    moreover have asmY: "?s' ''input'' = y" by simp
    hence "\<exists>t2. (g,?s') \<Rightarrow>\<^bsup> t2 \<^esup> ?s'(''input'':=z)" using assms(2) comp_def by blast
    ultimately show "(\<exists>t. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s(''input'' := z))" by auto
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
  from assms(3) obtain pd  where pd_props: "poly pd" "\<forall>x. \<exists>r. comp f x r \<and> r \<le> pd x "
    using poly_result_bounded_def result_bounded_def by auto
  show "\<exists>p. poly p \<and> (\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> p (s ''input'')) "
  proof -
    let ?p = "\<lambda>x. pf x + pg (pd x)"
    have "poly ?p" using poly_add pf_props(1) pg_props(1) poly_comp pd_props(1) by simp    
    moreover have "\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (s ''input'')" 
    proof
      fix s
      show "\<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (s ''input'')" 
      proof -
      obtain s1 t1 where stepf:"(f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s1" "t1 \<le> pf (s ''input'')"
        using pf_props(2)  by (simp add: time_bounded_def) blast
       obtain s2 t2 where stepg:"(g,s1) \<Rightarrow>\<^bsup> t2 \<^esup> s2" "t2 \<le> pg (s1 ''input'')"
         using pg_props(2)  by (simp add: time_bounded_def) blast
       let ?x = "s ''input''"
       obtain r where r_props: "comp f ?x r" "r \<le> pd ?x" using pd_props(2) by auto
       have "s1 ''input'' = r"
         by (metis (no_types, lifting) bigstepT_the_state fun_upd_same r_props(1) comp_def stepf(1))
       hence "t2 \<le> pg r" using stepg(2) by simp
       hence t2_ineq: "t2 \<le> pg (pd ?x)" using r_props(2) pd_props(1) pg_props(1) poly_monotonic
         by blast 
      from stepf stepg have "(f;;g,s) \<Rightarrow>\<^bsup> t1+t2 \<^esup> s2"  "t1+t2 \<le> pf ?x + pg (pd ?x)"
        by blast (simp add: add_mono stepf(2) t2_ineq)
      thus "?thesis" by blast 
    qed 
  qed
  ultimately show ?thesis by auto 
qed
qed

lemma p_sanity:
  assumes "D' \<in> P" "reduces D D'"
  shows "D \<in> P"
  using assms apply (auto simp add:P_def reduces_def)
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
  assumes "comp f x y" "verif g y z r"
  shows "verif (f;;g) x z r"
  apply(simp add: verif_def comp_def)
proof
  fix s
  show " s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow> (\<exists>t. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s(''input'' := r))" 
  proof
    assume asm:" s ''input'' = x \<and> s ''certificate'' = z"
    obtain s' where s'_def:"s' = s(''input'':=y)" by simp
    then obtain t1 where "(f,s)\<Rightarrow>\<^bsup>t1\<^esup> s'" using assms(1) comp_def asm by auto
    moreover have  "s' ''input'' = y" "s' ''certificate'' = z" using asm by (auto simp add: s'_def)
    then obtain t2 where "(g,s')\<Rightarrow>\<^bsup>t2\<^esup> s'(''input'':=r)" using assms(2) verif_def asm by auto
    ultimately have  "(f;;g,s)\<Rightarrow>\<^bsup> t1+t2 \<^esup>  s'(''input'':=r)" by auto
    moreover have " s'(''input'':=r) =  s(''input'' := r)" using s'_def by simp
    ultimately show "(\<exists>t. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s(''input'' := r)) " by auto
  qed
qed

lemma verif_det:
  assumes "verif f x z r" "verif f x z r'"
  shows "r = r'"
proof -
  obtain s where s_def: "s =<''input'':=x,''certificate'':=z>" by simp
  obtain s1 where s1_def: "s1 =<''input'':=r,''certificate'':=z>" by simp
  obtain s2 where s2_def: "s2 =<''input'':=r',''certificate'':=z>" by simp
  from s_def have s_cond:"s ''input'' = x \<and> s ''certificate'' = z" by simp 
  from s_def s1_def have "s(''input'':=r) = s1" by auto 
  hence "\<exists>t. (f,s)\<Rightarrow>\<^bsup>t\<^esup>s1"  using s_cond verif_def[of f x z r] assms(1) by auto
  moreover have "s(''input'':=r') = s2" using  s_def s2_def by auto
  hence "\<exists>t. (f,s)\<Rightarrow>\<^bsup>t\<^esup>s2"  using s_cond verif_def[of f x z r'] assms(2) by auto
  ultimately have "s1=s2"  using big_step_t_determ2 by blast 
  thus "r=r'"  by (metis \<open>s(''input'' := r') = s2\<close> \<open>s(''input'' := r) = s1\<close> fun_upd_eqD)  
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
    thus "(x \<in> D) = (\<exists>z r. verif (f;; g) x z r \<and> 0 < r)" using y_def(1) comp_verif
      by (metis (full_types) assms(2) is_verif_def verif_det) 
  qed
qed

lemma np_sanity:
  assumes "reduces D D'" "D' \<in> NP"
  shows "D \<in> NP"
proof
  from assms(1) obtain f
    where f_def: "is_reduction f D D'" "poly_time_bounded f" "poly_result_bounded f"
    using is_polyreduction_def reduces_def by auto
  from assms(2) obtain g
    where g_def: "is_verif g D'" "poly_time_bounded g" 
    using NP_def is_poly_verif_def by force
  from f_def(1) g_def(1) have "is_verif (f;;g) D" using reduction_verification_correct by simp
  moreover from f_def(2) f_def(3) g_def(2) have "poly_time_bounded (f;;g)"
    using reduction_poly by simp 
  ultimately show  ?thesis using NP_def is_poly_verif_def by auto
qed


  

