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
definition bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"bounded c p \<equiv> (\<forall>s. \<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> p (s ''input''))"

definition poly_bounded :: "com \<Rightarrow> bool" where
"poly_bounded c \<equiv> \<exists>p. poly p \<and> bounded c p"




definition res :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"res c x r \<equiv> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s (''input'':= r) ))"

lemma res_det: "\<lbrakk>res c x r ; res c x r'\<rbrakk> \<Longrightarrow> r= r'"
proof -
  assume asm1:"res c x r"
  assume asm2:"res c x r'"
  from asm1 have "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> <''input'':=r>" apply (simp add:res_def)
    by (metis fun_upd_same fun_upd_upd)
  moreover from asm2 have "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> <''input'':=r'>" apply (simp add:res_def)
    by (metis fun_upd_same fun_upd_upd)
  ultimately show "r=r'"
    by (meson bigstep_det fun_upd_eqD)  
qed

definition decides :: "com \<Rightarrow> lang \<Rightarrow> bool"
  where "decides c L  \<equiv> (\<forall>x. \<exists>r. res c x r \<and> ( x\<in>L \<longleftrightarrow> r > 0)) "

definition verifies :: "com \<Rightarrow> lang" where
"verifies c \<equiv> {x. \<exists>z.  \<down>\<^sub>s (c,<''input'' := x , ''certificate'':= z>) ''output''> 0 } "
  
(*
definition TIME :: "bound_fun \<Rightarrow> lang set" where
"TIME p \<equiv> {L. \<exists>c. decides c = L \<and> bounded c p}"
*)
definition P :: "lang set" where
"P \<equiv> {L. \<exists>c. poly_bounded c \<and> decides c L}"


definition is_poly_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_poly_verif c L \<equiv> verifies c = L \<and> poly_bounded c"

definition NP :: "lang set" where
"NP \<equiv> {L. \<exists>c. is_poly_verif c L}"

definition is_reduction :: "com \<Rightarrow> lang \<Rightarrow> lang  \<Rightarrow> bool" where
"is_reduction c D D' \<equiv> poly_bounded c \<and>
                      (\<exists>p. poly p \<and> (\<forall>x. \<exists>r. res c x r \<and> r \<le> p x ))\<and>
                       (\<forall>x. \<exists>r. res c x r \<and>( x \<in> D \<longleftrightarrow> r \<in> D')) "

definition reduces :: "lang \<Rightarrow> lang \<Rightarrow> bool" where
"reduces D D' \<equiv> \<exists>c. is_reduction c D D'"

lemma res_comp:
  assumes "res f x y" "res g y z"
  shows "res (f;;g) x z"
  apply (simp add:res_def)
  proof 
  fix s
  show "s ''input'' = x \<longrightarrow>(\<exists>t. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s(''input'' := z))"
  proof
    let ?s' = " s(''input'':=y)"
    assume asmX:"s ''input'' = x"
    from assms(1) have "\<exists>t1. (f,s) \<Rightarrow>\<^bsup> t1 \<^esup> ?s'"   by (simp add:asmX res_def)
    moreover have asmY: "?s' ''input'' = y" by simp
    hence "\<exists>t2. (g,?s') \<Rightarrow>\<^bsup> t2 \<^esup> ?s'(''input'':=z)" using assms(2) res_def by blast
    ultimately show "(\<exists>t. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s(''input'' := z))" by auto
  qed
  qed

lemma res_decomp:
  assumes "res (f;;g) x r" "res f x y"  "res g y z"
  shows "z =r"
  using assms res_comp res_det by blast

lemma reduction_correct: 
  assumes "is_reduction f D D'" "decides g D'"
  shows "decides (f;;g) D "
  apply ( simp add: is_reduction_def decides_def)
proof
  fix x
  obtain y where f_part:"res f x y" " x \<in> D \<longleftrightarrow> y \<in> D'" using assms(1) is_reduction_def by blast
  obtain z where g_part:"res g y z" "y \<in> D' \<longleftrightarrow> z > 0" using assms(2) decides_def by meson
  hence "res (f;;g) x z" using res_comp f_part(1)_g_part(1) by auto
  moreover have "x \<in>D \<longleftrightarrow> 0 < z" using f_part(2) g_part(2) by blast
  ultimately show "\<exists>r. res (f;; g) x r \<and> (x \<in> D) = (0 < r)" by auto 
qed

lemma reduction_poly:
  assumes "poly_bounded f" "poly_bounded g"  "(\<exists>p. poly p \<and> (\<forall>x. \<exists>r. res f x r \<and> r \<le> p x )) "
  shows "poly_bounded (f;;g)"
  apply (simp add:poly_bounded_def bounded_def)
proof -
  from assms(1) obtain pf where pf_props:"poly pf" "bounded f pf"  using poly_bounded_def by blast
  from assms(2) obtain pg where pg_props:"poly pg" "bounded g pg"  using poly_bounded_def by blast
  from assms(3) obtain pd  where pd_props: "poly pd" "\<forall>x. \<exists>r. res f x r \<and> r \<le> pd x " by auto
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
        using pf_props(2)  by (simp add: bounded_def) blast
       obtain s2 t2 where stepg:"(g,s1) \<Rightarrow>\<^bsup> t2 \<^esup> s2" "t2 \<le> pg (s1 ''input'')"
         using pg_props(2)  by (simp add: bounded_def) blast
       let ?x = "s ''input''"
       obtain r where r_props: "res f ?x r" "r \<le> pd ?x" using pd_props(2) by auto
       have "s1 ''input'' = r"
         by (metis (no_types, lifting) bigstepT_the_state fun_upd_same r_props(1) res_def stepf(1))
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
  assume assms:"is_reduction f D D'"
       "poly_bounded g" "decides g D'"
  show "poly_bounded (f;;g) \<and> decides (f;;g) D "
  proof
    show "poly_bounded (f;;g)"
      using assms is_reduction_def reduction_poly by auto
  next 
    show "decides (f;;g) D"
      using assms(1) assms(3) reduction_correct by blast 
qed


  

