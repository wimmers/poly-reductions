theory P imports "../IMP-/Big_StepT"  "../Polynomial_Growth_Functions"  "../Three_Sat_To_Set_Cover"begin

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
  
definition certif_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where 
"certif_bounded c p \<equiv> \<forall>x. (\<exists>z r. verif c x z r \<and> r >0) \<longrightarrow> (\<exists>z r. verif c x z r \<and> r>0 \<and> length z \<le> p (length x))"
definition poly_certif_bounded :: "com \<Rightarrow> bool" where 
"poly_certif_bounded c \<equiv> \<exists>p. poly p \<and> certif_bounded c p "
definition is_poly_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_poly_verif c L \<equiv> is_verif c L \<and> poly_time_bounded c \<and> poly_certif_bounded c"

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
lemma result_bounded_certif_bounded : 
  assumes "result_bounded f q" "cons_certif f" "certif_bounded g p" "\<forall>y z. \<exists>r. verif g y z r "
  shows "certif_bounded (f;;g) (make_mono p o q)"  
proof (auto simp add: certif_bounded_def)
  fix x z r
  assume local_asm:"verif (f;; g) x z r" "0 < r"
  from assms(1) obtain y where y_def: "comp f x y" "length y \<le> q (length x)" using result_bounded_def by blast
  from assms(4) obtain r'' where r'_def: "verif g y z r''"  using certif_bounded_def by presburger
  moreover from y_def(1) r'_def assms(2) have "verif (f;; g) x z r''" using comp_verif by simp
  hence  "r''>0" using local_asm verif_det by blast
  ultimately obtain z' r'   where  z'r'_def: " verif g y z' r'"  "0< r'"  "P.length z' \<le> p (length y)"
    using assms(3) certif_bounded_def by blast
  from z'r'_def(3) have "length z' \<le> make_mono p (length y)"
    using le_trans less_imp_le_nat by blast
  moreover have "make_mono p (length y) \<le> make_mono p (q (length x))"
    using y_def(2) mono_make_mono by (simp add: incseqD)
  ultimately have "length z' \<le>  make_mono p (q (length x)) " by simp
  moreover from z'r'_def(1) y_def(1) assms(2) have "verif (f;;g) x z' r'" using comp_verif by blast
  ultimately show "\<exists>z r. verif (f;; g) x z r \<and> 0 < r \<and> P.length z \<le> make_mono p (q (P.length x))"
    using z'r'_def(2) by blast
qed

lemma poly_result_bounded_poly_certif_bounded:
  assumes "poly_result_bounded f" "cons_certif f" "poly_certif_bounded g" "\<forall>y z. \<exists>r. verif g y z r "
  shows "poly_certif_bounded (f;;g)"
proof (auto simp add: poly_certif_bounded_def)
  
  show "\<exists>p. poly p \<and> certif_bounded (f;; g) p "
  proof - 
    from assms(1) obtain q where q_def: "poly q" "result_bounded f q" using poly_result_bounded_def
      by blast
    from  assms(3) obtain p where p_def: "poly p" "certif_bounded g p" using poly_certif_bounded_def
      by meson
    let ?p = "make_mono p o q"
    from q_def(1) p_def(1) have "poly ?p" 
      by (simp add: poly_compose poly_make_mono_iff)
    moreover have "certif_bounded (f;;g) ?p" using q_def(2) p_def(2) assms(2) assms(4) 
     result_bounded_certif_bounded by simp
    ultimately show ?thesis by blast
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
    where g_def: "is_verif g D'" "poly_time_bounded g" "poly_certif_bounded g"
    using NP_def is_poly_verif_def by force
  from f_def(1) have "cons_certif f" by (simp add: P.is_reduction_def)
  moreover from g_def(1) have "\<forall>y z. \<exists>r. verif g y z r " by (simp add: is_verif_def)
  ultimately have "poly_certif_bounded (f;;g)" using f_def(3) g_def(3) 
      poly_result_bounded_poly_certif_bounded   by blast
  moreover from f_def(1) g_def(1) have "is_verif (f;;g) D" using reduction_verification_correct by simp
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

lemma result_bounded_compose:
  assumes "result_bounded f pf" "result_bounded g pg"
  shows "result_bounded (f;;g) (make_mono pg o pf)"
  apply(auto simp add:result_bounded_def)
proof -
  fix x 
  obtain y z
   where yz_def:"comp f x y" "comp g y z" "length y \<le> pf (length x)" "length z \<le> pg(length y)"
   using assms result_bounded_def by blast
  hence  "comp (f;;g) x z" using comp_comp by simp
  moreover have  "length z \<le> make_mono pg (length y)" using yz_def(4) le_trans by blast 
  hence  " length z \<le> make_mono pg (pf (length x))"
    using yz_def mono_make_mono  le_trans monoD by blast
 ultimately show "\<exists>r. P.comp (f;; g) x r \<and> P.length r \<le> make_mono pg (pf (P.length x))" by auto
qed

lemma poly_result_compose : 
  assumes "poly_result_bounded f" "poly_result_bounded g"
  shows "poly_result_bounded (f;;g)"
   proof -
    obtain pf pg where pf_pg_def: "poly pf" "poly pg " "result_bounded f pf" "result_bounded g pg" 
      using assms is_polyreduction_def poly_result_bounded_def by auto
    have "poly (make_mono pg o pf)" 
      by (simp add: pf_pg_def(1) pf_pg_def(2) poly_compose poly_make_mono_iff)
    moreover have "result_bounded (f;;g) (make_mono pg o pf)"
      using result_bounded_compose pf_pg_def by auto
    ultimately show ?thesis by (auto simp add:poly_result_bounded_def)
  qed

lemma is_reduction_compose:
  assumes "is_reduction f D D'" "is_reduction g D' D''"
  shows "is_reduction (f;;g) D D''"
  apply(auto simp add: is_reduction_def)
  using assms apply(simp add: cons_certif_def is_reduction_def) apply fastforce
proof -
  fix x
   obtain y where y_def: "comp f x y" "(x\<in>D) =(y\<in>D')"
     using assms(1) by (auto simp add:is_reduction_def)
   obtain z where z_def: "comp g y z" "(y\<in>D') =(z\<in>D'')"
     using assms(2) by (auto simp add:is_reduction_def)    
   have  "P.comp (f;; g) x z  \<and> (x \<in> D) = (z \<in> D'')"
     using y_def z_def comp_comp by simp
   thus  "\<exists>r. P.comp (f;; g) x r \<and> (x \<in> D) = (r \<in> D'')" by blast
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
    using fg_def is_reduction_compose apply (simp add: is_polyreduction_def) apply blast
    using fg_def apply (auto simp add: poly_result_compose is_polyreduction_def)
    done
  thus "poly_reduces D D''" by (auto simp add:poly_reduces_def)
qed
lemma "poly_time_bounded c \<Longrightarrow> poly_result_bounded c" oops

definition NP_hard :: "lang set" where 
"NP_hard \<equiv> {L'. \<forall>L\<in>NP. poly_reduces L L'}"

definition NP_complete :: "lang set" where
"NP_complete \<equiv> NP_hard \<inter> NP"

locale encode_decode_sat =
  fixes encode_sat :: "nat three_sat \<Rightarrow> nat" (*I think it should be bounded*)
  fixes decode_sat :: "nat\<Rightarrow> nat three_sat"
  assumes decode_encode_inv : "decode_sat (encode_sat F) = F"
begin
definition IMP_SAT :: "nat set" where 
"IMP_SAT == encode_sat ` {n. sat n}"

lemma main_lemma : 
  fixes c pt p_cer
  assumes "poly pt"
  assumes "poly p_cer"
  assumes "\<forall>s. \<exists>t. Ex (big_step_t (c, s) t) \<and> t \<le> pt (length (s ''input''))"
  assumes "\<forall>x z. \<exists>r. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)"
  shows "\<exists>imp_to_sat t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>s t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')
       \<and> (\<forall>x. \<exists>f.    length f \<le> s_red ( length x )
                   \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(length x)))
                   \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                                        (\<exists>z. length z \<le> p_cer (length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' >0))
                                        )
                      )"
  sorry
lemma NP_reduces_SAT:
  assumes "L \<in> NP"
  shows "poly_reduces L IMP_SAT"
proof -
  obtain v p p_cer where pv_def:"poly p" "is_verif v L" "time_bounded v p" "certif_bounded v p_cer"
    "poly p_cer"
    using assms
    by (auto simp add: NP_def is_poly_verif_def poly_time_bounded_def poly_certif_bounded_def)
  have "poly p" "poly p_cer" using pv_def by auto
  moreover have "\<forall>s. \<exists>t. Ex (big_step_t (v, s) t) \<and> t \<le> p (length (s ''input''))" using pv_def(3) 
    by(auto simp add: time_bounded_def)
  moreover have " \<forall>x z. \<exists>r. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)" using pv_def (2)
    by (auto simp add: is_verif_def verif_def)
  ultimately have "\<exists>imp_to_sat t_red s_red. 
      poly t_red \<and> 
      poly s_red \<and>
      poly p_cer \<and>
       (\<forall>s t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'') \<and>
      (\<forall>x. \<exists>f. length f \<le> s_red ( length x )
              \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(length x)))
              \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                     (\<exists>z. length z \<le> p_cer (length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' >0))
                                        )
      )" using main_lemma by auto
  then obtain imp_to_sat t_red s_red where main_res:
          "poly t_red " "poly s_red" "\<forall>x. \<exists>f. (length f \<le> s_red ( length x ))
              \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(length x)))
              \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                     (\<exists>z. length z \<le> p_cer (length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' >0))
                                        )"
 "cons_certif imp_to_sat"  by (auto simp add:cons_certif_def)
  have "time_bounded imp_to_sat t_red"  using main_res(3)  by (auto simp add:time_bounded_def) blast 
  hence "poly_time_bounded imp_to_sat" using main_res(1) by (auto simp add:poly_time_bounded_def)
  moreover have "result_bounded imp_to_sat s_red"
    apply (auto simp add: result_bounded_def comp_def) 
     using main_res(3) by metis
  hence "poly_result_bounded imp_to_sat" using main_res(2) by(auto simp add:poly_result_bounded_def)
  moreover have "is_reduction imp_to_sat L IMP_SAT" apply (auto simp add:is_reduction_def)
    using main_res(4) apply simp
    subgoal for x
  proof -
    have  "\<exists>f. (length f \<le> s_red ( length x ))
              \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(length x)))
              \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                     (\<exists>z. length z \<le> p_cer (length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' >0))
                                        )"
      using main_res(3) 
      by simp
    then obtain f where f_def: "\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(length x))" 
                        " f \<in> IMP_SAT \<longleftrightarrow>
                    (\<exists>z. length z \<le> p_cer (length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' >0))"
      by auto
    have "comp imp_to_sat x f" using f_def(1) apply (simp add: comp_def) by blast
    moreover have "x\<in>L \<longleftrightarrow> f \<in> IMP_SAT"
    proof
      assume "x\<in>L"
      hence  "\<exists>z r. verif v x z r \<and> 0 < r" using pv_def by (auto simp add: is_verif_def)
      hence  "\<exists>z r. verif v x z r \<and> 0 < r \<and> length z \<le> p_cer (length x)"
        using pv_def(4) certif_bounded_def by blast
      then obtain z  where z_def: "\<forall>r. verif v x z r \<longrightarrow>0< r "  "length z \<le> p_cer (length x)"
        using verif_det by blast
      have "\<forall>s t s'. s ''input'' = x \<and> s ''certificate'' = z 
                             \<and> (v, s) \<Rightarrow>\<^bsup> t \<^esup> s'
                                         \<longrightarrow> s' ''input'' >0"
        apply auto
        subgoal for s t s' 
        proof -
          assume assms: " x = s ''input'' " "(v, s) \<Rightarrow>\<^bsup> t \<^esup> s'"  "z = s ''certificate''"
          obtain r where r_def :"verif v x z r" using pv_def(2) apply(auto simp add: is_verif_def) by blast
          hence "r = s' ''input'' " apply(simp add: verif_def)
            using assms big_step_t_determ2 by blast 
          hence "verif v x z (s' ''input'')" using r_def by simp 
          thus " 0 < s' ''input'' " using z_def  by simp
        qed
        done
      thus "f \<in> IMP_SAT" using f_def(2) z_def(2) bigstep_det  by (auto simp add: verif_def) 
    next 
      assume  "f \<in> IMP_SAT"
      then obtain z where z_def: "\<forall>s t s'. s ''input'' = x \<and> s ''certificate'' = z  \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s'
                           \<longrightarrow> s' ''input'' >0" using f_def by blast 
      obtain r where r_def :"verif v x z r" using pv_def(2) apply(auto simp add: is_verif_def)
        by blast
      obtain s where "s = <''input'':=x, ''certificate'':=z>" by simp
      then have s_def: " s ''input'' = x \<and> s ''certificate'' = z" by simp
      obtain t s' where ts'_def: " (v, s) \<Rightarrow>\<^bsup> t \<^esup> s'" "s' ''input'' = r"
        using r_def s_def apply(simp add: verif_def) by blast
      
      have "s' ''input'' > 0" using s_def ts'_def(1) z_def by auto
      hence "r>0" using ts'_def(2) by simp
      thus   "x \<in> L" using pv_def(2) using is_verif_def r_def by blast
    qed
    ultimately show ?thesis  by auto
  qed
  done
ultimately show ?thesis by (auto simp add:poly_reduces_def is_polyreduction_def)
qed

lemma cook_levin: "IMP_SAT \<in> NP_hard"
  by (simp add: NP_hard_def NP_reduces_SAT)
end


