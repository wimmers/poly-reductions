theory "IMP-_Reductions"
  imports Abstractions Bounds 
begin

definition is_reduction :: "com \<Rightarrow> lang \<Rightarrow> lang \<Rightarrow> bool" where
"is_reduction c D D' \<equiv> cons_certif c \<and>( \<forall>x. \<exists>r. comp c x r \<and>( x \<in> D \<longleftrightarrow> r \<in> D'))   "


lemma reduction_decision_correct: 
  assumes "is_reduction f D D'" "decides g D'"
  shows "decides (f;;g) D "
proof (auto simp add: is_reduction_def decides_def)
  fix x
  obtain y where f_part:"comp f x y" " x \<in> D \<longleftrightarrow> y \<in> D'" using assms(1) is_reduction_def by metis
  obtain z where g_part:"comp g y z" "y \<in> D' \<longleftrightarrow> z = 0" using assms(2) decides_def by meson
  hence "comp (f;;g) x z" using comp_comp f_part(1)_g_part(1) by auto
  moreover have "x \<in>D \<longleftrightarrow> 0 = z" using f_part(2) g_part(2) by blast
  ultimately show "\<exists>r. Abstractions.comp (f;; g) x r \<and> (x \<in> D) = (r = 0)" by blast
qed

lemma reduction_verification_correct:
  assumes "is_reduction f D D'" "is_verif g D'"
  shows "is_verif (f;;g) D"         
  apply(simp add:is_verif_def)
proof
  show "\<forall>x z. \<exists>r. verif (f;; g) x z r"
  proof fix x 
    show "\<forall>z. \<exists>r. verif (f;; g) x z r" 
    proof fix z
      from assms(1) obtain y where  "comp f x y " using is_reduction_def by meson
      moreover from assms(2) obtain r where  "verif g y z r" using is_verif_def by meson
      moreover have "cons_certif f" using assms(1) is_reduction_def  by simp
      ultimately show "\<exists>r. verif (f;;g) x z r" using comp_verif by blast
      qed
    qed
next
  show "\<forall>x. (x \<in> D) = (\<exists>z. verif (f;; g) x z 0)"
  proof
    fix x 
    from assms(1) obtain y where y_def:  "comp f x y " " (x\<in>D) = (y\<in>D')" 
      using is_reduction_def by meson
    moreover from assms(2) have "(y\<in>D')  = (\<exists>z. verif g y z 0)" 
      using is_verif_def by simp 
    ultimately have "(x \<in> D) = (\<exists>z. verif g y z 0) " by simp
    moreover have "cons_certif f" using assms(1) is_reduction_def  by simp
    ultimately show "(x \<in> D) = (\<exists>z. verif (f;; g) x z 0)" using y_def(1) comp_verif
      by (metis (full_types) assms(2) is_verif_def verif_det) 
  qed
qed

definition is_polyreduction :: "com \<Rightarrow> lang \<Rightarrow> lang  \<Rightarrow> bool" where
"is_polyreduction c D D' \<equiv> poly_time_bounded c \<and> is_reduction c D D' \<and> poly_result_bounded c "

definition poly_reduces :: "lang \<Rightarrow> lang \<Rightarrow> bool" where
"poly_reduces D D' \<equiv> \<exists>c. is_polyreduction c D D'"

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
        show " comp SKIP x x \<and> bit_length x \<le> bit_length x "
          by (auto simp add: comp_def)
      qed
      done
  qed
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
   have  "comp (f;; g) x z  \<and> (x \<in> D) = (z \<in> D'')"
     using y_def z_def comp_comp by simp
   thus  "\<exists>r. comp (f;; g) x r \<and> (x \<in> D) = (r \<in> D'')" by blast
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


end

