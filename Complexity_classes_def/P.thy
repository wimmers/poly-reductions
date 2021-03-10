theory P 
  imports "../IMP-/Big_StepT"  
    "../Polynomial_Growth_Functions"
    "../Three_Sat_To_Set_Cover"  Bounds Abstractions  "IMP-_Reductions"

begin

type_synonym lang = "nat set"
type_synonym bound_fun = "nat \<Rightarrow> nat"


definition P :: "lang set" where
"P \<equiv> {L. \<exists>c. poly_time_bounded c \<and> decides c L}"


definition is_poly_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_poly_verif c L \<equiv> is_verif c L \<and> poly_verif_time_bounded c \<and> poly_certif_bounded c"

definition NP :: "lang set" where
"NP \<equiv> {L. \<exists>c. is_poly_verif c L}"





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


lemma np_sanity:
  assumes "poly_reduces D D'" "D' \<in> NP"
  shows "D \<in> NP"
proof -
  from assms(1) obtain f
    where f_def: "is_reduction f D D'" "poly_time_bounded f" "poly_result_bounded f"
    using is_polyreduction_def poly_reduces_def by auto
  from assms(2) obtain g
    where g_def: "is_verif g D'" "poly_verif_time_bounded g" "poly_certif_bounded g"
    using NP_def is_poly_verif_def by force
  from f_def(1) have "cons_certif f" by (simp add: is_reduction_def)
  moreover from g_def(1) have "\<forall>y z. \<exists>r. verif g y z r " by (simp add: is_verif_def)
  ultimately have "poly_certif_bounded (f;;g)" using f_def(3) g_def(3) 
      poly_result_bounded_poly_certif_bounded   by blast
  moreover from f_def(1) g_def(1) have "is_verif (f;;g) D" using reduction_verification_correct by simp
  moreover from f_def(2) f_def(3) g_def(2) have "poly_verif_time_bounded (f;;g)"
    using verif_reduction_poly \<open>cons_certif f\<close> by blast
  ultimately show  ?thesis using NP_def is_poly_verif_def  by auto
qed

lemma "poly_time_bounded c \<Longrightarrow> poly_result_bounded c" oops

definition NP_hard :: "lang set" where 
"NP_hard \<equiv> {L'. \<forall>L\<in>NP. poly_reduces L L'}"

definition NP_complete :: "lang set" where
"NP_complete \<equiv> NP_hard \<inter> NP"

locale NP_using_P =
  fixes entuple::com
  fixes detuple::com
  assumes en_bound:"poly_verif_time_bounded entuple" "poly_verif_result_bounded entuple"
  assumes de_bound:"poly_time_bounded detuple" "poly_rev_verif_result_bounded detuple"
  assumes total_en:"\<forall>x z. \<exists>r. verif entuple x z r"
  assumes total_de:"\<forall>r. \<exists>x z. rev_verif detuple x z r"
  assumes equiv_en_de:"verif entuple x z r \<longleftrightarrow> rev_verif detuple x z r "
begin
definition sc  :: "com \<Rightarrow> nat \<Rightarrow> nat" where 
"sc c x \<equiv> Min {z. \<exists>r.  verif c x z r \<and> r > 0}"

definition cert_lang_of :: "com \<Rightarrow> lang" where 
"cert_lang_of v \<equiv> {tuple. \<exists>x z. verif entuple x z tuple \<and> verif v x z 0 }"


lemma verif_entuple_det:
  assumes "verif entuple x z r"
  assumes "verif entuple x' z' r"
  shows "x=x' \<and> z=z'"
  using assms equiv_en_de rev_verif_det by auto


lemma NP_to_P:"is_verif v L \<Longrightarrow> decides (detuple;;v) (cert_lang_of v)"
proof (auto simp add: decides_def)
  fix tu
  assume asm:"is_verif v L"
  then obtain x z where xz_def: "rev_verif detuple x z tu" using total_de by blast
  hence entuple_rel:"verif entuple x z tu" using equiv_en_de by simp
  obtain r where r_def: "verif v x z r" using asm is_verif_def by metis
  have "(tu \<in> cert_lang_of v) = (0 = r)"
  proof
    assume "tu \<in> cert_lang_of v"
    then obtain x' z'  where def':"verif entuple x' z' tu" " verif v x' z' 0"
      using cert_lang_of_def by blast
    then have "x=x'" "z=z'" using entuple_rel verif_entuple_det by auto
    hence "verif v x z 0" using def'(2) by simp
    thus "0=r" using r_def verif_det by auto
  next
    assume "0 = r" 
    thus " tu \<in> cert_lang_of v" using r_def entuple_rel cert_lang_of_def by blast
  qed
  moreover have "comp (detuple;; v) tu r" using r_def xz_def verif_rev_verif by simp 
  ultimately show " \<exists>r. Abstractions.comp (detuple;; v) tu r \<and> (tu \<in> cert_lang_of v) = (r = 0)"
    by blast
qed

lemma P_to_NP:
  assumes "decides c L'"
  assumes "\<forall>x. x\<in>L \<longleftrightarrow> (\<exists>tu z. tu\<in>L' \<and> verif entuple x z tu)"
  shows "is_verif (entuple;;c) L"
proof (auto simp add:is_verif_def)
  fix x z
  obtain tu where "verif entuple x z tu " using total_en by auto
  moreover obtain r where "comp c tu r" using assms(1) decides_def by blast
  ultimately have "verif (entuple;;c) x z r" using verif_comp by simp 
  thus "\<exists>r. verif (entuple;; c) x z r" by auto
next
  fix x
  assume "x\<in>L"
  then obtain tu z where tu_z_def: "tu \<in> L'" "verif entuple x z tu"  using assms(2) by blast
  hence r_def:"comp c tu 0"  using assms(1) decides_def by blast
  from tu_z_def(2) r_def(1) have "verif (entuple;; c) x z 0" using verif_comp by simp
  thus "\<exists>z. verif (entuple;; c) x z 0" using r_def by blast
next
  fix x z r
  assume asm: "verif (entuple;; c) x z 0" 
  obtain tu where tu_def: "verif entuple x z tu" using total_en by blast
  moreover obtain r' where r'_def:"comp c tu r'" "(tu \<in> L') \<longleftrightarrow> (r' = 0)" 
    using assms(1) decides_def by blast 
  ultimately have "verif (entuple;;c) x z r'" using verif_comp by simp
  hence "r'= 0" using asm verif_det by simp
  hence "tu \<in> L'" using r'_def(2) by simp
  thus  "x\<in>L" using tu_def assms(2) by blast
qed

lemma "L \<in> NP \<longleftrightarrow> (\<exists>L' p. L' \<in> P \<and> poly p \<and> 
                  (\<forall>tu x z . tu \<in> L' \<and> verif entuple x z tu \<longrightarrow>
                    (\<exists>tu' z'. tu' \<in> L' \<and> verif entuple x z' tu' \<and> 
                              bit_length z' \<le> p (bit_length x))) \<and> 
                  (\<forall>x. x\<in>L \<longleftrightarrow> (\<exists>tu z. tu\<in>L' \<and> verif entuple x z tu)))"
proof
  assume " L \<in> NP"
  then obtain v where v_def: "is_poly_verif v L" using NP_def by blast
  let ?L' = "cert_lang_of v"
  obtain p where p_def: "poly p" "certif_bounded v p"
    using v_def is_poly_verif_def poly_certif_bounded_def by blast
  have "decides (detuple;;v) ?L'" using v_def is_poly_verif_def NP_to_P by blast
  moreover have "poly_time_bounded (detuple;;v)"
    using v_def is_poly_verif_def de_bound rev_verif_bounds by blast
  ultimately have "?L' \<in> P" using P_def by blast
  moreover have "\<forall>x.(x \<in> L) = (\<exists>tu z. tu \<in> ?L' \<and> verif entuple x z tu)"
  proof auto
    fix x
    assume "x \<in> L"
    then obtain z where zr_def: "verif v x z 0"
      using v_def is_poly_verif_def is_verif_def by force
    obtain tu where tu_def:"verif entuple x z tu" using total_en by blast
    hence "tu \<in> ?L'" using zr_def cert_lang_of_def by blast
    thus "\<exists>tu. tu \<in> ?L' \<and> (\<exists>z. verif entuple x z tu)" using tu_def  by blast
  next
    fix x tu z 
    assume asm: "tu \<in> ?L'" "verif entuple x z tu"
    then obtain x' z' where defs: "verif entuple x' z' tu"  "verif v x' z' 0"
      using cert_lang_of_def by auto
    hence "x=x'" "z=z'" using asm(2) verif_entuple_det by auto
    thus "x \<in> L" using defs(2) v_def is_poly_verif_def is_verif_def by blast
  qed
  moreover have "\<forall>tu x z . tu \<in> ?L' \<and> verif entuple x z tu \<longrightarrow>
                    (\<exists>tu' z'. tu' \<in> ?L' \<and> verif entuple x z' tu' \<and> 
                       bit_length z' \<le> p (bit_length x))"
  proof auto
    fix tu x z 
    assume asm:"tu \<in> cert_lang_of v" " verif entuple x z tu"
    then obtain x' z' where def': "verif entuple x' z' tu" "verif v x' z' 0" 
      using cert_lang_of_def by blast
    hence "x' =x " using asm(2)  verif_entuple_det by blast
    hence "verif v x z' 0" using def'(2) by blast
    then obtain z'' where def'':"verif v x z'' 0" "bit_length z'' \<le> p (bit_length x)"
      using p_def certif_bounded_def def'(2) by blast
    obtain tu'' where tu''_def: "verif entuple x z'' tu''" using total_en by fast
    moreover have "tu'' \<in> cert_lang_of v " 
      using def''(1) def''(2) tu''_def cert_lang_of_def by blast
    ultimately show " \<exists>tu'. tu' \<in> cert_lang_of v \<and> (\<exists>z'. verif entuple x z' tu' \<and> bit_length z' \<le> p (bit_length x))"
      using def''(2) def''(2) by blast
    qed
  ultimately show "\<exists>L' p. L' \<in> P \<and> poly p \<and> (\<forall>tu x z.
           tu \<in> L' \<and> verif entuple x z tu \<longrightarrow>
           (\<exists>tu' z'. tu' \<in> L' \<and> verif entuple x z' tu' \<and> bit_length z' \<le> p (bit_length x))) \<and>
       (\<forall>x. (x \<in> L) = (\<exists>tu z. tu \<in> L' \<and> verif entuple x z tu))" 
    using p_def(1)  by blast
next
  assume "\<exists>L' p.
       L' \<in> P \<and>
       poly p \<and>
       (\<forall>tu x z.
           tu \<in> L' \<and> verif entuple x z tu \<longrightarrow>
           (\<exists>tu' z'. tu' \<in> L' \<and> verif entuple x z' tu' \<and> bit_length z' \<le> p (bit_length x))) \<and>
       (\<forall>x. (x \<in> L) = (\<exists>tu z. tu \<in> L' \<and> verif entuple x z tu))"
  then obtain L' p where L'_def: "L' \<in> P" "poly p" 
      "\<forall>x. (x \<in> L) = (\<exists>tu z. tu \<in> L' \<and> verif entuple x z tu)"
      " (\<forall>tu x z.
           tu \<in> L' \<and> verif entuple x z tu \<longrightarrow>
           (\<exists>tu' z'. tu' \<in> L' \<and> verif entuple x z' tu' \<and> bit_length z' \<le> p (bit_length x)))"
    by blast
  then obtain c where c_def:"decides c L'" "poly_time_bounded c" using P_def by blast
  from L'_def(3) c_def(1) P_to_NP have "is_verif (entuple;;c) L" by presburger
  moreover have "poly_time_bounded (entuple;;c)"
    using c_def(2) en_bound reduction_poly by metis
  hence "poly_verif_time_bounded (entuple;;c)" using comp_to_verif by simp
  moreover have "poly_certif_bounded (entuple;;c)"
  proof (auto simp add: poly_certif_bounded_def certif_bounded_def)
    have "(\<forall>x. (\<exists>z r. verif (entuple;; c) x z 0) \<longrightarrow>
             (\<exists>z r. verif (entuple;; c) x z 0 \<and> bit_length z \<le> p (bit_length x)))"
    proof auto
      fix x z 
      assume asm: "verif (entuple;;c) x z 0"
      obtain tu where tu_def: "verif entuple x z tu" using total_en by blast
      obtain r' where r'_def:"comp c tu r'" "tu \<in> L' \<longleftrightarrow> r'=0" using c_def decides_def by blast
      from tu_def r'_def(1) have "verif (entuple;;c) x z r'" using verif_comp by simp
      hence "r' = 0" using asm(1) verif_det by blast
      hence "tu \<in> L'" using r'_def(2)  asm by blast
      then obtain tu' z' 
        where tuz'_def: "tu' \<in> L'" " verif entuple x z' tu'" "bit_length z' \<le> p (bit_length x)"
        using L'_def(4) tu_def by blast
      then obtain r'' 
        where r''_def: "comp c tu' r''" "tu' \<in> L' \<longleftrightarrow> r''=0" using c_def decides_def by blast
      have "verif (entuple;;c) x z' r''" using r''_def(1) tuz'_def(2) verif_comp by fast
      moreover have "r'' = 0" using r''_def(2) tuz'_def(1) by simp
      ultimately show "\<exists>z. verif (entuple;; c) x z 0 \<and> bit_length z \<le> p (bit_length x)"
        using tuz'_def(3) by blast
    qed
    thus "\<exists>p. poly p \<and>
        (\<forall>x. (\<exists>z. verif (entuple;; c) x z 0) \<longrightarrow>
             (\<exists>z. verif (entuple;; c) x z 0 \<and> bit_length z \<le> p (bit_length x))) "
      using L'_def(2) by auto
  qed
  ultimately show "L \<in> NP" using NP_def is_poly_verif_def by auto
qed

end
  
end

