theory Set_Auxiliaries
  imports Main Graph_Theory.Stuff
begin


lemma card_greater_1_contains_two_elements:
  assumes "card S > 1"
  shows "\<exists>u v. v\<in> S \<and> u\<in> S \<and> u \<noteq> v"
proof -
  have "S \<noteq> {}"
    using assms 
    by(auto)
  then have "\<exists>v. v \<in> S" 
    by(auto)
  then obtain v where "v \<in> S" 
    by auto 
  have "(S-{v}) \<noteq> {}" 
    using assms
    by (metis Diff_empty Diff_idemp Diff_insert0 \<open>S \<noteq> {}\<close> card.insert_remove card_empty finite.emptyI insert_Diff less_Suc0 less_numeral_extra(4) less_one)
  then have "\<exists>u. u \<in> S-{v}" 
    by(auto)
  then obtain u where "u\<in> S-{v}"
    by auto
  then have "u\<in> S" 
    by(auto)
  then have "u \<noteq> v" 
    using \<open>u\<in>S-{v}\<close> 
    by(auto)
  then show ?thesis 
    using \<open>u\<in> S\<close> \<open>v \<in> S\<close> 
    by auto
qed

lemma contains_two_card_greater_1:
  assumes "v \<in> S" "u \<in> S" "u \<noteq> v" "finite S"
  shows "1 < card S"
  using assms apply(auto) 
  by (meson card_le_Suc0_iff_eq not_le_imp_less) 

lemma e_in_E_e_explicit: 
  assumes "card e = 2" 
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v" 
proof -
  have 1: "card e = 2" 
    using assms 
    by blast 
  then have 2: "finite e" 
    using card_infinite
    by fastforce
  then have "\<exists>u. u \<in> e"
    using all_not_in_conv 1 
    by fastforce 
  then obtain u where u_def: "u \<in> e"
    by auto
  then have 3: "card (e -{u}) = 1" 
    by (simp add: 1 2)  
  then have 4: "finite (e -{u})" 
    by (simp add: 2)
  then have "\<exists>v. v \<in> (e -{u})" 
    using all_not_in_conv 3 2
    by (metis card_1_singletonE singletonI) 
  then obtain v where v_def: "v \<in> (e -{u})"
    by auto
  then have 5: "card (e -{u, v}) = 0"
    using 2 3 4 
    by (metis Diff_insert2 card_Diff_singleton_if diff_is_0_eq' le_numeral_extra(4)) 
  then have "finite (e -{u, v})" 
    using 4 2 
    by blast
  then have "(e -{u, v}) = {}" 
    using 5 
    by auto
  then have "e = {u, v}"
    using 1 u_def v_def 
    by auto  
  then show ?thesis using u_def v_def by auto 
qed


lemma card_dep_on_other_set:
  assumes "finite T" 
  shows "card {{u. f u j}|j. j \<in> T} \<le> card T" 
  using assms 
proof (induction "card T" arbitrary: T)
  case 0
  then have "T = {}" 
    using assms 
    by simp
  then have "{{u. f u j}|j. j \<in> T} = {}" 
    using assms 0 
    by auto
  then show ?case 
    by auto
next
  case (Suc x)
  then have "\<exists>x. x \<in> T" 
    by (metis card_eq_SucD insertI1) 
  then obtain t where t_def: "t \<in> T" 
    by auto
  then obtain T' where T'_def: "T' = T - {t}" 
    by auto
  then have card: "x = card T'" 
    using Suc t_def 
    by simp
  have "finite T'" 
    using Suc 
    by (simp add: T'_def) 
  then have 1: "card {{u. f u j}|j. j \<in> T'} \<le> card T'" 
    using Suc card   
    by blast 
  have 2: "T = T' \<union> {t}" 
    using T'_def t_def 
    by auto 
  then have "{{u. f u j}|j. j \<in> T} = {{u. f u j}|j. j \<in> T'} \<union> {{u. f u t}}"
    using T'_def 
    by blast
  then have "card {{u. f u j}|j. j \<in> T} = card ({{u. f u j}|j. j \<in> T'} \<union> {{u. f u t}})"
    by simp
  then have "card {{u. f u j}|j. j \<in> T}  \<le> card {{u. f u j}|j. j \<in> T'} + card {{u. f u t}}"
    by (metis (no_types, lifting) card_Un_le) 
  then have 3: "card {{u. f u j}|j. j \<in> T}  \<le> card T' + 1" 
    using 1 by simp
  have "card T = card T' + 1" 
    using 2 t_def T'_def Suc.hyps(2) card 
    by linarith  
  then have "card {{u. f u j}|j. j \<in> T}  \<le> card T" 
    using 2 3 
    by linarith
  then show ?case 
    using Suc 
    by argo
qed


lemma fin_dep_on_other_set:
  assumes "finite T" 
  shows "finite {{u. f u j}|j. j \<in> T}" 
  using assms 
proof (induction "card T" arbitrary: T)
  case 0
  then have "T = {}" 
    using assms 
    by simp
  then have "{{u. f u j}|j. j \<in> T} = {}" 
    using assms 0 
    by auto
  then show ?case 
    by auto
next
  case (Suc x)
  then have "\<exists>x. x \<in> T" 
    by (metis card_eq_SucD insertI1) 
  then obtain t where t_def: "t \<in> T" 
    by auto
  then obtain T' where T'_def: "T' = T - {t}" 
    by auto
  then have card: "x = card T'" 
    using Suc t_def 
    by simp
  have "finite T'" 
    using Suc 
    by (simp add: T'_def) 
  then have 1: "finite {{u. f u j}|j. j \<in> T'}" 
    using Suc card   
    by blast
  have 2: "T = T' \<union> {t}" 
    using T'_def t_def 
    by auto 
  then have 3: "{{u. f u j}|j. j \<in> T} = {{u. f u j}|j. j \<in> T'} \<union> {{u. f u t}}"
    using T'_def 
    by blast
  then have "finite ({{u. f u j}|j. j \<in> T'} \<union> {{u. f u t}})"
    using 1 
    by blast 
  then have "finite {{u. f u j}|j. j \<in> T}"
    using 3 
    by simp
  then show ?case 
    by simp
qed

lemma finite_union_if_all_subset_fin:
  assumes "\<forall>S' \<in> S. finite S'" "finite S"  
  shows "finite (\<Union> S)"
  using assms by auto 


lemma card_union_if_all_subsets_card_1:
  assumes "\<forall>S' \<in> S. card S' \<le> 1" "finite S"  
  shows "card (\<Union> S) \<le> card S"
proof (cases "finite (\<Union> S)")
  case True
  then show ?thesis 
    using assms 
  proof(induction "card S" arbitrary: S)
    case 0
    then have "S = {}" 
      using assms 0 
      by simp
    then show ?case 
      by simp
  next
    case (Suc x)
    then have "\<exists>x. x \<in> S" 
      by (metis card_eq_SucD insertI1) 
    then obtain S' where S'_def: "S' \<in> S" 
      by auto
    then obtain T where T_def: "T = S - {S'}" 
      by auto
    then have card_T: "card T = x" 
      using Suc S'_def 
      by auto
    then have "\<forall>S' \<in> T. card S' \<le> 1" "finite T" 
      using Suc T_def 
      by(blast)+
    then have 1: "card (\<Union> T) \<le> card T" 
      using Suc card_T 
      by fastforce
    have card_S': "card S' \<le> 1" 
      using Suc S'_def 
      by fast 
    have fin: "finite S'" 
      using True S'_def Suc.prems(1) rev_finite_subset 
      by blast  
    then have 2: "card ((\<Union> T) \<union> S') \<le> card T+1" 
      using 1 Suc S'_def card_S' fin 
    proof - 
      have "card ((\<Union> T) \<union> S') \<le> card (\<Union> T) + card S'" 
        by (simp add: card_Un_le) 
      then have "card ((\<Union> T) \<union> S') \<le> card (\<Union> T) + 1" 
        using card_S' 
        by force
      then have "card ((\<Union> T) \<union> S') \<le> card T + 1" 
        using 1 
        by auto
      then show ?thesis .
    qed
    have 3: "card T +1 = card S" 
      using S'_def T_def Suc.hyps(2) card_T 
      by linarith 
    have "(\<Union> T) \<union> S' = \<Union>S" 
      using S'_def T_def 
      by auto 
    then show ?case 
      using 2 3 Suc S'_def 
      by argo   
  qed
next
  case False
  then have "card (\<Union> S) = 0" 
    by simp
  then show ?thesis 
    by simp
qed


lemma card_forall_for_elements: 
  assumes "\<forall>j \<in> T. card {u. f u j} \<le> 1" "S = {{u. f u j}| j. j \<in> T}"
  shows "\<forall>S' \<in> S. card S' \<le> 1"
proof 
  fix S' assume "S' \<in> S" 
  then have "\<exists>j \<in> T. S' = {u. f u j}" 
    using assms 
    by blast
  then show "card S' \<le> 1" 
    using assms 
    by blast 
qed


lemma card_leq_1_set_explicit: 
  assumes "card S \<le> 1" "finite S"
  shows "(\<exists>x. S = {x}) \<or> S = {}"
  using assms card_0_eq card_1_singletonE le_eq_less_or_eq 
  by auto 


lemma get_some_in_set: 
  assumes "S \<noteq> {}" "e = (SOME e. e \<in> S)"
  shows "e \<in> S" 
  using assms 
  by (meson all_not_in_conv tfl_some) 

end