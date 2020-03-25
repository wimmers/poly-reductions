theory Set_Auxiliaries
  imports Main Graph_Theory.Stuff
begin

section\<open>Set auxiliaries\<close>

lemma card_greater_1_contains_two_elements:
  assumes "card S > 1"
  shows "\<exists>u v. v \<in> S \<and> u \<in> S \<and> u \<noteq> v"
  by (metis One_nat_def assms card_eq_0_iff card_le_Suc0_iff_eq le_eq_less_or_eq
        less_one not_less_iff_gr_or_eq)

lemma contains_two_card_greater_1:
  assumes "v \<in> S" "u \<in> S" "u \<noteq> v" "finite S"
  shows "1 < card S"
  using assms  by simp (meson card_le_Suc0_iff_eq not_le_imp_less)

lemma e_in_E_e_explicit:
  assumes "card e = 2"
  shows "\<exists>u v. e = {u ,v} \<and> u \<noteq> v"
proof -
  from assms have "finite e"
    using card_infinite by fastforce
  then obtain xs where "distinct xs" "set xs = e" "length xs = card e"
    by (metis assms distinct_card finite_distinct_list)
  with assms show ?thesis
    by (metis card_eq_SucD numeral_2_eq_2 singleton_iff)
qed

lemma card_dep_on_other_set:
  assumes "finite T"
  shows "card {{u. f u j}|j. j \<in> T} \<le> card T"
  using assms by (simp add: Setcompr_eq_image card_image_le)

lemma finite_union_if_all_subset_fin:
  assumes "\<forall>S' \<in> S. finite S'" "finite S"
  shows "finite (\<Union> S)"
  using assms by auto

(* XXX Move to library *)
lemma card_UN_le_sum_cards:
  assumes "finite S"
  shows "card (\<Union> S) \<le> (\<Sum>S' \<in> S. card S')"
proof (cases "\<forall>S' \<in> S. finite S'")
  case True
  with assms show ?thesis
    by induction (auto intro: card_Un_le order.trans)
next
  case False
  then have "infinite (\<Union> S)"
    by (meson Sup_upper finite_subset)
  then show ?thesis
    by simp
qed

lemma card_union_if_all_subsets_card_i:
  assumes "\<forall>S' \<in> S. card S' \<le> i" "finite S"
  shows "card (\<Union> S) \<le> i * card S"
  using assms
  by (smt Groups.mult_ac(2) card_UN_le_sum_cards id_apply of_nat_eq_id order.trans sum_bounded_above)

lemma card_forall_for_elements:
  assumes "\<forall>j \<in> T. card {u. f u j} \<le> 1" "S = {{u. f u j}| j. j \<in> T}"
  shows "\<forall>S' \<in> S. card S' \<le> 1"
proof
  fix S' assume "S' \<in> S"
  then have "\<exists>j \<in> T. S' = {u. f u j}"
    using assms by blast
  then show "card S' \<le> 1"
    using assms by blast
qed

lemma card_union_if_all_subsets_card_1:
  assumes "\<forall>S' \<in> S. card S' \<le> 1" "finite S"
  shows "card (\<Union> S) \<le> card S"
  using assms card_union_if_all_subsets_card_i by fastforce

lemma card_leq_1_set_explicit:
  assumes "card S \<le> 1" "finite S"
  shows "(\<exists>x. S = {x}) \<or> S = {}"
  using assms card_0_eq card_1_singletonE le_eq_less_or_eq by auto

end