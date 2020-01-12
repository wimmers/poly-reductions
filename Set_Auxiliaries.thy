theory Set_Auxiliaries
  imports Main Graph_Theory.Stuff
begin


lemma card_greater_1_contains_two_elements:
  assumes "card S > 1"
  shows "\<exists>u v. v\<in> S \<and> u\<in> S \<and> u \<noteq> v"
proof -
  have "S \<noteq> {}"
    using assms by(auto)
  then have "\<exists>v. v \<in> S" by(auto)
  then obtain v where "v \<in> S" by auto 
  have "(S-{v}) \<noteq> {}" 
    using assms
    by (metis Diff_empty Diff_idemp Diff_insert0 \<open>S \<noteq> {}\<close> card.insert_remove card_empty finite.emptyI insert_Diff less_Suc0 less_numeral_extra(4) less_one)
  then have "\<exists>u. u \<in> S-{v}" 
    by(auto)
  then obtain u where "u\<in> S-{v}"
    by auto
  then have "u\<in> S" by(auto)
  then have "u \<noteq> v" using \<open>u\<in>S-{v}\<close> by(auto)
  then show ?thesis using \<open>u\<in> S\<close> \<open>v \<in> S\<close> by auto
qed

lemma contains_two_card_greater_1:
  assumes "v \<in> S" "u \<in> S" "u \<noteq> v" "finite S"
  shows "1 < card S"
  using assms apply(auto) 
  by (meson card_le_Suc0_iff_eq not_le_imp_less) 

end