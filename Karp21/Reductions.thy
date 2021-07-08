section \<open>Fundamental Definitions\<close>

subsection \<open>Reductions\<close>

theory Reductions
  imports Main
begin

definition is_reduction :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_reduction f A B \<equiv> \<forall>a. a \<in> A \<longleftrightarrow> f a \<in> B "

lemma is_reduction_trans:
  assumes "is_reduction f A B" "is_reduction g B C"
  shows "is_reduction (g o f) A C"
  using assms unfolding is_reduction_def by auto

end