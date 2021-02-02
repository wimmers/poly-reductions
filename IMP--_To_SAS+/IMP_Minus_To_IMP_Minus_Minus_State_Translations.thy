\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to IMP-- State Translations"

theory IMP_Minus_To_IMP_Minus_Minus_State_Translations imports "../IMP-/Small_StepT" IMP_Minus_Minus_Small_StepT 
begin 

definition var_to_var_bit:: "vname \<Rightarrow> (vname * nat) option" where
"var_to_var_bit v = (if length v > 0 then (if hd v = CHR ''#'' 
  then (let t = dropWhile (\<lambda>i. i = CHR ''#'') v; 
  l = length (takeWhile (\<lambda>i. i = CHR ''#'') v) - 1 in
  (if length t > 0 \<and> hd t = CHR ''$'' then Some (tl t, l) else None))
  else None)
  else None)"

fun n_hashes:: "nat \<Rightarrow> string" where
"n_hashes 0 = []" |
"n_hashes (Suc n) = (CHR ''#'') # (n_hashes n)" 

definition var_bit_to_var:: "(vname * nat) \<Rightarrow> vname" where
"var_bit_to_var vk = (n_hashes (snd vk + 1)) @ ''$''  @ (fst vk)" 

lemma dropWhile_n_hashes[simp]: "dropWhile (\<lambda>i. i = CHR ''#'') (n_hashes x @ CHR ''$'' # y) 
  = CHR ''$'' # y" 
  apply(induction x)
  by(auto)

lemma length_takeWhile_n_hashes[simp]: 
  "length (takeWhile (\<lambda>i. i = CHR ''#'') (n_hashes x @ CHR ''$'' # y)) = x"
  apply(induction x)
  by auto

lemma encoded_var_decomposition[simp]: "x \<noteq> [] \<Longrightarrow> hd x = CHR ''#''
  \<Longrightarrow> hd (dropWhile (\<lambda>i. i = CHR ''#'') x) = CHR ''$'' 
  \<Longrightarrow> c \<in> set x \<Longrightarrow> c \<noteq> CHR ''#''
  \<Longrightarrow> n_hashes (length (takeWhile (\<lambda>i. i = CHR ''#'') x)) 
    @ CHR ''$'' # tl (dropWhile (\<lambda>i. i = CHR ''#'') x) = x"
proof (induction x)
  case (Cons a x)
  hence *: "x \<noteq> []" by auto
  have "hd x = CHR ''#'' \<or> hd x \<noteq> CHR ''#''" by auto
  thus ?case
    apply(elim disjE)
    using Cons * apply(auto)
    by (smt hd_Cons_tl list.size(3) n_hashes.simps(1) self_append_conv2 takeWhile.simps(1) 
        takeWhile_dropWhile_id takeWhile_tail)
qed auto

lemma var_to_var_bit_var_bit_to_var[simp]: "var_to_var_bit (var_bit_to_var x) = Some x" 
  by (auto simp: var_to_var_bit_def var_bit_to_var_def Let_def)

lemma var_to_var_bit_eq_Some_iff: "var_to_var_bit x = Some y \<longleftrightarrow> x = var_bit_to_var y" 
proof
  assume "var_to_var_bit x = Some y" 
  thus "x = var_bit_to_var y" 
    apply(auto simp: var_to_var_bit_def var_bit_to_var_def Let_def split: if_splits)
    using encoded_var_decomposition 
    by (smt Nitpick.size_list_simp(2) One_nat_def char.inject length_tl list.expand list.sel(1) 
        list.sel(3) list.simps(3) n_hashes.simps(2) self_append_conv2 
        takeWhile_dropWhile_id tl_append2)
qed auto

lemma var_bit_to_var_eq_iff: "var_bit_to_var (a, b) = var_bit_to_var (c, d) \<longleftrightarrow> (a = c \<and> b = d)" 
  apply(auto simp: var_bit_to_var_def)
   apply (metis dropWhile_n_hashes list.inject)
  by (metis length_takeWhile_n_hashes)

lemma var_to_var_bit_of_non_zero_indicator[simp]: "var_to_var_bit (CHR ''?'' # CHR ''$'' # v) = None" 
  by(auto simp: var_to_var_bit_def)

lemma var_bit_to_var_neq_non_zero_indicator[simp]: "(''?$'' @ x \<noteq> var_bit_to_var (v, y))"
  by(auto simp: var_bit_to_var_def)

lemma var_bit_to_var_neq_non_zero_indicator'[simp]: "(var_bit_to_var (a, b) = CHR ''?'' # CHR ''$'' # v) 
  \<longleftrightarrow> False"
  by(auto simp: var_bit_to_var_def)

lemma var_to_var_bit_of_carry[simp]: "var_to_var_bit ''carry'' = None"
  by(auto simp: var_to_var_bit_def)

lemma var_bit_to_var_neq_carry[simp]: "''carry'' \<noteq> var_bit_to_var (x, y) "
  by(auto simp: var_bit_to_var_def)

lemma var_bit_to_var_neq_carry'[simp]: "var_bit_to_var (x, y) = ''carry'' \<longleftrightarrow> False"
  by(auto simp: var_bit_to_var_def)

fun nth_bit:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit x 0 = x mod 2" |
"nth_bit x (Suc n) = nth_bit (x div 2) n"

lemma zero_le_nth_bit_then[simp]: "0 < nth_bit x n \<longleftrightarrow> nth_bit x n = 1" 
  apply(induction n arbitrary: x)
  by auto

lemma nth_bit_of_zero[simp]: "nth_bit 0 n = 0" 
  by (induction n) auto

lemma nth_bit_eq_zero_or_one: "nth_bit x n = y \<Longrightarrow> (y = 0 \<or> y = 1)" 
  by (induction n arbitrary: x) auto

definition IMP_Minus_State_To_IMP_Minus_Minus:: "state \<Rightarrow> nat \<Rightarrow> state" where
"IMP_Minus_State_To_IMP_Minus_Minus s n = (\<lambda>v. (case var_to_var_bit v of 
  Some (v', k) \<Rightarrow> if k < n then nth_bit (s v') k else 0 |
  None \<Rightarrow> (if length v > 1 \<and> take 2 v = ''?$'' \<and> (s (drop 2 v)) > 0 then 1 else 0)))"

lemma IMP_Minus_State_To_IMP_Minus_Minus_of_non_zero_indicator[simp]: 
  "IMP_Minus_State_To_IMP_Minus_Minus s n (CHR ''?'' # CHR ''$'' # x) = (if s x \<noteq> 0 then 1
    else 0)" 
  by (auto simp: IMP_Minus_State_To_IMP_Minus_Minus_def)

fun atomExp_to_constant:: "AExp.atomExp \<Rightarrow> nat" where
"atomExp_to_constant (AExp.V var) = 0" |
"atomExp_to_constant (AExp.N val) = val"

fun aexp_max_constant:: "AExp.aexp \<Rightarrow> nat" where
"aexp_max_constant (AExp.A a) = atomExp_to_constant a" |
"aexp_max_constant (AExp.Plus a b) = max (atomExp_to_constant a) (atomExp_to_constant b)" |
"aexp_max_constant (AExp.Sub a b) = max (atomExp_to_constant a) (atomExp_to_constant b)"

fun max_constant :: "Com.com \<Rightarrow> nat" where
"max_constant (Com.SKIP) = 0" |
"max_constant (Com.Assign vname aexp) = aexp_max_constant aexp" |
"max_constant (Com.Seq c1  c2) = max (max_constant c1) (max_constant c2)" |         
"max_constant (Com.If  _ c1 c2) = max (max_constant c1) (max_constant c2)"  |   
"max_constant (Com.While _ c) = max_constant c"

lemma Max_range_le_then_element_le: "finite (range s) \<Longrightarrow> 2 * Max (range s) < (x :: nat) \<Longrightarrow> 2 * (s y) < x" 
proof -
  assume "2 * Max (range s) < (x :: nat)"
  moreover have "s y \<in> range s" by simp
  moreover assume "finite (range s)" 
  moreover hence "s y \<le> Max (range s)" by simp
  ultimately show ?thesis by linarith
qed

lemma aval_le_when: 
  assumes "finite (range s)" "2 * max (Max (range s)) (aexp_max_constant a) < x" 
  shows "AExp.aval a s < x"
using assms proof(cases a)
  case (A x1)
  thus ?thesis using assms
  proof(cases x1)
    case (V x2)
    thus ?thesis using assms A Max_range_le_then_element_le[where ?s=s and ?x = x and ?y=x2] by simp
  qed simp
next
  case (Plus x21 x22)
  hence "2 * max (AExp.atomVal x21 s) (AExp.atomVal x22 s) < x" 
    apply(cases x21)
     apply(cases x22)
      prefer 3
    apply(cases x22)
    using assms 
    by (auto simp add: Max_range_le_then_element_le nat_mult_max_right)
  thus ?thesis using Plus by auto
next
  case (Sub x31 x32)
  then show ?thesis 
    apply(cases x31)
     apply(cases x32)
      prefer 3
      apply(cases x32)
    using assms apply(auto simp add: Max_range_le_then_element_le nat_mult_max_right)
    using Max_range_le_then_element_le 
    by (metis gr_implies_not0 lessI less_imp_diff_less less_imp_le_nat less_le_trans 
        linorder_neqE_nat n_less_m_mult_n numeral_2_eq_2)+
qed

end