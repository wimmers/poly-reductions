\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to IMP-- State Translations"

theory IMP_Minus_To_IMP_Minus_Minus_State_Translations 
  imports "../../IMP-/Small_StepT" "../IMP_Minus_Minus_Small_StepT"
begin

type_synonym state = AExp.state
type_synonym bit_state = IMP_Minus_Minus_Small_StepT.state

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

lemma var_bit_to_var_eq_iff[simp]: "var_bit_to_var (a, b) = var_bit_to_var (c, d) \<longleftrightarrow> (a = c \<and> b = d)" 
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

lemma take_2_var_bit_to_var[simp]: "take 2 (var_bit_to_var (x, y)) = ''?$'' \<longleftrightarrow> False" 
  by(auto simp: var_bit_to_var_def)

fun nth_bit_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_nat x 0 = x mod 2" |
"nth_bit_nat x (Suc n) = nth_bit_nat (x div 2) n"

definition nth_bit:: "nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_bit x n = nat_to_bit (nth_bit_nat x n)" 

lemma nth_bit_of_zero[simp]: "nth_bit 0 n = Zero" 
  by (induction n) (auto simp: nth_bit_def)

fun operand_bit_to_var:: "(char * nat) \<Rightarrow> vname" where 
"operand_bit_to_var (c, 0) = [c]" |
"operand_bit_to_var (c, (Suc n)) = c # operand_bit_to_var (c, n)"

definition var_to_operand_bit:: "vname \<Rightarrow> (char * nat) option" where
"var_to_operand_bit v = (if v \<noteq> [] \<and> v = (operand_bit_to_var (hd v, length v - 1)) 
  then Some (hd v, length v - 1) else None)" 

lemma hd_of_operand_bit_to_var[simp]: 
  "hd (operand_bit_to_var (op, n)) = op" by (induction n) auto

lemma take_2_of_operand_bit_to_var[simp]:
  "take 2 (operand_bit_to_var (c, k)) = operand_bit_to_var (c, min k 1)" 
  apply (cases k)
   apply(auto)
  using hd_of_operand_bit_to_var
  by (metis lessI less_Suc_eq_0_disj list.discI operand_bit_to_var.simps(1) 
      operand_bit_to_var.simps(2) take0 take_Suc)

lemma length_of_operand_bit_to_var[simp]:
  "length (operand_bit_to_var (op, n)) = n + 1" by (induction n) auto  

lemma var_to_operand_bit_of_operand_bit_to_var[simp]: 
  "var_to_operand_bit (operand_bit_to_var (op, n)) = Some (op, n)"
  apply(induction n)
  by(auto simp: var_to_operand_bit_def)

lemma var_to_operand_bit_eq_Some_iff: "var_to_operand_bit x = Some (op, i) 
  \<longleftrightarrow> x = operand_bit_to_var (op, i)" 
  apply(auto simp: var_to_operand_bit_def)
  apply(cases i)
  by auto

lemma var_to_operand_bit_of_carry[simp]: "var_to_operand_bit ''carry'' = None" 
  by(simp add: var_to_operand_bit_def)

lemma operand_bit_to_var_neq_carry[simp]: "operand_bit_to_var (op, k) = ''carry'' \<longleftrightarrow> False" 
proof 
  assume "operand_bit_to_var (op, k) = ''carry''" 
  moreover hence "op = CHR ''c''" by (metis hd_of_operand_bit_to_var list.sel)
  ultimately show False 
    by (metis option.simps var_to_operand_bit_of_carry var_to_operand_bit_of_operand_bit_to_var)
qed auto
                                                       
lemma set_of_operand_bit_to_var[simp]: "set (operand_bit_to_var (op, b)) = { op }" 
  by (induction b) auto

lemma var_to_operand_bit_var_bit_to_var[simp]: "var_to_operand_bit (var_bit_to_var (a, b)) = None" 
  apply(simp add: var_to_operand_bit_def var_bit_to_var_def)
  apply(rule ccontr)
  apply simp
  apply(drule arg_cong[where ?f=set])
  by simp

lemma var_to_var_bit_operand_bit_to_var[simp]: "var_to_var_bit (operand_bit_to_var (c, k)) = None" 
  by (simp add: var_to_var_bit_def)

lemma var_to_operand_bit_non_zero_indicator[simp]: 
  "var_to_operand_bit (CHR ''?'' # CHR ''$'' # v) = None"
  apply(auto simp: var_to_operand_bit_def)
  apply(rule ccontr)
  apply simp
  apply(drule arg_cong[where ?f=set])
  by simp

lemma operand_bit_to_var_ne_non_zero_indicator[simp]: 
  "operand_bit_to_var (c, k) \<noteq> CHR ''?'' # CHR ''$'' # v" 
  apply(induction k)
   apply auto
proof -
  fix ka :: nat
  assume "operand_bit_to_var (CHR ''?'', ka) = CHR ''$'' # v"
  then have "CHR ''?'' = CHR ''$''" by (metis hd_of_operand_bit_to_var list.sel(1))
  then show False by force
qed

lemma operand_bit_to_var_non_empty: "operand_bit_to_var (op, n) \<noteq> []"
  by (induction n) auto

lemma operand_bit_to_var_eq_operand_bit_to_var_iff[simp]: 
  "operand_bit_to_var (op, a) = operand_bit_to_var (op', b) 
  \<longleftrightarrow> (op = op' \<and> a = b)" 
proof 
  assume "operand_bit_to_var (op, a) = operand_bit_to_var (op', b)" 
  hence "length (operand_bit_to_var (op, a)) = length (operand_bit_to_var (op', b))
    \<and> set (operand_bit_to_var (op, a)) = set (operand_bit_to_var (op', b))" by simp
  thus "op = op' \<and> a = b" by auto
qed auto

lemma var_bit_to_var_neq_operand_bit_to_var[simp]: 
  "var_bit_to_var (v, a) \<noteq> operand_bit_to_var (op, b)"
proof(rule ccontr)
  assume "\<not> (var_bit_to_var (v, a) \<noteq> operand_bit_to_var (op, b))" 
  hence "set (var_bit_to_var (v, a)) = set (operand_bit_to_var (op, b))" by simp
  thus False using set_of_operand_bit_to_var by(auto simp: var_bit_to_var_def)
qed

definition IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b:: 
  "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n a b = (\<lambda>v. 
  (case var_to_var_bit v of 
  Some (v', k) \<Rightarrow> if k < n then Some (nth_bit (s v') k) else None |
  None \<Rightarrow> (case var_to_operand_bit v of 
    Some (CHR ''a'', k) \<Rightarrow> if k < n then Some (nth_bit a k) else None |
    Some (CHR ''b'', k) \<Rightarrow> if k < n then Some (nth_bit b k) else None | 
    _ \<Rightarrow> (if v = ''carry'' then Some Zero else None))))"

definition IMP_Minus_State_To_IMP_Minus_Minus:: "state \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_Minus_State_To_IMP_Minus_Minus s n 
  = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n 0 0 "

definition IMP_Minus_State_To_IMP_Minus_Minus_partial:: 
  "(vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> bit_state" where
"IMP_Minus_State_To_IMP_Minus_Minus_partial s n = (\<lambda>v. (case var_to_var_bit v of 
  Some (v', k) \<Rightarrow> if k < n then ((\<lambda>x. Some (nth_bit x k)) \<circ>\<^sub>m s) v' else None |
  None \<Rightarrow> (case var_to_operand_bit v of 
    Some (CHR ''a'', k) \<Rightarrow> if k < n then Some Zero else None |
    Some (CHR ''b'', k) \<Rightarrow> if k < n then Some Zero else None | 
    _ \<Rightarrow> (if v = ''carry'' then Some Zero else None))))"

lemma IMP_Minus_State_To_IMP_Minus_Minus_as_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b:
  "IMP_Minus_State_To_IMP_Minus_Minus s n 
    = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n 0 0"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def fun_eq_iff 
      var_to_operand_bit_eq_Some_iff IMP_Minus_State_To_IMP_Minus_Minus_def 
      split: char.splits option.splits bool.splits)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_carry[simp]: 
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b ''carry'' = Some Zero"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_operand_a[simp]: 
  "j < k \<Longrightarrow> IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b 
  (operand_bit_to_var (CHR ''a'', j)) = Some (nth_bit a j)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

lemma IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_of_operand_b[simp]: 
  "j < k \<Longrightarrow> IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s k a b 
  (operand_bit_to_var (CHR ''b'', j)) = Some (nth_bit b j)"
  by(auto simp: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)
end