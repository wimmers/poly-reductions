\<^marker>\<open>creator Florian Keßler\<close>

section "Binary Arithmetic"
                                                    
theory Binary_Arithmetic 
  imports Main "../IMP_Minus_Minus_Small_StepT" "HOL-Library.Discrete"

begin 

text \<open> In this theory, we introduce functions to access bits out of nats, and Lemmas that relate 
        the bits in the result of addition and subtraction to the bits of the original numbers. \<close>

fun nth_bit_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_nat x 0 = x mod 2" |
"nth_bit_nat x (Suc n) = nth_bit_nat (x div 2) n"

lemma nth_bit_nat_is_right_shift: "nth_bit_nat x n = (x div 2 ^ n) mod 2"
  apply(induction n arbitrary: x)
  by(auto simp:  div_mult2_eq)

definition nth_bit:: "nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_bit x n = nat_to_bit (nth_bit_nat x n)" 

fun nth_bit_of_num:: "num \<Rightarrow> nat \<Rightarrow> bit" where
"nth_bit_of_num Num.One 0 = One" |
"nth_bit_of_num Num.One (Suc n) = Zero" | 
"nth_bit_of_num (Num.Bit0 x) 0 = Zero" |
"nth_bit_of_num (Num.Bit1 x) 0 = One" |
"nth_bit_of_num (Num.Bit0 x) (Suc n) = nth_bit_of_num x n" |
"nth_bit_of_num (Num.Bit1 x) (Suc n) = nth_bit_of_num x n"

lemma nth_bit_nat_of_zero[simp]: "nth_bit_nat 0 n = 0" 
  by (induction n) auto

lemma nth_bit_of_zero[simp]: "nth_bit 0 n = Zero" 
  by (induction n) (auto simp: nth_bit_def)

lemma nth_bit_of_one[simp]: "nth_bit (Suc 0) n = (if n = 0 then One else Zero)"
  apply(cases n)
  by(auto simp: nth_bit_def nat_to_bit_eq_Zero_iff)

lemma one_plus_2n_is_odd[simp]: "Suc (n + n) mod 2 = 1" by presburger

lemma nth_bit_of_nat_of_num: "nth_bit (nat_of_num x) n = nth_bit_of_num x n" 
proof(induction n arbitrary: x)
  case 0
  then show ?case by (cases x) (auto simp: nth_bit_def nat_to_bit_eq_One_iff)
next
  case (Suc n)
  then show ?case using Suc by (cases x) (auto simp: nth_bit_def)
qed

lemma nth_bit_is_nth_bit_of_num: "nth_bit x n = (if x = 0 then Zero
  else nth_bit_of_num (num_of_nat x) n)" 
proof (cases "x = 0")
  case False
  hence "nth_bit x n = nth_bit (nat_of_num (num_of_nat x)) n" using num_of_nat_inverse by auto
  thus ?thesis using False by(simp add: nth_bit_of_nat_of_num)
qed auto

lemma le_2_to_the_n_then_nth_bit_zero: "x < 2 ^ n \<Longrightarrow> nth_bit x n = Zero" 
  by(auto simp: nth_bit_def nat_to_bit_eq_Zero_iff nth_bit_nat_is_right_shift)

fun nth_carry:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_carry 0 a b = (if (nth_bit a 0 = One \<and> nth_bit b 0 = One) then One else Zero)" | 
"nth_carry (Suc n) a b = (if (nth_bit a (Suc n) = One \<and> nth_bit b (Suc n) = One) 
  \<or> ((nth_bit a (Suc n) = One \<or> nth_bit b (Suc n) = One) \<and> nth_carry n a b = One) 
  then One else Zero)" 

lemma a_mod_n_plus_b_mod_n_geq_a_plus_b_mod_n: "(a :: nat) mod n + b mod n \<ge> (a + b) mod n" 
  by (metis mod_add_eq mod_less_eq_dividend)

lemma a_mod_2_to_the_n_decomposition: "(a :: nat) mod (2 * 2 ^ n) 
  = a div 2 ^ n mod 2 * 2 ^ n +  a mod 2 ^ n" 
  by (metis mod_mult2_eq mult.commute)

lemma a_mod_plus_b_mod_div_le_2: "((a :: nat) mod 2 ^ n + b mod 2 ^ n) div 2 ^ n < 2" 
proof-
  have "a mod 2 ^ n < 2 ^ n" "b mod 2 ^ n < 2 ^ n" by auto
  hence "(a mod 2 ^ n + b mod 2 ^ n) < 2 * 2 ^ n" by linarith
  thus ?thesis using less_mult_imp_div_less by simp
qed

lemma a_mod_plus_b_mod: "((a :: nat) mod (2 * 2 ^ n) + b mod (2 * 2 ^ n)) div (2 * 2 ^ n) mod 2 
  = (a div 2 ^ n mod 2 + b div 2 ^ n mod 2 + 
      (a mod (2 ^ n) + b mod (2 ^ n)) div (2 ^ n) mod 2) div 2" 
proof -
  have "(a mod (2 * 2 ^ n) + b mod (2 * 2 ^ n)) div (2 * 2 ^ n) mod 2 
    = (a div 2 ^ n mod 2 * 2 ^ n + b div 2 ^ n mod 2 * 2 ^ n 
      + a mod 2 ^ n + b mod 2 ^ n) div (2 * 2 ^ n) mod 2"
    using a_mod_2_to_the_n_decomposition by presburger
  also have "... = ((a div 2 ^ n mod 2 * 2 ^ n + b div 2 ^ n mod 2 * 2 ^ n 
      + a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n) div 2 mod 2"
    by (metis (mono_tags, lifting) div_mult2_eq mult.commute)
  also have "... = ((a div 2 ^ n mod 2 * 2 ^ n) div 2 ^ n  + (b div 2 ^ n mod 2 * 2 ^ n) div 2 ^ n
      + (a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n) div 2 mod 2" by (simp add: add.assoc)
  also have "... = (a div 2 ^ n mod 2  + b div 2 ^ n mod 2 
      + (a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n) div 2 mod 2" by simp
  also have "... = (a div 2 ^ n mod 2  + b div 2 ^ n mod 2 
      + (a mod 2 ^ n + b mod 2 ^ n) div 2 ^ n mod 2) div 2 mod 2" 
    using a_mod_plus_b_mod_div_le_2 by simp
  finally show ?thesis by simp
qed

lemma nth_carry_mod: "nth_carry n a b = 
  nth_bit ((a mod 2 ^ Suc n) + (b mod 2 ^ Suc n)) (Suc n)" 
proof(induction n)
  case 0
  then show ?case by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift)
next
  case (Suc n)
  then show ?case 
    apply(cases "nth_carry n a b")
      by(auto simp: nth_bit_def nat_to_bit_cases nth_bit_nat_is_right_shift 
          a_mod_plus_b_mod[where ?n="Suc n", simplified] algebra_simps split: if_splits)
qed

lemma first_bit_of_add: "nth_bit (a + b) 0 
  = (if nth_bit a 0 = One then if nth_bit b 0 = One then Zero else One 
     else if nth_bit b 0 = One then One else Zero)" 
  apply(auto simp: nth_bit_def nat_to_bit_eq_One_iff nat_to_bit_eq_Zero_iff)
  by presburger

lemma nth_bit_of_add: "nth_bit (a + b) (Suc n) = (let u = nth_bit a (Suc n); 
  v = nth_bit b (Suc n); w = nth_carry n a b in 
  (if u = One then 
    if v = One then
     if w = One then One else Zero
    else
     if w = One then Zero else One
   else
    if v = One then
     if w = One then Zero else One
    else
     if w = One then One else Zero))"
  apply(auto simp: Let_def nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases nth_carry_mod)
  by (metis div_add1_eq even_add even_iff_mod_2_eq_zero not_mod2_eq_Suc_0_eq_0)+

lemma no_overflow_condition: "a + b < 2 ^ n \<Longrightarrow> nth_carry (n - 1) a b = Zero" 
  apply(cases n)
  by(auto simp: nth_carry_mod nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)

lemma has_bit_one_then_greater_zero: "nth_bit a j = One \<Longrightarrow> 0 < a" 
  apply(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)
  by (metis One_nat_def div_less dvd_0_right even_mod_2_iff gr_zeroI less_2_cases_iff 
      odd_one zero_less_power)

lemma greater_zero_then_has_bit_one: "x > 0 \<Longrightarrow> x < 2 ^ n \<Longrightarrow> \<exists>b \<in> {0..<n}. nth_bit x b = One" 
proof(rule ccontr)
  assume "x > 0" "x < 2 ^ n" "\<not> (\<exists>b\<in>{0..<n}. nth_bit x b = One)" 
  hence "(\<forall>b. nth_bit x b = Zero) \<or> (\<exists>b \<ge> n. nth_bit x b = One)" by auto
  thus False 
  proof(elim disjE)
    assume "\<forall>b. nth_bit x b = Zero"
    hence "nth_bit x (Discrete.log x) = Zero" by auto
    moreover have "x div 2 ^ Discrete.log x = 1" 
      using Discrete.log_exp2_gt log_exp2_le[OF \<open>x > 0\<close>]
      by (metis Euclidean_Division.div_eq_0_iff One_nat_def leD less_2_cases_iff 
          less_mult_imp_div_less power_not_zero zero_neq_numeral)
    ultimately show False by(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)
  next 
    assume "\<exists>b \<ge> n. nth_bit x b = One"
    then obtain b where "b \<ge> n \<and> nth_bit x b = One" by blast
    thus False using \<open>x < 2 ^ n\<close> 
      apply(auto simp: nth_bit_def nth_bit_nat_is_right_shift nat_to_bit_cases)
      by (metis div_greater_zero_iff gr0I leD le_less_trans less_2_cases_iff less_Suc0 
          mod_less_eq_dividend nat_power_less_imp_less)
  qed
qed   

fun nth_carry_sub:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_carry_sub 0 a b = (if (nth_bit a 0 = Zero \<and> nth_bit b 0 = One) then One else Zero)" | 
"nth_carry_sub (Suc n) a b = 
  (if (nth_bit a (Suc n) = Zero \<and> ( nth_bit b (Suc n) = One \<or> nth_carry_sub n a b = One))
    \<or> (nth_bit a (Suc n) = One \<and> (nth_bit b (Suc n)) = One \<and> nth_carry_sub n a b = One) then One
  else Zero)"

lemma first_bit_of_sub_n_no_underflow: "a \<ge> b \<Longrightarrow> nth_bit (a - b) 0 = (if nth_bit a 0 = One then
  (if nth_bit b 0 = One then Zero else One)
  else (if nth_bit b 0 = One then One else Zero))" 
  apply(auto simp: nth_bit_def nat_to_bit_eq_One_iff nat_to_bit_eq_Zero_iff)
  by presburger+

lemma nth_bit_of_sub_n_no_underflow: "a \<ge> b \<Longrightarrow> 
  nth_bit (a - b) (Suc n) = (let an = nth_bit a (Suc n); bn = nth_bit b (Suc n);
  c = nth_carry_sub n a b in (if (bn = Zero \<and> c = Zero) \<or> (bn = One \<and> c = One) then an 
    else (if (bn = One \<or> c = One) \<and> an = Zero then One else Zero)))" 
  sorry

lemma nth_bit_of_sub_n_underflow: "a < b \<Longrightarrow> 
  nth_bit (a - b) (Suc n) = Zero" 
  by simp

lemma nth_carry_sub_underflow: "a < b \<Longrightarrow> a < 2 ^ n \<Longrightarrow> b < 2 ^ n 
  \<Longrightarrow> nth_carry_sub (n - 1) (2^n + a) b = One" 
  sorry         

lemma nth_carry_sub_no_underflow: "a \<ge> b \<Longrightarrow> a < 2 ^ n \<Longrightarrow> b < 2 ^ n 
  \<Longrightarrow> nth_carry_sub (n - 1) a b = Zero" 
  by (smt bit_neq_zero_iff le_add_diff_inverse no_overflow_condition nth_bit_of_add 
      nth_bit_of_sub_n_no_underflow)

lemma nth_bit_add_out_of_range: "a < 2 ^ n \<Longrightarrow> j < n \<Longrightarrow> nth_bit (2 ^ n + a) j = nth_bit a j" 
  sorry

lemma div2_is_right_shift: "nth_bit (x div 2) n = nth_bit x (Suc n)" 
  by(auto simp: nth_bit_def)

fun bit_list_to_nat:: "bit list \<Rightarrow> nat" where
"bit_list_to_nat [] = 0" |
"bit_list_to_nat (x # xs) = (case x of Zero \<Rightarrow> 2 * bit_list_to_nat xs |
  One \<Rightarrow> 1 + 2 * bit_list_to_nat xs)" 

lemma nth_bit_of_bit_list_to_nat[simp]: "nth_bit (bit_list_to_nat l) k 
  = (if k < length l then l ! k else Zero)" 
  sorry

lemma bit_list_to_nat_geq_two_to_the_k_then: "bit_list_to_nat l \<ge> 2 ^ k
  \<Longrightarrow> (\<exists>i. k \<le> i \<and> i < length l \<and> l ! i = One)" 
  sorry

lemma bit_list_to_nat_eq_nat_iff: "bit_list_to_nat l = y \<longleftrightarrow> (y < 2 ^ length l \<and>
  (\<forall>i < length l. l ! i = nth_bit y i))"
  sorry

lemma all_bits_equal_then_equal: "x < 2 ^ n \<Longrightarrow> y < 2 ^ n \<Longrightarrow> (\<forall>i < n. nth_bit x i = nth_bit y i) 
  \<Longrightarrow> x = y" sorry


end