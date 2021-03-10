\<^marker>\<open>creator Florian Keßler\<close>

section "Binary Arithmetic"
                                                    
theory Binary_Arithmetic 
  imports Main "../IMP_Minus_Minus_Small_StepT"
begin 

fun nth_bit_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_nat x 0 = x mod 2" |
"nth_bit_nat x (Suc n) = nth_bit_nat (x div 2) n"

definition nth_bit:: "nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_bit x n = nat_to_bit (nth_bit_nat x n)" 

lemma nth_bit_of_zero[simp]: "nth_bit 0 n = Zero" 
  by (induction n) (auto simp: nth_bit_def)

fun nth_carry:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bit" where
"nth_carry 0 a b = (if (nth_bit a 0 = One \<and> nth_bit b 0 = One) then One else Zero)" | 
"nth_carry (Suc n) a b = (if (nth_bit a (Suc n) = One \<and> nth_bit b (Suc n) = One) 
  \<or> ((nth_bit a (Suc n) = One \<or> nth_bit b (Suc n) = One) \<and> nth_carry n a b = One) 
  then One else Zero)"

lemma first_bit_of_add: "nth_bit (a + b) 0 
  = (if nth_bit a 0 = One then if nth_bit b 0 = One then Zero else One 
     else if nth_bit b 0 = One then One else Zero)" 
  sorry

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
  sorry

lemma no_overflow_condition: "a + b < 2^n \<Longrightarrow> nth_carry (n - 1) a b = Zero" 
  sorry

lemma has_bit_one_then_greater_zero: "nth_bit a j = One \<Longrightarrow> 0 < a" 
  sorry

lemma greater_zero_then_has_bit_one: "x > 0 \<Longrightarrow> x < 2 ^ n \<Longrightarrow> \<exists>b \<in> {0..<n}. nth_bit x b = One" 
  sorry

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