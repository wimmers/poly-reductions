\<^marker>\<open>creator Florian Keßler\<close>

section "Binary Operations in IMP--"
                                                    
theory Binary_Operations 
  imports IMP_Minus_To_IMP_Minus_Minus_State_Translations "../IMP_Minus_Max_Constant" 
    "../IMP--_To_SAS++/IMP_Minus_Minus_Subprograms"
begin 

type_synonym IMP_Minus_com = Com.com
type_synonym IMP_Minus_Minus_com = com

unbundle Com.no_com_syntax

fun com_list_to_seq:: "IMP_Minus_Minus_com list \<Rightarrow> IMP_Minus_Minus_com" where
"com_list_to_seq [] = SKIP" | 
"com_list_to_seq (c # cs) = c ;; (com_list_to_seq cs)"

lemma t_small_step_fun_com_list_to_seq_terminates: "t1 + t2 < t
  \<Longrightarrow> t_small_step_fun t1 (com_list_to_seq as, s1) = (SKIP, s3)
  \<Longrightarrow> t_small_step_fun t2 (com_list_to_seq bs, s3) = (SKIP, s2)
  \<Longrightarrow> t_small_step_fun t (com_list_to_seq (as @ bs), s1) = (SKIP, s2)"
proof(induction as arbitrary: s1 t1 t)
  case Nil
  then show ?case using t_small_step_fun_increase_time 
    by (metis Pair_inject append_self_conv2 com_list_to_seq.simps le_add2 
        less_imp_le_nat t_small_step_fun_SKIP)
next
  case (Cons a as)
  then obtain ta sa where ta_def: "ta < t1 \<and> t_small_step_fun ta (a, s1) = (SKIP, sa) 
    \<and> t_small_step_fun (t1 - (ta + 1)) (com_list_to_seq as, sa) = (SKIP, s3)"
    by (auto simp: seq_terminates_iff)
  hence "t_small_step_fun (t - (ta + 1)) (com_list_to_seq (as @ bs), sa) = (SKIP, s2)"  
    apply -
    apply(rule Cons(1))
    using Cons by(auto)
  thus ?case using ta_def Cons seq_terminates_iff by fastforce
qed

lemma com_list_to_seq_of_length_one_terminates_iff: 
  "t_small_step_fun t (com_list_to_seq [c], s1) = (SKIP, s2) \<longleftrightarrow>
  (t > 0 \<and> t_small_step_fun (t - 1) (c, s1) = (SKIP, s2))" 
  apply(auto simp: seq_terminates_iff)
  using t_small_step_fun_increase_time apply (metis One_nat_def diff_Suc_1 le_add1 less_imp_Suc_add)
  using diff_Suc_less by blast

lemma com_list_to_seq_variables: "set (enumerate_variables (com_list_to_seq cs))
  = { v | v c. c \<in> set cs \<and> v \<in> set (enumerate_variables c)}" 
  apply(induction cs)
   apply(auto simp: set_enumerate_variables_seq)
  by(simp add: enumerate_variables_def)

fun binary_assign_constant:: "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where 
"binary_assign_constant 0 v x = SKIP" |
"binary_assign_constant (Suc n) v x = (var_bit_to_var (v, n)) ::= nth_bit x n ;;
  binary_assign_constant n v x" 

lemma result_of_binary_assign_constant: "t_small_step_fun (3 * n) 
  (binary_assign_constant n v x, s) 
  = (SKIP, \<lambda>w. (case var_to_var_bit w of
      Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit x m) else s w) |
      _ \<Rightarrow> s w))"
proof(induction n arbitrary: s)
  case (Suc n)
  thus ?case 
    apply auto
    apply(rule seq_terminates_when[where ?t1.0=1 and ?t2.0="3*n" and 
          ?s3.0="s(var_bit_to_var (v, n) \<mapsto> nth_bit x n)"])
    by(auto simp: fun_eq_iff var_to_var_bit_eq_Some_iff  split: option.splits)
qed (auto simp: fun_eq_iff split: option.splits)

lemma binary_assign_constant_variables: "set (enumerate_variables (binary_assign_constant n v x))
  = { var_bit_to_var (v, i) | i. i < n }" 
  apply(induction n)
   apply(auto simp: set_enumerate_variables_seq)
  by(auto simp: enumerate_variables_def)

lemma result_of_binary_assign_constant_on_translated_state:
  assumes "n > 0" "x < 2 ^ n" 
  shows "t_small_step_fun (50 * (n + 1)) (binary_assign_constant n v x, 
    IMP_Minus_State_To_IMP_Minus_Minus s n)
    = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus (s(v := x)) n)"
  apply(rule t_small_step_fun_increase_time[where ?t="3*n"])
  apply simp
  apply(subst result_of_binary_assign_constant)
  using assms 
  by (auto simp: fun_eq_iff IMP_Minus_State_To_IMP_Minus_Minus_def 
      IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def split: option.splits)

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

fun copy_var_to_operand:: "nat \<Rightarrow> char \<Rightarrow> vname \<Rightarrow> IMP_Minus_Minus_com" where
"copy_var_to_operand 0 op v = SKIP" |
"copy_var_to_operand (Suc i) op v = 
   (IF [var_bit_to_var (v, i)] \<noteq>0 THEN 
   (operand_bit_to_var (op, i)) ::= One 
    ELSE 
    (operand_bit_to_var (op, i)) ::= Zero) ;;
    copy_var_to_operand i op v " 

lemma copy_var_to_operand_result:
  "t_small_step_fun (4 * n) (copy_var_to_operand n op v, s)
  = (SKIP, \<lambda>w. (case var_to_operand_bit w of
    Some (op', i) \<Rightarrow> (if op' = op \<and> i < n 
  then (case s (var_bit_to_var (v, i)) of Some x \<Rightarrow> Some x | None \<Rightarrow> Some One)
  else s w) |
    _ \<Rightarrow> s w))" 
proof(induction n arbitrary: s)
  case 0
  then show ?case by (auto simp: fun_eq_iff split: option.splits)
next
  case (Suc n)
  let ?s' = "s(operand_bit_to_var (op, n) 
    \<mapsto> (case s (var_bit_to_var (v, n)) of Some x \<Rightarrow> x | None \<Rightarrow> One))"
  show ?case using Suc
    by(auto simp: fun_eq_iff var_to_operand_bit_eq_Some_iff numeral_3_eq_3 less_Suc_eq_le
      split!: option.splits if_splits
      intro!: seq_terminates_when[where ?t1.0=3 and ?t2.0="4 * n" and ?s3.0="?s'"])    
qed

fun copy_const_to_operand:: "nat \<Rightarrow> char \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
"copy_const_to_operand 0 op x = SKIP" |
"copy_const_to_operand (Suc i) op x = 
   (operand_bit_to_var (op, i)) ::= (nth_bit x i) ;;
    copy_const_to_operand i op x " 

lemma copy_const_to_operand_result:
  "t_small_step_fun (4 * n) (copy_const_to_operand n op x, s)
  = (SKIP, \<lambda>w. (case var_to_operand_bit w of
    Some (op', i) \<Rightarrow> (if op' = op \<and> i < n then Some (nth_bit x i) else s w) |
    _ \<Rightarrow> s w))" 
proof(induction n arbitrary: s)
  case 0
  then show ?case by (simp add: fun_eq_iff split: option.splits)
next
  case (Suc n)
  let ?s' = "s(operand_bit_to_var (op, n) \<mapsto> nth_bit x n)"
  show ?case using Suc 
    apply(auto simp: fun_eq_iff var_to_operand_bit_eq_Some_iff split!: option.splits if_splits
      intro!: seq_terminates_when[where ?t1.0=1 and ?t2.0 ="4*n" and ?s3.0="?s'"])
  using less_antisym by blast
qed
  

definition copy_atom_to_operand:: "nat \<Rightarrow> char \<Rightarrow> AExp.atomExp \<Rightarrow> IMP_Minus_Minus_com" where
"copy_atom_to_operand n op a = (case a of 
  AExp.N x \<Rightarrow> copy_const_to_operand n op x |
  AExp.V x \<Rightarrow> copy_var_to_operand n op x)" 

lemma copy_atom_to_operand_a_result: 
  "t_small_step_fun (4 * n) (copy_atom_to_operand n (CHR ''a'') a,
   IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n b c)
  = (SKIP,  IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n (AExp.atomVal a s) c)"
  by(auto simp: copy_atom_to_operand_def fun_eq_iff copy_const_to_operand_result 
      copy_var_to_operand_result IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def 
      var_to_operand_bit_eq_Some_iff
      split!: option.splits AExp.atomExp.splits char.splits bool.splits)

lemma copy_atom_to_operand_b_result: 
  "t_small_step_fun (4 * n) (copy_atom_to_operand n (CHR ''b'') a,
   IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n b c)
  = (SKIP,  IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n b (AExp.atomVal a s))"
  by(auto simp: copy_atom_to_operand_def fun_eq_iff copy_const_to_operand_result 
      copy_var_to_operand_result IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def 
      var_to_operand_bit_eq_Some_iff
      split!: option.splits AExp.atomExp.splits char.splits bool.splits) 

lemma copy_atom_to_operand_variables:
  "set (enumerate_variables (copy_atom_to_operand n op a)) 
    = { operand_bit_to_var (op, i) | i. i < n } 
    \<union> { var_bit_to_var (v, i) | i v. i < n \<and> v \<in> set (atomExp_var a) }" 
  apply (induction n)
  apply(cases a)
    apply (auto simp: copy_atom_to_operand_def enumerate_variables_def)[1]
   apply (auto simp: copy_atom_to_operand_def enumerate_variables_def)[1]
  apply(cases a)
   apply (auto simp: copy_atom_to_operand_def set_enumerate_variables_seq)
  by(auto simp: enumerate_variables_def var_bit_to_var_neq_operand_bit_to_var[symmetric]) 

definition assign_var_carry:: 
  "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
"assign_var_carry i v a b c = 
  (var_bit_to_var (v, i)) ::= (if a + b + c = 1 \<or> a + b + c = 3 then One else Zero) ;; 
  ''carry'' ::= (if a + b + c \<ge> 2 then One else Zero)"

lemma result_of_assign_var_carry:  
  "t_small_step_fun 7 (assign_var_carry i v a b c, s)
    = (SKIP, s(var_bit_to_var (v, i) \<mapsto> (if a + b + c = 1 \<or> a + b + c = 3 then One else Zero),
     ''carry'' \<mapsto> (if a + b + c \<ge> 2 then One else Zero)))"
  by(auto simp: assign_var_carry_def t_small_step_fun_terminate_iff)

definition full_adder:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_Minus_com" where
"full_adder i v  = (let assign = assign_var_carry i v; op_a = operand_bit_to_var (CHR ''a'', i);
  op_b = operand_bit_to_var (CHR ''b'', i) in 
  IF [op_a]\<noteq>0 THEN 
    IF [''carry'']\<noteq>0 THEN
      IF [op_b]\<noteq>0 THEN assign 1 1 1 
      ELSE assign 1 1 0
    ELSE 
      IF [op_b]\<noteq>0 THEN assign 1 0 1
      ELSE assign 1 0 0
  ELSE 
    IF [''carry'']\<noteq>0 THEN
      IF [op_b]\<noteq>0 THEN assign 0 1 1
      ELSE assign 0 1 0
    ELSE 
      IF [op_b]\<noteq>0 THEN assign 0 0 1
      ELSE assign 0 0 0)"

lemma full_adder_correct: 
  assumes "i = 0 \<longrightarrow> s ''carry'' = Some Zero" 
    "i > 0 \<longrightarrow> s ''carry'' = Some (nth_carry (i - 1) a b)"
    "s (operand_bit_to_var (CHR ''a'', i)) = Some (nth_bit a i)" 
    "s (operand_bit_to_var (CHR ''b'', i)) = Some (nth_bit b i)"
  shows "t_small_step_fun 10 (full_adder i v, s) = (SKIP, 
    s(var_bit_to_var (v, i) \<mapsto> nth_bit (a + b) i, ''carry'' \<mapsto> nth_carry i a b))" 
  using assms 
  apply(simp add: full_adder_def Let_def t_small_step_fun_terminate_iff result_of_assign_var_carry)
  apply(cases i)
  by(simp_all add: fun_eq_iff first_bit_of_add nth_bit_of_add)

lemma full_adder_variables: "set (enumerate_variables (full_adder i v)) = 
  { operand_bit_to_var (CHR ''a'', i), operand_bit_to_var (CHR ''b'', i), var_bit_to_var (v, i),
    ''carry''}" 
  apply (auto simp: full_adder_def Let_def)
  by(simp_all add: enumerate_variables_def assign_var_carry_def split: if_splits) 

lemma sequence_of_full_adders: 
  assumes 
    "s ''carry'' = Some Zero" 
    "\<forall>j < k. s (operand_bit_to_var (CHR ''a'', j)) = Some (nth_bit a j)" 
    "\<forall>j < k. s (operand_bit_to_var (CHR ''b'', j)) = Some (nth_bit b j)"
  shows
   "t_small_step_fun (12 * k) (com_list_to_seq (map (\<lambda>i. full_adder i v) [0..< k]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < k then Some (nth_bit (a + b) m) else s w) |
    _ \<Rightarrow> (if w = ''carry'' \<and> k > 0 then Some (nth_carry (k - 1) a b)  
          else s w))))"   
  using assms
proof(induction k)
  case 0
  then show ?case by(auto simp: fun_eq_iff split: option.splits)
next
  case (Suc k)
  hence "t_small_step_fun (12 + 12 * k)
   (com_list_to_seq ((map (\<lambda>i. full_adder i v) [0..< k]) @ [full_adder k v]), s)
    = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < Suc k then Some (nth_bit (a + b) m) else s w) |
    _ \<Rightarrow> (if w = ''carry'' \<and> Suc k > 0 then Some (nth_carry k a b)  
          else s w))))"
    apply(auto simp only: com_list_to_seq_of_length_one_terminates_iff 
        intro!: t_small_step_fun_com_list_to_seq_terminates[where ?t1.0="12 * k" and ?t2.0=11])
    apply(auto)
    apply(subst full_adder_correct)
    by(auto simp add: fun_eq_iff var_to_var_bit_eq_Some_iff split!: option.splits)
  thus ?case by auto
qed

definition adder:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_Minus_com" where
"adder n v = com_list_to_seq (map (\<lambda>i. full_adder i v) [0..< n]) ;;
  ''carry'' ::= Zero" 

lemma result_of_adder: 
  assumes "a + b < 2 ^ n" 
  shows "t_small_step_fun (12 * n + 2) (adder n v, 
    IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b s n a b) 
    = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b (s(v := a + b)) n a b)"
  apply(simp only: adder_def)
  apply(rule seq_terminates_when[OF _  sequence_of_full_adders,
        where ?t2.0="1" and ?b="''carry'' ::= Zero"])
  by(auto simp: fun_eq_iff IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def 
      split: option.splits)

definition binary_adder:: "nat \<Rightarrow> vname \<Rightarrow> AExp.atomExp \<Rightarrow> AExp.atomExp \<Rightarrow> IMP_Minus_Minus_com" where
"binary_adder n v a b = 
  copy_atom_to_operand n (CHR ''a'') a ;;
  (copy_atom_to_operand n (CHR ''b'') b ;;
  (adder n v ;;
  (copy_atom_to_operand n (CHR ''a'') (AExp.N 0) ;;
  copy_atom_to_operand n (CHR ''b'') (AExp.N 0))))"

lemma binary_adder_correct:
  assumes "n > 0"
    "AExp.atomVal a s + AExp.atomVal b s < 2 ^ n" 
  shows "t_small_step_fun (50 * (n + 1)) (binary_adder n v a b, 
    IMP_Minus_State_To_IMP_Minus_Minus s n) 
    = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus (s(v := AExp.atomVal a s + AExp.atomVal b s)) n)"
  using seq_terminates_when'[OF copy_atom_to_operand_a_result[where ?n=n]
      seq_terminates_when'[OF copy_atom_to_operand_b_result
      seq_terminates_when'[OF result_of_adder
      seq_terminates_when'[OF copy_atom_to_operand_a_result copy_atom_to_operand_b_result]]]] 
  assms 
  by(fastforce simp: binary_adder_def 
      IMP_Minus_State_To_IMP_Minus_Minus_as_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b)

definition assign_var_carry_sub:: 
  "nat \<Rightarrow> vname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
"assign_var_carry_sub i v a b c = 
  (var_bit_to_var (v, i)) ::= (if b + c = 0 \<or> b + c = 2 then (if a = 1 then One else Zero)
    else (if b + c = 1 \<and> a = 0 then One else Zero)) ;; 
  ''carry'' ::= (if a < b + c then One else Zero)"

lemma result_of_assign_var_carry_sub:  
  "t_small_step_fun 7 (assign_var_carry_sub i v a b c, s)
    = (SKIP, s(var_bit_to_var (v, i) \<mapsto> (if b + c = 0 \<or> b + c = 2 then (if a = 1 then One else Zero)
    else (if b + c = 1 \<and> a = 0 then One else Zero)),
     ''carry'' \<mapsto>  (if a < b + c then One else Zero)))"
  by(auto simp: assign_var_carry_sub_def t_small_step_fun_terminate_iff)

definition full_subtractor:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_Minus_com" where
"full_subtractor i v  = (let assign = assign_var_carry_sub i v; 
  op_a = [operand_bit_to_var (CHR ''a'', i)];
  op_b = [operand_bit_to_var (CHR ''b'', i)] in 
  IF op_a\<noteq>0 THEN 
    IF [''carry'']\<noteq>0 THEN
      IF op_b\<noteq>0 THEN assign 1 1 1 
      ELSE assign 1 1 0
    ELSE 
      IF op_b\<noteq>0 THEN assign 1 0 1
      ELSE assign 1 0 0
  ELSE 
    IF [''carry'']\<noteq>0 THEN
      IF op_b\<noteq>0 THEN assign 0 1 1
      ELSE assign 0 1 0
    ELSE 
      IF op_b\<noteq>0 THEN assign 0 0 1
      ELSE assign 0 0 0)"

lemma full_subtractor_correct_no_underflow: 
  assumes "a \<ge> b"
    "i = 0 \<longrightarrow> s ''carry'' = Some Zero" 
    "i > 0 \<longrightarrow> s ''carry'' = Some (nth_carry_sub (i - 1) a b)"
    "s (operand_bit_to_var (CHR ''a'', i)) = Some (nth_bit a i)" 
    "s (operand_bit_to_var (CHR ''b'', i)) = Some (nth_bit b i)"
  shows "t_small_step_fun 10 (full_subtractor i v, s) = (SKIP, 
    s(var_bit_to_var (v, i) \<mapsto> nth_bit (a - b) i, ''carry'' \<mapsto> nth_carry_sub i a b))" 
  using assms 
  apply(simp add: full_subtractor_def Let_def t_small_step_fun_terminate_iff 
      result_of_assign_var_carry_sub)
  apply(cases i)
  by(simp_all add: fun_eq_iff first_bit_of_sub_n_no_underflow nth_bit_of_sub_n_no_underflow Let_def)

lemma full_subtractor_variables: "set (enumerate_variables (full_subtractor i v)) = 
  { operand_bit_to_var (CHR ''a'', i), operand_bit_to_var (CHR ''b'', i), var_bit_to_var (v, i),
    ''carry''}" 
  apply (auto simp: full_subtractor_def Let_def)
  by(simp_all add: enumerate_variables_def assign_var_carry_sub_def split: if_splits) 

lemma sequence_of_full_subtractors_no_underflow: 
  assumes "a \<ge> b"
    "s ''carry'' = Some Zero" 
    "\<forall>j \<le> n. s (operand_bit_to_var (CHR ''a'', j)) = Some (nth_bit a j)" 
    "\<forall>j \<le> n. s (operand_bit_to_var (CHR ''b'', j)) = Some (nth_bit b j)"
  shows
   "t_small_step_fun (12 * n)
                       (com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..< n]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < n then Some (nth_bit (a - b) m) else s w) |
    _ \<Rightarrow> (if w = ''carry'' \<and> n > 0 then Some (nth_carry_sub (n - 1) a b)  
          else s w))))"
  using assms
proof(induction n)
  case 0
  then show ?case by(auto simp: fun_eq_iff split: option.splits)
next
  case (Suc n)
  have "t_small_step_fun (12 + 12 * n)
   (com_list_to_seq ((map (\<lambda>i. full_subtractor i v) [0..< n]) @ [full_subtractor n v]), s)
    = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m < Suc n then Some (nth_bit (a - b) m) else s w) |
    _ \<Rightarrow> (if w = ''carry'' \<and> Suc n > 0 then Some (nth_carry_sub n a b)  
          else s w))))"
    apply(rule t_small_step_fun_com_list_to_seq_terminates[OF _ Suc.IH 
          iffD2[OF com_list_to_seq_of_length_one_terminates_iff[where ?t="11"]]])
    using Suc  apply(auto)
    apply(subst full_subtractor_correct_no_underflow)
    using Suc
    by(auto simp add: fun_eq_iff var_to_var_bit_eq_Some_iff split!: option.splits)
  thus ?case by auto
qed

lemma sequence_of_full_subtractors_with_underflow: 
  assumes "a < b"
    "a < 2^(n)" "b < 2^(n)" 
    "s ''carry'' = Some Zero" 
    "\<forall>j \<le> k. s (operand_bit_to_var (CHR ''a'', j)) = Some (nth_bit a j)" 
    "\<forall>j \<le> k. s (operand_bit_to_var (CHR ''b'', j)) = Some (nth_bit b j)"
  shows
   "t_small_step_fun (12 * n)
                       (com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..< n]), s)
  = (SKIP, (\<lambda>w. (case var_to_var_bit w of
    Some (w', m) \<Rightarrow> (if w' = v \<and> m \<le> k then Some (nth_bit (2^(k+2) + a - b) m) else s w) |
    _ \<Rightarrow> (if w = ''carry'' then Some One
          else s w))))"   
  sorry

definition underflow_handler:: "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_Minus_com" where
"underflow_handler n v = (IF [''carry'']\<noteq>0 THEN (''carry'' ::= Zero ;;
  binary_assign_constant n v 0)
  ELSE SKIP)" 

definition subtract_handle_overflow:: 
  "nat \<Rightarrow> vname \<Rightarrow> IMP_Minus_Minus_com" where
"subtract_handle_overflow n v = 
  com_list_to_seq (map (\<lambda>i. full_subtractor i v) [0..<n]) ;; 
  underflow_handler n v"


lemma subtract_handle_overflow_variables:
  "set (enumerate_variables (subtract_handle_overflow n v)) 
  = { operand_bit_to_var (op, i) | i op. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') } 
    \<union> { var_bit_to_var (v, i) | i. i < n }
    \<union> { ''carry'' }"
  apply(auto simp: subtract_handle_overflow_def 
      set_enumerate_variables_seq com_list_to_seq_variables full_subtractor_variables
      set_enumerate_variables_if underflow_handler_def binary_assign_constant_variables)
  by(auto simp: underflow_handler_def enumerate_variables_def split: if_splits)

definition binary_subtractor:: "nat \<Rightarrow> vname \<Rightarrow> AExp.atomExp \<Rightarrow> AExp.atomExp \<Rightarrow> IMP_Minus_Minus_com" where
"binary_subtractor n v a b = 
  copy_atom_to_operand n (CHR ''a'') a ;;
  (copy_atom_to_operand n (CHR ''b'') b ;;
  (subtract_handle_overflow n v ;;
  (copy_atom_to_operand n (CHR ''a'') (AExp.N 0) ;;
  copy_atom_to_operand n (CHR ''b'') (AExp.N 0))))"

lemma binary_subtractor_correct: 
  assumes "n > 0"
    "AExp.atomVal a s < 2 ^ n" "AExp.atomVal b s < 2 ^ n" 
  shows "t_small_step_fun (50 * (n + 1)) (binary_subtractor n v a b, 
    IMP_Minus_State_To_IMP_Minus_Minus s n) 
    = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus (s(v := AExp.atomVal a s - AExp.atomVal b s)) n)"
  sorry

definition assignment_to_binary:: "nat \<Rightarrow> vname \<Rightarrow> AExp.aexp \<Rightarrow> IMP_Minus_Minus_com" where
"assignment_to_binary n v aexp = (case aexp of
  AExp.A a \<Rightarrow> binary_adder n v a (AExp.N 0) |
  AExp.Plus a b \<Rightarrow> binary_adder n v a b |
  AExp.Sub a b \<Rightarrow> binary_subtractor n v a b)" 

lemma assignment_to_binary_correct: 
  assumes "n > 0"  "AExp.aval a s < 2 ^ n" "\<forall>v. s v < 2 ^ n" "aexp_max_constant a < 2 ^ n"
  shows "t_small_step_fun (50 * (n + 1)) (assignment_to_binary n v a,  
  IMP_Minus_State_To_IMP_Minus_Minus s n) 
  = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus (s(v := AExp.aval a s)) n)" 
using assms binary_adder_correct proof(cases a)
  case (Sub x31 x32)
  then show ?thesis 
    apply(simp add: assignment_to_binary_def)  
    apply(rule binary_subtractor_correct[simplified])
    using assms by(cases x31; cases x32; auto)+
qed (auto simp: assignment_to_binary_def)

lemma assignment_to_binary_variables:
  "set (enumerate_variables (assignment_to_binary n v a)) \<subseteq> 
    { var_bit_to_var (w, i) | w i. i < n \<and> (w = v \<or> w \<in> set (aexp_vars a)) }
    \<union> { operand_bit_to_var (op, i) | op i. i < n \<and> (op = CHR ''a'' \<or> op = CHR ''b'') }
    \<union> { ''carry'' }" 
  apply(cases a)
  by(auto simp: assignment_to_binary_def binary_adder_def set_enumerate_variables_seq 
      copy_atom_to_operand_variables adder_def com_list_to_seq_variables full_adder_variables
      binary_subtractor_def subtract_handle_overflow_variables)

end 