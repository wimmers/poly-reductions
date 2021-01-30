\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to IMP--"

theory IMP_Minus_To_IMP_Minus_Minus imports Binary_Operations
begin

fun IMP_Minus_To_IMP_Minus_Minus:: "IMP_Minus_com \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
"IMP_Minus_To_IMP_Minus_Minus Com.SKIP n = SKIP" |
"IMP_Minus_To_IMP_Minus_Minus (Com.Assign v aexp) n = 
  com_list_to_seq (((''?$'' @ v) ::= A (N 0)) # (map (case aexp of
    AExp.A a \<Rightarrow> (\<lambda>i. full_adder i v a (AExp.N 0)) |
    AExp.Plus a b \<Rightarrow> (\<lambda>i. full_adder i v a b) | 
    AExp.Sub a b \<Rightarrow> (\<lambda>i. full_subtractor i v a b)) [0..<n])) ;; overflow_handler v n" |
"IMP_Minus_To_IMP_Minus_Minus (Com.Seq c1 c2) n = 
  (IMP_Minus_To_IMP_Minus_Minus c1 n ;; IMP_Minus_To_IMP_Minus_Minus c2 n )" |
"IMP_Minus_To_IMP_Minus_Minus (Com.If v c1 c2) n = (IF (''?$'' @ v)\<noteq>0 THEN
  IMP_Minus_To_IMP_Minus_Minus c1 n ELSE IMP_Minus_To_IMP_Minus_Minus c2 n)" |
"IMP_Minus_To_IMP_Minus_Minus (Com.While v c) n = (WHILE (''?$'' @ v)\<noteq>0 DO
  IMP_Minus_To_IMP_Minus_Minus c n)"

fun atomExp_to_constant:: "AExp.atomExp \<Rightarrow> nat" where
"atomExp_to_constant (AExp.V var) = 0" |
"atomExp_to_constant (AExp.N val) = val"

fun max_constant :: "IMP_Minus_com \<Rightarrow> nat" where
"max_constant (Com.SKIP) = 0" |
"max_constant (Com.Assign vname aexp) = (case aexp of
  (AExp.A a) \<Rightarrow> atomExp_to_constant a |
  (AExp.Plus a b) \<Rightarrow> max (atomExp_to_constant a) (atomExp_to_constant b) |
  (AExp.Sub a b) \<Rightarrow> max (atomExp_to_constant a) (atomExp_to_constant b))" |
"max_constant (Com.Seq c1  c2) = max (max_constant c1) (max_constant c2)" |         
"max_constant (Com.If  _ c1 c2) = max (max_constant c1) (max_constant c2)"  |   
"max_constant (Com.While _ c) = max_constant c"

fun bit_length::"nat \<Rightarrow> nat" where
"bit_length  0 = 0" | 
"bit_length  n = 1 + bit_length (n div 2) "

lemma IMP_Minus_To_IMP_Minus_Minus: 
  assumes 
    "(c1 :: IMP_Minus_com, s1) \<rightarrow>\<^bsup>t\<^esup> (Com.SKIP, s2)"
    "n > t + bit_length (max (Max (domain s1)) (max_constant c1))"
  shows
    "t_small_step_fun (100 * n * t) 
      (IMP_Minus_To_IMP_Minus_Minus c1 n, IMP_Minus_State_To_IMP_Minus_Minus s1 n)
     = (SKIP, IMP_Minus_State_To_IMP_Minus_Minus s2 n)"
using assms proof(induction c1 arbitrary: s2)
  case SKIP
  then show ?case by (cases t) auto
next
  case (Assign v a)
  hence "100 * n * t > 0" using small_step_progress by auto
  thus ?case using Assign
    apply(cases a)
      apply(auto simp: t_small_step_fun_ge_0)
    apply(auto simp: seq_terminates_iff)

next
  case (Seq c11 c12)
  then show ?case sorry
next
  case (If x1 c11 c12)
  then show ?case sorry
next
  case (While x1 c1)
  then show ?case sorry
qed
  
end