theory Binary_Arithmetic_IMP 
  imports "../../../IMP-/IMP_Minus_Nat_Bijection"  Binary_Arithmetic_Nat
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax
unbundle Com.no_com_syntax


fun nth_bit_of_num_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_nat x n  = 
  (if x = 0 then
    (if n = 0 then
       1
     else
       0)
   else
     if n = 0 then
       (if hd_nat x = 0 then
          0
        else
          1)
     else
        nth_bit_of_num_nat (tl_nat x) (n-1)
   )"

fun nth_bit_of_num_nat_imp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_nat_imp x n  = 
(
  let
    next_iteration = (0::nat)
  in
    (if x \<noteq> 0 then
       if n \<noteq> 0 then
         (let
            x = tl_nat x;
            n = n - 1;
            next_iteration = nth_bit_of_num_nat x n
          in 
            next_iteration
         )
       else
         let
           hd_x = hd_nat x
         in
           (if hd_x \<noteq> 0 then
             (let
                ret = 1
              in 
                ret
             )
            else
             (let
                ret = 0
              in 
                ret
             )
           )
     else
       if n \<noteq> 0 then
         (let
            ret = 0
          in 
            ret
         )
       else
         (let
            ret = 1
          in 
            ret
         )
     )
)"

lemma nth_bit_of_num_nat_imp_correct:
  "nth_bit_of_num_nat x n = nth_bit_of_num_nat_imp x n"
  by (auto simp: Let_def)


(* [''tl''] ''xs'' ::=  (A ( V ''x'')) ;;
   invoke_subprogram ''tl'' tl_IMP;;
   ''x'' ::= [''tl''] (A (V ''ans''));;
   [''tl''] ''ans'' ::= A (N 0);;
   ''n'' ::= (V ''n'' \<ominus> N 1 );; 
   IF ''x''\<noteq>0 THEN 
        (IF ''n''\<noteq>0 THEN ''b''::= A (N 1) ELSE ''b''::= A (N 0)) 
        ELSE ''b''::= A (N 0) 
   
*)

term invoke_subprogram

abbreviation "invoke_program_1 pfx prog input1 output \<equiv>
          [pfx] ''input1'' ::=  (A ( V input1)) ;;
          invoke_subprogram pfx tl_IMP;;
          output ::= [pfx] (A (V ''ans''));;
          [pfx] ''ans'' ::= A (N 0)
"


definition nth_bit_of_num_iteration::pcom  where "nth_bit_of_num_iteration \<equiv>
     ''next_iteration'' ::= A (N 0);;
     IF ''x''\<noteq>0 THEN
       IF ''n''\<noteq>0 THEN
            invoke_program_1 ''tl'' tl_IMP ''x'' ''x'';;
            ''n'' ::= (V ''n'' \<ominus> N 1 );;
            ''next_iteration'' ::= A(N 1)
       ELSE
            invoke_program_1 ''hd'' hd_IMP ''x'' ''hd_x'';;
            IF ''hd_x''\<noteq>0 THEN
                ''ret'' ::= A (N 1)
            ELSE
                ''ret'' ::= A (N 0)
     ELSE
       IF ''n''\<noteq>0 THEN
            ''ret'' ::= A (N 0)
       ELSE
            ''ret'' ::= A (N 1)
"

definition nth_bit_of_num_loop :: "pcom" where 
"nth_bit_of_num_loop \<equiv> WHILE ''b''\<noteq>0 DO nth_bit_of_num_iteration"

lemma tl_nat_le: "tl_nat x \<le> x"
  sorry

function (sequential) nth_bit_of_num_loop_t':: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_loop_t' 0 _ _  = 2 "|
"nth_bit_of_num_loop_t' (Suc b) x n  = (let
  x' = tl_nat x; n' = n - 1; b' = (if x'>0 \<and> n'>0 then Suc 0 else 0)
in
  b' + (nth_bit_of_num_iteration_t x n + nth_bit_of_num_loop_t' b' x' n')) "
  by pat_completeness simp_all
termination (* Proof proceeds by noticing that the sum of the three arguments is always decreasing, rest is hammering *)
  by(relation "measure (\<lambda>(b, x, n) . b+x+n)") (auto simp add: add.commute add_increasing le_imp_less_Suc tl_nat_le)


function (sequential) nth_bit_of_num_loop_state_transformer' ::
    "char list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (char list \<Rightarrow> nat) \<Rightarrow> char list \<Rightarrow> nat" where
  "nth_bit_of_num_loop_state_transformer' p 0 x n = id "|
  "nth_bit_of_num_loop_state_transformer' p b x n = (let
    x' = tl_nat x; n' = n-1;
    b' = (if x'>0 \<and> n'>0 then Suc 0 else 0)
  in
    nth_bit_of_num_iteration_state_transformer p x n o nth_bit_of_num_loop_state_transformer' p b' x' n')"
 by pat_completeness simp_all
termination (* Proof proceeds by noticing that the sum of the last three arguments is always decreasing, rest is hammering *)
  by (relation "measure (\<lambda>(p, b, x, n) . b+x+n)") (auto simp add: add.commute add_increasing le_imp_less_Suc tl_nat_le) 


definition nth_bit_of_num_if ::pcom where "nth_bit_of_num_if \<equiv>
 IF ''x''\<noteq>0 THEN 
        (IF ''n''\<noteq>0 THEN ''b''::= A (N 1) ELSE ''b''::= A (N 0)) 
        ELSE ''b''::= A (N 0) 
"

abbreviation nth_bit_of_num_if_state_transformer 
  where "nth_bit_of_num_if_state_transformer p x n \<equiv>
    state_transformer p [(''b'',if x >0 \<and> n>0 then 1 else 0)]
"

fun nth_bit_of_num_if_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"nth_bit_of_num_if_time 0 _ = 3"|
"nth_bit_of_num_if_time _ _ = 4"

lemma nth_bit_of_num_if_correct[intro]:
"\<lbrakk> s (add_prefix p ''x'')= x ; s (add_prefix p ''n'') = n  \<rbrakk> \<Longrightarrow>
(nth_bit_of_num_if p, s) \<Rightarrow>\<^bsup>nth_bit_of_num_if_time x n \<^esup>
nth_bit_of_num_if_state_transformer p x n s "
  unfolding nth_bit_of_num_if_def 
  apply (cases x;cases n)
     apply (rule Big_StepT.IfFalse)
       apply simp
      apply (rule terminates_in_time_state_intro)
        apply blast
       apply simp
      apply simp
     apply simp
 apply (rule Big_StepT.IfFalse)
       apply simp
      apply (rule terminates_in_time_state_intro)
        apply blast
       apply simp
      apply simp
    apply simp
   apply (rule Big_StepT.IfTrue)
     apply simp
    apply (rule Big_StepT.IfFalse)
      apply simp
        apply (rule terminates_in_time_state_intro)
       apply fast
      apply fast
     apply force
    apply simp
   apply simp
      apply (rule Big_StepT.IfTrue)
    apply simp
            apply (rule Big_StepT.IfTrue)
     apply simp
              apply (rule terminates_in_time_state_intro)
  apply blast
     apply simp
    apply simp
  apply simp
  by simp
  
definition nth_bit_of_num_iteration::pcom  where "nth_bit_of_num_iteration \<equiv>
  [''tl''] ''xs'' ::=  (A ( V ''x'')) ;;
   invoke_subprogram ''tl'' tl_IMP;;
   ''x'' ::= [''tl''] (A (V ''ans''));;
   [''tl''] ''ans'' ::= A (N 0);;
   ''n'' ::= (V ''n'' \<ominus> N 1 );; 
    nth_bit_of_num_if
"

definition nth_bit_of_num_iteration_t :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"nth_bit_of_num_iteration_t x n = 8 + tl_time x + nth_bit_of_num_if_time (tl_nat x) (n-1)"

abbreviation nth_bit_of_num_iteration_state_transformer 
  where "nth_bit_of_num_iteration_state_transformer p x n \<equiv>
     nth_bit_of_num_if_state_transformer p (tl_nat x) (n-1) o  state_transformer (''tl'' @ p) [( ''ans'', 0)] o
 tl_state_transformer (''tl'' @ p) x o  state_transformer p [(''x'', tl_nat x),(''n'',n-1)] 
"
value "nth_bit_of_num_iteration_state_transformer"
lemma nth_bit_of_num_iteration_correct[intro]:
 " s (add_prefix p ''x'') = x \<Longrightarrow> s (add_prefix p ''n'') = n \<Longrightarrow>
(nth_bit_of_num_iteration p,s)  \<Rightarrow>\<^bsup>nth_bit_of_num_iteration_t x n \<^esup> 
nth_bit_of_num_iteration_state_transformer p x n s"
  unfolding nth_bit_of_num_iteration_def nth_bit_of_num_iteration_t_def
  apply (rule terminates_in_time_state_intro)
    apply (rule Big_StepT.Seq)+
              apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
 apply fastforce
   apply fastforce
by fastforce
  
  




definition nth_bit_of_num_loop :: "pcom" where 
"nth_bit_of_num_loop \<equiv> WHILE ''b''\<noteq>0 DO nth_bit_of_num_iteration"

lemma tl_nat_le: "tl_nat x \<le> x"
  sorry

function (sequential) nth_bit_of_num_loop_t':: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_loop_t' 0 _ _  = 2 "|
"nth_bit_of_num_loop_t' (Suc b) x n  = (let
  x' = tl_nat x; n' = n - 1; b' = (if x'>0 \<and> n'>0 then Suc 0 else 0)
in
  b' + (nth_bit_of_num_iteration_t x n + nth_bit_of_num_loop_t' b' x' n')) "
  by pat_completeness simp_all
termination (* Proof proceeds by noticing that the sum of the three arguments is always decreasing, rest is hammering *)
  by(relation "measure (\<lambda>(b, x, n) . b+x+n)") (auto simp add: add.commute add_increasing le_imp_less_Suc tl_nat_le)


function (sequential) nth_bit_of_num_loop_state_transformer' ::
    "char list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (char list \<Rightarrow> nat) \<Rightarrow> char list \<Rightarrow> nat" where
  "nth_bit_of_num_loop_state_transformer' p 0 x n = id "|
  "nth_bit_of_num_loop_state_transformer' p b x n = (let
    x' = tl_nat x; n' = n-1;
    b' = (if x'>0 \<and> n'>0 then Suc 0 else 0)
  in
    nth_bit_of_num_iteration_state_transformer p x n o nth_bit_of_num_loop_state_transformer' p b' x' n')"
 by pat_completeness simp_all
termination (* Proof proceeds by noticing that the sum of the last three arguments is always decreasing, rest is hammering *)
  by (relation "measure (\<lambda>(p, b, x, n) . b+x+n)") (auto simp add: add.commute add_increasing le_imp_less_Suc tl_nat_le) 

fun nth_bit_of_num_loop_t:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"nth_bit_of_num_loop_t 0 _ _  = 2 "|
"nth_bit_of_num_loop_t (Suc b) x n  = (let x' = tl_nat x; 
n' = n - 1 
in ( if x'>0 \<and> n'>0 then 1 + nth_bit_of_num_iteration_t x n + nth_bit_of_num_loop_t (Suc 0) x' n'
else 1 + nth_bit_of_num_iteration_t x n + nth_bit_of_num_loop_t 0 x' n'
) ) "

fun nth_bit_of_num_loop_state_transformer ::
"char list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (char list \<Rightarrow> nat) \<Rightarrow> char list \<Rightarrow> nat" where 
"nth_bit_of_num_loop_state_transformer p 0 x n = id "|
"nth_bit_of_num_loop_state_transformer p (Suc b) x n = (let x' = tl_nat x; n' = n-1;
iteration = nth_bit_of_num_iteration_state_transformer p x n  in 
(if x'>0 \<and> n'>0 then nth_bit_of_num_loop_state_transformer p (Suc 0) x' n' o iteration else
nth_bit_of_num_loop_state_transformer p 0 x' n' o iteration
 ))"

lemma "
(nth_bit_of_num_iteration_state_transformer p (tl_nat x) (n-1) o
     nth_bit_of_num_iteration_state_transformer p x n) s = nth_bit_of_num_iteration_state_transformer p (tl_nat x) (n-1) s 
"
  sledgehammer
lemma " x' = tl_nat x \<Longrightarrow> n' = n-1 \<Longrightarrow> x>0 \<Longrightarrow> n> 0 \<Longrightarrow>
             (nth_bit_of_num_loop_state_transformer p (Suc 0) x' n'
o nth_bit_of_num_iteration_state_transformer p x n ) s = 
      (nth_bit_of_num_loop_state_transformer p (Suc 0) x' n') s"
  apply (induction  x' n' arbitrary: x n s rule:nth_bit_of_num_nat.induct)
  apply auto
  apply fastforce
fun nth_bit_of_num_loop_state_transformer' ::
"char list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (char list \<Rightarrow> nat) \<Rightarrow> char list \<Rightarrow> nat" where 
"nth_bit_of_num_loop_state_transformer' p 0 x n = id "|
"nth_bit_of_num_loop_state_transformer' p b x n = (let x' = tl_nat x; n' = n-1;
b' = (if x'>0 \<and> n'>0 then Suc 0 else 0); iteration = nth_bit_of_num_iteration_state_transformer p x n
 in 
 iteration o nth_bit_of_num_loop_state_transformer' p b' x' n')"


thm Big_StepT.WhileTrue

  
  

lemma 
"\<lbrakk>s (add_prefix p ''x'') = x ; s (add_prefix p ''n'') = n ; s (add_prefix p ''b'') = b \<rbrakk>
\<Longrightarrow> (nth_bit_of_num_loop p,s) \<Rightarrow>\<^bsup>nth_bit_of_num_loop_t b x n \<^esup>
      nth_bit_of_num_loop_state_transformer p b x n s"
  unfolding nth_bit_of_num_loop_def 
  apply(induction b x n arbitrary:s rule: nth_bit_of_num_loop_t.induct)
  apply(rule terminates_in_time_state_intro)
     apply (rule Big_StepT.WhileFalse)
     apply simp
  apply simp
   apply simp
      apply(rule terminates_in_time_state_intro)
    apply (rule Big_StepT.WhileTrue)
       apply linarith
      apply auto[1]
     apply (split if_splits) apply (auto simp only:)
  oops 

lemma
"(nth_bit_of_num_loop p,s) \<Rightarrow>\<^bsup>nth_bit_of_num_loop_t (s (add_prefix p ''b''))
 (s (add_prefix p ''x''))
 (s (add_prefix p ''n'')) \<^esup>
      nth_bit_of_num_loop_state_transformer p (s (add_prefix p ''b'')) (s (add_prefix p ''x''))
  (s (add_prefix p ''n'')) s"
  unfolding nth_bit_of_num_loop_def 
proof(induction "(s (add_prefix p ''b''))" "s (add_prefix p ''x'')" "s (add_prefix p ''n'')" arbitrary:s rule: nth_bit_of_num_loop_t.induct)
case (1)
  show ?case 
  apply(rule terminates_in_time_state_intro)
 apply (rule Big_StepT.WhileFalse)
   using 1  by auto
next
  case (2 v)
  obtain s' where s'_def: "s' = (state_transformer p
       [(''b'',
         if 0 < tl_nat (s (add_prefix p ''x'')) \<and> 0 < s (add_prefix p ''n'') - 1 then 1
         else 0)] \<circ>
      state_transformer (''tl'' @ p) [(''ans'', 0)] \<circ>
      tl_state_transformer (''tl'' @ p) (s (add_prefix p ''x'')) \<circ>
      state_transformer p
       [(''x'', tl_nat (s (add_prefix p ''x''))), (''n'', s (add_prefix p ''n'') - 1)])
      s" by simp
    show ?case 
      apply(rule terminates_in_time_state_intro [where s'= "if  0 < tl_nat (s (add_prefix p ''x'')) \<and> 0 < s (add_prefix p ''n'') - 1 then s1 else s2"  
     for s1 s2] )
        apply (rule Big_StepT.WhileTrue[where 
 y= "if  0 < tl_nat (s (add_prefix p ''x'')) \<and> 0 < s (add_prefix p ''n'') - 1 then t1 else t2"  
     for t1 t2])
       using 2(3) apply linarith
           apply rule
            apply simp
           apply simp
       apply(rule terminates_split_if)
       using 2(1)[of s'] s'_def apply fastforce
       using 2(2)[of s'] s'_def apply fastforce
         apply fastforce
       using 2(3)[symmetric] apply auto[1]
       apply (smt (z3) One_nat_def less_diff_conv plus_1_eq_Suc) 
       using 2(3)[symmetric] apply auto
       apply (auto simp only:Let_def comp_apply)
       
qed

thm If_tE
end 