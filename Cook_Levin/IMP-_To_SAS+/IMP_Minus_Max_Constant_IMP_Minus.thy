theory IMP_Minus_Max_Constant_IMP_Minus
  imports IMP_Minus_Max_Constant_Nat
    "../../IMP-/IMP_Minus_Nat_Bijection"
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax

definition atomExp_to_constant_IMP_Minus where "atomExp_to_constant_IMP_Minus \<equiv>
  ''atomExp_to_constant'' ::= (A (V ''a'')) ;;
  IMP_Minus_fst_nat ;;
  ''a'' ::= (A (V ''atomExp_to_constant'')) ;;
  IMP_Minus_snd_nat ;;
  (IF ''fst_nat'' \<noteq>0 
  THEN 
    ''atomExp_to_constant'' ::= (A (V ''snd_nat''))  
  ELSE
    ''atomExp_to_constant'' ::=  (A (N 0)));;
  ''fst_nat'' ::= (A (N 0)) ;;
  ''snd_nat'' ::= (A (N 0))"

definition atomExp_to_constant_IMP_Minus_time where "atomExp_to_constant_IMP_Minus_time x \<equiv>
  11 + 2 * IMP_Minus_fst_nat_time x"

lemma atomExp_to_constant_IMP_Minus_correct:
  "(atomExp_to_constant_IMP_Minus, s) \<Rightarrow>\<^bsup>atomExp_to_constant_IMP_Minus_time (s ''a'')\<^esup> 
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0,
      ''atomExp_to_constant'' := atomExp_to_constant_tail (s ''a''))"
  apply(cases "fst_nat (s ''a'')")
  unfolding atomExp_to_constant_IMP_Minus_def atomExp_to_constant_tail_def
    atomExp_to_constant_nat_def atomExp_to_constant_IMP_Minus_time_def
  by (fastforce 
      intro!: terminates_in_state_intro[OF Seq]
      IMP_Minus_fst_nat_correct      
      IMP_Minus_snd_nat_correct)+

definition aexp_max_constant_IMP_Minus where "aexp_max_constant_IMP_Minus \<equiv> 
  ''aexp_max_constant'' ::= (A (V ''a'')) ;;

  ''a'' ::= (A (N 1)) ;;
  ''b'' ::= (A (V ''aexp_max_constant'')) ;;
  nth_nat_IMP_Minus ;;
  
  ''a'' ::= (A (V ''nth_nat'')) ;;
  atomExp_to_constant_IMP_Minus ;;
  
  ''a'' ::= (A (N 2)) ;;
  ''b'' ::= (A (V ''aexp_max_constant'')) ;;
  nth_nat_IMP_Minus ;;
  
  ''a'' ::= (A (V ''nth_nat'')) ;;
  ''nth_nat'' ::= (A (V ''atomExp_to_constant'')) ;;
  atomExp_to_constant_IMP_Minus ;;

  ''a'' ::= ((V ''aexp_max_constant'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;

  ''a'' ::= ((N 3) \<ominus> (V ''fst_nat'')) ;;
  IF ''a'' \<noteq>0 
  THEN
  (
    IF ''fst_nat'' \<noteq>0
    THEN
      ''b'' ::= (A (V ''atomExp_to_constant''))
    ELSE
      ''b'' ::= (A (V ''nth_nat''))
  )
  ELSE
  (
    IF ''fst_nat'' \<noteq>0
    THEN
      ''b'' ::= (A (V ''nth_nat''))
    ELSE
      ''b'' ::= (A (V ''nth_nat''))
  );;

  ''a'' ::= (A (V ''nth_nat'')) ;;

  IMP_Minus_max_a_min_b ;;
  ''aexp_max_constant'' ::= (A (V ''a'')) ;;
  ''a'' ::= (A (N 0)) ;; 
  ''b'' ::= (A (N 0)) ;;
  ''nth_nat'' ::= (A (N 0)) ;;
  ''atomExp_to_constant'' ::= (A (N 0)) ;;
  ''fst_nat'' ::= (A (N 0))"

definition aexp_max_constant_IMP_Minus_time where "aexp_max_constant_IMP_Minus_time x \<equiv>
  38 + nth_nat_IMP_Minus_time 1 x + atomExp_to_constant_IMP_Minus_time (nth_nat 1 x)
  + nth_nat_IMP_Minus_time 2 x +  atomExp_to_constant_IMP_Minus_time (nth_nat 2 x)
  + IMP_Minus_fst_nat_time (x - 1) + 11" 

lemma Seq: "\<lbrakk>(c1,s1) \<Rightarrow>\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>\<^bsup> y \<^esup> s3 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y \<^esup> s3"
  by auto

lemma aexp_max_constant_IMP_Minus_correct:
  "(aexp_max_constant_IMP_Minus, s) 
    \<Rightarrow>\<^bsup>aexp_max_constant_IMP_Minus_time (s ''a'')\<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0,
      ''nth_nat'' := 0,
      ''atomExp_to_constant'' := 0,
      ''aexp_max_constant'' := aexp_max_constant_tail (s ''a''))"
  unfolding aexp_max_constant_IMP_Minus_def aexp_max_constant_IMP_Minus_time_def
  apply(cases "3 - fst_nat (s ''a'' - Suc 0)"; cases "fst_nat (s ''a'' - Suc 0)")
     apply simp
  apply(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)
  (*apply(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)*)
  subgoal
    by(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)
  subgoal
    by(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)
  done


end