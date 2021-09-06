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


definition add_res_nat_first_part where "add_res_nat_first_part \<equiv>
  ''d'' ::= (A (V ''a'')) ;;
  ''e'' ::= (A (V ''b'')) ;;

  ''a'' ::= ((V ''e'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''f'' ::= (A (V ''fst_nat'')) ;;

  ''a'' ::= ((V ''e'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  ''g'' ::= (A (V ''snd_nat'')) ;;

  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''h'' ::= (A (V ''fst_nat'')) ;;

  ''a'' ::= (A (N (Suc 0))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''i'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc 0)))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''j'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc (Suc 0))))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus"

definition add_res_nat_first_part_time where "add_res_nat_first_part_time n s \<equiv>
  (let h = hd_nat s in
    32 + 2 * IMP_Minus_fst_nat_time (s - 1) + IMP_Minus_fst_nat_time (h - 1)
    + nth_nat_IMP_Minus_time (Suc 0) h + nth_nat_IMP_Minus_time (Suc (Suc 0)) h
    + nth_nat_IMP_Minus_time (Suc (Suc (Suc 0))) h)"

lemma add_res_nat_first_part_correct:
  "(add_res_nat_first_part, s) \<Rightarrow>\<^bsup>add_res_nat_first_part_time (s ''a'') (s ''b'')\<^esup>
    (let h = hd_nat (s ''b''); 
         t = tl_nat (s ''b''); 
         c = hd_nat h;  
         e1 = nth_nat (Suc 0) h ; 
         e2 = nth_nat (Suc (Suc 0)) h; 
         e3 = nth_nat (Suc (Suc (Suc 0))) h in 
       s(''a'' := 0,
         ''b'' := 0,
         ''c'' := 0,
         ''d'' := s ''a'',
         ''e'' := s ''b'',
         ''f'' := h,
         ''g'' := t,
         ''h'' := c,
         ''i'' := e1,
         ''j'' := e2,
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := e3))"
  unfolding Let_def add_res_nat_first_part_def add_res_nat_first_part_time_def hd_nat_def tl_nat_def
  by (fastforce intro: terminates_in_time_state_intro[OF Seq] 
      terminates_in_state_intro[OF nth_nat_IMP_Minus_correct]
      IMP_Minus_fst_nat_correct IMP_Minus_snd_nat_correct)

definition add_res_nat_second_part where "add_res_nat_second_part \<equiv>
  ''k'' ::= (A (V ''d'')) ;;

  cons_list_IMP_Minus [N 7, V ''k'', N 0] ;;   
  cons_IMP_Minus (V ''cons'') (N 0) ;;
  ''l'' ::= (A (V ''cons'')) ;;

  cons_list_IMP_Minus [N 3, V ''i'', V ''j'', V ''k'', N 0] ;;
  cons_IMP_Minus (V ''cons'') (V ''g'') ;;
  ''m'' ::= (A (V ''cons'')) ;;
  
  cons_list_IMP_Minus [N 4, V ''i'', V ''j'', V ''nth_nat'', V ''k'', N 0] ;;
  cons_IMP_Minus (V ''cons'') (V ''g'') ;;
  ''n'' ::= (A (V ''cons'')) ;;

  cons_list_IMP_Minus [N 6, V ''i'', V ''k'', N 0] ;;
  cons_IMP_Minus (V ''cons'') (V ''g'') ;;

  ''f'' ::= (A (N 0)) ;;
  ''g'' ::= (A (N 0)) ;;
  ''i'' ::= (A (N 0)) ;;
  ''j'' ::= (A (N 0)) ;;
  ''nth_nat'' ::= (A (N 0)) "

definition add_res_nat_second_part_time where "add_res_nat_second_part_time n s \<equiv>
  (let h = hd_nat s; 
       t = tl_nat s; 
       c = hd_nat h;  
       e1 = nth_nat (Suc 0) h ; 
       e2 = nth_nat (Suc (Suc 0)) h; 
       e3 = nth_nat (Suc (Suc (Suc 0))) h;
       l1 = [7, n, 0];
       l2 = [3, e1, e2, n, 0];
       l3 = [4, e1, e2, e3, n, 0];
       l4 = [6, e1, n, 0]
    in 
      18 + cons_list_IMP_Minus_time l1 + cons_list_IMP_Minus_time l2 
         + cons_list_IMP_Minus_time l3 + cons_list_IMP_Minus_time l4
         + cons_IMP_Minus_time (cons_list l1) 0 + cons_IMP_Minus_time (cons_list l2) t
         + cons_IMP_Minus_time (cons_list l3) t + cons_IMP_Minus_time (cons_list l4) t)"

lemma add_res_nat_second_part_correct:  
  "(add_res_nat_first_part ;; add_res_nat_second_part, s) 
    \<Rightarrow>\<^bsup>add_res_nat_first_part_time (s ''a'') (s ''b'') 
      + add_res_nat_second_part_time (s ''a'') (s ''b'') \<^esup>
    (let h = hd_nat (s ''b''); 
       t = tl_nat (s ''b''); 
       c = hd_nat h;  
       e1 = nth_nat (Suc 0) h ; 
       e2 = nth_nat (Suc (Suc 0)) h; 
       e3 = nth_nat (Suc (Suc (Suc 0))) h;
       l1 = [7, s ''a'', 0];
       l2 = [3, e1, e2, s ''a'', 0];
       l3 = [4, e1, e2, e3, s ''a'', 0];
       l4 = [6, e1, s ''a'', 0]
    in 
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := s ''b'',
        ''f'' := 0,
        ''g'' := 0,
        ''h'' := c,
        ''i'' := 0,
        ''j'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := 0,
        ''k'' := s ''a'',
        ''l'' := (cons_list l1) ## 0,
        ''m'' := (cons_list l2) ## t,
        ''n'' := (cons_list l3) ## t,
        ''cons'' := (cons_list l4) ## t,
        ''triangle'' := 0,
        ''prod_encode'' := 0))"
  apply(rule terminates_in_state_intro[OF Seq'[OF add_res_nat_first_part_correct]])
  unfolding add_res_nat_second_part_def add_res_nat_second_part_time_def Let_def
  by (fastforce intro: cons_IMP_Minus_correct cons_list_IMP_Minus_correct)+

(*"add_res_nat n s = ( d e
  if s = 0 then  (7##n##0) ## 0
else (
let h =hd_nat s; f
    t =tl_nat s; g
    c = hd_nat h; h 
    e1 = nth_nat (Suc 0) h ; i 
    e2 = nth_nat (Suc (Suc 0)) h; j 
    e3 = nth_nat (Suc (Suc (Suc 0))) h in nth_nat
if c = 2 then (3##e1##e2##n##0)##t else 
if c = 3 then (4##e1##e2##e3##n##0)##t else 
if c = 5 then (6##e1##n##0)##t else s   *)

definition add_res_nat_third_part where "add_res_nat_third_part \<equiv>
  IF ''e'' \<noteq>0
  THEN
  (
    ''a'' ::= ((V ''h'') \<ominus> (N 1)) ;;
    IF ''a'' \<noteq>0
    THEN
    (
      ''a'' ::= ((V ''h'') \<ominus> (N 3)) ;;
      IF ''a'' \<noteq>0
      THEN
      (
        ''a'' ::= ((V ''h'') \<ominus> (N 4)) ;;
        IF ''a'' \<noteq>0
        THEN
        (
           ''a'' ::= ((V ''h'') \<ominus> (N 5)) ;;
           IF ''a'' \<noteq>0
           THEN
           (
            ''add_res'' ::= (A (V ''e''))
           )
           ELSE
           (
            ''add_res'' ::= (A (V ''cons''))
           )
        )
        ELSE
        (
          ''add_res'' ::= (A (V ''e'')) ;;
          Com.SKIP ;; Com.SKIP ;; Com.SKIP
        )
      )
      ELSE
      (
         ''a'' ::= ((V ''h'') \<ominus> (N 2)) ;;
         IF ''a'' \<noteq>0
         THEN 
         (
          ''add_res'' ::= (A (V ''n'')) 
         )
         ELSE
         (
          ''add_res'' ::= (A (V ''m''))
         ) ;;
        Com.SKIP ;; Com.SKIP ;; Com.SKIP
      )
    )
    ELSE
    (
      ''add_res'' ::= (A (V ''e'')) ;;
      Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
      Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
      Com.SKIP ;; Com.SKIP ;; Com.SKIP
    )
  )
  ELSE
  (
    ''add_res'' ::= (A (V ''l'')) ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP
  );;
  ''a'' ::= (A (N 0)) ;;
  ''e'' ::= (A (N 0)) ;;
  ''h'' ::= (A (N 0)) ;;
  ''k'' ::= (A (N 0)) ;;
  ''l'' ::= (A (N 0)) ;;
  ''m'' ::= (A (N 0)) ;;
  ''n'' ::= (A (N 0)) ;;
  ''cons'' ::= (A (N 0))"

definition add_res_nat_IMP_Minus where "add_res_nat_IMP_Minus \<equiv>
  add_res_nat_first_part ;;
  add_res_nat_second_part ;;
  add_res_nat_third_part"

definition add_res_nat_IMP_Minus_time where "add_res_nat_IMP_Minus_time n s \<equiv>
  add_res_nat_first_part_time n s
  + add_res_nat_second_part_time n s
  + 31"

lemma add_res_nat_IMP_Minus_correct:
  "(add_res_nat_IMP_Minus, s)
   \<Rightarrow>\<^bsup>add_res_nat_IMP_Minus_time (s ''a'') (s ''b'') \<^esup>
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := 0,
        ''f'' := 0,
        ''g'' := 0,
        ''h'' := 0,
        ''i'' := 0,
        ''j'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := 0,
        ''k'' := 0,
        ''l'' := 0,
        ''m'' := 0,
        ''n'' := 0,
        ''cons'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''add_res'' := add_res_nat (s ''a'') (s ''b''))"
proof(cases "s ''b''")
  case 0
  show ?thesis
    unfolding add_res_nat_IMP_Minus_def add_res_nat_IMP_Minus_time_def
    apply(rule terminates_in_time_state_intro[OF Seq'
          [OF add_res_nat_second_part_correct]])
    unfolding add_res_nat_third_part_def Let_def
    using \<open>s ''b'' = 0\<close> 
    by(fastforce)+
next
  case (Suc nat)
  let ?c = "hd_nat (hd_nat (s ''b''))"
  have "?c = 0 \<or> ?c = 1 \<or> ?c = 2 \<or> ?c = 3 \<or> ?c = 4 \<or> ?c = 5 \<or> ?c > 5"
    by auto
  then show ?thesis
    apply(elim disjE)
    unfolding add_res_nat_IMP_Minus_def add_res_nat_IMP_Minus_time_def
    unfolding add_res_nat_third_part_def Let_def
    using \<open>s ''b'' = Suc nat\<close> 
    by (fastforce 
        intro!: terminates_in_time_state_intro[OF Seq'
          [OF add_res_nat_second_part_correct]]
        simp: Let_def)+
qed
end