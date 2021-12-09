\<^marker>\<open>creator Florian Kessler\<close>

theory IMP_Minus_Nat_Bijection
  imports Multiplication "HOL-Library.Nat_Bijection" 
    "../Cook_Levin/IMP-_To_SAS+/IMP-_To_IMP--/Primitives"
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax
unbundle Com.no_com_syntax

definition triangle_IMP_Minus where "triangle_IMP_Minus \<equiv>
  [''a''] ''a'' ::= (A (V ''a'')) ;;
  [''a''] ''b'' ::= ((V ''a'') \<oplus> (N 1)) ;;
  invoke_subprogram ''a'' mul_IMP_minus ;;
  ''triangle'' ::= [''a''] ((V ''c'') \<then>) ;;
  ''a'' ::= (A (N 0))"

thm add.commute
lemma comp_add:"(\<lambda>x::'a::ab_semigroup_add. f (x +c)) = f o ((+) c)"
  by (auto simp add: comp_def add.commute[symmetric])

lemma poly_const:"poly ((+) c)"
proof -
  have 1:"poly (\<lambda>x. x)"
    by (rule poly_linear)
  have 2:"poly (\<lambda>x. c)" by simp
  have "((+)c) = (\<lambda>x . x + c)"  by auto
  moreover from 1 2 have "poly (\<lambda>x. x + c) " by auto
  ultimately show ?thesis by auto
qed
find_theorems poly  "(o)" 

lemma poly_shift: "poly f \<Longrightarrow> poly (\<lambda>x. f(x + c))"
  by (subst comp_add) (auto intro: poly_const)

   
  

lemma "poly (f o g) \<Longrightarrow> poly ((\<lambda>x. f(x + c)) o g)"
  oops
definition triangle_IMP_Minus_time where "triangle_IMP_Minus_time x \<equiv>
  mul_IMP_Minus_time (1 + x) + 8"
lemma "poly (triangle_IMP_Minus_time o exp2)"
  unfolding triangle_IMP_Minus_time_def 
  oops
abbreviation triangle_IMP_Minus_state_transformer where 
  "triangle_IMP_Minus_state_transformer p n  \<equiv>
    state_transformer p [(''triangle'', triangle n), (''a'', 0)] \<circ> 
    mul_IMP_Minus_state_transformer (''a'' @ p) n (n + 1)"

lemma triangle_IMP_Minus_correct[intro]: 
   "(triangle_IMP_Minus p, s) 
      \<Rightarrow>\<^bsup>triangle_IMP_Minus_time (s (add_prefix p ''a''))\<^esup> 
      triangle_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) s"
  unfolding triangle_IMP_Minus_def triangle_def triangle_IMP_Minus_time_def
  by (fastforce intro!: terminates_in_time_state_intro[OF Seq])

definition prod_encode_IMP_Minus where "prod_encode_IMP_Minus \<equiv>
  [''a''] ''a'' ::= ((V ''a'') \<oplus> (V ''b'')) ;;
  invoke_subprogram ''a'' triangle_IMP_Minus ;;
  ''prod_encode'' ::= [''a''] (A (V ''triangle'')) ;;
  [''a''] ''triangle'' ::= (A (N 0)) ;;
  ''prod_encode'' ::= ((V ''a'') \<oplus> (V ''prod_encode'')) ;;
  zero_variables [''a'', ''b'']"

definition prod_encode_IMP_Minus_time where "prod_encode_IMP_Minus_time x y \<equiv>
  triangle_IMP_Minus_time (x + y) + 8 + zero_variables_time [''a'', ''b'']"

abbreviation prod_encode_IMP_Minus_state_transformer where 
  "prod_encode_IMP_Minus_state_transformer p x y \<equiv>
    state_transformer p [(''prod_encode'', prod_encode (x, y)), (''a'', 0), (''b'', 0)] \<circ>
    state_transformer (''a'' @ p) [(''triangle'', 0)] \<circ> 
    triangle_IMP_Minus_state_transformer (''a'' @ p) (x + y)"

lemma prod_encode_IMP_Minus_correct[intro]: 
  "(prod_encode_IMP_Minus p, s) 
      \<Rightarrow>\<^bsup>prod_encode_IMP_Minus_time (s (add_prefix p ''a'')) (s (add_prefix p ''b''))\<^esup> 
      prod_encode_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) (s (add_prefix p ''b'')) s"
  unfolding prod_encode_IMP_Minus_def prod_encode_def prod_encode_IMP_Minus_time_def
  by(fastforce intro!: terminates_in_time_state_intro[OF Seq])

fun prod_decode_aux_iterations :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "prod_decode_aux_iterations k m =
    (if m \<le> k then 0 else Suc (prod_decode_aux_iterations (Suc k) (m - Suc k)))"

declare prod_decode_aux_iterations.simps [simp del]

definition prod_decode_aux_iteration where "prod_decode_aux_iteration \<equiv>
  ''a'' ::= ((V ''a'') \<oplus> (N 1)) ;;
  ''b'' ::= ((V ''b'') \<ominus> (V ''a'')) ;;
  ''c'' ::= ((V ''b'') \<ominus> (V ''a''))"

abbreviation prod_decode_aux_loop_state_transformer 
  where "prod_decode_aux_loop_state_transformer p x y \<equiv>
    state_transformer p [(''a'', fst (prod_decode_aux x y)
                               + snd (prod_decode_aux x y)),
                         (''b'', fst (prod_decode_aux x y)),
                         (''c'', 0)]"

lemma prod_decode_aux_loop_correct: 
  "s (add_prefix p ''a'') = k \<Longrightarrow> s (add_prefix p ''b'') = m \<Longrightarrow> s (add_prefix p ''c'') = m - k 
  \<Longrightarrow> ((WHILE ''c'' \<noteq>0 DO prod_decode_aux_iteration) p, s) 
      \<Rightarrow>\<^bsup>2 + 7 * prod_decode_aux_iterations k m\<^esup> 
      (if m - k \<noteq> 0 then prod_decode_aux_loop_state_transformer p k m s else s)"
proof(induction k m arbitrary: s rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case
  proof(cases "m - k")
    case 0
    then show ?thesis
      using 1 terminates_in_state_intro[OF Big_StepT.WhileFalse]
      by(auto simp:  prod_decode_aux.simps numeral_eq_Suc 
          prod_decode_aux_iterations.simps)
  next
    case (Suc nat)

    show ?thesis
      apply(rule terminates_in_time_state_intro[OF Big_StepT.WhileTrue[OF _ _ "1.IH"]])
      unfolding prod_decode_aux_iteration_def
      using \<open>s (add_prefix p ''a'') = k\<close>  \<open>s (add_prefix p ''b'') = m\<close>  
        \<open>s (add_prefix p ''c'') = m - k\<close> \<open>m - k = Suc nat\<close>
        prod_decode_aux_iterations.simps[where ?k = k]
        prod_decode_aux.simps[where ?k = k]
        prod_decode_aux.simps[where ?k = "(Suc (s (add_prefix p ''a'')))"]
      by fastforce+
  qed
qed

definition fst_nat_IMP_Minus where "fst_nat_IMP_Minus \<equiv>
  ''b'' ::= (A (V ''a'')) ;; 
  ''a'' ::= (A (N 0)) ;;
  ''c'' ::= ((V ''b'') \<ominus> (V ''a'')) ;;
  WHILE ''c'' \<noteq>0 DO prod_decode_aux_iteration ;;
  ''fst_nat'' ::= (A (V ''b'')) ;;
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (N 0))"

definition fst_nat_IMP_Minus_time where "fst_nat_IMP_Minus_time x \<equiv>
  14 + 7 * prod_decode_aux_iterations 0 x"

abbreviation fst_nat_IMP_Minus_state_transformer where "fst_nat_IMP_Minus_state_transformer p x
  \<equiv> state_transformer p [(''a'', 0),
                          (''b'', 0),
                          (''c'', 0),
                          (''fst_nat'', fst_nat x)]"

lemma fst_nat_IMP_Minus_correct[intro]: 
  "(fst_nat_IMP_Minus p, s) 
      \<Rightarrow>\<^bsup>fst_nat_IMP_Minus_time (s (add_prefix p ''a''))\<^esup> 
    fst_nat_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) s"
  unfolding fst_nat_IMP_Minus_def fst_nat_def fst_nat_IMP_Minus_time_def
  by (fastforce simp: prod_decode_def prod_decode_aux.simps[of 0 0] 
      intro!: prod_decode_aux_loop_correct
      terminates_in_time_state_intro[OF Seq'])

definition hd_IMP where "hd_IMP \<equiv>
  [''fst''] ''a'' ::=  (V ''xs'' \<ominus> N 1) ;;
  invoke_subprogram ''fst'' fst_nat_IMP_Minus ;;
  ''ans'' ::= [''fst''] A (V ''fst_nat'');;
  ''xs'' ::= A (N 0)
"


abbreviation hd_state_transformer where 
"hd_state_transformer p xs \<equiv> 
state_transformer p [(''ans'',hd_nat xs) , (''xs'',0)] o
fst_nat_IMP_Minus_state_transformer (''fst''@ p) (xs -1)
"

definition hd_time where "
hd_time x \<equiv> fst_nat_IMP_Minus_time (x-1) + 6 "

lemma hd_nat_IMP_Minus_correct[intro]: 
  "(hd_IMP p, s) 
      \<Rightarrow>\<^bsup>  hd_time (s (add_prefix p ''xs''))\<^esup> 
   hd_state_transformer p (s (add_prefix p ''xs'')) s"
  unfolding hd_IMP_def hd_time_def  hd_nat_def
  apply (rule terminates_in_time_state_intro)
    apply (rule Big_StepT.Seq)+
  by fastforce+
  
  
  
fun f::"real\<Rightarrow>real" where "f x = x^3  -4x^2 + x+3"

value "f (-2)"
value "f (4)"
value "f ((-2* f(4) + 4*f(-2))/ (f(4)-f(-2)))"

definition snd_nat_IMP_Minus where "snd_nat_IMP_Minus \<equiv>
  ''b'' ::= (A (V ''a'')) ;; 
  ''a'' ::= (A (N 0)) ;;
  ''c'' ::= ((V ''b'') \<ominus> (V ''a'')) ;;
  WHILE ''c'' \<noteq>0 DO prod_decode_aux_iteration ;;
  ''snd_nat'' ::= ((V ''a'') \<ominus> (V ''b'')) ;;
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (N 0))"

definition snd_nat_IMP_Minus_time where "snd_nat_IMP_Minus_time x \<equiv>
  14 + 7 * prod_decode_aux_iterations 0 x"

abbreviation snd_nat_IMP_Minus_state_transformer where "snd_nat_IMP_Minus_state_transformer p x
  \<equiv> state_transformer p [(''a'', 0),
                          (''b'', 0),
                          (''c'', 0),
                          (''snd_nat'', snd_nat x)]"

lemma snd_nat_IMP_Minus_correct[intro]: 
  "(snd_nat_IMP_Minus p, s) 
      \<Rightarrow>\<^bsup>snd_nat_IMP_Minus_time (s (add_prefix p ''a''))\<^esup> 
    snd_nat_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) s"
  unfolding snd_nat_IMP_Minus_def snd_nat_def snd_nat_IMP_Minus_time_def
  by (fastforce simp: prod_decode_def prod_decode_aux.simps[of 0 0] 
      intro!: prod_decode_aux_loop_correct
      terminates_in_time_state_intro[OF Seq'])

definition tl_IMP where "tl_IMP \<equiv>
  [''snd''] ''a'' ::=  (V ''xs'' \<ominus> N 1) ;;
  invoke_subprogram ''snd'' snd_nat_IMP_Minus ;;
  ''ans'' ::= [''snd''] A (V ''snd_nat'');;
  [''snd''] ''snd_nat'' ::= A (N 0);;
  ''xs'' ::= A (N 0)
"


abbreviation tl_state_transformer where 
"tl_state_transformer p xs \<equiv> 
state_transformer p [(''ans'',tl_nat xs) , (''xs'',0)] o
state_transformer (''snd'' @ p) [(''snd_nat'',0)] o
snd_nat_IMP_Minus_state_transformer (''snd''@ p) (xs -1)
"

definition tl_time where "
tl_time x \<equiv> snd_nat_IMP_Minus_time (x-1) + 8 "

lemma tl_nat_IMP_Minus_correct[intro]: 
  "(tl_IMP p, s) 
      \<Rightarrow>\<^bsup>  tl_time (s (add_prefix p ''xs''))\<^esup> 
   tl_state_transformer p (s (add_prefix p ''xs'')) s"
  unfolding tl_IMP_def tl_time_def  tl_nat_def 
  apply (rule terminates_in_time_state_intro)
    apply (rule Big_StepT.Seq)+
  by fastforce+

definition nth_nat_iteration where "nth_nat_iteration \<equiv>
  [''a''] ''a'' ::= ((V ''a'') \<ominus> (N 1)) ;;
  invoke_subprogram ''a'' snd_nat_IMP_Minus ;;
  ''a'' ::= [''a''] (A (V ''snd_nat'')) ;;
  [''a''] ''snd_nat'' ::= (A (N 0)) ;;
  ''nth_nat'' ::= ((V ''nth_nat'') \<ominus> (N 1))"

fun nth_nat_loop_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_nat_loop_time 0 x = 2" |
"nth_nat_loop_time (Suc n) x = 9 + snd_nat_IMP_Minus_time (x - 1) 
  + nth_nat_loop_time n (tl_nat x)"

fun drop_n_nat :: "nat \<Rightarrow> nat\<Rightarrow> nat" where 
"drop_n_nat 0 x = x "|
"drop_n_nat (Suc n) x = drop_n_nat n (tl_nat x)"

lemma nth_nat_is_hd_of_drop_n_nat:
  "nth_nat n x = fst_nat (drop_n_nat n x - Suc 0)"
  by (induction n arbitrary: x)
    (auto simp: hd_nat_def)

abbreviation nth_nat_loop_state_transformer where "nth_nat_loop_state_transformer p k x \<equiv>
  (if k = 0 then (\<lambda>s. s)
   else 
        state_transformer p [
        (''a'', drop_n_nat k x),
        (''nth_nat'',  0)]
        \<circ> state_transformer (''a'' @ p) [
          (''snd_nat'', 0)]
        \<circ> snd_nat_IMP_Minus_state_transformer (''a'' @ p) 0)"

lemma nth_nat_loop_correct:
  "s (add_prefix p ''nth_nat'') = k
  \<Longrightarrow> ((WHILE ''nth_nat'' \<noteq>0 DO nth_nat_iteration) p, s) 
      \<Rightarrow>\<^bsup>nth_nat_loop_time k (s (add_prefix p ''a''))\<^esup>
      nth_nat_loop_state_transformer p k (s (add_prefix p ''a'')) s "
proof(induction k arbitrary: s)
  case 0
  then show ?case
    by(auto simp: numeral_eq_Suc fun_eq_iff 
        intro!: terminates_in_state_intro[OF Big_StepT.WhileFalse])
next
  case (Suc k)
  show ?case
    apply(rule terminates_in_time_state_intro[OF Big_StepT.WhileTrue[OF _ _ Suc.IH]])
    using \<open>s (add_prefix p ''nth_nat'') = Suc k\<close>
    unfolding nth_nat_iteration_def
    by (fastforce simp: tl_nat_def)+
qed


definition nth_nat_IMP_Minus where "nth_nat_IMP_Minus \<equiv>
  ''nth_nat'' ::= (A (V ''a'')) ;;
  ''a'' ::= (A (V ''b'')) ;;
  WHILE ''nth_nat'' \<noteq>0 DO nth_nat_iteration ;;
  [''b''] ''a'' ::= ((V ''a'') \<ominus> (N 1)) ;;
  invoke_subprogram ''b'' fst_nat_IMP_Minus ;;
  ''nth_nat'' ::= [''b''] (A (V ''fst_nat'')) ;;
  [''b''] ''fst_nat'' ::= (A (N 0)) ;;
  zero_variables [''a'', ''b'']"

definition nth_nat_IMP_Minus_time where "nth_nat_IMP_Minus_time n x \<equiv>
  10 + nth_nat_loop_time n x + fst_nat_IMP_Minus_time ((drop_n_nat n x) - 1)
  + zero_variables_time [''a'', ''b'']"

abbreviation nth_nat_IMP_Minus_state_transformer where "nth_nat_IMP_Minus_state_transformer p k x
  \<equiv> state_transformer p [(''nth_nat'', nth_nat k x), (''a'', 0), (''b'', 0)]
     \<circ> state_transformer (''b'' @ p) [(''fst_nat'', 0)]
     \<circ> fst_nat_IMP_Minus_state_transformer (''b'' @ p) 0
     \<circ> nth_nat_loop_state_transformer p k x"

lemma nth_nat_IMP_Minus_correct:
  "(nth_nat_IMP_Minus p, s) 
    \<Rightarrow>\<^bsup>nth_nat_IMP_Minus_time (s (add_prefix p ''a'')) (s (add_prefix p ''b''))\<^esup>
    nth_nat_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) (s (add_prefix p ''b'')) s"
  unfolding nth_nat_IMP_Minus_def nth_nat_IMP_Minus_time_def tl_nat_def 
  by (cases "s (add_prefix p ''a'') = 0") (fastforce 
      simp: hd_nat_def nth_nat_is_hd_of_drop_n_nat
      intro!: terminates_in_time_state_intro[OF Seq']
      intro: nth_nat_loop_correct)+

definition cons_IMP_Minus
  where "cons_IMP_Minus \<equiv> 
    [''a''] ''a'' ::= (A (V ''a'')) ;;
    [''a''] ''b'' ::= (A (V ''b'')) ;;
    invoke_subprogram ''a'' prod_encode_IMP_Minus ;;
    ''cons'' ::= [''a''] ((V ''prod_encode'') \<oplus> (N 1)) ;;
    [''a''] ''prod_encode'' ::= (A (N 0)) ;;
    zero_variables [''a'', ''b'']"

definition cons_IMP_Minus_time where "cons_IMP_Minus_time h t \<equiv>
  8 + prod_encode_IMP_Minus_time h t + zero_variables_time [''a'', ''b'']"

abbreviation cons_IMP_Minus_state_transformer where "cons_IMP_Minus_state_transformer p h t
  \<equiv> state_transformer p [(''cons'', h ## t), (''a'', 0), (''b'', 0)]
    \<circ> state_transformer (''a'' @ p) [(''prod_encode'', 0)]
    \<circ> prod_encode_IMP_Minus_state_transformer (''a'' @ p) h t"

lemma cons_IMP_Minus_correct[intro]:
  "(cons_IMP_Minus p, s) 
    \<Rightarrow>\<^bsup>cons_IMP_Minus_time (s (add_prefix p ''a'')) (s (add_prefix p ''b''))\<^esup>
     cons_IMP_Minus_state_transformer p (s (add_prefix p ''a'')) (s (add_prefix p ''b'')) s"
  unfolding cons_IMP_Minus_def cons_IMP_Minus_time_def cons_def
  by (fastforce intro!: terminates_in_time_state_intro[OF Seq'])

fun cons_list_IMP_Minus :: "vname list \<Rightarrow> pcom" where
"cons_list_IMP_Minus [] = SKIP" |
"cons_list_IMP_Minus (a # as) = (if as = [] 
  then 
    ''cons_list'' ::= [''a''] (A (V a)) ;;
    [''a''] a ::= (A (N 0))
  else
    cons_list_IMP_Minus as ;;
    [''b''] ''a'' ::= [''a''] (A (V a)) ;; 
    [''b''] ''b'' ::= (A (V ''cons_list'')) ;;
    invoke_subprogram ''b'' cons_IMP_Minus ;;
    ''cons_list'' ::= [''b''] (A (V ''cons'')) ;;
    [''b''] ''cons'' ::= (A (N 0)) ;;
    [''a''] a ::= (A (N 0)))" (* TODO: don't zero here: will break if variable names not distinct*)

fun cons_list :: "nat list \<Rightarrow> nat" where
"cons_list [] = 0" |
"cons_list (a # as) = 
  (if as = [] 
   then a
   else a ## cons_list as)"

fun cons_list_IMP_Minus_time :: "nat list \<Rightarrow> nat" where
"cons_list_IMP_Minus_time [] = 1" | 
"cons_list_IMP_Minus_time (a # as) = 
  (if as = []
   then 4
   else cons_list_IMP_Minus_time as + 2 + 2 + cons_IMP_Minus_time a (cons_list as) + 2 + 2 + 2)"

fun cons_list_IMP_Minus_state_transformer where 
  "cons_list_IMP_Minus_state_transformer p [] vs = (\<lambda>s. s)" |
  "cons_list_IMP_Minus_state_transformer p (a # as) (v#vs) = (if as = [] then
    state_transformer (''a'' @ p) [(v, 0)]
  \<circ> state_transformer p [(''cons_list'', a)]
    else
  (\<lambda> s0 .
      let s1 = cons_list_IMP_Minus_state_transformer p as vs s0;
          s2 = state_transformer (''b'' @ p) [(''a'', s1 (add_prefix (''a'' @ p) v))] s1;
          s3 = state_transformer (''b'' @ p) [(''b'', s2 (add_prefix p ''cons_list''))] s2;
          s4 = cons_IMP_Minus_state_transformer (''b'' @ p) (s3 (add_prefix (''b'' @ p) ''a'')) (s3 (add_prefix (''b'' @ p) ''b'')) s3;
          s5 = state_transformer p [(''cons_list'', s4 (add_prefix (''b'' @ p) ''cons''))] s4;
          s6 = state_transformer (''b'' @ p) [(''cons'', 0)] s5;
          s7 = state_transformer (''a'' @ p) [(v, 0)] s6
  in s7 )
  )
"

lemma auxxx: "(let s1 = t1; s2 = t2 s1; s3 = t3 s2; s4 = t4 s3;
                s5 = t5 s4; s6 = t6 s5; s7 = t7 s6 in s7) a
 =
(let s1 = t1; s2 = t2 s1; s3 = t3 s2; s4 = t4 s3;
                s5 = t5 s4; s6 = t6 s5; s7 = t7 s6 in s7 a)" by simp

lemma cons_list_state_arv:
  assumes arg_def: "ar = add_prefix (''a'' @ p)"
  assumes dist: "distinct (v#vs)"
  shows "cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (ar i)) vs) vs s (ar v) = s (ar v)"
  using dist
proof(induct vs)
  case (Cons b' bs')
  then have "v \<noteq> b'" by simp
  then show ?case
    using Cons
      auxxx[of "cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (ar i)) bs') bs' s"
        "\<lambda> s1. state_transformer (''b'' @ p) [(''a'', s1 (add_prefix (''a'' @ p) b'))] s1"
        "\<lambda> s2. state_transformer (''b'' @ p) [(''b'', s2 (add_prefix p ''cons_list''))] s2"
        "\<lambda> s3. cons_IMP_Minus_state_transformer (''b'' @ p) (s3 (add_prefix (''b'' @ p) ''a'')) (s3 (add_prefix (''b'' @ p) ''b'')) s3"
        "\<lambda> s4. state_transformer p [(''cons_list'', s4 (add_prefix (''b'' @ p) ''cons''))] s4"
        "state_transformer (''b'' @ p) [(''cons'', 0)]" "state_transformer (''a'' @ p) [(b', 0)]" ] 
    by (auto simp: arg_def)
qed simp

lemma cons_list_IMP_Minus_correct[intro]:
  assumes "distinct vs"
  shows
    "(cons_list_IMP_Minus vs p, s) 
      \<Rightarrow>\<^bsup>cons_list_IMP_Minus_time (map (\<lambda>i. s (add_prefix (''a'' @ p) i)) vs)\<^esup>
      cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (add_prefix (''a'' @ p) i)) vs) vs s"
  using assms
proof(induction vs arbitrary: s)
  case ConsV: (Cons v vs)
  show ?case
  proof (cases vs)
    case Nil
    then show ?thesis
      by(auto intro!: terminates_in_time_state_intro[OF Seq'])
  next
    case ConsB: (Cons b bs)
    define arg where "arg \<equiv> add_prefix (''a'' @ p)"

    define s1 where "s1 =
      cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (arg i)) vs) vs s"
    define s2 where "s2 =
      s1(add_prefix (''b'' @ p) ''a'' := aval (aexp_add_prefix (''a'' @ p) (A (V v))) s1)"
    define s3 where "s3 =
      s2(add_prefix (''b'' @ p) ''b'' := aval (aexp_add_prefix p (A (V ''cons_list''))) s2)"

    have d: "distinct vs" using ConsV by simp

    have "cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (arg i)) vs) vs s (arg v) = s (arg v)"
      using cons_list_state_arv arg_def ConsV(2) by simp

    then have c1: "(s3 (add_prefix (''b'' @ p) ''a'')) = (s (arg v))"
      by (auto simp: s3_def s2_def s1_def arg_def)

    have c2a: "(s3 (add_prefix (''b'' @ p) ''b''))
       = cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (arg i)) vs) vs
          s (add_prefix p ''cons_list'')"
      using s1_def s2_def s3_def by simp

    have c2b: "(vs = [] \<Longrightarrow> s (add_prefix p ''cons_list'') = 0) \<Longrightarrow>
      cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (arg i)) vs) vs
          s (add_prefix p ''cons_list'') =
 (cons_list (map (\<lambda>i. s (arg i)) vs))"
      using ConsV(2)
    proof(induct vs rule: cons_list_IMP_Minus.induct)
      case (2 b' bs')
      then show ?case
      proof(cases bs')
        case (Cons c cs)
        then have ih: "cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (arg i)) bs') bs' s (add_prefix p ''cons_list'') = cons_list (map (\<lambda>i. s (arg i)) bs')"
          using 2 by simp
        have d: "distinct (b' # bs')" using 2(3) by simp
        show ?thesis
          using cons_list_state_arv[of arg, OF _ d]
            auxxx[of "cons_list_IMP_Minus_state_transformer p (map (\<lambda>i. s (arg i)) bs') bs' s"
              "\<lambda> s1. state_transformer (''b'' @ p) [(''a'', s1 (add_prefix (''a'' @ p) b'))] s1"
              "\<lambda> s2. state_transformer (''b'' @ p) [(''b'', s2 (add_prefix p ''cons_list''))] s2"
              "\<lambda> s3. cons_IMP_Minus_state_transformer (''b'' @ p) (s3 (add_prefix (''b'' @ p) ''a'')) (s3 (add_prefix (''b'' @ p) ''b'')) s3"
              "\<lambda> s4. state_transformer p [(''cons_list'', s4 (add_prefix (''b'' @ p) ''cons''))] s4"
              "state_transformer (''b'' @ p) [(''cons'', 0)]" "state_transformer (''a'' @ p) [(b', 0)]"] 
            Cons ih arg_def  by simp
      qed simp
    qed simp

    have c2: "(s3 (add_prefix (''b'' @ p) ''b'')) = (cons_list (map (\<lambda>i. s (arg i)) vs))"
      using c2a c2b ConsB by auto

    show ?thesis
      apply(subst arg_def[symmetric])+

      apply(subst cons_list_IMP_Minus.simps(2))
      apply(subst ConsB)
      apply(subst List.list.simps(3))
      apply(subst HOL.if_False)
      apply(subst List.list.map(2))
      apply(subst cons_list_IMP_Minus_time.simps(2))
      apply(subst ConsB)
      apply(subst ConsB)
      apply(subst ConsB[symmetric])
      apply(subst List.list.map(2))
      apply(subst List.list.simps(3))
      apply(subst HOL.if_False)
      apply(rule Seq')+
            apply(subst arg_def)
            apply(rule ConsV)
            apply(simp add: d)

           apply(subst arg_def[symmetric])
           apply(subst s1_def[symmetric])

           apply(rule terminates_in_time_state_intro[OF Big_StepT.Assign])
            apply simp  apply(rule refl)
          apply(subst s2_def[symmetric])
          apply(rule terminates_in_time_state_intro[OF Big_StepT.Assign])
           apply simp apply (rule refl)
         apply(subst s3_def[symmetric])
         apply(rule terminates_in_time_state_intro[OF cons_IMP_Minus_correct])
          apply(subst c1) apply(subst c2)

          apply(fastforce intro!: terminates_in_time_state_intro[OF Big_StepT.Assign]
          simp add: ConsB Let_def
          s3_def s2_def s1_def)+
      done
  qed
qed simp



definition reverse_nat_acc_IMP_Minus_iteration where "reverse_nat_acc_IMP_Minus_iteration \<equiv>
  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  
  cons_IMP_Minus (V ''fst_nat'') (V ''e'') ;;

  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  
  ''e'' ::= (A (V ''cons'')) ;;
  ''f'' ::= (A (V ''snd_nat'')) ;;

  zero_variables [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'']"

definition reverse_nat_acc_IMP_Minus_iteration_time where 
  "reverse_nat_acc_IMP_Minus_iteration_time acc n \<equiv>
    8 + IMP_Minus_fst_nat_time (n - 1) + cons_IMP_Minus_time (hd_nat n) acc
    + IMP_Minus_fst_nat_time (n - 1)
    + zero_variables_time [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'']"

(*"reverse_nat_acc acc e  n f =
  (if n = 0 then acc 
   else reverse_nat_acc ((hd_nat n) ## acc) (tl_nat n) )"*)

lemma reverse_nat_acc_IMP_Minus_iteration_correct: 
  "(reverse_nat_acc_IMP_Minus_iteration, s) 
    \<Rightarrow>\<^bsup>reverse_nat_acc_IMP_Minus_iteration_time (s ''e'') (s ''f'')\<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''d'' := 0,
      ''e'' := ((hd_nat (s ''f'')) ## (s ''e'')),
      ''f'' := (tl_nat (s ''f'')),
      ''triangle'' := 0,
      ''prod_encode'' := 0,
      ''cons'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0)"
  unfolding reverse_nat_acc_IMP_Minus_iteration_def 
    reverse_nat_acc_IMP_Minus_iteration_time_def
  by(fastforce 
       simp: hd_nat_def tl_nat_def 
       intro!: terminates_in_time_state_intro[OF Seq']
       intro: IMP_Minus_fst_nat_correct IMP_Minus_snd_nat_correct zero_variables_correct
       cons_IMP_Minus_correct)

(* WHILE ''f'' \<noteq>0 DO reverse_nat_acc_IMP_Minus_loop_iteration *)

fun reverse_nat_acc_IMP_Minus_loop_time where 
"reverse_nat_acc_IMP_Minus_loop_time acc n = 
  (if n = 0 then 2 
   else 1 + reverse_nat_acc_IMP_Minus_iteration_time acc n + 
    reverse_nat_acc_IMP_Minus_loop_time ((hd_nat n) ## acc) (tl_nat n))"

lemma reverse_nat_acc_IMP_Minus_loop_correct[intro]: 
  "(WHILE ''f'' \<noteq>0 DO reverse_nat_acc_IMP_Minus_iteration, s) 
    \<Rightarrow>\<^bsup>reverse_nat_acc_IMP_Minus_loop_time (s ''e'') (s ''f'')\<^esup>
    (if s ''f'' \<noteq> 0 then
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := reverse_nat_acc (s ''e'') (s ''f''),
        ''f'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''cons'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0)
      else s)"
proof(induction "s ''e''" "s ''f''" arbitrary: s rule: reverse_nat_acc.induct)
  case 1
  then show ?case
  proof(cases "s ''f''")
    case 0
    then show ?thesis
      by (fastforce intro: terminates_in_time_state_intro[OF Big_StepT.WhileFalse])
  next
    case (Suc nat)
        
    then show ?thesis
      by(fastforce intro!: terminates_in_time_state_intro[OF
        Big_StepT.WhileTrue[OF _ reverse_nat_acc_IMP_Minus_iteration_correct 1(1)]])
  qed
qed

definition "reverse_nat_acc_IMP_Minus" where "reverse_nat_acc_IMP_Minus \<equiv>
  ''e'' ::= (A (V ''a'')) ;;
  ''f'' ::= (A (V ''b'')) ;;
  WHILE ''f'' \<noteq>0 DO reverse_nat_acc_IMP_Minus_iteration ;;
  ''reverse_nat_acc'' ::= (A (V ''e'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'', ''e'',
    ''triangle'', ''prod_encode'']"

definition reverse_nat_acc_IMP_Minus_time where "reverse_nat_acc_IMP_Minus_time acc n \<equiv>
  6 + reverse_nat_acc_IMP_Minus_loop_time acc n
  + zero_variables_time 
    [''a'', ''b'', ''c'', ''d'', ''fst_nat'', ''snd_nat'', ''cons'', ''e'',
      ''triangle'', ''prod_encode'']"

lemma reverse_nat_acc_IMP_Minus_correct:
  "(reverse_nat_acc_IMP_Minus, s) 
    \<Rightarrow>\<^bsup>reverse_nat_acc_IMP_Minus_time (s ''a'') (s ''b'')\<^esup>
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := 0,
        ''f'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''cons'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''reverse_nat_acc'' := reverse_nat_acc (s ''a'') (s ''b''))"
  unfolding reverse_nat_acc_IMP_Minus_def reverse_nat_acc_IMP_Minus_time_def
  apply(cases "s ''b''") 
  by(fastforce 
      intro!: HOL.ext terminates_in_time_state_intro[OF Seq'] 
      zero_variables_correct reverse_nat_acc_IMP_Minus_loop_correct
      intro:  reverse_nat_acc_IMP_Minus_loop_correct)+
  
end