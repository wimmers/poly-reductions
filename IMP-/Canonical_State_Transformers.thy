theory Canonical_State_Transformers
  imports Com
begin

definition add_prefix :: "string \<Rightarrow> vname \<Rightarrow> vname" where
"add_prefix p s = (concat (map (\<lambda>i. i # ''!'') p)) @ ''**'' @ s"

lemma length_concat_map[simp]: 
  "length (concat (map (\<lambda>i. [i, x]) p)) = 2 * length p" 
  by (induction p) auto

lemma take_concat_map[simp]:
  "take (2 * x) (concat (map (\<lambda>i. [i, y]) p)) = (concat (map (\<lambda>i. [i, y]) (take x p)))"
proof (induction x arbitrary: p)
  case (Suc x)
  then show ?case
    by (cases p) auto
qed auto

lemma drop_concat_map[simp]:
  "drop (2 * x) (concat (map (\<lambda>i. [i, y]) p)) = (concat (map (\<lambda>i. [i, y]) (drop x p)))"
proof (induction x arbitrary: p)
  case (Suc x)
  then show ?case
    by (cases p) auto
qed auto

lemma drop_add_prefix[simp]:
  "drop (2 + 2 * length p) (add_prefix p x) = x"
  unfolding add_prefix_def
  by auto

declare drop_add_prefix[simplified, simp]

lemma concat_map_eq_iff[simp]:
  "(concat (map (\<lambda>i. [i, y]) p) = concat (map (\<lambda>i. [i, y]) p'))
    \<longleftrightarrow> p = p'"
proof(induction p arbitrary: p')
  case (Cons a p)
  then show ?case
    by (cases p') auto
qed auto

lemma add_prefix_equal_then_prefix_equal: 
  assumes "add_prefix p v = add_prefix p' v'"
  shows "p = p'"
proof -
  have "length p < length p' \<or> length p = length p' \<or> length p > length p'"
    by auto
  thus ?thesis
  proof(elim disjE)
    assume "length p < length p'"

    then obtain p'' p''' x where "drop (length p) p' = p''" "p'' = x # p'''"
      by (metis Cons_nth_drop_Suc)

    thus ?thesis
      using assms \<open>length p < length p'\<close> 
      unfolding add_prefix_def 
      by(auto simp: append_eq_append_conv_if)
  next
    assume "length p = length p'"
    thus ?thesis
      using assms  
      unfolding add_prefix_def 
      by(auto simp: append_eq_append_conv_if)
  next 
    assume "length p > length p'"

    then obtain p'' p''' x where "drop (length p') p = p''" "p'' = x # p'''"
      by (metis Cons_nth_drop_Suc)

    thus ?thesis
      using assms \<open>length p > length p'\<close> 
      unfolding add_prefix_def 
      by(auto simp: append_eq_append_conv_if)
  qed
qed

lemma add_prefix_same_prefix_eq_iff[simp]: "add_prefix p x = add_prefix p y
  \<longleftrightarrow> x = y"
proof
  assume "add_prefix p x = add_prefix p y"
  hence "drop (2 * length p + 2) (add_prefix p x) = drop (2 * length p + 2) (add_prefix p y)"
    by auto
  thus "x = y" 
    unfolding add_prefix_def
    by simp
qed auto

lemma add_prefix_inj: "inj (add_prefix p)"
  by (auto intro: injI)

lemma add_prefix_equal_iff[simp]: "add_prefix p a = add_prefix p' b \<longleftrightarrow>
  p = p' \<and> a = b"
  using add_prefix_equal_then_prefix_equal add_prefix_same_prefix_eq_iff
  by blast

definition state_transformer :: "string \<Rightarrow> (vname * nat) list \<Rightarrow> state \<Rightarrow> state" where
  "state_transformer p vs s = 
    (\<lambda>v. (case 
           (map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs)) v of
             (Some y) \<Rightarrow> y
             | None \<Rightarrow> s v))"

(* Only use for intermediate states. State transformer definitions of sub-programs
   should not depend on the state before the program invocation, because we do not
   want to compute that when composing state transformers *)

abbreviation state_transformer' where "state_transformer' p vs s \<equiv>
  state_transformer p (vs (\<lambda>v. s (add_prefix p v))) s"

lemma state_transformer_no_update[simp]:
  "state_transformer p [] s = s"
  unfolding state_transformer_def
  by auto

lemma state_transformer_commutes:
  assumes "p \<noteq> p'"
  shows "state_transformer p vs \<circ> state_transformer p' vs' 
          = state_transformer p' vs' \<circ> state_transformer p vs"
  unfolding state_transformer_def comp_def
  using \<open>p \<noteq> p'\<close>
  by(fastforce 
      dest: map_of_SomeD add_prefix_equal_then_prefix_equal
      split: option.splits)

lemma state_transformer_commutes':
  assumes "p \<noteq> p'"
  shows "state_transformer p vs (state_transformer p' vs' s)  
          = state_transformer p' vs' (state_transformer p vs s)"
  using state_transformer_commutes[OF \<open>p \<noteq> p'\<close>]
  by (metis comp_eq_dest)

lemma state_transformer_comp_same_prefix[simp]: 
  "state_transformer p vs (state_transformer p vs' s)
    = state_transformer p (vs @ vs') s"
  unfolding state_transformer_def
  by(fastforce split: option.splits)

lemma state_transformer_commutes_comp[simp]:
  assumes "p \<noteq> p'" 
  shows "state_transformer p vs (state_transformer p' vs' (state_transformer p vs'' s))
    = state_transformer p (vs @ vs'') (state_transformer p' vs' s)"
  using state_transformer_commutes'[OF \<open>p \<noteq> p'\<close>]
  by simp

lemma map_of_eq_then_map_of_map_of_add_prefix_eq:
  assumes "map_of vs = map_of vs'" 
  shows "map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs) 
          = map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs')"
proof -
  have "map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs) x
          = map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs') x" for x
  proof(cases "\<exists>x'. x = add_prefix p x'")
    case True
    then obtain x' where "x = add_prefix p x'"
      by auto
    then show ?thesis
    proof (cases "(map_of vs) x'")
      case None
      thus ?thesis
        using  \<open>map_of vs = map_of vs'\<close>
      proof(cases "(map_of vs') x'")
        case None
        hence "map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs) x = None"
          "map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs') x = None"
          using \<open>map_of vs x' = None\<close> \<open>map_of vs' x' = None\<close>
            \<open>x = add_prefix p x'\<close>
          by(force simp add: map_of_eq_None_iff)+
        then show ?thesis 
          by simp
      qed auto
    next
      case (Some y)
      thus ?thesis
        using \<open>map_of vs = map_of vs'\<close>
      proof (cases "(map_of vs') x'")
        case (Some y')
        thus ?thesis
          using
            map_of_mapk_SomeI[OF add_prefix_inj]  \<open>map_of vs x' = Some y\<close>
            \<open>map_of vs' x' = Some y'\<close>  \<open>x = add_prefix p x'\<close>
            \<open>map_of vs = map_of vs'\<close> \<open>map_of vs x' = Some y\<close>
          by metis
      qed auto
    qed
  next
    case False
    hence "map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs) x = None"
      "map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs') x = None"
      by(force simp add: map_of_eq_None_iff)+
    then show ?thesis
      by simp
  qed
  thus ?thesis 
    by auto
qed

lemma state_transformer_same_prefix_equal_intro[intro]:
  assumes "map_of vs = map_of vs'"
  shows  "state_transformer p vs = state_transformer p vs'"
  unfolding state_transformer_def
  using map_of_eq_then_map_of_map_of_add_prefix_eq[OF \<open>map_of vs = map_of vs'\<close>]
  by(auto intro!: HOL.ext  split: option.splits)

lemma state_transformer_same_prefix_equal_commutes[simp]:
  assumes "p \<noteq> p'"
  shows "state_transformer p vs (state_transformer p' vs' s) = 
    state_transformer p' vs'' (state_transformer p vs''' s')
    \<longleftrightarrow> 
      state_transformer p vs (state_transformer p' vs' s) = 
      state_transformer p vs''' (state_transformer p' vs'' s')"
  using state_transformer_commutes'[OF \<open>p \<noteq> p'\<close>]
  by simp

declare fun_cong[OF state_transformer_same_prefix_equal_intro, intro]

declare cong[OF cong[OF cong [OF refl[of state_transformer] refl] refl], intro]

declare cong[OF state_transformer_same_prefix_equal_intro, intro]

lemma map_of_map_add_prefix_of_add_prefix[simp]:
  "map_of (map (\<lambda>(i, y). (add_prefix p i, y)) vs) (add_prefix p x) = map_of vs x"
proof(cases "map_of vs x")
  case None
  hence "map_of (map (\<lambda>(i, y). (add_prefix p i, y)) vs) (add_prefix p x) = None"
    by(force simp: map_of_eq_None_iff)
  thus ?thesis
    using None
    by simp
next
  case (Some a)
  hence "map_of (map (\<lambda>(i, y). (add_prefix p i, y)) vs) (add_prefix p x) = Some a"
    using map_of_mapk_SomeI[OF add_prefix_inj]
    by fastforce
  then show ?thesis
    using Some
    by simp
qed

lemma state_transformers_same_prefix_equal_iff[simp]:
  "state_transformer p vs s = state_transformer p vs' s \<longleftrightarrow>
    (\<forall>x \<in> set (map fst (vs @ vs')). (map_of vs x = map_of vs' x) 
        \<or> (map_of vs x = None \<and> map_of vs' x = Some (s (add_prefix p x)))
        \<or> (map_of vs' x = None \<and> map_of vs x = Some (s (add_prefix p x))))"
proof
  assume "state_transformer p vs s = state_transformer p vs' s"

  have "x \<in> set (map fst (vs @ vs')) \<Longrightarrow> 
    map_of vs x = map_of vs' x \<or>
      map_of vs x = None \<and> map_of vs' x = Some (s (add_prefix p x)) \<or>
      map_of vs' x = None \<and> map_of vs x = Some (s (add_prefix p x))" for x
  proof -
    assume "x \<in> set (map fst (vs @ vs'))"
    have "state_transformer p vs s (add_prefix p x) = state_transformer p vs' s (add_prefix p x)"
      using \<open>state_transformer p vs s = state_transformer p vs' s\<close>
      by auto
    thus ?thesis
      unfolding state_transformer_def
      by(auto split: option.splits)
  qed
  thus "(\<forall>x \<in> set (map fst (vs @ vs')).
      map_of vs x = map_of vs' x \<or>
      map_of vs x = None \<and> map_of vs' x = Some (s (add_prefix p x)) \<or>
      map_of vs' x = None \<and> map_of vs x = Some (s (add_prefix p x)))"
    by auto
next
  assume *: "\<forall>x\<in>set (map fst (vs @ vs')).
       map_of vs x = map_of vs' x \<or>
       map_of vs x = None \<and> map_of vs' x = Some (s (add_prefix p x)) \<or>
       map_of vs' x = None \<and> map_of vs x = Some (s (add_prefix p x))"

  hence "state_transformer p vs s x = state_transformer p vs' s x" for x
  proof(cases "\<exists>x'. x = add_prefix p x'")
    case True
    then obtain x' where "x = add_prefix p x'"
      by auto
    then show ?thesis
      unfolding state_transformer_def
      using *
      apply(auto split: option.splits)
      by (metis UnCI UnI2 domI domIff map_of_eq_None_iff option.inject)+
  next
    case False
    thus ?thesis
      unfolding state_transformer_def
      using *
      by(auto dest!: map_of_SomeD split: option.splits)
  qed
  thus "state_transformer p vs s = state_transformer p vs' s"
    by auto
qed

lemma state_transformers_of_x_same_prefix_equal_iff[simp]:
  "state_transformer p vs s x = state_transformer p vs' s' x \<longleftrightarrow>
    (x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
              (map_of vs (drop (2 + 2 * length p) x) = map_of vs' (drop (2 + 2 * length p) x)) 
            \<or> (map_of vs (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs' (drop (2 + 2 * length p) x) = Some (s x))
            \<or> (map_of vs' (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs (drop (2 + 2 * length p) x) = Some (s' x)))
          \<and> (x \<notin> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
             s x = s' x)"
proof
  assume "state_transformer p vs s x = state_transformer p vs' s' x"

  have "x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<Longrightarrow> 
   (map_of vs (drop (2 + 2 * length p) x) = map_of vs' (drop (2 + 2 * length p) x)) 
            \<or> (map_of vs (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs' (drop (2 + 2 * length p) x) = Some (s x))
            \<or> (map_of vs' (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs (drop (2 + 2 * length p) x) = Some (s' x))"
  proof -
    assume "x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs'))"
    then obtain x' where "x = add_prefix p x'" "x' \<in> set (map fst (vs @ vs'))"
      by auto
    thus ?thesis
      using \<open>state_transformer p vs s x = state_transformer p vs' s' x\<close> 
      unfolding state_transformer_def
      by(auto split: option.splits)
  qed

  moreover have "x \<notin> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<Longrightarrow> s x = s' x"
  proof -
    assume "x \<notin> set (map ((add_prefix p) \<circ> fst) (vs @ vs'))"
    hence "state_transformer p vs s x = s x" "state_transformer p vs' s' x = s' x" 
      unfolding state_transformer_def
      by(force dest!: map_of_SomeD split: option.splits)+
    thus "s x = s' x"
      using \<open>state_transformer p vs s x = state_transformer p vs' s' x\<close>
      by simp
  qed

  ultimately show " 
          (x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
              (map_of vs (drop (2 + 2 * length p) x) = map_of vs' (drop (2 + 2 * length p) x)) 
            \<or> (map_of vs (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs' (drop (2 + 2 * length p) x) = Some (s x))
            \<or> (map_of vs' (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs (drop (2 + 2 * length p) x) = Some (s' x)))
          \<and> (x \<notin> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
             s x = s' x)"
    by simp
next
  assume *: "
          (x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
              (map_of vs (drop (2 + 2 * length p) x) = map_of vs' (drop (2 + 2 * length p) x)) 
            \<or> (map_of vs (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs' (drop (2 + 2 * length p) x) = Some (s x))
            \<or> (map_of vs' (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs (drop (2 + 2 * length p) x) = Some (s' x)))
          \<and> (x \<notin> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
             s x = s' x)"

  have "state_transformer p vs s x = state_transformer p vs' s' x" 
  proof(cases "x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs'))")
    case True
    then obtain x' where "x = add_prefix p x'"
      by auto
    then show ?thesis
      unfolding state_transformer_def
      using * True \<open>x = add_prefix p x'\<close>
      apply(auto split: option.splits)
      by (metis option.distinct weak_map_of_SomeI)+
  next
    case False
    thus ?thesis
      unfolding state_transformer_def
      using * False
      by(auto simp: rev_image_eqI dest!: map_of_SomeD split: option.splits)
  qed
  thus "state_transformer p vs s x = state_transformer p vs' s' x"
    by auto
qed

lemma state_transformers_same_prefix_equal_iff'[simp]:
  "state_transformer p vs s = state_transformer p vs' s'
    \<longleftrightarrow> (\<forall>x. 
          (x \<in> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
              (map_of vs (drop (2 + 2 * length p) x) = map_of vs' (drop (2 + 2 * length p) x)) 
            \<or> (map_of vs (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs' (drop (2 + 2 * length p) x) = Some (s x))
            \<or> (map_of vs' (drop (2 + 2 * length p) x) = None 
               \<and> map_of vs (drop (2 + 2 * length p) x) = Some (s' x)))
          \<and> (x \<notin> set (map ((add_prefix p) \<circ> fst) (vs @ vs')) \<longrightarrow>
             s x = s' x))"
  by(auto simp: fun_eq_iff)

lemma state_transformer_of_same_prefix[simp]: "state_transformer p vs s (add_prefix p v)
  = (case (map_of (map (\<lambda>(i, j). (add_prefix p i, j)) vs)) (add_prefix p v) of
      (Some y) \<Rightarrow> y |
       None \<Rightarrow> s (add_prefix p v))"
  by(auto simp: state_transformer_def split: option.splits)

lemma state_transformer_of_different_prefix[simp]: "p \<noteq> p'
  \<Longrightarrow> state_transformer p vs s (add_prefix p' v) = s (add_prefix p' v)"
  by(auto dest!: map_of_SomeD simp: state_transformer_def split: option.splits)

lemma unchanged_by_state_transformer_intro[intro!]: 
  "list_all (\<lambda>(i, j). x \<noteq> (add_prefix p i) \<or> j = s x) vs 
    \<Longrightarrow> state_transformer p vs s x = s x"
  by(auto 
      dest!: map_of_SomeD 
      simp: state_transformer_def list_all_def 
      split: option.splits)

lemma state_transformer_of_update_same_prefix[simp]:
  "state_transformer p vs (s((add_prefix p v) := y)) = state_transformer p (vs @ [(v, y)]) s"
  unfolding state_transformer_def
  by (auto intro!: HOL.ext split: option.splits)

(* TODO: more elegant / general way of doing this *)
lemma state_transformer_of_update_same_prefix'[simp]:
  assumes "p \<noteq> p'"
  shows "state_transformer p vs 
    (state_transformer p' vs' (s((add_prefix p v) := y))) 
    = state_transformer p (vs @ [(v, y)]) (state_transformer p' vs' s)"
proof -
  have "state_transformer p vs 
    (state_transformer p' vs' (s((add_prefix p v) := y))) =
      state_transformer p' vs' (state_transformer p (vs @ [(v, y)]) s)"
    using \<open>p \<noteq> p'\<close> state_transformer_commutes' 
    by (metis state_transformer_of_update_same_prefix)
  thus ?thesis
    using \<open>p \<noteq> p'\<close> state_transformer_commutes' 
    by simp
qed

lemma state_transformer_update_same_prefix[simp]:
  "(state_transformer p vs s)((add_prefix p v) := y) = state_transformer p ((v, y) # vs) s"
  unfolding state_transformer_def
  by (auto intro!: HOL.ext split: option.splits)

lemma state_transformer_update_different_prefix[simp]:
  "p \<noteq> p' 
    \<Longrightarrow>(state_transformer p vs s)((add_prefix p' v) := y) 
         = state_transformer p' [(v, y)] (state_transformer p vs s)"
  unfolding state_transformer_def
  by (auto intro!: HOL.ext split: option.splits)

declare unchanged_by_state_transformer_intro[symmetric, intro]

lemma lambda_as_state_transformer[simp]:
  "(\<lambda>x. if x = add_prefix p a
           then y
           else s x) = state_transformer p [(a, y)] s"
  unfolding state_transformer_def
  by auto

lemma updated_state_as_state_transformer[simp]:
  "s(add_prefix p x := y) = state_transformer p [(x, y)] s"
  unfolding state_transformer_def
  by auto

type_synonym pcom = "string \<Rightarrow> com"

fun atomExp_add_prefix where
"atomExp_add_prefix p (N a) = N a" |
"atomExp_add_prefix p (V v) = V (add_prefix p v)"

fun aexp_add_prefix where
"aexp_add_prefix p (A a) = A (atomExp_add_prefix p a)" |
"aexp_add_prefix p (Plus a b) = Plus (atomExp_add_prefix p a) (atomExp_add_prefix p b)" |
"aexp_add_prefix p (Sub a b) = Sub (atomExp_add_prefix p a) (atomExp_add_prefix p b)"  | 
"aexp_add_prefix p (Parity a) = Parity (atomExp_add_prefix p a)" |
"aexp_add_prefix p (RightShift a) = RightShift (atomExp_add_prefix p a)"

abbreviation pcom_SKIP where "pcom_SKIP p \<equiv> SKIP"

abbreviation pcom_Assign where "pcom_Assign v aexp p \<equiv>
  Assign (add_prefix p v) (aexp_add_prefix p aexp)"

abbreviation pcom_Seq where "pcom_Seq a b p \<equiv> (a  p) ;; (b p)"

abbreviation pcom_If where "pcom_If v a b p \<equiv> 
  If (add_prefix p v) (a p) (b p)"

abbreviation pcom_While where "pcom_While v a p \<equiv> While (add_prefix p v) (a p)"

abbreviation invoke_subprogram :: "string \<Rightarrow> pcom \<Rightarrow> pcom" 
  where "invoke_subprogram p' c \<equiv> (\<lambda>p. c (p' @ p))"

abbreviation write_subprogram_param where "write_subprogram_param p' a  b \<equiv>
  (\<lambda>p. Assign (add_prefix (p' @ p) a) (aexp_add_prefix p b))"

abbreviation read_subprogram_param where "read_subprogram_param a p' b \<equiv> 
  (\<lambda>p. Assign (add_prefix p a) (aexp_add_prefix (p' @ p) b))"

abbreviation read_write_subprogram_param where "read_write_subprogram_param p' a p'' b \<equiv>
  (\<lambda>p. Assign (add_prefix (p' @ p) a) (aexp_add_prefix (p'' @ p) b))"

unbundle no_com_syntax

bundle pcom_syntax
begin
notation pcom_SKIP ("SKIP" [] 61) and
         pcom_Assign ("_ ::= _" [1000, 61] 61) and
         write_subprogram_param ("[_] _ ::= _" [1000, 61, 61] 61) and
         read_subprogram_param ("_ ::= [_] _" [1000, 61, 61] 61) and
         read_write_subprogram_param ("[_] _ ::= [_] _" [1000, 61, 61, 61] 61) and
         pcom_Seq ("_;;/ _"  [60, 61] 60) and
         pcom_If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         pcom_While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

bundle no_pcom_syntax
begin
no_notation pcom_SKIP ("SKIP" [] 61) and
            pcom_Assign ("_ ::= _" [1000, 61] 61) and
            write_subprogram_param ("[_] _ ::= _" [1000, 61, 61] 61) and
            read_subprogram_param ("_ ::= [_] _" [1000, 61, 61] 61) and
            read_write_subprogram_param ("[_] _ ::= [_] _" [1000, 61, 61, 61] 61) and
            pcom_Seq ("_;;/ _"  [60, 61] 60) and
            pcom_If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
            pcom_While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

unbundle pcom_syntax

end