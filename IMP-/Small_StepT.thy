theory Small_StepT
  imports Main Big_StepT HOL.Transitive_Closure "~~/src/HOL/IMP/Star"
begin

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "s b \<noteq> 0 \<Longrightarrow> (IF b \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "s b = 0 \<Longrightarrow> (IF b \<noteq>0  THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

WhileTrue:   "s b \<noteq> 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>
            (c ;; WHILE b \<noteq>0 DO c,s)" |
WhileFalse:   "s b = 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>
            (SKIP,s)"

abbreviation
  small_steps_star :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>**" 55)
where "x \<rightarrow>** y == star small_step x y"

abbreviation
  small_steps :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool" ("_ \<rightarrow>* _ \<down> _" 55)
  where "x \<rightarrow>* t \<down> y == (small_step ^^ t) x y"


subsection\<open>Executability\<close>

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t .
   ((''x'' ::= A (V ''z'');; ''y'' ::=A ( V ''x''),
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>** (c',t))}"

subsection\<open>Proof infrastructure\<close>

subsubsection\<open>Induction rules\<close>

text\<open>The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form \<open>a \<rightarrow> b \<Longrightarrow> \<dots>\<close> where \<open>a\<close> and \<open>b\<close> are
not already pairs \<open>(DUMMY,DUMMY)\<close>. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
\<open>\<rightarrow>\<close> into pairs:\<close>
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection\<open>Proof automation\<close>

declare small_step.intros[simp,intro]

text\<open>Rule inversion:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b\<noteq>0 THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b\<noteq>0 DO c, s) \<rightarrow> ct"

text\<open>A simple property:\<close>
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
        apply blast+
  apply auto
done

subsection "Equivalence with big-step semantics"

lemma star_seq2: "(c1,s) \<rightarrow>* t \<down> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* t  \<down> (c1';;c2,s')"
proof(induction t arbitrary: c1 c1' s s')
  case 0
  then show ?case by simp
next
  case (Suc t)
  then obtain c1'' s'' where "(c1,s) \<rightarrow>* t \<down> (c1'', s'')" 
                         and "(c1'', s'') \<rightarrow> (c1', s')" by auto
  moreover then have "(c1;;c2, s) \<rightarrow>* t \<down> (c1'';;c2, s'')" using Suc by auto
  ultimately show ?case by auto
qed

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* t1 \<down> (SKIP,s2); (c2,s2) \<rightarrow>* t2 \<down> (c3,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (t1 + t2 + 1) \<down> (c3,s3)"
proof (induction t1 arbitrary: c1 s1)
  case 0
  then have "(c1;;c2, s1) \<rightarrow> (c2, s2)" by auto
  then show ?case using 0 by (metis Suc_eq_plus1 add_cancel_right_left relpowp_Suc_I2)
next
  case (Suc t1)
  (* is there a way to directly obtain the pair? *)
  then obtain c1s1' where *: "(c1, s1) \<rightarrow> c1s1'" 
                      and "(c1s1') \<rightarrow>* t1 \<down> (SKIP,s2)" using relpowp_Suc_E2 by metis
  moreover obtain c1' s1' where **: "c1s1' = (c1', s1')" by (cases c1s1') auto
  ultimately have "(c1';;c2, s1') \<rightarrow>* (t1 + t2 + 1) \<down> (c3, s3)" using Suc by blast 
  then show ?case using Suc by (metis Seq2 * ** add_Suc relpowp_Suc_I2)
qed

lemma  "(c, s) \<Rightarrow> t \<Down> s' \<Longrightarrow> t = Suc t' \<Longrightarrow> (c, s) \<rightarrow>* t' \<down> (SKIP,s')"
proof (induction arbitrary: t' rule: big_step_t_induct)
  case (Skip s)
  then show ?case by simp
next
  case (Assign x a s)
  then have "t' = Suc 0" by auto
  moreover have "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" by blast
  ultimately show ?case by (meson relpowp_0_I relpowp_Suc_I)
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  then obtain x' y' where *: "x = Suc x'" and **: "y = Suc y'" by (meson bigstep_progress gr0_implies_Suc)
  then have "(c1, s1) \<rightarrow>* x' \<down> (SKIP, s2)" using Seq by auto
  moreover have "(c2, s2) \<rightarrow>* y' \<down> (SKIP, s3)" using Seq ** by auto
  ultimately have "(c1 ;; c2, s1) \<rightarrow>* (x' + y' + 1) \<down> (SKIP, s3)" using seq_comp by simp  
  then show ?case using Seq * ** by simp
next
  case (IfTrue s b c1 x t y c2)
  then obtain x' where "x = Suc x'" by (meson bigstep_progress gr0_implies_Suc)
  then show ?case using IfTrue 
    by (metis add_diff_cancel_left' add_diff_cancel_right' plus_1_eq_Suc relpowp_Suc_I2 small_step.IfTrue)
next
  case (IfFalse s b c2 x t y c1)
  then obtain x' where "x = Suc x'" by (meson bigstep_progress gr0_implies_Suc)
  then show ?case using IfFalse
    by (metis add_diff_cancel_left' add_diff_cancel_right' plus_1_eq_Suc relpowp_Suc_I2 small_step.IfFalse)
next
  case (WhileFalse s b c)
  then show ?case sorry
next
  case (WhileTrue s1 b c x s2 y s3 z)
  then show ?case sorry
qed

end