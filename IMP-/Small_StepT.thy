\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "Small step semantics of IMP- "

subsection "Small step semantics definition"
theory Small_StepT  imports Main Big_StepT Rel_pow begin

paragraph "Summary"
text\<open>We give small step semantics with time for IMP-. 
Based on the small step semantics definition time for IMP\<close>

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"  (infix "\<rightarrow>" 55)
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

subsection "Transitive Closure"
abbreviation
  small_step_pow :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool"
  where "small_step_pow x t y == (rel_pow  small_step t)  x y"

bundle small_step_syntax
begin
notation small_step (infix "\<rightarrow>" 55) and
         small_step_pow ("_ \<rightarrow>* _ \<down> _" 55)
end

bundle no_small_step_syntax
begin
no_notation small_step_pow ("_ \<rightarrow>* _ \<down> _" 55) and
            small_step_pow ("_ \<rightarrow>* _ \<down> _" 55)
end

unbundle small_step_syntax

subsection\<open>Executability\<close>

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t .
   ((''x'' ::= A (V ''z'');; ''y'' ::=A ( V ''x''),
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* 1 \<down> (c',t))}"
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
thm WhileE
text\<open>A simple property:\<close>
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
        apply blast+
  apply auto
done

section "Equivalence with big-step semantics"
declare rel_pow_intros[simp,intro]
text "sequence property"
lemma star_seq2: "(c1,s) \<rightarrow>* t \<down> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* t  \<down> (c1';;c2,s')"
proof(induction t arbitrary: c1 c1' s s')
  case 0
  then show ?case by auto
next
  case (Suc t)
  then obtain c1'' s'' where "(c1,s) \<rightarrow> (c1'', s'')" 
                         and "(c1'', s'')  \<rightarrow>* t \<down>  (c1', s')" by auto
  moreover then have "(c1'';;c2, s'') \<rightarrow>* t \<down> (c1';;c2, s')" using Suc by simp
  ultimately show ?case by auto
qed

text "sequence time is one plus sum of the sub-commands times"
lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* t1 \<down> (SKIP,s2); (c2,s2) \<rightarrow>* t2 \<down> (c3,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (t1 + t2 +1) \<down> (c3,s3)"
proof (induction t1 arbitrary: c1 s1)
  case 0
  then have "(c1;;c2, s1) \<rightarrow> (c2, s2)" by auto
  then show ?case using 0  by simp
next
  case (Suc t1)
  then obtain c1' s1' where *: "(c1, s1) \<rightarrow> (c1',s1')" and "(c1',s1') \<rightarrow>* t1 \<down> (SKIP,s2)"
    using relpowp_Suc_E2 by auto
    then have "(c1';;c2, s1') \<rightarrow>* (t1 + t2 + 1) \<down> (c3, s3)" using Suc by blast 
    then show ?case using Suc by auto
  qed


text "from Big step to small step semantics"
lemma big_to_small_helper: "(c, s) \<Rightarrow> t \<Down> s' \<Longrightarrow> t = Suc t' \<Longrightarrow> (c, s) \<rightarrow>* t' \<down> (SKIP, s')"
proof (induction arbitrary: t' rule: big_step_t_induct)
  case (Skip s)
  then show ?case by simp
next
  case (Assign x a s)
  then have "t' = Suc 0" by auto
  moreover have "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" by blast
  ultimately show ?case by blast
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  then obtain x' y' where suc_ex: "x = Suc x'" "y = Suc y'"
    by (meson bigstep_progress gr0_implies_Suc)
  then have "(c1, s1) \<rightarrow>* x' \<down> (SKIP, s2)" using Seq by auto
  moreover have "(c2, s2) \<rightarrow>* y' \<down> (SKIP, s3)" using Seq suc_ex by auto
  ultimately have "(c1 ;; c2, s1) \<rightarrow>* (x' + y' + 1) \<down> (SKIP, s3)" using seq_comp by simp  
  then show ?case using Seq suc_ex by simp
next
  case (IfTrue s b c1 x t y c2)
  then obtain x' where "x = Suc x'" using bigstep_progress gr0_implies_Suc by blast
  then show ?case using IfTrue by auto
next
  case (IfFalse s b c2 x t y c1)
  then obtain x' where "x = Suc x'" by (meson bigstep_progress gr0_implies_Suc)
  then show ?case using IfFalse by auto
next
  case (WhileFalse s b c)
  then show ?case by fastforce
next
  case (WhileTrue s1 b c x s2 y s3 z)
  let ?w = "WHILE b \<noteq>0 DO c"
  obtain x' y' where suc_def:"x =Suc x'" "y = Suc y'"
    by (meson WhileTrue.hyps(2) WhileTrue.hyps(3) bigstep_progress gr0_implies_Suc)
  have "(?w, s1) \<rightarrow>*1 \<down> (c ;; ?w, s1)" using WhileTrue by auto
  moreover have "(c ;; ?w, s1)\<rightarrow>* x' \<down> (SKIP ;; ?w, s2)" 
    using WhileTrue by (simp add: suc_def star_seq2) 
  moreover have "(SKIP ;; ?w, s2) \<rightarrow>* 1 \<down>(?w, s2)" by auto
  moreover have "(?w, s2) \<rightarrow>* y' \<down> (SKIP, s3)" using WhileTrue  \<open>y = Suc y'\<close> by blast
  ultimately have "(?w, s1) \<rightarrow>* 1 + x' + 1 + y'\<down> (SKIP, s3)" by (meson rel_pow_sum) 
  moreover have "t' = Suc (Suc (x' + y')) " using WhileTrue suc_def by auto 
  thus ?case  using calculation by simp
qed

lemma big_to_small: "(c, s) \<Rightarrow> Suc t \<Down> s' \<Longrightarrow> (c, s) \<rightarrow>* t \<down> (SKIP,s')"
  using big_to_small_helper by blast

text "from small to big semantics"
lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Down> cs'' \<Longrightarrow> cs \<Rightarrow> Suc t \<Down> cs''"
  apply (induction arbitrary: cs'' t rule:small_step.induct )
  apply auto
  apply fastforce
  done


lemma small_to_big :
 "cs \<rightarrow>* t \<down> (SKIP,s') \<Longrightarrow> cs \<Rightarrow> Suc t \<Down> s' "
  apply(induction t arbitrary:cs s')
   apply auto[1]
  using small1_big_continue by blast

text "Equivalence statement"
lemma equiv_small_big_pair:
 "(c,s) \<rightarrow>* t \<down> (SKIP,s') \<longleftrightarrow> (c,s) \<Rightarrow> Suc t \<Down> s' "
  using big_to_small small_to_big  by auto 

lemma equiv_small_big:
 "cs \<rightarrow>* t \<down> (SKIP,s') = cs \<Rightarrow> Suc t \<Down> s' "
  using equiv_small_big_pair
  by (metis old.prod.exhaust) 

end