\<^marker>\<open>creator Florian Kessler\<close>

theory Omega_Small_StepT  imports Main Com "../IMP-/Rel_Pow" Subprograms begin

paragraph "Summary"
text\<open>We give small step semantics with time for IMP-. 
Based on the small step semantics definition time for IMP\<close>

datatype EVal = Num nat | \<omega>

type_synonym state = "vname \<Rightarrow> val"
type_synonym EState = "vname \<Rightarrow> EVal"

fun atomVal :: "atomExp \<Rightarrow> EState \<Rightarrow> nat \<Rightarrow> EVal" where
"atomVal (V var) s _ = s var" |
"atomVal (N number) _ r = (if number \<le> r then Num number else \<omega>)"

fun eval :: "aexp \<Rightarrow> EState \<Rightarrow> nat \<Rightarrow> EVal" where
"eval (A atomExp) s r = atomVal atomExp s r" |
"eval (Plus a b) s r = (case s a of Num x \<Rightarrow> if x + b \<le> r then Num (x + b) else \<omega> | \<omega> \<Rightarrow> \<omega>)" |
"eval (Sub a b) s r =  (case s a of Num x \<Rightarrow> if x - b \<le> r then Num (x - b) else \<omega> | \<omega> \<Rightarrow> \<omega>)"

inductive
  \<omega>_small_step :: "com * EState \<Rightarrow> nat  \<Rightarrow> com * EState \<Rightarrow> bool"  ("_ \<rightarrow>\<^bsub>_\<^esub> _" 55)
where
Assign:  "(x ::= a, s) \<rightarrow>\<^bsub>r\<^esub> (SKIP, s(x := eval a s r))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "s b \<noteq> Num 0 \<Longrightarrow> (IF b \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>1,s)" |
IfFalse: "s b = Num 0 \<Longrightarrow> (IF b \<noteq>0  THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>2,s)" |

WhileTrue:   "s b \<noteq> Num 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>\<^bsub>r\<^esub>
            (c ;; (WHILE b \<noteq>0 DO c), s)" |
WhileFalse:   "s b = Num 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>\<^bsub>r\<^esub>
            (SKIP,s)"

subsection "Transitive Closure"
abbreviation
  \<omega>_small_step_pow :: "com * EState \<Rightarrow> nat \<Rightarrow>  nat \<Rightarrow> com * EState \<Rightarrow> bool" ("_ \<rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" 55)
  where "x \<rightarrow>\<^bsub>r\<^esub>\<^bsup>t\<^esup> y == (rel_pow  (\<lambda>c1 c2. \<omega>_small_step c1 r c2) t) x y"

bundle small_step_syntax
begin
notation \<omega>_small_step ("_ \<rightarrow>\<^bsub>_\<^esub> _" 55) and
         \<omega>_small_step_pow ("_ \<rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" 55)
end

bundle no_small_step_syntax
begin
no_notation \<omega>_small_step ("_ \<rightarrow>\<^bsub>_\<^esub> _" 55) and
            \<omega>_small_step_pow ("_ \<rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" 55)
end

subsection\<open>Executability\<close>

code_pred \<omega>_small_step .

lemmas \<omega>_small_step_induct = \<omega>_small_step.induct[split_format(complete)]

subsubsection\<open>Proof automation\<close>

declare \<omega>_small_step.intros[simp,intro]

text\<open>Rule inversion:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow>\<^bsub>r\<^esub> ct"
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow>\<^bsub>r\<^esub> ct"
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow>\<^bsub>r\<^esub> ct"
inductive_cases IfE[elim!]: "(IF b\<noteq>0 THEN c1 ELSE c2,s) \<rightarrow>\<^bsub>r\<^esub> ct"
inductive_cases WhileE[elim]: "(WHILE b\<noteq>0 DO c, s) \<rightarrow>\<^bsub>r\<^esub> ct"

text\<open>A simple property:\<close>
lemma deterministic: "cs \<rightarrow>\<^bsub>r\<^esub> cs' \<Longrightarrow> cs \<rightarrow>\<^bsub>r\<^esub> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction arbitrary: cs'' rule: \<omega>_small_step.induct)
  by blast+

text "sequence property"
lemma star_seq2: "(c1,s) \<rightarrow>\<^bsub>r\<^esub>\<^bsup>t\<^esup> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>\<^bsub>r\<^esub>\<^bsup> t \<^esup> (c1';;c2,s')"
proof(induction t arbitrary: c1 c1' s s')
  case (Suc t)
  then obtain c1'' s'' where "(c1,s) \<rightarrow>\<^bsub>r\<^esub> (c1'', s'')" 
                         and "(c1'', s'')  \<rightarrow>\<^bsub>r\<^esub>\<^bsup> t \<^esup>  (c1', s')" by auto
  moreover then have "(c1'';;c2, s'') \<rightarrow>\<^bsub>r\<^esub>\<^bsup> t \<^esup> (c1';;c2, s')" using Suc by simp
  ultimately show ?case by auto
qed auto

definition \<omega>_equivalent:: "nat \<Rightarrow> state \<Rightarrow> EState \<Rightarrow> bool" where 
"\<omega>_equivalent r s s' \<equiv> (\<forall>v. (Num (s v) = s' v) \<or> (s v > r \<and> s' v = \<omega>))"

lemma \<omega>_equivalent_Num_then: "\<omega>_equivalent r s s' \<Longrightarrow> s' v = Num x \<Longrightarrow> s v = x" 
  apply (auto simp: \<omega>_equivalent_def)
  by (metis EVal.distinct EVal.inject)

lemma \<omega>_equivalent_\<omega>_then: "\<omega>_equivalent r s s' \<Longrightarrow> s' v = \<omega> \<Longrightarrow> s v > r" 
  apply (auto simp: \<omega>_equivalent_def)
  by (metis EVal.distinct EVal.inject)

lemma \<omega>_equivalent_0_iff:
  assumes "\<omega>_equivalent r s s'" 
  shows "(s' v = Num 0) \<longleftrightarrow> (s v = 0)"
  using \<omega>_equivalent_Num_then apply(auto)
  using assms apply(auto simp: \<omega>_equivalent_def)
  by (metis gr_implies_not_zero)

lemma \<omega>_equivalent_increasing: "\<omega>_equivalent r s s' \<Longrightarrow> \<omega>_equivalent (r - x) s s'" 
  by (auto simp: \<omega>_equivalent_def)
lemma \<omega>_equivalent_increasing': "r' \<le> r \<Longrightarrow> \<omega>_equivalent r s s' \<Longrightarrow> \<omega>_equivalent r' s s'" 
  by (auto simp: \<omega>_equivalent_def)

lemma small_step_omega_equivalence_step: "(c1, s1) \<rightarrow> (c2, s2)
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c) \<Longrightarrow>  \<omega>_equivalent r' s1 s1' \<Longrightarrow> r \<ge> r' 
  \<Longrightarrow> r' > max_constant c 
  \<Longrightarrow>  (\<exists>s2'. (c1, s1') \<rightarrow>\<^bsub>r\<^esub> (c2, s2') \<and> \<omega>_equivalent (r' - max_constant c) s2 s2')"
proof (induction c1 s1 c2 s2  rule: small_step_induct)
  case (Assign x a s)
  let ?s2' = "s1'(x := eval a s1' r)"
  have "((x ::= a), s1') \<rightarrow>\<^bsub>r\<^esub> (SKIP, ?s2')" by auto
  moreover have "\<omega>_equivalent (r' - max_constant c) (s(x := aval a s)) ?s2'"
  proof (cases a)
    case (A atom)
    then show ?thesis using Assign by (cases atom) (auto simp: \<omega>_equivalent_def split: if_splits)
  next
    case (Plus var val)
    then show ?thesis using Assign \<omega>_equivalent_Num_then[where ?s=s and ?v = var] 
        \<omega>_equivalent_\<omega>_then[where ?s=s and ?s'=s1' and ?v = var and ?r=r']
      by (auto simp: \<omega>_equivalent_def  split: EVal.splits if_splits)
  next
    case (Sub var val)
    then show ?thesis using Assign Sub enumerate_subprograms_max_constant 
        \<omega>_equivalent_Num_then[where ?s=s and ?v = var] 
        \<omega>_equivalent_\<omega>_then[where ?s=s and ?s'=s1' and ?v = var and ?r=r']
      by (fastforce simp: \<omega>_equivalent_def split: EVal.splits if_splits)
  qed
  ultimately show ?case by blast
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then have "c\<^sub>1 \<in> set (enumerate_subprograms (c\<^sub>1 ;; c\<^sub>2))" using c_in_all_subprograms_c by auto
  then have "c\<^sub>1 \<in> set (enumerate_subprograms c)" using Seq2 enumerate_subprograms_transitive by blast
  then show ?case using Seq2 by auto
next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  then have "(IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2, s1') \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>1, s1') \<and> \<omega>_equivalent (r' - max_constant c) s s1'" 
    by (auto simp: \<omega>_equivalent_0_iff \<omega>_equivalent_increasing)
  then show ?case using IfTrue by auto
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  then have "(IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2, s1') \<rightarrow>\<^bsub>r\<^esub> (c\<^sub>2, s1') \<and> \<omega>_equivalent (r' - max_constant c) s s1'" 
    by (auto simp: \<omega>_equivalent_0_iff \<omega>_equivalent_increasing)
  then show ?case using IfTrue by auto
next
  case (WhileTrue s b c)
  then have "(WHILE b\<noteq>0 DO c, s1') \<rightarrow>\<^bsub>r\<^esub> (c ;; WHILE b\<noteq>0 DO c, s1') \<and> \<omega>_equivalent (r' - max_constant c) s s1'"
    by (auto simp: \<omega>_equivalent_0_iff \<omega>_equivalent_increasing)
  then show ?case using WhileTrue \<omega>_equivalent_increasing by blast
next
  case (WhileFalse s b c)
  then have "(WHILE b\<noteq>0 DO c, s1') \<rightarrow>\<^bsub>r\<^esub> (SKIP, s1') \<and> \<omega>_equivalent (r' - max_constant c) s s1'"
    by (auto simp: \<omega>_equivalent_0_iff \<omega>_equivalent_increasing)
  then show ?case using WhileFalse \<omega>_equivalent_increasing by blast
qed (auto simp: \<omega>_equivalent_increasing)

lemma small_step_omega_equivalence: "(c1, s1) \<rightarrow>\<^bsup> t \<^esup> (c2, s2)
  \<Longrightarrow> c1 \<in> set (enumerate_subprograms c) \<Longrightarrow>  \<omega>_equivalent r' s1 s1' \<Longrightarrow> r \<ge> r' 
  \<Longrightarrow> r' > t * max_constant c 
  \<Longrightarrow>  (\<exists>s2'. (c1, s1') \<rightarrow>\<^bsub>r\<^esub>\<^bsup> t \<^esup> (c2, s2') \<and> \<omega>_equivalent (r' - t * max_constant c) s2 s2')"
proof (induction t arbitrary: c2 s2)
  case (Suc t)
  have "\<exists>c3 s3. ((c1, s1) \<rightarrow>\<^bsup>t\<^esup> (c3, s3)) \<and> ((c3, s3) \<rightarrow> (c2, s2))" 
    using Suc(2) rel_pow_Suc_E by fast 
  then obtain  c3 s3 where c3s3_def: "((c1, s1) \<rightarrow>\<^bsup>t\<^esup> (c3, s3)) \<and> ((c3, s3) \<rightarrow> (c2, s2)) 
    \<and> c3 \<in> set (enumerate_subprograms c)" using enumerate_subprograms_complete Suc(3)
    by (metis enumerate_subprograms_def enumerate_subprograms_transitive set_remdups)
  then obtain s3' where "(c1, s1') \<rightarrow>\<^bsub>r\<^esub>\<^bsup> t \<^esup> (c3, s3') \<and> \<omega>_equivalent (r' - t * max_constant c) s3 s3'" 
    using Suc by auto
  moreover then have "\<exists>s2'. (c3, s3') \<rightarrow>\<^bsub>r\<^esub> (c2, s2') \<and> \<omega>_equivalent (r' - (t + 1) * max_constant c) s2 s2'" 
    using c3s3_def small_step_omega_equivalence_step[where ?s1.0 = s3] Suc 
    by (fastforce simp: add.commute)
  moreover then obtain s2' where "(c3, s3') \<rightarrow>\<^bsub>r\<^esub> (c2, s2') \<and> \<omega>_equivalent (r' - (t + 1) * max_constant c) s2 s2'"
    by auto
  ultimately have "(c1, s1') \<rightarrow>\<^bsub>r\<^esub>\<^bsup>t + 1\<^esup> (c2, s2') \<and> \<omega>_equivalent (r' - (t + 1) * max_constant c) s2 s2'"
    by (meson rel_pow_step1 rel_pow_sum)
  then show ?case by auto
qed auto

lemma omega_small_step_equivalence_step: "(c1, s1') \<rightarrow>\<^bsub>r\<^esub> (c2, s2')
  \<Longrightarrow>  \<omega>_equivalent r' s1 s1' \<Longrightarrow> r \<ge> r' \<Longrightarrow> r' > max_constant c1 
  \<Longrightarrow>  (\<exists>s2. (c1, s1) \<rightarrow> (c2, s2) \<and> \<omega>_equivalent (r' - max_constant c1) s2 s2')"
proof (induction c1 s1' r c2 s2' rule: \<omega>_small_step_induct)
  case (Assign x a s r)
  let ?s2 = "s1(x := aval a s1)"
  have "((x ::= a, s1) \<rightarrow> (SKIP, ?s2))" by simp
  moreover have "\<omega>_equivalent (r' - max_constant (x ::= a)) ?s2 (s(x := eval a s r))"
  using Assign proof (cases a)
    case (Plus var val)
    then show ?thesis using Assign \<omega>_equivalent_Num_then[where ?s=s1 and ?v = var] 
        \<omega>_equivalent_\<omega>_then[where ?s=s1 and ?s'=s and ?v = var and ?r=r']
      by (auto simp: \<omega>_equivalent_def  split: EVal.splits if_splits)
  next
    case (Sub var val)
    then show ?thesis using Assign Sub 
        \<omega>_equivalent_Num_then[where ?s=s1 and ?v = var] 
        \<omega>_equivalent_\<omega>_then[where ?s=s1 and ?s'=s and ?v = var and ?r=r']
      by (auto simp: \<omega>_equivalent_def split: EVal.splits if_splits)
  qed (auto simp: \<omega>_equivalent_def split: atomExp.splits)
  ultimately show ?case using Assign by blast
next
  case (Seq2 c\<^sub>1 s r c\<^sub>1' s' c\<^sub>2)
  then obtain  s2 where "(c\<^sub>1, s1) \<rightarrow> (c\<^sub>1', s2) \<and> \<omega>_equivalent (r' - max_constant c\<^sub>1) s2 s'" by auto
  then have "(c\<^sub>1 ;; c\<^sub>2, s1) \<rightarrow> (c\<^sub>1' ;; c\<^sub>2, s2) \<and> \<omega>_equivalent (r' - max_constant c\<^sub>1) s2 s'" by auto
  then have "(c\<^sub>1 ;; c\<^sub>2, s1) \<rightarrow> (c\<^sub>1' ;; c\<^sub>2, s2) 
    \<and> \<omega>_equivalent (r' - (max (max_constant c\<^sub>1) (max_constant c\<^sub>2))) s2 s'" 
    using \<omega>_equivalent_increasing'[where ?r ="r' - max_constant c\<^sub>1" and ?r' = "r' - (max (max_constant c\<^sub>1) (max_constant c\<^sub>2))"]
    by simp
  then show ?case using Seq2 \<omega>_equivalent_increasing by auto
qed (auto simp: \<omega>_equivalent_increasing \<omega>_equivalent_0_iff)

lemma omega_small_step_equivalence: "(c1, s1') \<rightarrow>\<^bsub>r\<^esub>\<^bsup> t \<^esup> (c2, s2')
  \<Longrightarrow> \<omega>_equivalent r' s1 s1' \<Longrightarrow> r \<ge> r' \<Longrightarrow> r' > t * max_constant c1
  \<Longrightarrow> (\<exists>s2. (c1, s1) \<rightarrow>\<^bsup> t \<^esup> (c2, s2) \<and> \<omega>_equivalent (r' - t * max_constant c1) s2 s2')"
proof (induction t arbitrary: c2 s2')
  case (Suc t)
  have "\<exists>c3 s3'. ((c1, s1') \<rightarrow>\<^bsub>r\<^esub>\<^bsup>t\<^esup> (c3, s3')) \<and> ((c3, s3') \<rightarrow>\<^bsub>r\<^esub> (c2, s2'))" 
    using Suc(2) rel_pow_Suc_E by fast 
  then obtain c3 s3' where c3s3_def: "((c1, s1') \<rightarrow>\<^bsub>r\<^esub>\<^bsup>t\<^esup> (c3, s3')) \<and> ((c3, s3') \<rightarrow>\<^bsub>r\<^esub> (c2, s2')) "
    by auto
  then obtain s3 where s3_def: "(c1, s1) \<rightarrow>\<^bsup> t \<^esup> (c3, s3) \<and> \<omega>_equivalent (r' - t * max_constant c1) s3 s3'"
    using Suc by auto
  then have c3_leq_c1: "max_constant c3 \<le> max_constant c1" using execution_cant_increase_max_constant
    by auto
  moreover then have "\<exists>s2. (c3, s3) \<rightarrow> (c2, s2) \<and> \<omega>_equivalent (r' - t * max_constant c1 - max_constant c3) s2 s2'" 
    using c3s3_def s3_def omega_small_step_equivalence_step Suc 
    by (fastforce simp: add.commute)
  moreover then obtain s2 where "(c3, s3) \<rightarrow> (c2, s2) \<and> \<omega>_equivalent (r' - (t + 1) * max_constant c1) s2 s2'"
    using c3_leq_c1 \<omega>_equivalent_increasing'[where ?r = "r' - t * max_constant c1 - max_constant c3"]
    by fastforce
  ultimately have "(c1, s1) \<rightarrow>\<^bsup>t + 1\<^esup> (c2, s2) \<and> \<omega>_equivalent (r' - (t + 1) * max_constant c1) s2 s2'"
    using s3_def by (meson rel_pow_step1 rel_pow_sum)
  then show ?case by auto
qed auto


end