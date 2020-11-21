 (*
    Authors: Bilel Ghorbel, Florian Kessler
    Based on the Big step semantics definition  with time of IMP
 *)
section "Big step semantics of IMP-"
theory Big_StepT imports Main Com begin

subsection "Big step semantics definition:"

text "In IMP- Branching is only based on whether a variable's value equals 0."

inductive
  big_step_t :: "com \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow> _ \<Down> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow> Suc (0::nat) \<Down> s"|
Assign: "(x ::= a,s) \<Rightarrow> Suc (Suc 0) \<Down> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow> x \<Down> s2;  (c2,s2) \<Rightarrow> y \<Down> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> z \<Down> s3" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow> x \<Down> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> y \<Down> t" |
IfFalse: "\<lbrakk> s b = 0; (c2,s) \<Rightarrow> x \<Down> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> y \<Down> t" |
WhileFalse: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow> Suc (Suc 0) \<Down> s" |
WhileTrue: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow> x \<Down> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow> y \<Down> s3; 1+x+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow> z \<Down> s3" 
code_pred big_step_t .

text "finding out the final state and running time of a command:"
schematic_goal ex: "(''x'' ::= A (N 5);; ''y'' ::= A (V ''x''), s) \<Rightarrow> ?t \<Down> ?s"
apply(rule Seq)
apply(rule Assign)
apply simp
apply(rule Assign)
apply simp
done
thm ex[simplified]


values "{(t, x). big_step_t (SKIP, \<lambda>_. 0) x t}"

values "{map t [''x''] |t x. (SKIP, <''x'' := 42>) \<Rightarrow> x \<Down> t}"

values "{map t [''x''] |t x. (''x'' ::=A (N 2), <''x'' := 42>) \<Rightarrow> x \<Down> t}"

values "{(map t [''x''],x) |t x. (WHILE ''x''\<noteq>0 DO ''x''::= Sub (V ''x'') (N 1),<''x'':=5>) \<Rightarrow> x \<Down> t }"

text "proof automation:"

text "Introduction rules:"
declare big_step_t.intros [intro]

text "Induction rules with pair splitting"
lemmas big_step_t_induct = big_step_t.induct[split_format(complete)]

subsection "Rule inversion"
inductive_cases Skip_tE[elim!]: "(SKIP,s) \<Rightarrow> x \<Down> t"
thm Skip_tE
inductive_cases Assign_tE[elim!]: "(x ::= a,s) \<Rightarrow> p \<Down> t"
thm Assign_tE
inductive_cases Seq_tE[elim!]: "(c1;;c2,s1) \<Rightarrow> p \<Down> s3"
thm Seq_tE
inductive_cases If_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow> x \<Down> t"
thm If_tE

inductive_cases While_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow> x \<Down> t"
thm While_tE

text "Rule inversion use examples:"
lemma "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow> x \<Down> t \<Longrightarrow> t = s"
  by blast

lemma assumes "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow> x \<Down> t"
  shows "t = s"
proof -
  from assms show ?thesis
  proof cases
  case (IfTrue x)
  then show ?thesis by blast
next
  case (IfFalse x)
  then show ?thesis by blast
qed
qed
lemma assign_t_simp:
  "((x ::= a,s) \<Rightarrow> Suc(Suc 0) \<Down>  s') \<longleftrightarrow> (s' = s(x := aval a s))"
  by (auto)

subsection "Determinism of Big semantics of IMP-"
theorem big_step_t_determ2: "\<lbrakk> (c,s) \<Rightarrow> p \<Down> t; (c,s) \<Rightarrow> q \<Down> u \<rbrakk> \<Longrightarrow> (u = t \<and> p=q)"
  apply  (induction arbitrary: u q rule: big_step_t_induct)
    apply(elim Skip_tE) apply(simp)
    apply(elim Assign_tE) apply(simp)
  apply blast
    apply(elim If_tE) apply(simp) apply blast
    apply(elim If_tE)  apply (linarith)apply simp
    apply(erule While_tE) apply(simp) apply simp
    proof (goal_cases)
      case 1
      from 1(7) show ?case apply(safe) 
        apply(erule While_tE)
          using 1(1-6) apply fast
          using 1(1-6) apply (simp)
        apply(erule While_tE)
          using 1(1-6) apply fast
          using 1(1-6) by (simp)
      qed

lemma bigstep_det: "(c1, s) \<Rightarrow> p1 \<Down> t1 \<Longrightarrow> (c1, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp

subsection "Progress property"
text "every command costs time"
lemma bigstep_progress: "(c, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p > 0"
  apply(induct rule: big_step_t.induct, auto) done

subsection "abbreviations and properties"
abbreviation terminates ("\<down>") where "terminates cs \<equiv> (\<exists>n a. (cs \<Rightarrow> n \<Down> a))"
abbreviation thestate ("\<down>\<^sub>s") where "thestate cs \<equiv> (THE a. \<exists>n. (cs \<Rightarrow> n \<Down> a))" 
abbreviation thetime ("\<down>\<^sub>t") where "thetime cs \<equiv> (THE n. \<exists>a. (cs \<Rightarrow> n \<Down> a))"


lemma bigstepT_the_cost: "(c, s) \<Rightarrow> t \<Down> s' \<Longrightarrow> \<down>\<^sub>t(c, s) = t"
  using bigstep_det by blast 

lemma bigstepT_the_state: "(c, s) \<Rightarrow> t \<Down> s' \<Longrightarrow> \<down>\<^sub>s(c, s) = s'"
  using bigstep_det by blast 

lemma SKIPnot: "(\<not> (SKIP, s) \<Rightarrow> p \<Down> t) \<longleftrightarrow> (s\<noteq>t \<or> p\<noteq>Suc 0)" by blast

lemma SKIPp: "\<down>\<^sub>t(SKIP,s) = Suc 0"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma SKIPt: "\<down>\<^sub>s(SKIP,s) = s"
  apply(rule the_equality)
  apply fast
  apply auto done 


lemma ASSp: "(THE p. Ex (big_step_t (x ::= e, s) p)) = Suc(Suc 0)"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma ASSt: "(THE t. \<exists>p. (x ::= e, s) \<Rightarrow> p \<Down> t) = s(x := aval e s)"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma ASSnot: "( \<not> (x ::= e, s) \<Rightarrow> p \<Down> t ) = (p\<noteq>Suc(Suc 0) \<or> t\<noteq>s(x := aval e s))"
  apply auto done

lemma If_THE_True: "Suc (THE n. \<exists>a. (c1, s) \<Rightarrow> n \<Down> a) =  (THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a)"
     if T: "s b \<noteq> 0" and c1_t: "terminates (c1,s)" for s l
proof -
  from c1_t obtain p t where a: "(c1, s) \<Rightarrow> p \<Down> t" by blast
  with T have b: "(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> p+1 \<Down> t"  using IfTrue by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c1, s) \<Rightarrow> n \<Down> a) = p" by simp
moreover    
  from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a) = p+1" by simp
ultimately
  show ?thesis by simp
qed

lemma If_THE_False: "Suc (THE n. \<exists>a. (c2, s) \<Rightarrow> n \<Down> a) =  (THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a)"
     if T: "s b = 0" and c2_t: "\<down> (c2,s)" for s l
proof -
  from c2_t obtain p t where a: "(c2, s) \<Rightarrow> p \<Down> t"  by blast
  with T have b: "(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> p+1 \<Down> t"  using IfFalse by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c2, s) \<Rightarrow> n \<Down> a) = p" by simp
moreover    
  from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a) = p+1" by simp
ultimately
  show ?thesis by simp
qed
    

end