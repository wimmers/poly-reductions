\<^marker>\<open>creator Florian Keßler\<close>

section "Domains"

theory Domains imports Small_StepT
begin

fun max_constant :: "com \<Rightarrow> nat" where
"max_constant (SKIP) = 0" |
"max_constant (Assign vname aexp) = (case aexp of
  (A a) \<Rightarrow> (case a of (V var) \<Rightarrow> 0 | (N val) \<Rightarrow> val) |
  (Plus a b) \<Rightarrow> b |
  (Sub a b) \<Rightarrow> b)" |
"max_constant (Seq c1  c2) = max (max_constant c1) (max_constant c2)" |         
"max_constant (If  _ c1 c2) = max (max_constant c1) (max_constant c2)"  |   
"max_constant (While _ c) = max_constant c"

lemma step_cant_increase_max_constant: "(c1, s1) \<rightarrow> (c2, s2) \<Longrightarrow> max_constant c1 \<ge> max_constant c2"
proof (induction c1 arbitrary: s1 c2 s2)
  case (Seq c11 c12)
  then show ?case by force
qed auto

lemma execution_cant_increase_max_constant: "(c1, s1) \<rightarrow>\<^bsup> t \<^esup> (c2, s2)
   \<Longrightarrow> max_constant c1 \<ge> max_constant c2"
proof (induction t c1 s1 c2 s2 rule: rel_pow_induct)
next
  case (step a b a b n a b)
  then show ?case using step_cant_increase_max_constant by fastforce
qed auto

lemma [simp]: "\<exists>y. nat \<bar>int (s x) - int (s y)\<bar> \<le> z"
proof
  show "nat \<bar>int (s x) - int (s x)\<bar> \<le> z" by auto
qed

lemma [simp]: "\<exists>y. nat \<bar>int (s x) + int z - int (s y)\<bar> \<le> z"
proof
  show "nat \<bar>int (s x) + int z - int (s x)\<bar> \<le> z" by auto
qed

lemma [simp]: "\<exists>y. nat \<bar>int (s x - z) - int (s y)\<bar> \<le> z" 
proof
  show "nat \<bar>int (s x - z) - int (s x)\<bar> \<le> z" by auto
qed

lemma exists_bigger_helper: "a \<le> b \<Longrightarrow> (\<exists>v2. nat \<bar>int (s' v1) - int (s v2)\<bar> \<le> a)
   \<Longrightarrow>  (\<exists>v2. nat \<bar>int (s' v1) - int (s v2)\<bar> \<le> b)"
  using le_trans by blast

lemma register_change_single_step_bound: "(c1, s1) \<rightarrow> (c2, s2) 
  \<Longrightarrow> (s2 v1 \<le> max_constant c1) \<or> (\<exists>v2. nat \<bar>(int (s2 v1)) - (int (s1 v2))\<bar> \<le> max_constant c1)"
proof (induction c1 s1 c2 s2 rule: small_step.induct[split_format(complete)])
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  have "s' v1 \<le> max_constant (c\<^sub>1 ;; c\<^sub>2) \<or> (\<exists>v2. nat \<bar>int (s' v1) - int (s v2)\<bar> \<le> max_constant c\<^sub>1)" 
    using Seq2 by auto
  then show ?case
  proof (elim disjE)
    assume "(\<exists>v2. nat \<bar>int (s' v1) - int (s v2)\<bar> \<le> max_constant c\<^sub>1)"
    moreover have *: "max_constant c\<^sub>1 \<le> max_constant (c\<^sub>1 ;; c\<^sub>2)" by auto
    ultimately show ?thesis using Seq2 exists_bigger_helper[OF *] by metis
  qed auto
qed (auto split: aexp.splits atomExp.splits) 

lemma register_change_bounded:
   "(c1, s1) \<rightarrow>\<^bsup>t\<^esup> (c2, s2) \<Longrightarrow> (s2 v1 \<le>  t * (max_constant c1)) \<or> 
             (\<exists>v2. nat \<bar>(int (s2 v1)) - (int (s1 v2))\<bar> \<le> t * (max_constant c1))"
proof (induction t arbitrary: c2 s2 v1)
  case (Suc t)
  then obtain c1' s1' where *: "((c1, s1) \<rightarrow>\<^bsup> t \<^esup> (c1', s1')) \<and> ((c1', s1') \<rightarrow> (c2, s2))"
    using rel_pow_Suc_E by (metis old.prod.exhaust)
  then have "(s2 v1 \<le>  max_constant c1') \<or> (\<exists>v2. nat \<bar>(int (s2 v1)) - (int (s1' v2))\<bar> \<le> max_constant c1')"
    using register_change_single_step_bound by blast
  then show ?case
  proof (elim disjE)
    assume "s2 v1 \<le> max_constant c1'"
    then show ?thesis using * execution_cant_increase_max_constant by fastforce
  next
    assume "\<exists>v2. nat \<bar>(int (s2 v1)) - (int (s1' v2))\<bar> \<le> max_constant c1'"
    then obtain v2 where v2_def: "nat \<bar>(int (s2 v1)) - (int (s1' v2))\<bar> \<le> max_constant c1'" by blast
    then have "s1' v2 \<le> t * max_constant c1 \<or>
      (\<exists>v3. nat \<bar>int (s1' v2) - int (s1 v3)\<bar> \<le> t * max_constant c1)" using Suc * by blast
    then show ?thesis
    proof (elim disjE)
      assume "s1' v2 \<le> t * max_constant c1"
      then show ?thesis using execution_cant_increase_max_constant * v2_def by fastforce
    next
      assume "\<exists>v3. nat \<bar>int (s1' v2) - int (s1 v3)\<bar> \<le> t * max_constant c1"
      moreover then obtain v3 where "nat \<bar>int (s1' v2) - int (s1 v3)\<bar> \<le> t * max_constant c1" by blast
      ultimately have "nat \<bar>int (s2 v1) - int (s1 v3)\<bar> \<le> (t + 1) * max_constant c1"  
        using execution_cant_increase_max_constant * v2_def by fastforce
      then show ?thesis by auto
    qed
  qed
qed auto

datatype domain_element = Num val | \<omega> 

definition domain :: "com \<Rightarrow> nat \<Rightarrow> domain_element list" where
"domain c t = (let m = max_constant c in map Num [0 ..<(2 * t * m + 1)]) @ [\<omega>]"

end