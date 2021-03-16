\<^marker>\<open>creator Bilel Ghorbel\<close>
chapter \<open>Abstractions over IMP-\<close>
paragraph \<open>Summary\<close>
text \<open>We define an abstraction layer over our computation model 
      to be able to define complexity classes easily.

The theory contains definitions of e.g. computing, verifying w.r.t IMP- 
\<close>
theory Abstractions
  imports  "../IMP-/Big_StepT"
begin
paragraph \<open>Definitions\<close>
text \<open>
\<bullet> Formal Languages
\<bullet> Computing a certain result for a certain input
\<bullet> Verifying a certain certificate for a certain value with a specific result
\<bullet> Conserving a certificate
\<bullet> Decider program for a language
\<bullet> Verifier program for a language
\<close>
paragraph \<open>Formal Languages\<close>
text \<open>In IMP- we work on natural numbers.
      Hence words are actually natural numbers instead of sequences of symbols
      and formal languages as sets of them
      This is admissible due to the existence of bijections 
      between natural numbers and symbol sequences \<close>
type_synonym lang = "nat set"

paragraph \<open>Register conventions\<close>
text \<open>
\<bullet> The input for a program (indepentently of its purpose e.g: 
computing a function, decision, verification) is expected to be in the register called ''input''
\<bullet> The certificate (if needed) is expected to be found in the register ''certificate''
\<bullet> The output/result/main result is expected to be found in the same register as the input.
This allows to easily compose to obtain computing code of the composition of computable functions
just by sequencing their computing codes
\<bullet> If not otherwise mentioned, the input is strictly the inital content of the ''input'' register.
In some particular contexts in the theory, we might consider the certificate as second input.
But this will be explicitly mentioned.
\<close>
paragraph \<open>Certificate conserving\<close>
text \<open>The code always terminates with a final state that 
has the same certificate register content as the initial state.\<close> 
definition cons_certif :: "com \<Rightarrow> bool" where
"cons_certif c = (\<forall>s t s'. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')"

subsection \<open>Computing\<close>
paragraph \<open>Definition\<close>
text \<open>A code c computes for an input x a result r if it always terminates with the result r 
given the initial input is x.\<close>

definition comp :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"comp c x r \<equiv> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = r ))"

text \<open>Using computation, every code defines a binary relation between inputs and results.
We could say that `comp c` is the computed relation of the code c.
\<close>


paragraph \<open>Computing determinism\<close>
text \<open>Thanks to the determinism of IMP-, computed relations are deterministic.
i.e. every code c computes for every input x either exactly one result, or no result

You can think also of it as, that, comp c, the computed relation for every fixed code c,
is a partial function\<close>
lemma comp_det: "\<lbrakk>comp c x r ; comp c x r'\<rbrakk> \<Longrightarrow> r= r'"
proof -
  assume asm1:"comp c x r"
  assume asm2:"comp c x r'"
  from asm1 obtain s1 where s1_def: "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> s1" "s1 ''input'' =r" 
    by (metis fun_upd_same comp_def)
  moreover from asm2 obtain s2 where s2_def: "\<exists>t. (c, <''input'':=x>) \<Rightarrow>\<^bsup>t\<^esup> s2 " "s2 ''input''=r'" 
    by (metis fun_upd_same fun_upd_upd comp_def)
  ultimately have "s1 = s2"
    by (meson bigstep_det fun_upd_eqD)
  thus "r=r'" using s1_def s2_def by simp
qed

paragraph \<open>Computing: composition and sequencing\<close>
text \<open> By sequencing two codes, we compose the computed partial functions.\<close>
lemma comp_comp:
  assumes "comp f x y" "comp g y z"
  shows "comp (f;;g) x z"
  apply (simp add:comp_def)
  proof 
  fix s
  show "s ''input'' = x \<longrightarrow>(\<exists>t s'. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = z)"
  proof
    assume asmX:"s ''input'' = x"
    from assms(1) obtain s' where s'_def: "\<exists>t1. (f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s'" "s' ''input''= y"
      using comp_def asmX by blast    
    moreover  obtain s'' where s''_def:  "\<exists>t2. (g,s') \<Rightarrow>\<^bsup> t2 \<^esup> s''" "s'' ''input''=z"
      using assms(2) comp_def s'_def(2) by blast
    ultimately have "(\<exists>t. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup>s'')" by auto
    thus "(\<exists>t s'. (f;; g, s)\<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = z)" using s''_def(2)  by auto  
  qed
qed

text \<open>The property is uni-directional. i.e: comp g o comp f \<subseteq> comp (f;;g) \<close>
(*We could prove it actually! How does relation composition work*)

subsection \<open>Decision problems\<close>
paragraph \<open>Convention\<close>
text \<open>Decision programs are programs that compute a boolean logical result 
(hence a decision) given an input.
IMP- does only support natural number values. But we can make our own interpretation of the result
r::nat as a boolean value. 

Theoretically, every predicate in HOL over the result r is an admissible interpretation.
Yet we choose the following convention from now on:
\<bullet> the result r is interpreted as True iff. r = 0

This convention goes in sync with our semantics that check for equality to 0 exclusively 
for branching conditions.

Generally programming languages tend to interpret non-zero values as True rather than zero.
Yet this a design choice since the negation could be implemented using a constant time program.
To avoid complications for proving Cook-Levin, we use 0 for True and non-zero values for False 
\<close>

paragraph \<open>Deciding a language: definition\<close>
text \<open>A decider for a language L should for every input x, compute a unique result (otherwise 
it is depending on other variables).

The result/decision is True iff x \<in> L .\<close>
definition decides :: "com \<Rightarrow> lang \<Rightarrow> bool"
  where "decides c L  \<equiv> (\<forall>x. \<exists>r. comp c x r \<and> ( x\<in>L \<longleftrightarrow> r = 0))" 

subsection \<open>Verification\<close>
paragraph \<open>Definition\<close>
text \<open>In contrast to computing, verifying is about checking the correspondence 
of a certificate to some input and returns some result.

Differently to some literature, we do not restrict the result to a 2-value domain.
A result of a verification could be any value (to be interpreted as Boolean as mentioned before
if needed).
Hence a verification could be regarded as a 2-parameter computation.
 i.e. a computation returning a result depending on both input and certificate, not just input.
The formal definition is totally analogous.
Every code forms a ternary relation.\<close>
definition verif :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"verif c x z r \<equiv> (\<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                  (\<exists>t s'. (c,s)\<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = r ))"


paragraph \<open>Verification determinism\<close>
text \<open>Analogously to computing, verifying is determinstic\<close>
lemma verif_det:
  assumes "verif f x z r" "verif f x z r'"
  shows "r = r'"
proof -
  obtain s where "s =<''input'':=x,''certificate'':=z>" by simp
  hence s_def: "s ''input'' = x \<and> s ''certificate'' = z" by simp
  obtain s1 where s1_def:  "\<exists>t. (f,s)\<Rightarrow>\<^bsup>t\<^esup>s1" "s1 ''input'' = r" 
    using assms(1) s_def verif_def by blast
   moreover obtain s2 where s2_def:  "\<exists>t. (f,s)\<Rightarrow>\<^bsup>t\<^esup>s2" "s2 ''input'' = r'" 
    using assms(2) s_def verif_def by blast
  ultimately show  "r=r'"  using big_step_t_determ2 by blast   
qed

paragraph \<open>Sequencing computation and verification\<close>
text \<open>Sequencing a computation and verification gives a verification.
Analogously to composing two compuations, the composition of a computation's and a verification's 
relation is a subset of the relation of their sequenced codes.\<close>
lemma comp_verif:
  assumes "comp f x y" "verif g y z r" "cons_certif f"
  shows "verif (f;;g) x z r"
  apply(simp add: verif_def comp_def)
proof
  fix s
  show " s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
             (\<exists>t s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)" 
  proof
    assume asm:" s ''input'' = x \<and> s ''certificate'' = z"
    then obtain s' t1 where s'_def:"(f,s)\<Rightarrow>\<^bsup>t1\<^esup> s'" "s' ''input'' = y" "s' ''certificate'' =z" 
      using assms(1) assms(3) comp_def asm cons_certif_def by metis 
    moreover obtain s'' t2 where "(g,s')\<Rightarrow>\<^bsup>t2\<^esup> s''" " s'' ''input'' = r"
        using assms(2) verif_def s'_def  by auto
    ultimately have  "(f;;g,s)\<Rightarrow>\<^bsup> t1+t2 \<^esup>  s'' \<and> s'' ''input''=r " by auto
    thus "(\<exists>t s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r) " by auto
  qed
qed

lemma verif_comp: 
  assumes "verif v x z r"
  assumes "comp f r r'"
  shows "verif (v;;f) x z r' "
  apply(simp add:verif_def)
proof 
  fix s
  show "s ''input'' = x \<and> s ''certificate'' = z
           \<longrightarrow> (\<exists>t s'. (v;; f, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r')"
  proof
    assume " s ''input'' = x \<and> s ''certificate'' = z"
    then obtain s1 t1 where def1:"(v,s) \<Rightarrow>\<^bsup> t1 \<^esup> s1" "s1 ''input''=r" 
      using assms(1) verif_def by blast
    then obtain s2 t2 where def2: "(f,s1)\<Rightarrow>\<^bsup> t2 \<^esup> s2" "s2 ''input''=r'"
      using assms(2) comp_def by blast
    show "\<exists>t s'. (v;; f, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r'" using def1 def2 by blast
  qed
qed
subsection \<open>Verifier programs\<close>
paragraph \<open>Definition\<close>
text \<open>After defining verification on the word/natural number level. We define verification on 
the language level.

A verifier for a language L should return a unique verification result/decision r 
for every combination of input x and certificate z.
This result should say whether this certificate z 
is valid for that input x.(result is to be interpreted as a boolean)

Every input x has at least one corresponding valid certificate iff. x \<in> L\<close>


definition is_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_verif c L  \<equiv> (\<forall>x z. \<exists>r. verif c x z r) \<and> (\<forall>x. (x\<in>L \<longleftrightarrow> (\<exists>z. verif c x z 0))) "


subsection \<open>Reverse verification\<close>

paragraph \<open>Motivation\<close>
text \<open>Although not a common term in computation theory. Reverse modification is useful later 
to define NP using P.
\<close>

paragraph \<open>Definition\<close>
text \<open>In reverse verification, rev_verif c x z r means that code c will always return
 x in input and z in certificate if fed r in input.

 Since it is generally used simultaneously to verif. We kept the same order of the arguments\<close>

definition rev_verif:: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where 
"rev_verif c x z r \<equiv>  (\<forall>s. s ''input'' = r \<longrightarrow> 
                   (\<exists>t s'.(c,s)\<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = x \<and> s' ''certificate''= z ))"

paragraph \<open>Determinism\<close>
text \<open>Same as before\<close>
lemma rev_verif_det: 
  assumes "rev_verif c x z r" 
  assumes "rev_verif c x' z' r"
  shows "x=x' \<and> z=z'"
proof -
  obtain s where "s = <''input'' := r>" by auto
  hence r_def: "s ''input'' = r" by auto
  obtain s1 where s1_def:"\<exists>t. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s1" "s1 ''input'' = x" "s1 ''certificate'' = z"
    using assms(1) rev_verif_def r_def by blast
  obtain s2 where s2_def:"\<exists>t. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s2" "s2 ''input'' = x'" "s2 ''certificate'' = z'" 
    using assms(2)rev_verif_def r_def by blast
  from s1_def s2_def Big_StepT.big_step_t_determ2 show "x=x' \<and> z=z'" by blast
qed

paragraph \<open>Compostion properties\<close>
lemma verif_rev_verif:
  assumes "rev_verif c1 x z r0"
  assumes "verif c2 x z r"
  shows "comp (c1;;c2) r0 r" 
proof (auto simp add:comp_def verif_def rev_verif_def)
  fix s
  assume "r0 = s ''input''"
  then obtain t1 s1 where def1:"(c1,s)\<Rightarrow>\<^bsup> t1 \<^esup> s1" " s1 ''input'' = x" "s1 ''certificate'' = z"
    using assms(1) by (auto simp add:rev_verif_def)
  then obtain t2 s2 where def2:"(c2,s1)\<Rightarrow>\<^bsup> t2 \<^esup> s2" "s2 ''input'' = r"
    using assms(2) by (auto simp add:verif_def)
  from def1 def2 have "(c1;;c2,s)\<Rightarrow>\<^bsup> t1+t2 \<^esup> s2 " by blast
  then show  "\<exists>t s'. (c1;; c2, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r" using def2(2) by blast
qed 

  

end