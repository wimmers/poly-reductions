\<^marker>\<open>creator Bilel Ghorbel\<close>
chapter \<open>Bounds for IMP- programs\<close>
paragraph \<open>Summary\<close>
text \<open>We define the necessary bounds for complexity theory.
There exists several types of bounds in the theory:

\<bullet> Time bounded programs
\<bullet> result bounded programs
\<bullet> valid certificate bounded programs
\<close>
theory Bounds
  imports Bit_Length Abstractions "../IMP-/Big_StepT"  "../Polynomial_Growth_Functions"
begin

paragraph \<open>Bounding functions\<close>
text \<open> We restrict/over-approximate the behaviour of our programs by defining
 an upper bound to the execution time/result etc. depending on the input size.
The upper bound function is hence nothing but a function over natural numbers (input size)
to natural numbers (time steps/result size/ certificate size)\<close>
type_synonym bound_fun = "nat \<Rightarrow> nat" 

subsection \<open>Time bounded programs\<close>
paragraph \<open>Definition\<close>
text \<open>We are only interested in programs that always terminate.
A program c is bounded by a function p, if it does always terminate AND the termination time t is 
always less than p(l). l being the input size.\<close>
definition time_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"time_bounded c p \<equiv> (\<forall>s. \<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> p (bit_length (s ''input'')))"

definition poly_time_bounded :: "com \<Rightarrow> bool" where
"poly_time_bounded c \<equiv> \<exists>p. poly p \<and> time_bounded c p"


paragraph \<open>verif_time_bounded ?\<close>
text \<open>An alternative where the input size depends on the size of both 
''input'' AND ''certificate'' registers.\<close>
definition verif_time_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where 
"verif_time_bounded v p \<equiv> (\<forall>s. \<exists>t s'. (v,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le>
                         p (bit_length (s ''input'')+ bit_length (s ''certificate'')))"

definition poly_verif_time_bounded :: "com \<Rightarrow> bool" where 
"poly_verif_time_bounded v \<equiv> \<exists>p. poly p \<and> verif_time_bounded v p"

subsection \<open>Result bounded programs \<close>
paragraph \<open>Definition\<close>
text \<open>We restrict our definition to programs whose output depend only on the ''input'' register.
That output/result is bounded by p(l) , l being the bitsize of the input.\<close>
definition result_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"result_bounded c p \<equiv> \<forall>x. \<exists>r. comp c x r \<and> bit_length r \<le> p (bit_length x)"

definition poly_result_bounded :: "com \<Rightarrow> bool" where
"poly_result_bounded c \<equiv> \<exists>p. poly p \<and> result_bounded c p"

paragraph \<open>2-register result\<close>
text \<open>The definition below is analogous to the previous one, with the exception that the
result of our program is distributed over 2 registers. Hence the result size is their combined
bit-sizes. \<close>
definition rev_verif_result_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where 
"rev_verif_result_bounded c p\<equiv> \<forall>r. \<exists>x z. rev_verif c x z r 
                            \<and> bit_length x + bit_length z \<le> p (bit_length r)"
definition poly_rev_verif_result_bounded :: "com \<Rightarrow> bool" where 
"poly_rev_verif_result_bounded c \<equiv> \<exists>p. poly p \<and> rev_verif_result_bounded c p"

subsection \<open>Bounded programs properties\<close>


paragraph \<open>From strict to less-strict \<close>
lemma comp_to_verif:
  assumes "poly_time_bounded c"
  shows "poly_verif_time_bounded c"
proof (auto simp add:poly_verif_time_bounded_def verif_time_bounded_def)
  obtain p where p_def: "poly p" "time_bounded c p" using assms poly_time_bounded_def by auto
  hence "poly (make_mono p)" using poly_make_mono_iff by simp
  moreover have "\<forall>s. \<exists>t. (\<exists>s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
                 t \<le> make_mono p (bit_length (s ''input'') + bit_length (s ''certificate''))"
  proof
    fix s::state
    let ?x = "s ''input''"
    let ?z = "s ''certificate''"
    obtain s' t where defs: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s'" "t \<le> p (bit_length ?x) " 
      using p_def(2) time_bounded_def by metis
    hence " t\<le> make_mono p (bit_length ?x + bit_length ?z)" using mono_make_mono
      by (meson incseq_def le_add1 le_make_mono le_trans)
    thus "\<exists>t. (\<exists>s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
                 t \<le> make_mono p (bit_length ?x  + bit_length ?z )" using defs(1)  by blast
  qed
  ultimately show "\<exists>p. poly p \<and>
        (\<forall>s. \<exists>t. (\<exists>s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
                 t \<le> p (bit_length (s ''input'') + bit_length (s ''certificate'')))"
    by blast
qed

paragraph \<open>Sequencing two polynomialy time-bounded programs \<close>
text \<open>The lemmas are self-explanatory. They will be used to prove propertied on P, NP AND 
polynomial reductions\<close>
lemma reduction_poly:
  assumes "poly_time_bounded f" "poly_time_bounded g"  "poly_result_bounded f"
  shows "poly_time_bounded (f;;g)"
  apply (simp add:poly_time_bounded_def time_bounded_def)
proof -
  from assms(1) obtain pf where pf_props:"poly pf" "time_bounded f pf" 
    using poly_time_bounded_def by blast
  from assms(2) obtain pg where pg_props:"poly pg" "time_bounded g pg"
    using poly_time_bounded_def by blast
  from assms(3) obtain pd  where pd_props: "poly pd" "\<forall>x. \<exists>r. comp f x r \<and> bit_length r \<le> pd (bit_length x) "
    using poly_result_bounded_def result_bounded_def by auto
  show "\<exists>p. poly p \<and> (\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> p (bit_length (s ''input''))) "
  proof -
    let ?p = "\<lambda>x. pf x + (make_mono pg o pd) x"
    have "poly ?p"
      using poly_add pf_props(1) pg_props(1) poly_compose pd_props(1) poly_make_mono_iff by metis   
    moreover have "\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (bit_length (s ''input''))" 
    proof
      fix s
      show "\<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (bit_length (s ''input''))" 
      proof -
      obtain s1 t1 where stepf:"(f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s1" "t1 \<le> pf (bit_length(s ''input''))"
        using pf_props(2)  by (simp add: time_bounded_def) blast
       obtain s2 t2 where stepg:"(g,s1) \<Rightarrow>\<^bsup> t2 \<^esup> s2" "t2 \<le> pg (bit_length (s1 ''input''))"
         using pg_props(2)  by (simp add: time_bounded_def) blast
       let ?x = "s ''input''"
       obtain r where r_props: "comp f ?x r" "bit_length r \<le> pd (bit_length ?x)" using pd_props(2) by auto
       have "s1 ''input'' = r"
         by (metis (no_types, lifting) bigstepT_the_state fun_upd_same r_props(1) comp_def stepf(1))
       hence "t2 \<le> pg(bit_length  r)" using stepg(2) by simp
       hence "t2 \<le> make_mono pg (bit_length r)" using le_trans by blast
       moreover have "make_mono pg (bit_length r) \<le> make_mono pg (pd (bit_length ?x))"
         using r_props(2) mono_make_mono[of pg] incseq_def  by blast
       ultimately have t2_ineq: "t2 \<le> (make_mono pg o pd)(bit_length ?x)" by fastforce
       hence "(f;;g,s) \<Rightarrow>\<^bsup> t1+t2 \<^esup> s2"  "t1+t2 \<le> pf (bit_length ?x) + (make_mono pg o pd) (bit_length ?x)"
         using stepf(1) stepg (1) apply blast
          using add_mono stepf(2) t2_ineq by blast
      thus "?thesis" by blast 
    qed 
  qed
  ultimately show ?thesis by auto 
qed
qed

lemma verif_reduction_poly : 
  assumes "poly_time_bounded f" "cons_certif f"  "poly_result_bounded f" "poly_verif_time_bounded g"
  shows "poly_verif_time_bounded (f;;g)"
proof (auto simp add: poly_verif_time_bounded_def verif_time_bounded_def)
  obtain pf where pf_props: "poly pf " "time_bounded f pf" using assms(1) poly_time_bounded_def by blast
  obtain pg where pg_props:"poly pg"  "verif_time_bounded g pg"
    using assms(4) poly_verif_time_bounded_def by blast
  obtain pd where pd_props:"poly pd" "result_bounded f pd" using assms(3) poly_result_bounded_def by blast
  let ?p= "\<lambda>x. make_mono pf x + make_mono pg  (make_mono pd x  + x)"
  have  "poly (\<lambda>x. make_mono pd x  + x)"
    using poly_add  pd_props(1) poly_make_mono_iff poly_linear by simp
  hence "poly(make_mono pg o (\<lambda>x. (make_mono pd x  + x)))"
    using pg_props poly_compose poly_make_mono_iff by simp
  moreover have "poly (make_mono pf)" using pf_props(1) poly_make_mono_iff by fast
  ultimately have "poly ?p"
     using poly_add by force  
   moreover have "\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
                 t \<le> ?p (bit_length (s ''input'') + bit_length (s ''certificate''))"
   proof
     fix s::state
     obtain x z where  xz_def:"x = s ''input''" "z = s ''certificate''" by simp
     then obtain sf tf where f_def: "(f,s)\<Rightarrow>\<^bsup> tf \<^esup> sf"  "tf \<le> pf (bit_length x) "
       using pf_props(2) time_bounded_def by blast
     obtain y where y_def:"comp f x y" "bit_length y \<le> pd (bit_length x)"
       using result_bounded_def pd_props(2) by blast
     then have registers: "sf ''input''  = y" "sf ''certificate'' = z" using comp_def xz_def(1) f_def(1) big_step_t_determ2 try0
        apply metis
       using assms(2) cons_certif_def xz_def(2) f_def(1) by metis
     obtain  sg tg where g_def: "(g,sf)\<Rightarrow>\<^bsup> tg \<^esup> sg" "tg \<le> pg(bit_length y + bit_length z)"
       using pg_props(2) verif_time_bounded_def registers by blast
       have "tg \<le> make_mono pg( make_mono pd (bit_length x) + bit_length z) "
          using y_def(2) g_def(2) mono_make_mono
          by (meson add_right_mono incseq_def le_make_mono le_trans)
        moreover have "make_mono pd (bit_length x) + bit_length z \<le>  make_mono pd (bit_length x + bit_length z) + bit_length z"
          using  mono_make_mono  by (simp add: monoD)
        ultimately have "tg \<le> make_mono pg( make_mono pd (bit_length x + bit_length z) + bit_length z) "
          using mono_make_mono
          by (smt mono_def order_subst1)
        then have "tg \<le> make_mono pg( make_mono pd (bit_length x + bit_length z) + bit_length x + bit_length z)"
          using mono_make_mono
          by (smt Groups.add_ac(2) Groups.add_ac(3) incseq_def le_add1 le_trans)
        then have "tf + tg \<le>make_mono pf (bit_length x + bit_length z)+ make_mono pg( make_mono pd (bit_length x + bit_length z) + bit_length x + bit_length z) "
          using mono_make_mono
          by (metis add_mono f_def(2) incseq_def le_add1 le_make_mono le_trans)
        hence "tf +tg \<le> ?p (bit_length x + bit_length z)"
          by (simp add: add.assoc) 
        moreover have "(f;;g,s)\<Rightarrow>\<^bsup> tf+tg \<^esup> sg" using g_def(1) f_def(1) by fast
        ultimately show "\<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
                 t \<le> ?p (bit_length (s ''input'') + bit_length (s ''certificate''))"  using xz_def 
          by fast  
      qed
      ultimately show "\<exists>p. poly p \<and>
        (\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
                 t \<le> p (bit_length (s ''input'') + bit_length (s ''certificate''))) " by blast
qed

lemma rev_verif_bounds:
  assumes "poly_time_bounded f" "poly_rev_verif_result_bounded f" "poly_verif_time_bounded g"
  shows "poly_time_bounded (f;;g)"
proof (auto simp add:poly_time_bounded_def time_bounded_def)
  obtain pf where pf_def:"poly pf" "time_bounded f pf" using assms(1) poly_time_bounded_def by blast
  obtain pd where pd_def:"poly pd" "rev_verif_result_bounded f pd"
    using assms(2) poly_rev_verif_result_bounded_def by blast
  obtain pg where pg_def:"poly pg" "verif_time_bounded g pg" 
    using assms(3) poly_verif_time_bounded_def by blast
  let ?p= "(\<lambda>x. pf x + (make_mono pg o pd) x )"
  have "poly ?p"  using pf_def(1) pg_def(1) pd_def(1) poly_add poly_compose poly_make_mono_iff 
    by presburger
  moreover have "(\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (bit_length (s ''input'')))"
  proof
    fix s::state
    obtain tu where tu_def: " tu = s ''input''" by simp
    then obtain tf sf where tsf_def: "(f,s)\<Rightarrow>\<^bsup> tf \<^esup> sf" "tf \<le> pf (bit_length tu)" 
      using pf_def(2) time_bounded_def by blast
    obtain x z where xz_def: "rev_verif f x z tu" "bit_length x + bit_length z \<le> pd (bit_length tu)"
      using pd_def(2) rev_verif_result_bounded_def by meson
    have "sf ''input'' = x"  "sf ''certificate'' = z" 
      using xz_def(1)  tsf_def(1) big_step_t_determ2  rev_verif_def tu_def apply metis
      using xz_def(1)  tsf_def(1) big_step_t_determ2  rev_verif_def tu_def by smt
    then obtain tg sg where tsg_def: "(g,sf)\<Rightarrow>\<^bsup> tg \<^esup> sg" "tg \<le> pg(bit_length x + bit_length z)"
      using pg_def(2) verif_time_bounded_def by blast
    hence "tg \<le> (make_mono pg o pd) (bit_length tu)" using xz_def(2) mono_make_mono
      by (metis comp_apply incseq_def le_make_mono le_trans)
    hence "tf + tg \<le> ?p (bit_length tu)" using tsf_def(2) by fastforce
    moreover have "(f;; g, s) \<Rightarrow>\<^bsup> tf+tg \<^esup> sg" using tsf_def(1) tsg_def(1) by fast
    ultimately show "\<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (bit_length (s ''input''))" 
      using tu_def by blast
  qed
  ultimately show "\<exists>p. poly p \<and> (\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> p (bit_length (s ''input'')))"
    by blast
qed


subsection \<open>Valid certificate bounds\<close>
paragraph \<open>Definition\<close>
text \<open>
Given a program c AND an input x, a valid certificate z is a certificate for which the verifier c,
will return 0.
p is valid-certificate-bounded iff for every input x that has a corresponding valid certificate,
there EXISTS a valid certificate limited by p(l), l being the input size (''input'' register)
\<close>
definition certif_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where 
"certif_bounded c p \<equiv> \<forall>x. (\<exists>z. verif c x z 0)
                             \<longrightarrow> (\<exists>z. verif c x z 0 \<and> bit_length z \<le> p (bit_length x))"

definition poly_certif_bounded :: "com \<Rightarrow> bool" where 
"poly_certif_bounded c \<equiv> \<exists>p. poly p \<and> certif_bounded c p "

subsection \<open>Properties: Effects of sequencing over certifcate- AND result-bounded programs\<close>
paragraph \<open>Sequencing two valid-certificate-bounded programs\<close>
lemma result_bounded_certif_bounded : 
  assumes "result_bounded f q" "cons_certif f" "certif_bounded g p" "\<forall>y z. \<exists>r. verif g y z r "
  shows "certif_bounded (f;;g) (make_mono p o q)"  
proof (auto simp add: certif_bounded_def)
  fix x z
  assume local_asm:"verif (f;; g) x z 0" 
  from assms(1) obtain y where y_def: "comp f x y" "bit_length y \<le> q (bit_length x)" using result_bounded_def by blast
  from assms(4) obtain r where r'_def: "verif g y z r"  using certif_bounded_def by presburger
  moreover from y_def(1) r'_def assms(2) have "verif (f;; g) x z r" using comp_verif by simp
  hence  "r = 0" using local_asm verif_det by blast
  ultimately obtain z'  where  z'r'_def: " verif g y z' 0" "bit_length z' \<le> p (bit_length y)"
    using assms(3) certif_bounded_def by blast
  from z'r'_def(2) have "bit_length z' \<le> make_mono p (bit_length y)"
    using le_trans less_imp_le_nat by blast
  moreover have "make_mono p (bit_length y) \<le> make_mono p (q (bit_length x))"
    using y_def(2) mono_make_mono by (simp add: incseqD)
  ultimately have "bit_length z' \<le>  make_mono p (q (bit_length x)) " by simp
  moreover from z'r'_def(1) y_def(1) assms(2) have "verif (f;;g) x z' 0" using comp_verif by blast
  ultimately show "\<exists>z. verif (f;; g) x z 0 \<and> bit_length z \<le> make_mono p (q (bit_length x))"
    using z'r'_def(2) by blast
qed

lemma poly_result_bounded_poly_certif_bounded:
  assumes "poly_result_bounded f" "cons_certif f" "poly_certif_bounded g" "\<forall>y z. \<exists>r. verif g y z r "
  shows "poly_certif_bounded (f;;g)"
proof (auto simp add: poly_certif_bounded_def)
  
  show "\<exists>p. poly p \<and> certif_bounded (f;; g) p "
  proof - 
    from assms(1) obtain q where q_def: "poly q" "result_bounded f q" using poly_result_bounded_def
      by blast
    from  assms(3) obtain p where p_def: "poly p" "certif_bounded g p" using poly_certif_bounded_def
      by meson
    let ?p = "make_mono p o q"
    from q_def(1) p_def(1) have "poly ?p" 
      by (simp add: poly_compose poly_make_mono_iff)
    moreover have "certif_bounded (f;;g) ?p" using q_def(2) p_def(2) assms(2) assms(4) 
     result_bounded_certif_bounded by simp
    ultimately show ?thesis by blast
  qed
qed

paragraph \<open>Sequencing two result-bounded programs\<close>
lemma result_bounded_compose:
  assumes "result_bounded f pf" "result_bounded g pg"
  shows "result_bounded (f;;g) (make_mono pg o pf)"
  apply(auto simp add:result_bounded_def)
proof -
  fix x 
  obtain y z
   where yz_def:"comp f x y" "comp g y z" "bit_length y \<le> pf (bit_length x)" "bit_length z \<le> pg(bit_length y)"
   using assms result_bounded_def by blast
  hence  "comp (f;;g) x z" using comp_comp by simp
  moreover have  "bit_length z \<le> make_mono pg (bit_length y)" using yz_def(4) le_trans by blast 
  hence  " bit_length z \<le> make_mono pg (pf (bit_length x))"
    using yz_def mono_make_mono  le_trans monoD by blast
 ultimately show "\<exists>r. comp (f;; g) x r \<and> bit_length r \<le> make_mono pg (pf (bit_length x))" by auto
qed


lemma poly_result_compose : 
  assumes "poly_result_bounded f" "poly_result_bounded g"
  shows "poly_result_bounded (f;;g)"
   proof -
    obtain pf pg where pf_pg_def: "poly pf" "poly pg " "result_bounded f pf" "result_bounded g pg" 
      using assms poly_result_bounded_def by auto
    have "poly (make_mono pg o pf)" 
      by (simp add: pf_pg_def(1) pf_pg_def(2) poly_compose poly_make_mono_iff)
    moreover have "result_bounded (f;;g) (make_mono pg o pf)"
      using result_bounded_compose pf_pg_def by auto
    ultimately show ?thesis by (auto simp add:poly_result_bounded_def)
  qed

end