theory Abstractions
  imports  "../IMP-/Big_StepT"
begin
type_synonym lang = "nat set"

definition cons_certif :: "com \<Rightarrow> bool" where
"cons_certif c = (\<forall>s t s'. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')"

definition comp :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"comp c x r \<equiv> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = r ))"


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

definition computedFun :: "com \<Rightarrow> nat \<Rightarrow> nat" where 
"computedFun c x \<equiv> THE r. comp c x r "
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


definition decides :: "com \<Rightarrow> lang \<Rightarrow> bool"
  where "decides c L  \<equiv> (\<forall>x. \<exists>r. comp c x r \<and> ( x\<in>L \<longleftrightarrow> r = 0))" 

definition verif :: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"verif c x z r \<equiv> (\<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                  (\<exists>t s'. (c,s)\<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = r ))"
definition rev_verif:: "com \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where 
"rev_verif c x z r \<equiv>  (\<forall>s. s ''input'' = r \<longrightarrow> 
                   (\<exists>t s'.(c,s)\<Rightarrow>\<^bsup>t\<^esup> s' \<and> s' ''input'' = x \<and> s' ''certificate''= z ))"
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

definition is_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_verif c L  \<equiv> (\<forall>x z. \<exists>r. verif c x z r) \<and> (\<forall>x. (x\<in>L \<longleftrightarrow> (\<exists>z r. verif c x z r \<and> r = 0))) "
  

end