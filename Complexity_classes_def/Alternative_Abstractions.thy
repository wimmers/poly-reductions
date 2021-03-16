theory Alternative_Abstractions
  imports  "../IMP-/Big_StepT"
begin

type_synonym lang = "nat set"

definition cons_certif :: "com \<Rightarrow> bool" where
"cons_certif c = (\<forall>s t s'. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')"

definition comp :: "com \<Rightarrow> vname list \<Rightarrow> val list \<Rightarrow> vname list \<Rightarrow> val list \<Rightarrow> bool" where
"comp c inputNames inputVals resultNames resultVals \<equiv> 
    distinct inputNames \<and>
    length inputNames = length inputVals \<and>
    (\<forall>s. map s inputNames = inputVals \<longrightarrow> 
                      (\<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> map s' resultNames = resultVals ))"

fun state_maker :: "vname list \<Rightarrow> val list \<Rightarrow> state \<Rightarrow> state" where 
"state_maker [] [] s = s"|
"state_maker (v#vs) (x#xs) s = state_maker vs xs (s (v:=x))"

lemma state_maker_works_helper:
  "\<lbrakk>v \<notin> set vs; length vs = length xs \<rbrakk> \<Longrightarrow>  state_maker vs xs (sa(v := x)) v = x "
  by(induction vs xs sa arbitrary: v x rule:state_maker.induct)
    (auto simp add: fun_upd_twist)
      
lemma state_maker_works:
  assumes "distinct vs"
  assumes "length xs = length vs"
  assumes "s' = state_maker vs xs s"
  shows "map s' vs = xs"
  using assms
  by (induction  vs xs s rule:state_maker.induct)  (auto simp add: state_maker_works_helper)
      

     
     


lemma comp_det: 
  assumes "comp c input xs result rs" "comp c input xs result rs'"
  shows "rs = rs'"
  using assms
proof -
  assume asm:"comp c input xs result rs" "comp c input xs result rs'"
  obtain s where s_def: "s = state_maker input xs <>" by blast
  have s_prop:"map s input = xs" using s_def asm(1) comp_def state_maker_works by simp
  obtain s1 where s1_def : "\<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s1" "map s1 result =rs"
    using asm(1) s_prop comp_def by metis
  obtain s2 where s2_def : "\<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s2" "map s2 result =rs'"
    using asm(2) s_prop comp_def by metis 
  have "s1 = s2" using s1_def(1) s2_def(1) big_step_t_determ2 by blast
  thus "rs = rs'" using s1_def(2) s2_def(2) by simp
qed

lemma comp_comp:
  assumes "comp f nxs xs nys ys" "comp g nys ys nzs zs"
  shows "comp (f;;g) nxs xs nzs zs"
proof (auto simp add:comp_def)
  show "distinct nxs" using assms(1) comp_def by auto
next
  show "length nxs = length xs"  using assms(1) comp_def by auto
next
  fix s
  assume asm:" xs = map s nxs"
  obtain tf sf where tsf_def: "(f, s) \<Rightarrow>\<^bsup> tf \<^esup> sf" "map sf nys = ys"
    using assms(1) comp_def asm by auto
  obtain tg sg where tsg_def: "(g, sf) \<Rightarrow>\<^bsup> tg \<^esup> sg" "map sg nzs = zs" 
    using assms(2) comp_def tsf_def(2) by blast
  have " (f;; g, s) \<Rightarrow>\<^bsup> tf+tg\<^esup> sg" using tsf_def(1) tsg_def(1) by blast
  thus "\<exists>t s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> map s' nzs = zs " using tsg_def(2) by blast
qed
end

  
