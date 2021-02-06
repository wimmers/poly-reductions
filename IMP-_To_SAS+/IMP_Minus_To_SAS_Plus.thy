\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- to SAS+"

theory IMP_Minus_To_SAS_Plus
  imports "IMP-_To_IMP--/IMP_Minus_To_IMP_Minus_Minus" 
    "IMP--_To_SAS++/IMP_Minus_Minus_To_SAS_Plus_Plus_Correctness"
    "SAS++_To_SAS+/SAS_Plus_Plus_To_SAS_Plus"
    "IMP_Minus_Max_Constant"
begin

type_synonym SAS_problem = "(IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations.variable, 
  IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations.domain_element) problem" 

fun bit_length::"nat \<Rightarrow> nat" where
"bit_length  0 = 0" | 
"bit_length  n = 1 + bit_length (n div 2) "

definition max_input_bits:: "IMP_Minus_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"max_input_bits c I r = 
  bit_length (max (max (Max (ran I)) r) (IMP_Minus_Max_Constant.max_constant c))" 

definition IMP_Minus_to_SAS_Plus:: "IMP_Minus_com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> (vname \<rightharpoonup> nat) 
  \<Rightarrow>  nat \<Rightarrow> SAS_problem" where
"IMP_Minus_to_SAS_Plus c I r G t = (let 
  n = max_input_bits c I r ;
  I' = (\<lambda>x. Some (Num x)) \<circ>\<^sub>m I ;
  G' = (\<lambda>x. Some (Num x)) \<circ>\<^sub>m G in 
  SAS_Plus_Plus_To_SAS_Plus (imp_minus_minus_to_sas_plus (IMP_Minus_To_IMP_Minus_Minus c n) I' G' t))"

lemma IMP_Minus_to_SAS_Plus_correctness:
  assumes "finite (ran I)"
    "\<forall>s. \<exists>s2. \<exists>t' \<le> t. (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2"
  shows  "(\<exists>s1 s2 t'. I \<subseteq>\<^sub>m Some \<circ> s1 \<and> G  \<subseteq>\<^sub>m Some \<circ> s2 \<and> (c, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2)
    \<longleftrightarrow> (\<exists>plan. length plan \<le> 100 * (max_input_bits c I r) * (t - 1) + 100 + 

end