theory Bounds
  imports Bit_Length  "../IMP-/Big_StepT"  "../Polynomial_Growth_Functions"
begin
type_synonym bound_fun = "nat \<Rightarrow> nat" 
 definition time_bounded :: "com \<Rightarrow> bound_fun \<Rightarrow> bool" where
"time_bounded c p \<equiv> (\<forall>s. \<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> p (bit_length (s ''input'')))"

definition poly_time_bounded :: "com \<Rightarrow> bool" where
"poly_time_bounded c \<equiv> \<exists>p. poly p \<and> time_bounded c p"

end