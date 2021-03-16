theory Alternative_Bounds
  imports Bit_Length  Alternative_Abstractions "../IMP-/Big_StepT"  "../Polynomial_Growth_Functions"
begin
type_synonym bound_fun = "nat \<Rightarrow> nat"
fun bit_size :: "val list \<Rightarrow> nat" where
"bit_size [] = 0"|
"bit_size (l#ls) = bit_length l + bit_size ls"

definition time_bounded :: "com \<Rightarrow> vname list \<Rightarrow> bound_fun \<Rightarrow> bool" where
"time_bounded c l p \<equiv> (\<forall>s. \<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> t \<le> p (bit_size (map s l)))"

definition poly_time_bounded :: "com \<Rightarrow> vname list \<Rightarrow> bool" where 
"poly_time_bounded c l \<equiv> \<exists>p. poly p \<and> time_bounded c l p"

definition result_bounded :: "com \<Rightarrow> vname list \<Rightarrow> vname list \<Rightarrow> bound_fun \<Rightarrow> bool" where
"result_bounded c input output p \<equiv> \<forall>x. \<exists>r. comp c input x output r \<and>
                                               bit_size r  \<le> p (bit_size x)"
definition poly_result_bounded :: "com \<Rightarrow> vname list \<Rightarrow> vname list \<Rightarrow> bool" where
"poly_result_bounded c input output \<equiv> \<exists>p. poly p \<and> result_bounded c input output p"

lemma reduction_poly:
  assumes "poly_time_bounded f nxs" "poly_time_bounded g nys"  "poly_result_bounded f nxs nys"
  shows "poly_time_bounded (f;;g) nxs"
  proof (simp add:poly_time_bounded_def time_bounded_def)
  from assms(1) obtain pf where pf_props:"poly pf" "time_bounded f nxs pf" 
    using poly_time_bounded_def by blast
  from assms(2) obtain pg where pg_props:"poly pg" "time_bounded g nys pg"
    using poly_time_bounded_def by blast
  from assms(3) obtain pd  where pd_props: "poly pd" "\<forall>x. \<exists>r. comp f nxs x nys r \<and>
                                                     bit_size r \<le> pd (bit_size x) "
    using poly_result_bounded_def result_bounded_def by auto
  let ?p = "\<lambda>x. pf x + (make_mono pg o pd) x"
  have "poly ?p"
    using poly_add pf_props(1) pg_props(1) poly_compose pd_props(1) poly_make_mono_iff by metis
  moreover have "\<forall>s. \<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and> t \<le> ?p (bit_size (map s nxs))"
  proof
    fix s
    obtain x::"val list" where x_def: "x = map s nxs" by blast
    then obtain sf tf where stepf:"(f,s) \<Rightarrow>\<^bsup> tf \<^esup> sf" "tf \<le> pf (bit_size x)"
        using pf_props(2)  by (simp add: time_bounded_def) blast
    obtain y where stepd: "comp f nxs x nys y" "bit_size y \<le> pd (bit_size x)" using pd_props(2)
        by auto
      then obtain s1 t1 where step':"(f,s) \<Rightarrow>\<^bsup> t1 \<^esup> s1" "map s1 nys = y" using comp_def x_def 
        by blast
      hence "map sf nys = y" using stepf(1) big_step_t_determ2 by blast
      then obtain  sg tg where g_def: "(g,sf)\<Rightarrow>\<^bsup> tg \<^esup> sg" "tg \<le> pg(bit_size y)"
        using pg_props(2) time_bounded_def by blast
       hence "tg \<le> make_mono pg (bit_size y)" using le_trans by blast
       moreover have "make_mono pg (bit_size y) \<le> make_mono pg (pd (bit_size x))"
         using stepd(2) mono_make_mono[of pg] incseq_def  by blast
       ultimately have t2_ineq: "tg \<le> (make_mono pg o pd)(bit_size x)" by fastforce
       hence "(f;;g,s) \<Rightarrow>\<^bsup> tf+tg \<^esup> sg" 
          "tf+tg \<le> pf (bit_size x) + (make_mono pg o pd) (bit_size x)"
        using stepf(1) g_def (1) apply blast
        using add_mono stepf(2) t2_ineq by blast
      thus "\<exists>t. (\<exists>s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s') \<and>
             t \<le> pf (bit_size (map s nxs)) + (make_mono pg \<circ> pd) (bit_size (map s nxs)) "
        using x_def by blast
qed

end