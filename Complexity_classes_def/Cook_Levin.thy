\<^marker>\<open>creator Bilel Ghorbel\<close>
chapter \<open>The mighty Cook-Levin Theorem\<close>
paragraph \<open>Summary\<close>
text \<open>Stating the Cook-Levin theorem based on a homomorphism of SAT formulas.

Since IMP- works on natural numbers. We prove that the set of encoded satisfiable formulae 
is NP-Hard.

The homomorphism in HOL should be polynomially bounded in time. The statement cannot be formalized ? 
\<close>
theory Cook_Levin
  imports Complexity_Classes
begin
locale encode_decode_sat =
  fixes encode_sat :: "nat three_sat \<Rightarrow> nat" (*I think we  should find a way to make it polynomially  bounded*)
  fixes decode_sat :: "nat\<Rightarrow> nat three_sat"

assumes decode_encode_inv : "decode_sat (encode_sat F) = F"
begin
definition IMP_SAT :: "nat set" where 
  "IMP_SAT == encode_sat ` {n. sat n}"
paragraph \<open>Main lemma\<close>
text \<open>This is the most important part while proving Cook-Levin.
We have to prove that for every verifier, that is polynomially bounded, we could find a reduction
that says for every input whether there exists an accepting certificate up to a certain limit.\<close>
lemma main_lemma : 
  fixes c pt p_cer
  assumes "poly pt"
  assumes "poly p_cer"
  assumes "\<forall>s. \<exists>t. Ex (big_step_t (c, s) t) \<and> t \<le> 
                      pt (bit_length (s ''input'') + bit_length (s ''certificate''))"
  assumes "\<forall>x z. \<exists>r. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)"
  shows "\<exists>imp_to_sat t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>s t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')
       \<and> (\<forall>x. \<exists>f.    bit_length f \<le> s_red ( bit_length x )
                   \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(bit_length x)))
                   \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                                        (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' = 0))
                                        )
                      )"
  sorry
paragraph \<open>Main Lemma on HOL level \<close>
text \<open>Same lemma but we assume that the reduction is written in HOL \<close>
lemma main_lemma_hol: 
  fixes c pt p_cer
  assumes "poly pt"
  assumes "poly p_cer"
  assumes "\<forall>s. \<exists>t. Ex (big_step_t (c, s) t) \<and> t \<le>
                 pt (bit_length (s ''input'') + bit_length (s ''certificate''))"
  assumes "\<forall>x z. \<exists>r. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)"
  shows "\<exists>imp_to_sat t_red s_red.
         poly t_red 
       \<and> poly s_red
       \<and> (\<forall>x. \<exists>f.    bit_length (encode_sat f) \<le> s_red ( bit_length x ) \<and> imp_to_sat x = f
                   \<and> ( sat f  \<longleftrightarrow>
                                        (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' = 0))
                                        )
                      )"
  sorry
text \<open>Prove for every NP program that it can be reduced to IMP_SAT using 
the reduction of main lemma \<close>

lemma NP_reduces_SAT:
  assumes "L \<in> NP"
  shows "poly_reduces L IMP_SAT"
proof -
  obtain v p p_cer where pv_def:"poly p" "is_verif v L"
    "time_bounded v [''input'',''certificate''] p" "certif_bounded v p_cer"
    "poly p_cer"
    using assms
    by (auto simp add: NP_def is_poly_verif_def poly_time_bounded_def poly_certif_bounded_def)
  have "poly p" "poly p_cer" using pv_def by auto
  moreover have "\<forall>s. \<exists>t. Ex (big_step_t (v, s) t) \<and> t \<le> p (bit_length (s ''input'') + bit_length (s ''certificate''))" using pv_def(3) 
    by(auto simp add: time_bounded_def)
  moreover have " \<forall>x z. \<exists>r. \<forall>s. s ''input'' = x \<and> s ''certificate'' = z \<longrightarrow>
                         (\<exists>t s'. (v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> s' ''input'' = r)" using pv_def (2)
    by (auto simp add: is_verif_def verif_def comp_def)
  ultimately have "\<exists>imp_to_sat t_red s_red. 
      poly t_red \<and> 
      poly s_red \<and>
      poly p_cer \<and>
       (\<forall>s t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'') \<and>
      (\<forall>x. \<exists>f. bit_length f \<le> s_red ( bit_length x )
              \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(bit_length x)))
              \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                     (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' =0))
                                        )
      )" using main_lemma by auto
  then obtain imp_to_sat t_red s_red where main_res:
    "poly t_red " "poly s_red" "\<forall>x. \<exists>f. (bit_length f \<le> s_red ( bit_length x ))
              \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(bit_length x)))
              \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                     (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' =0))
                                        )"
    "cons_certif imp_to_sat"  by (auto simp add:cons_certif_def)
  have "time_bounded imp_to_sat [''input''] t_red"
    using main_res(3)  by (auto simp add:time_bounded_def) blast 
  hence "poly_time_bounded imp_to_sat [''input'']"
    using main_res(1) by (auto simp add:poly_time_bounded_def)
  moreover have "result_bounded imp_to_sat [''input''] [''input''] s_red"
    apply (auto simp add: result_bounded_def comp_def) 
  proof -
    fix xs::"val list"
    assume "length xs = Suc 0"
    then obtain x where x_def: "xs =[x]"
      by (metis Suc_length_conv length_0_conv)
    obtain y where y_def: "bit_length y \<le> s_red ( bit_length x)"  
      "\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = y \<and> t \<le> t_red(bit_length x))"
      using main_res(3)  by metis
    obtain r where r_def:"r = [y]" by simp
    have "length r = Suc 0 \<and>
        (\<forall>s. s ''input'' = x \<longrightarrow>
             (\<exists>t s'. (imp_to_sat, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> (\<forall>x\<in>set (zip [''input''] r). s' (fst x) = snd x))) \<and>
        bit_size r \<le> s_red (bit_length x)"
      using r_def y_def by fastforce
    thus " \<exists>r. length r = Suc 0 \<and>
             (\<forall>s::state. map (s \<circ> fst) (zip [''input''] xs) = xs \<longrightarrow>
                  (\<exists>t s'::state.
                      (imp_to_sat, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and>
                      (\<forall>x\<in>set (zip [''input''] r). s' (fst x) = snd x))) \<and>
             bit_size r \<le> s_red (bit_size xs)" by (auto simp add:x_def)
  qed
  hence "poly_result_bounded  imp_to_sat [''input''] [''input'']" 
    using main_res(2) by(auto simp add:poly_result_bounded_def)
  moreover have "is_reduction imp_to_sat L IMP_SAT" apply (auto simp add:is_reduction_def)
    using main_res(4) apply simp
    subgoal for x
    proof -
      have  "\<exists>f. (bit_length f \<le> s_red ( bit_length x ))
              \<and> (\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(bit_length x)))
              \<and> ( f \<in> IMP_SAT \<longleftrightarrow>
                     (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' =0))
                                        )"
        using main_res(3) 
        by simp
      then obtain f where f_def: "\<forall>s. s ''input'' = x \<longrightarrow> (\<exists>t s'. (imp_to_sat,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> 
                                          s' ''input'' = f \<and> t \<le> t_red(bit_length x))" 
        " f \<in> IMP_SAT \<longleftrightarrow>
                    (\<exists>z. bit_length z \<le> p_cer (bit_length x) \<and>
                                                      (\<forall>s t s'. s ''input'' = x 
                                                      \<and> s ''certificate'' = z 
                                                      \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s' ''input'' =0))"
        by auto
      have "comp' imp_to_sat x f" using f_def(1) apply (simp add: comp'_def comp_def) by blast
      moreover have "x\<in>L \<longleftrightarrow> f \<in> IMP_SAT"
      proof
        assume "x\<in>L"
        hence  "\<exists>z. verif v x z 0" using pv_def by (auto simp add: is_verif_def)
        hence  "\<exists>z. verif v x z 0 \<and> bit_length z \<le> p_cer (bit_length x)"
          using pv_def(4) certif_bounded_def certif_bounded_to_goal_def by blast
        then obtain z  where z_def: "\<forall>r. verif v x z r \<longrightarrow> 0 = r "
          "bit_length z \<le> p_cer (bit_length x)"
          using comp_det verif_def
          by (smt fst_conv 
              iszero_primfun_list.simps(1) iszero_primfun_list.simps(2) list.simps(9) pair_list_eqI)
        have "\<forall>s t s'. s ''input'' = x \<and> s ''certificate'' = z 
                             \<and> (v, s) \<Rightarrow>\<^bsup> t \<^esup> s'
                                         \<longrightarrow> s' ''input'' =0"
          apply auto
          subgoal for s t s' 
          proof -
            assume assms: " x = s ''input'' " "(v, s) \<Rightarrow>\<^bsup> t \<^esup> s'"  "z = s ''certificate''"
            obtain r where r_def :"verif v x z r" using pv_def(2)
              apply(auto simp add: is_verif_def) by blast
            hence "r = s' ''input'' " apply(simp add: verif_def comp_def)
              using assms big_step_t_determ2 by blast
            hence "verif v x z (s' ''input'')" using r_def by simp 
            thus " s' ''input'' = 0" using z_def  by simp
          qed
          done
        thus "f \<in> IMP_SAT" using f_def(2) z_def(2) bigstep_det  by (auto simp add: verif_def) 
      next 
        assume  "f \<in> IMP_SAT"
        then obtain z
          where z_def: "\<forall>s t s'. s ''input'' = x \<and> s ''certificate'' = z  \<and>(v, s) \<Rightarrow>\<^bsup> t \<^esup> s'
                           \<longrightarrow> s' ''input'' = 0" using f_def by blast 
        obtain r where r_def :"verif v x z r" using pv_def(2) apply(auto simp add: is_verif_def)
          by blast
        obtain s where "s = <''input'':=x, ''certificate'':=z>" by simp
        then have s_def: " s ''input'' = x \<and> s ''certificate'' = z" by simp
        obtain t s' where ts'_def: " (v, s) \<Rightarrow>\<^bsup> t \<^esup> s'" "s' ''input'' = r"
          using r_def s_def apply(simp add: verif_def comp_def ) by blast
        have "s' ''input'' = 0" using s_def ts'_def(1) z_def by auto
        hence "r = 0" using ts'_def(2) by simp
        thus   "x \<in> L" using pv_def(2) using is_verif_def r_def by blast
      qed
      ultimately show ?thesis by auto
    qed
    done
  ultimately show ?thesis by (auto simp add:poly_reduces_def is_polyreduction_def)
qed

text\<open>Stating cook-levin \<close>

lemma cook_levin: "IMP_SAT \<in> NP_hard"
  by (simp add: NP_hard_def NP_reduces_SAT)
end
end
