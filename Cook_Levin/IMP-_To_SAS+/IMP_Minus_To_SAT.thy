theory IMP_Minus_To_SAT
  imports "IMP_Minus_To_SAS_Plus" "Verified_SAT_Based_AI_Planning.SAT_Solve_SAS_Plus"
    "../Complexity_classes/Cook_Levin"
begin

section \<open>Translation from IMP- to SAT\<close>

text \<open>In this theory the translations `from IMP- to SAS+`
      and `SAS+ to SAT` are composed and the `main_lemma` for
      the Cook_Levin theorem is proven correct.\<close>


subsection \<open>The partial steps:\<close>

text \<open>theorems about the translation from IMP- to SAS+
      by Florian Keßler\<close>
thm SAS_Plus_to_IMP_Minus_correctness

thm IMP_Minus_to_SAS_Plus_correctness


text \<open>theorem about the translation from SAS+ to SAT
      by Mohammad Abdulaziz and Fred Kurz\<close>
thm sas_plus_problem_has_serial_solution_iff



subsection \<open>Putting things together\<close>

text \<open>Putting things together works in three steps:
  \<^item> first we put together the transformations on the HOL level
  \<^item> then we synthesize a IMP- program that refines the HOL algorithm
  \<^item> then we instantiate the Cook_Levin locale\<close>

subsubsection \<open>Putting things together on the HOL level\<close>

definition encode_sat :: "nat three_sat \<Rightarrow> nat"  where
  "encode_sat F = undefined"

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
  oops

definition decode_sat :: "nat \<Rightarrow> nat three_sat" where
  "decode_sat n = undefined"


interpretation encode_decode_sat encode_sat decode_sat
  sorry


subsubsection \<open>Synthesizing the IMP- Program\<close>

lemma main_lemma_synth : 
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


subsubsection \<open>Instantiating the Cook_Levin locale\<close>

interpretation Cook_Levin_assumes_Main_lemma encode_sat decode_sat
  apply standard
  by (fact main_lemma_synth) 
   


end