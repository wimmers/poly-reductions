theory IMP_Minus_To_SAT_Nat 
  imports IMP_Minus_To_SAS_Plus_Nat IMP_Minus_To_SAT SAT_Plan_Base_Nat "IMP-_To_IMP--/Primitives"  
begin

fun poly_of :: "nat*nat \<Rightarrow> nat \<Rightarrow> nat" where 
"poly_of (a,0) x = a"|
"poly_of (a,Suc n) x = x * poly_of (a,n) x"

lemma mono_poly_of: "mono (poly_of p)"
  apply (auto simp add:incseq_def)
  apply (cases p)
  subgoal for m n a b
    apply auto
    apply(induct b arbitrary: p)
     apply auto
    using mult_le_mono by presburger
  done

lemma make_mono_mono_apply:"mono f \<Longrightarrow> make_mono f x = f x"
  apply(induct x)
   apply (auto simp add:incseq_def make_mono_def)
  by (simp add: antisym)

lemma make_mono_mono: "mono f \<Longrightarrow> make_mono f =f"
  using make_mono_mono_apply by blast

lemma sub_make_mono: "make_mono (poly_of p) = poly_of p"
  using mono_poly_of  make_mono_mono
  by presburger 
      

definition t'_pair :: "(nat*nat) \<Rightarrow> (nat*nat) \<Rightarrow> nat \<Rightarrow> nat" where 
"t'_pair pt p_cer x = poly_of pt (bit_length x + poly_of p_cer (bit_length x)) + 1"

lemma subpair_t':
"t'_pair pt p_cer x = t' (poly_of pt) (poly_of p_cer) x"
  apply (auto simp add: t'_pair_def t'_def sub_make_mono)
  done
lemma [termination_simp]: "0 < snd_nat p \<Longrightarrow> prod_encode (fst_nat p, snd_nat p - Suc 0) < p"
proof-
  assume asm: "0 < snd_nat p"
  obtain a b where "p = prod_encode(a,b)"
    by (metis prod_decode_aux.cases prod_decode_inverse)
  thus ?thesis using asm apply (auto simp add:sub_fst sub_snd) apply (auto simp add: prod_encode_def)
    by (metis Groups.add_ac(2) Suc_pred add_diff_cancel_left' le_add1 linorder_not_less not_less_eq_eq plus_nat.simps(2) triangle_Suc)
qed
  
fun poly_of_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"poly_of_nat p x = (if snd_nat p = 0 then fst_nat p else x * poly_of_nat (prod_encode (fst_nat p,snd_nat p -1)) x)"

lemma sub_poly_of: "poly_of_nat (prod_encode p) x = poly_of p x"
  apply (cases p)
  apply (auto simp only:)
  subgoal for a b
    apply (induct b arbitrary:p)
     apply (subst poly_of_nat.simps)
    apply (auto simp add: sub_fst sub_snd simp del:poly_of_nat.simps)
     apply (subst poly_of_nat.simps)
    apply (auto simp add: sub_fst sub_snd simp del:poly_of_nat.simps)
    done
  done

definition t'_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"t'_nat pt p_cer x = poly_of_nat pt (bit_length x + poly_of_nat p_cer (bit_length x)) + 1"

lemma subnat_t': 
"t'_nat (prod_encode pt) (prod_encode p_cer) x = t'_pair pt p_cer x"
  apply (auto simp only:t'_nat_def t'_pair_def sub_poly_of)
  done

definition "empty_sasp_action_nat \<equiv> (0 ## 0 ## 0)"
lemma sub_empty_sasp_action: "empty_sasp_action_nat = operator_plus_encode empty_sasp_action"
  apply (auto simp only:cons0 sub_cons 
        empty_sasp_action_nat_def empty_sasp_action_def operator_plus_encode_def list_encode_eq
            sas_plus_assignment_list_encode_def
        simp flip: list_encode.simps)
   apply auto
  done

definition
  "prob_with_noop_list \<Pi> \<equiv>
     \<lparr> variables_ofl = variables_ofl \<Pi>,
      operators_ofl = empty_sasp_action # operators_ofl \<Pi>, 
      initial_ofl = initial_ofl \<Pi>,
      goal_ofl = goal_ofl \<Pi>,
      range_ofl = range_ofl \<Pi>\<rparr>"

lemma sublist_prob_with_noop: 
"list_problem_to_problem (prob_with_noop_list \<Pi>) = prob_with_noop  (list_problem_to_problem \<Pi>)"
  apply (auto simp add: prob_with_noop_list_def prob_with_noop_def)
  done

definition encode_interfering_operator_pair_exclusion_list
  :: "'variable strips_list_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_interfering_operator_pair_exclusion_list \<Pi> k op\<^sub>1 op\<^sub>2
    \<equiv> let ops = operators_of \<Pi> in
      \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>1)))
      \<^bold>\<or> \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>2)))"

lemma sublist_encode_interfering_operator_pair_exclusion:
"encode_interfering_operator_pair_exclusion_list \<Pi> k op\<^sub>1 op\<^sub>2
= encode_interfering_operator_pair_exclusion (strips_list_problem_to_problem \<Pi>) k op\<^sub>1 op\<^sub>2
"
  apply (auto simp add:encode_interfering_operator_pair_exclusion_list_def 
encode_interfering_operator_pair_exclusion_def)
  done


definition encode_interfering_operator_exclusion_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_interfering_operator_exclusion_list \<Pi> t \<equiv> let
      ops = operators_of \<Pi>
      ; interfering = filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ops op\<^sub>1 \<noteq> index ops op\<^sub>2
        \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ops ops)
    in BigAnd (concat (map (\<lambda>(op\<^sub>1, op\<^sub>2). map (\<lambda>k. encode_interfering_operator_pair_exclusion_list \<Pi> k op\<^sub>1 op\<^sub>2)
      [0..<t]) interfering ))"

lemma sublist_encode_interfering_operator_exclusion:
"encode_interfering_operator_exclusion_list \<Pi> t
= encode_interfering_operator_exclusion (strips_list_problem_to_problem \<Pi>) t "
  apply (auto simp add:encode_interfering_operator_exclusion_list_def
encode_interfering_operator_exclusion_def
    sub_foldr sublist_encode_interfering_operator_pair_exclusion
)
  done

definition encode_problem_with_operator_interference_exclusion_list
  :: "'variable strips_list_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_problem_with_operator_interference_exclusion_list \<Pi> t
    \<equiv> encode_initial_state_list \<Pi>
      \<^bold>\<and> (encode_operators_list \<Pi> t
      \<^bold>\<and> (encode_all_frame_axioms_list \<Pi> t
      \<^bold>\<and> (encode_interfering_operator_exclusion_list \<Pi> t
      \<^bold>\<and> (encode_goal_state_list \<Pi> t))))"

lemma sublist_encode_problem_with_operator_interference_exclusion:
"encode_problem_with_operator_interference_exclusion_list \<Pi> t
= encode_problem_with_operator_interference_exclusion (strips_list_problem_to_problem \<Pi>) t"
  apply (auto simp only: encode_problem_with_operator_interference_exclusion_list_def 
encode_problem_with_operator_interference_exclusion_def
    sublist_encode_initial_state sublist_encode_operators sublist_encode_all_frame_axioms
    sublist_encode_interfering_operator_exclusion
    sublist_encode_goal_state
)
  done

 definition imp_to_sat_list :: "Com.com \<Rightarrow> (nat*nat) \<Rightarrow> (nat*nat) \<Rightarrow> nat \<Rightarrow> sat_plan_formula" where
    "imp_to_sat_list c pt p_cer x =
      (let I = [(''input'', x)]; 
          G = [(''input'',0)];
          guess_range = x + 1 + 2 * 2 ^ (poly_of p_cer (bit_length x));
          max_bits = max_input_bits c I guess_range
      in
        \<Phi>\<^sub>\<forall> (\<phi> prob_with_noop (IMP_Minus_to_SAS_Plus c I guess_range G (t'_pair pt p_cer x)))
           100 * (max_bits + (t'_pair pt p_cer x) + 1) * ((t'_pair pt p_cer x) - 1) +
             (max_bits + (t'_pair pt p_cer x) + 2) * (num_variables c + 2) + 52)"

end