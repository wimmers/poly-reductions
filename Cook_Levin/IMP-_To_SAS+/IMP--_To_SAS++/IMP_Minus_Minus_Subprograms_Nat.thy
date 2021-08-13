theory IMP_Minus_Minus_Subprograms_Nat
  imports "../IMP-_To_IMP--/Primitives" IMP_Minus_Minus_Subprograms 
begin 


fun map_all_subprograms:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_all_subprograms c n = (if n =0 then 0 else (2## (hd_nat n) ## (nth_nat (Suc (Suc 0)) c ) ## 0) ## map_all_subprograms c (tl_nat n) )"

lemma submap_all_subprograms:
  "map_all_subprograms c n = map_nat (\<lambda>c'. 2## c' ## (nth_nat (Suc (Suc 0)) c ) ## 0) n"
  apply (induct c n rule: map_all_subprograms.induct)
  apply auto
  done

fun map_all_subprograms2:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_all_subprograms2 c n = (if n =0 then 0 else ( 2## (hd_nat n) ## c ## 0) ## map_all_subprograms2 c (tl_nat n) )"
lemma submap_all_subprograms2:
"map_all_subprograms2 c n = map_nat (\<lambda>x. 2## x ## c ## 0) n"
  apply (induct c n rule: map_all_subprograms2.induct)
  apply auto
  done

declare nth_nat.simps[simp del]
fun all_subprograms_nat :: "nat \<Rightarrow> nat" where
"all_subprograms_nat c  = (if c=0 \<or> hd_nat c = 0 then (0##0)##0 else
if hd_nat c = 1 then c##(0##0)##0 else
if hd_nat c = 2 then append_nat (append_nat (map_all_subprograms c  (all_subprograms_nat (nth_nat (Suc 0) c)))
(all_subprograms_nat (nth_nat (Suc 0) c))) (all_subprograms_nat (nth_nat (Suc (Suc 0)) c)) else
if hd_nat c = 3 then c ## append_nat (all_subprograms_nat (nth_nat (Suc (Suc 0)) c)) (all_subprograms_nat (nth_nat (Suc (Suc (Suc 0))) c)) else
c ## (0##0) ## append_nat (all_subprograms_nat (nth_nat (Suc (Suc 0)) c)) (map_all_subprograms2 c  (all_subprograms_nat (nth_nat (Suc (Suc 0)) c))) 
)"
declare nth_nat.simps[simp]

lemma sub_all_subprograms:
 "all_subprograms_nat (comm_encode c) = list_encode(map comm_encode (all_subprograms c))"
  apply(induct c)
      apply (subst all_subprograms_nat.simps)
      apply (simp only: comm_encode.simps sub_hd head.simps cons0 all_subprograms.simps)
      apply simp
      apply (subst all_subprograms_nat.simps)
      apply (simp only: comm_encode.simps sub_hd head.simps cons0 sub_cons sub_append all_subprograms.simps)
     apply simp
     apply (subst all_subprograms_nat.simps)
    apply (simp only:  submap_all_subprograms comm_encode.simps sub_hd head.simps cons0 map_append map_map[of comm_encode] map_map[of _ comm_encode] comp_apply
          sub_map sub_nth nth.simps sub_cons sub_append all_subprograms.simps extract_lambda2[of "\<lambda>i j. list_encode [2, i, comm_encode j]" ] flip: extract_lambda )
    apply simp
     apply (subst all_subprograms_nat.simps)
    apply (simp only: comm_encode.simps sub_hd head.simps cons0 map_append map_map[of comm_encode] map_map[of _ comm_encode] comp_apply
          sub_map sub_nth nth.simps sub_cons sub_append all_subprograms.simps extract_lambda2[of "\<lambda>i j. list_encode [2, i, comm_encode j]" ] flip: extract_lambda )
   apply simp
     apply (subst all_subprograms_nat.simps)
    apply (simp only: submap_all_subprograms2  comm_encode.simps sub_hd head.simps cons0 map_append map_map[of comm_encode] map_map[of _ comm_encode] comp_apply
          sub_map sub_nth nth.simps sub_cons sub_append all_subprograms.simps extract_lambda2[of "\<lambda>i j. list_encode [2, i,j]" ] flip: extract_lambda )
  apply simp
  done


definition enumerate_subprograms_nat :: "nat \<Rightarrow>nat" where
"enumerate_subprograms_nat c = remdups_nat (all_subprograms_nat c)"

lemma sub_enumerate_subprograms:
"enumerate_subprograms_nat (comm_encode c) = list_encode (map comm_encode (enumerate_subprograms c))"
  using comm_inj
  apply (auto simp only: enumerate_subprograms_nat_def enumerate_subprograms_def remdups_map sub_all_subprograms sub_remdups list_encode_eq)
  done

fun all_variables_nat :: "nat \<Rightarrow>nat" where
"all_variables_nat n = (if n=0 \<or> hd_nat n =0 \<or> hd_nat n =2  then 0 else
if hd_nat n = 1 then (nth_nat (Suc 0) n) ## 0 else
nth_nat (Suc 0) n )"

lemma sub_all_variables: "all_variables_nat (comm_encode c) = vname_list_encode (all_variables c)"
  apply (cases c)
      apply (auto simp only:all_variables_nat.simps sub_hd comm_encode.simps head.simps 
              vname_list_encode_def cons0 sub_cons sub_nth nth.simps)
      apply auto
  done

fun map_all_variables:: "nat \<Rightarrow> nat" where 
"map_all_variables n = (if n =0 then 0 else (all_variables_nat (hd_nat n)) ## map_all_variables (tl_nat n) )"
lemma submap_all_variables:
"map_all_variables n = map_nat all_variables_nat n"
  apply (induct n rule:map_all_variables.induct)
  apply auto
  done

definition enumerate_variables_nat :: "nat \<Rightarrow> nat" where
"enumerate_variables_nat c =
     remdups_nat (concat_nat (map_all_variables (enumerate_subprograms_nat c)))"

thm "remdups_map"
lemma sub_enumerate_variables:
  "enumerate_variables_nat (comm_encode c) = vname_list_encode ( enumerate_variables c)"
  apply 
   (simp only:  submap_all_variables enumerate_variables_nat_def enumerate_variables_def sub_enumerate_subprograms 
                sub_map  map_map)
  apply (simp only: comp_def)
  apply (simp only: sub_all_variables)
  apply (simp only: flip:comp_def) 
  apply (simp only: flip:map_map)
  apply (simp only: vname_list_encode_as_comp)
  apply (simp only: flip:map_map)
  using vname_inj
  apply (simp only: sub_concat sub_remdups comp_apply map_concat flip:remdups_map )
  done


end 