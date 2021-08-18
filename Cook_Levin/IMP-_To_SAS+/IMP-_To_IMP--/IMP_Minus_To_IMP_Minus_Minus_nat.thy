theory IMP_Minus_To_IMP_Minus_Minus_nat 
  imports  IMP_Minus_To_IMP_Minus_Minus  "../IMP_Minus_Max_Constant_Nat" "Binary_Operations_Nat"
begin


fun map_var_bit_to_var:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var v n = (if n =0 then 0 else (var_bit_to_var_nat (prod_encode (v,hd_nat n)))## map_var_bit_to_var v (tl_nat n)  )"

lemma submap_var_bit_to_var :
"map_var_bit_to_var v n =  map_nat (\<lambda>i. var_bit_to_var_nat (prod_encode (v,i))) n "
  apply (induct v n rule:map_var_bit_to_var.induct)
  apply auto
  done

definition var_bit_list_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"var_bit_list_nat n v = map_var_bit_to_var v (list_less_nat n)"

lemma sub_var_bit_list: "var_bit_list_nat n (vname_encode v) = vname_list_encode (var_bit_list n v)"
  apply (simp only: submap_var_bit_to_var  var_bit_list_nat_def var_bit_list_def sub_var_bit_to_var sub_map sub_list_less
        vname_list_encode_def
 flip: vname_nat_encode.simps )
  apply auto
  by (metis comp_apply)


declare nth_nat.simps[simp del]
fun IMP_Minus_To_IMP_Minus_Minus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"IMP_Minus_To_IMP_Minus_Minus_nat c n = (if c =0 \<or> hd_nat c = 0 then  0##0
else if hd_nat c = 1 then assignment_to_binary_nat n (nth_nat (Suc 0) c) (nth_nat (Suc (Suc 0)) c)
else if hd_nat c = 2 then
2 ## (IMP_Minus_To_IMP_Minus_Minus_nat (nth_nat (Suc 0) c) n) ## (IMP_Minus_To_IMP_Minus_Minus_nat (nth_nat (Suc(Suc 0)) c) n) ## 0
else if hd_nat c = 3 then
3 ## (var_bit_list_nat n (nth_nat (Suc 0) c)) ## (IMP_Minus_To_IMP_Minus_Minus_nat (nth_nat (Suc(Suc 0)) c) n) ## (IMP_Minus_To_IMP_Minus_Minus_nat (nth_nat (Suc (Suc(Suc 0))) c) n) ## 0
else 
4 ## (var_bit_list_nat n (nth_nat (Suc 0) c)) ## (IMP_Minus_To_IMP_Minus_Minus_nat (nth_nat (Suc(Suc 0)) c) n) ## 0
)"
declare nth_nat.simps[simp]

lemma sub_IMP_Minus_To_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_nat (com_encode c) n = comm_encode (IMP_Minus_To_IMP_Minus_Minus c n)"
  apply(induct c)
      apply(subst IMP_Minus_To_IMP_Minus_Minus_nat.simps)
      apply (simp only: com_encode.simps sub_hd head.simps sub_nth nth.simps 
                sub_assignment_to_binary cons0)
      apply simp
       apply(subst IMP_Minus_To_IMP_Minus_Minus_nat.simps)
      apply (simp only: com_encode.simps sub_hd head.simps sub_nth nth.simps 
                sub_assignment_to_binary cons0)
     apply simp
      apply(subst IMP_Minus_To_IMP_Minus_Minus_nat.simps)
      apply (simp only: com_encode.simps sub_hd head.simps sub_nth nth.simps 
                sub_assignment_to_binary cons0 sub_cons)
    apply simp
   apply(subst IMP_Minus_To_IMP_Minus_Minus_nat.simps)
      apply (simp only: com_encode.simps sub_hd head.simps sub_nth nth.simps 
                sub_assignment_to_binary cons0 sub_cons sub_var_bit_list)
   apply simp
 apply(subst IMP_Minus_To_IMP_Minus_Minus_nat.simps)
      apply (simp only: com_encode.simps sub_hd head.simps sub_nth nth.simps 
                sub_assignment_to_binary cons0 sub_cons sub_var_bit_list)
  apply simp
  done


end