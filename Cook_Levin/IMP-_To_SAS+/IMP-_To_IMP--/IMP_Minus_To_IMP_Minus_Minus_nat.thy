theory IMP_Minus_To_IMP_Minus_Minus_nat 
  imports  IMP_Minus_To_IMP_Minus_Minus  "../IMP_Minus_Max_Constant_Nat" "Binary_Operations_Nat"
begin


fun map_var_bit_to_var:: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var v n = (if n =0 then 0 else (var_bit_to_var_nat (prod_encode (v,hd_nat n)))## map_var_bit_to_var v (tl_nat n)  )"

fun map_var_bit_to_var_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_acc acc v n = (if n =0 then acc 
else map_var_bit_to_var_acc ((var_bit_to_var_tail (prod_encode (v,hd_nat n)))## acc) v (tl_nat n)  )"

lemma submap_var_bit_to_var :
"map_var_bit_to_var v n =  map_nat (\<lambda>i. var_bit_to_var_nat (prod_encode (v,i))) n "
  apply (induct v n rule:map_var_bit_to_var.induct)
  apply auto
  done


lemma map_var_bit_to_var_append:
"map_var_bit_to_var v (append_nat xs ys) = 
append_nat(map_var_bit_to_var v xs) (map_var_bit_to_var v ys)"
proof -
  obtain xs' ys' where "ys = list_encode ys'"  "xs = list_encode xs'" 
  by (metis list_decode_inverse)
  thus ?thesis 
    apply(auto simp add: sub_append submap_var_bit_to_var
sub_map
 simp del:map_nat.simps
map_var_bit_to_var.simps)
    done
qed

lemma map_var_bit_to_var_induct:
"reverse_nat (map_var_bit_to_var v (append_nat xs ys))
= map_var_bit_to_var_acc (reverse_nat (map_var_bit_to_var v xs)) v ys"
  apply(induct ys arbitrary:xs rule:length_nat.induct)
   apply(auto simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps
          simp add: append_nat_0)
   apply simp
    apply(auto simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps
          simp add: append_nat_0 append_nat_Suc)
  apply (subst (2) map_var_bit_to_var_acc.simps)
  apply(auto simp add: map_var_bit_to_var_append subtail_var_bit_to_var
        reverse_append_nat simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps
          simp add: append_nat_0 append_nat_Suc)
  apply(subst map_var_bit_to_var.simps)
  apply(auto simp add: cons_Nil
 simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps)

  apply(auto simp only: cons0 sub_hd head.simps sub_tl tail.simps)
  apply(subst map_var_bit_to_var.simps)
    apply(auto simp add: reverse_singleton_nat append_singleton_nat
 simp del:  map_var_bit_to_var_acc.simps  map_var_bit_to_var.simps)
  done

definition map_var_bit_to_var_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_var_bit_to_var_tail v n = reverse_nat (map_var_bit_to_var_acc 0 v n)"

lemma subtail_map_var_bit_to_var:
"map_var_bit_to_var_tail v n = map_var_bit_to_var v n"
  apply(auto simp only: map_var_bit_to_var_tail_def)
  using map_var_bit_to_var_induct [of v 0 n] rev_rev_nat map_var_bit_to_var.simps
  by (metis append_nat.simps(1) reverse_nat_0)

definition var_bit_list_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"var_bit_list_nat n v = map_var_bit_to_var v (list_less_nat n)"

definition var_bit_list_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"var_bit_list_tail n v = map_var_bit_to_var_tail v (list_less_tail n)"

lemma subtail_var_bit_list: 
"var_bit_list_tail n v = var_bit_list_nat n v"
  apply(auto simp only: var_bit_list_tail_def var_bit_list_nat_def 
          subtail_list_less subtail_map_var_bit_to_var)
  done

lemma sub_var_bit_list: "var_bit_list_nat n (vname_encode v) = vname_list_encode (var_bit_list n v)"
  apply (simp only: submap_var_bit_to_var  var_bit_list_nat_def var_bit_list_def sub_var_bit_to_var sub_map sub_list_less
        vname_list_encode_def
 flip: vname_nat_encode.simps )
  apply auto
  by (metis comp_apply)


declare nth_nat.simps[simp del]
datatype IMPm_IMPmm = SKIP | 
                      Assign vname aexp |
                      Seq_0 IMP_Minus_com IMP_Minus_com |
                      Seq_m IMP_Minus_com IMP_Minus_com IMP_Minus_Minus_com |
                      Seq_f IMP_Minus_com IMP_Minus_com IMP_Minus_Minus_com IMP_Minus_Minus_com |
                      If_0  vname IMP_Minus_com IMP_Minus_com |
                      If_m  vname IMP_Minus_com IMP_Minus_com IMP_Minus_Minus_com |
                      If_f vname IMP_Minus_com IMP_Minus_com IMP_Minus_Minus_com IMP_Minus_Minus_com |
                      While_0 vname IMP_Minus_com|
                      While_f vname IMP_Minus_com IMP_Minus_Minus_com

fun push_on_Stack :: "IMP_Minus_com \<Rightarrow> IMPm_IMPmm list \<Rightarrow> IMPm_IMPmm list" where 
"push_on_Stack Com.SKIP stack = SKIP # stack "|
"push_on_Stack (Com.Assign v aexp) stack =  ( Assign v aexp) # stack "|
"push_on_Stack (Com.Seq c1 c2) stack =  ( Seq_0 c1 c2) # stack "|
"push_on_Stack (Com.If v c1 c2) stack =  (If_0 v c1 c2) # stack "|
"push_on_Stack (Com.While v c) stack =  (While_0 v c) # stack "

fun add_result_to_stack :: "IMP_Minus_Minus_com \<Rightarrow> IMPm_IMPmm list \<Rightarrow> IMPm_IMPmm list" where 
"add_result_to_stack"

                      
fun IMP_Minus_To_IMP_Minus_Minus:: "IMP_Minus_com \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
"IMP_Minus_To_IMP_Minus_Minus Com.SKIP n = IMP_Minus_Minus_Com.SKIP" |
"IMP_Minus_To_IMP_Minus_Minus (Com.Assign v aexp) n = assignment_to_binary n v aexp" |
"IMP_Minus_To_IMP_Minus_Minus (Com.Seq c1 c2) n = 
  (IMP_Minus_To_IMP_Minus_Minus c1 n ;; IMP_Minus_To_IMP_Minus_Minus c2 n )" |
"IMP_Minus_To_IMP_Minus_Minus (Com.If v c1 c2) n = (IF (var_bit_list n v)\<noteq>0 THEN
  IMP_Minus_To_IMP_Minus_Minus c1 n ELSE IMP_Minus_To_IMP_Minus_Minus c2 n)" |
"IMP_Minus_To_IMP_Minus_Minus (Com.While v c) n = (WHILE (var_bit_list n v)\<noteq>0 DO
  IMP_Minus_To_IMP_Minus_Minus c n)"

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