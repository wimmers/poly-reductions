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
datatype IMPm_IMPmm = Bot IMP_Minus_Minus_com |
                      SKIP nat| 
                      Assign vname aexp nat |
                      Seq_0 IMP_Minus_com IMP_Minus_com nat |
                      Seq_m IMP_Minus_com IMP_Minus_com nat IMP_Minus_Minus_com  |
                      Seq_f IMP_Minus_com IMP_Minus_com nat IMP_Minus_Minus_com IMP_Minus_Minus_com  |
                      If_0  vname IMP_Minus_com IMP_Minus_com nat|
                      If_m  vname IMP_Minus_com IMP_Minus_com nat IMP_Minus_Minus_com  |
                      If_f vname IMP_Minus_com IMP_Minus_com nat  IMP_Minus_Minus_com IMP_Minus_Minus_com |
                      While_0 vname IMP_Minus_com nat|
                      While_f vname IMP_Minus_com nat IMP_Minus_Minus_com


fun IMPm_IMPmm_encode :: "IMPm_IMPmm \<Rightarrow> nat" where 
"IMPm_IMPmm_encode (Bot x) = list_encode [0,comm_encode x]"|
"IMPm_IMPmm_encode (SKIP n) = list_encode [1, n]"|
"IMPm_IMPmm_encode (Assign v a n) = list_encode [2, vname_encode v, aexp_encode a , n]"|
"IMPm_IMPmm_encode (Seq_0 c1 c2 n) = list_encode [3, com_encode c1, com_encode c2, n]"|
"IMPm_IMPmm_encode (Seq_m c1 c2 n c3) = list_encode [4, com_encode c1 ,com_encode c2, n , comm_encode c3]"|
"IMPm_IMPmm_encode (Seq_f c1 c2 n c3 c4) = list_encode [5, com_encode c1 ,com_encode c2, n , comm_encode c3,comm_encode c4]"|
"IMPm_IMPmm_encode (If_0 v c1 c2 n) = list_encode [6, vname_encode v, com_encode c1, com_encode c2, n]"|
"IMPm_IMPmm_encode (If_m v c1 c2 n c3) = list_encode [7, vname_encode v, com_encode c1, com_encode c2, n, comm_encode c3]"|
"IMPm_IMPmm_encode (If_f v c1 c2 n c3 c4) = list_encode [8, vname_encode v, com_encode c1, com_encode c2, n, comm_encode c3 , comm_encode c4]"|
"IMPm_IMPmm_encode (While_0 v c n) = list_encode [9, vname_encode v, com_encode c , n]"|
"IMPm_IMPmm_encode (While_f v c n c') = list_encode [10, vname_encode v, com_encode c, n, comm_encode c']"

fun IMPm_IMPmm_decode :: "nat \<Rightarrow> IMPm_IMPmm" where 
"IMPm_IMPmm_decode  n = (case list_decode n of
    [0,x] \<Rightarrow> Bot (comm_decode x)|
    [Suc 0,n] \<Rightarrow> SKIP n|
    [Suc (Suc 0) , v , a, n] \<Rightarrow> Assign (vname_decode v) (aexp_decode a) n|
    [Suc (Suc (Suc 0)), c1, c2,n] \<Rightarrow> Seq_0 (com_decode c1) (com_decode c2) n|
    [Suc (Suc (Suc (Suc 0))), c1, c2 ,n, c3] \<Rightarrow> Seq_m (com_decode c1) (com_decode c2) n (comm_decode c3)|
    [Suc (Suc (Suc (Suc (Suc 0)))), c1, c2, n, c3,c4] \<Rightarrow> Seq_f (com_decode c1) (com_decode c2) n (comm_decode c3) (comm_decode c4)|
    [Suc (Suc (Suc (Suc (Suc (Suc 0))))), v ,c1, c2,n] \<Rightarrow> If_0 (vname_decode v) (com_decode c1)  (com_decode c2) n|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))), v ,c1 ,c2,n,c3] \<Rightarrow> If_m (vname_decode v) (com_decode c1) (com_decode c2) n (comm_decode c3)|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))),v ,c1 ,c2,n,c3,c4] \<Rightarrow> If_f (vname_decode v) (com_decode c1) (com_decode c2) n (comm_decode c3) (comm_decode c4)|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))),v,c,n] \<Rightarrow> While_0 (vname_decode v) (com_decode c)  n|
    [Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))), v, c, n, c'] \<Rightarrow> While_f (vname_decode v) (com_decode c) n (comm_decode c')
) "

lemma IMPm_IMPmm_id : 
"IMPm_IMPmm_decode (IMPm_IMPmm_encode x) = x"
  apply(cases x)
   apply(auto simp add: IMPm_IMPmm_encode.simps IMPm_IMPmm_decode.simps list_encode_inverse comm_id vname_id aexp_id com_id
                    simp del: comm_encode.simps com_encode.simps comm_decode.simps com_decode.simps aexp_encode.simps aexp_decode.simps)
  done

definition IMPm_IMPmm_list_encode :: "IMPm_IMPmm list \<Rightarrow> nat" where 
"IMPm_IMPmm_list_encode xs = list_encode (map IMPm_IMPmm_encode xs)"

definition IMPm_IMPmm_list_decode :: "nat \<Rightarrow> IMPm_IMPmm list " where 
"IMPm_IMPmm_list_decode xs = map IMPm_IMPmm_decode (list_decode xs)"

lemma IMPm_IMPmm_list_id: 
"IMPm_IMPmm_list_decode (IMPm_IMPmm_list_encode x) = x"
  apply(auto simp only:  IMPm_IMPmm_list_decode_def  IMPm_IMPmm_list_encode_def list_encode_inverse 
            map_map comp_def IMPm_IMPmm_id)
  apply auto
  done

fun push_on_stack :: "IMP_Minus_com \<Rightarrow> nat \<Rightarrow> IMPm_IMPmm list \<Rightarrow> IMPm_IMPmm list" where 
"push_on_stack Com.SKIP n stack = SKIP n # stack "|
"push_on_stack (Com.Assign v aexp) n stack =  ( Assign v aexp n) # stack "|
"push_on_stack (Com.Seq c1 c2) n stack =  ( Seq_0 c1 c2 n) # stack "|
"push_on_stack (Com.If v c1 c2) n stack =  (If_0 v c1 c2 n) # stack "|
"push_on_stack (Com.While v c) n stack =  (While_0 v c n) # stack "

fun push_on_stack_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"push_on_stack_nat c n s = (if hd_nat c = 0 then (1##n##0)##s else 
if hd_nat c = 1 then (2## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## n ## 0)## s else 
if hd_nat c = 2 then (3## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## n ## 0)## s else 
if hd_nat c = 3 then (6## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## (nth_nat (Suc (Suc (Suc 0))) c) ## n ## 0) ## s else
(9## (nth_nat (Suc 0) c) ## (nth_nat (Suc (Suc 0)) c) ## n ## 0)## s
)"

lemma sub_push_on_stack:
"push_on_stack_nat (com_encode c) n (IMPm_IMPmm_list_encode s) = 
IMPm_IMPmm_list_encode (push_on_stack c n s)"
  apply(cases c)
      apply (auto simp only: push_on_stack_nat.simps push_on_stack.simps sub_hd head.simps com_encode.simps
             IMPm_IMPmm_list_encode_def sub_cons cons0 sub_nth nth.simps)
  apply auto
  done



      
           
fun add_result_to_stack :: "IMP_Minus_Minus_com \<Rightarrow> IMPm_IMPmm list \<Rightarrow> IMPm_IMPmm list" where 
"add_result_to_stack c [] = [Bot c]"|
"add_result_to_stack c (Seq_0 c1 c2 n # stack) = Seq_m c1 c2 n c # stack" |
"add_result_to_stack c (Seq_m c1 c2 n c3 #stack) = (Seq_f c1 c2 n c3 c) # stack"|
"add_result_to_stack c (If_0 v c1 c2  n # stack)  = If_m v c1 c2 n c # stack"|
"add_result_to_stack c (If_m v c1 c2 n c3 #stack) = If_f v c1 c2 n c3 c # stack"|
"add_result_to_stack c (While_0 v c' n # stack ) = While_f v c' n c #stack"|
"add_result_to_stack c s = s"

fun add_result_to_stack_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add_result_to_stack_nat c s = (if s = 0 then (0##c##0)##0
else (let h = hd_nat s; con = hd_nat h; t = tl_nat s  in 
  if con = 3 then ((4## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h) ## c ## 0) ## t) 
  else if con = 4 then ((5## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h) ## c ## 0) ## t)
  else if con = 6 then ((7## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h) ## c ## 0) ## t)    
  else if con = 7 then ((8## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc 0)))) h)  ## (nth_nat (Suc (Suc (Suc ( Suc (Suc 0))))) h) ## c ## 0) ## t)
  else if con = 9 then ((10 ## (nth_nat (Suc 0) h) ## (nth_nat (Suc (Suc 0)) h) ## (nth_nat (Suc (Suc (Suc 0))) h) ## c ## 0) ## t) 
  else s
))"

lemma sub_add_result_to_stack:
"add_result_to_stack_nat (comm_encode c) (IMPm_IMPmm_list_encode s)
= IMPm_IMPmm_list_encode (add_result_to_stack c s) "
  apply(cases s)
      apply (auto simp only: map_is_Nil_conv
      list_encode_non_empty  
      list.simps add_result_to_stack_nat.simps add_result_to_stack.simps sub_hd head.simps comm_encode.simps
             IMPm_IMPmm_list_encode_def sub_cons cons0 sub_nth nth.simps)
    
   apply (auto simp del: list_encode.simps)
  subgoal for a xs
    apply(cases a)
   apply (auto simp add: Let_def sub_tl sub_cons sub_nth sub_hd list.simps simp del: list_encode.simps)
    done
  done

function IMP_Minus_to_IMP_Minus_Minus_stack :: "IMPm_IMPmm list \<Rightarrow> IMP_Minus_Minus_com" where 
"IMP_Minus_to_IMP_Minus_Minus_stack (Seq_0 c1 c2 n #stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c1 n (Seq_0 c1 c2 n #stack))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (Seq_m c1 c2 n c3 #stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c2 n (Seq_m c1 c2 n c3 #stack ))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (If_0 v c1 c2 n # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c1 n (If_0 v c1 c2 n #stack ))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (If_m v c1 c2 n c3 # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c2 n (If_m v c1 c2 n c3 #stack ))"|
"IMP_Minus_to_IMP_Minus_Minus_stack (While_0 v c n # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c n (While_0 v c n #stack ))" |
"IMP_Minus_to_IMP_Minus_Minus_stack (SKIP _ # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_Minus_Com.SKIP) stack)" |
"IMP_Minus_to_IMP_Minus_Minus_stack (Assign v aexp n # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (assignment_to_binary n v aexp) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (Seq_f _ _ _ c1 c2 # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_Minus_Com.Seq c1 c2) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (If_f v _ _ n c1 c2 # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack ( IMP_Minus_Minus_Com.If (var_bit_list n v) c1  c2) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (While_f v _ n c # stack) = 
  IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_Minus_Com.While (var_bit_list n v) c) stack)"|
"IMP_Minus_to_IMP_Minus_Minus_stack (Bot res # stack) =  res"
  sorry
termination sorry


function IMP_Minus_to_IMP_Minus_Minus_stack_nat :: "nat \<Rightarrow> nat" where 
"IMP_Minus_to_IMP_Minus_Minus_stack_nat s  = ( let h = hd_nat s ; c = hd_nat h ; t = tl_nat s in
  if c = 3  then  IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc 0) h) (nth_nat (Suc (Suc (Suc 0))) h) s)
else if c = 4 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc 0)) h) (nth_nat (Suc (Suc (Suc 0))) h) s) 
else if c = 6 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc 0)) h) (nth_nat (Suc (Suc (Suc (Suc 0)))) h) s)
else if c = 7 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc (Suc 0))) h) (nth_nat (Suc (Suc (Suc (Suc 0)))) h) s)
else if c = 9 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat (nth_nat (Suc (Suc 0)) h) (nth_nat (Suc (Suc (Suc 0))) h) s) 
else if c = 1 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (0##0) t)
else if c = 2 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (assignment_to_binary_nat (nth_nat (Suc (Suc (Suc 0))) h) (nth_nat (Suc 0) h) (nth_nat (Suc (Suc 0)) h)) t)
else if c = 5 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (2 ## (nth_nat (Suc (Suc (Suc (Suc 0)))) h) ## (nth_nat (Suc (Suc (Suc (Suc(Suc 0))))) h) ## 0  ) t) 
else if c = 8 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (3 ## (var_bit_list_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) h)
  (nth_nat (Suc 0) h))
 ## (nth_nat (Suc (Suc (Suc (Suc (Suc 0))))) h) ## (nth_nat (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) h) ## 0  ) t)
else if c = 10 then IMP_Minus_to_IMP_Minus_Minus_stack_nat (add_result_to_stack_nat (4 ## (var_bit_list_nat (nth_nat (Suc (Suc (Suc 0))) h)
  (nth_nat (Suc 0) h))
 ## (nth_nat (Suc (Suc (Suc (Suc 0)))) h)  ## 0  ) t )

else nth_nat (Suc 0) h

)"
  sorry
termination sorry

lemma push_non_empty : "push_on_stack c n s \<noteq> []"
  apply(cases c)
      apply auto
  done
lemma add_result_non_empty: "add_result_to_stack c s \<noteq> []"
  apply(cases s)
   apply auto
  subgoal for a xs
    apply(cases a)
              apply auto
    done 
  done

lemma subtailnat_IMP_Minus_to_IMP_Minus_Minus_stack:
"s \<noteq> []  \<Longrightarrow> IMP_Minus_to_IMP_Minus_Minus_stack_nat (IMPm_IMPmm_list_encode s)
= comm_encode (IMP_Minus_to_IMP_Minus_Minus_stack s) "
  apply(induct s rule: IMP_Minus_to_IMP_Minus_Minus_stack.induct )
  apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
            apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty )
 apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
           apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty )
 apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
          apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty )
 apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
         apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty )
 apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def sub_hd head.simps sub_nth nth.simps sub_push_on_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps)
            apply( simp only: sub_add_result_to_stack sub_push_on_stack flip:IMPm_IMPmm_encode.simps list.simps IMPm_IMPmm_list_encode_def)
        apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
 apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack  flip: IMPm_IMPmm_list_encode_def )
        apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack sub_assignment_to_binary  flip: IMPm_IMPmm_list_encode_def )
        apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  flip: comm_encode.simps )
       apply( simp only:sub_add_result_to_stack sub_assignment_to_binary  flip: IMPm_IMPmm_list_encode_def )
        apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
          apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
          apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
apply(subst IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps)
            apply(simp only: sub_var_bit_list sub_add_result_to_stack  Let_def cons0 sub_cons sub_hd sub_tl tail.simps head.simps sub_nth nth.simps sub_push_on_stack sub_add_result_to_stack sub_nth nth.simps
IMPm_IMPmm_list_encode_def list.simps IMPm_IMPmm_encode.simps  )
  apply(simp only: sub_add_result_to_stack flip: IMPm_IMPmm_list_encode_def comm_encode.simps)
          apply (auto simp del: IMP_Minus_to_IMP_Minus_Minus_stack_nat.simps simp add: push_non_empty add_result_non_empty)
  done

lemma IMP_Minus_to_IMP_Minus_Minus_stack_correct:
"IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c n stack) 
= IMP_Minus_to_IMP_Minus_Minus_stack (add_result_to_stack (IMP_Minus_To_IMP_Minus_Minus c n) stack)"
  by (induct c arbitrary:stack) auto

definition IMP_Minus_to_IMP_Minus_Minus_t:: "IMP_Minus_com \<Rightarrow> nat \<Rightarrow> IMP_Minus_Minus_com" where
  "IMP_Minus_to_IMP_Minus_Minus_t c n = 
IMP_Minus_to_IMP_Minus_Minus_stack (push_on_stack c n [])"

definition IMP_Minus_To_IMP_Minus_Minus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_To_IMP_Minus_Minus_nat c n = 
IMP_Minus_to_IMP_Minus_Minus_stack_nat (push_on_stack_nat c n 0)"

lemma IMPm_IMPmm_nil: "0 = IMPm_IMPmm_list_encode []"
  using IMPm_IMPmm_list_encode_def by force

lemma subtailnat_IMP_Minus_to_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_nat (com_encode c) n
= comm_encode (IMP_Minus_to_IMP_Minus_Minus_t c n)"
  using push_non_empty subtailnat_IMP_Minus_to_IMP_Minus_Minus_stack
  apply(auto simp only: IMPm_IMPmm_nil IMP_Minus_To_IMP_Minus_Minus_nat_def IMP_Minus_to_IMP_Minus_Minus_t_def 
       sub_push_on_stack )
  done

lemma subtail_IMP_Minus_to_IMP_Minus_Minus:
"IMP_Minus_to_IMP_Minus_Minus_t c n = 
IMP_Minus_To_IMP_Minus_Minus c n "
  using  IMP_Minus_to_IMP_Minus_Minus_stack_correct [of c n "[]"]
  apply (auto simp add:IMP_Minus_to_IMP_Minus_Minus_t_def)
  done
lemma sub_IMP_Minus_To_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_nat (com_encode c) n = comm_encode (IMP_Minus_To_IMP_Minus_Minus c n)"
  using subtail_IMP_Minus_to_IMP_Minus_Minus subtailnat_IMP_Minus_to_IMP_Minus_Minus by presburger

definition IMP_Minus_To_IMP_Minus_Minus_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"IMP_Minus_To_IMP_Minus_Minus_tail c n = IMP_Minus_To_IMP_Minus_Minus_nat c n "

lemma subtail_IMP_Minus_To_IMP_Minus_Minus:
"IMP_Minus_To_IMP_Minus_Minus_tail c n = IMP_Minus_To_IMP_Minus_Minus_nat c n "
  by (simp add: IMP_Minus_To_IMP_Minus_Minus_tail_def)






end