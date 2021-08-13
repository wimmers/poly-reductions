theory Binary_Arithmetic_Nat 
  imports Binary_Arithmetic  Primitives
begin


fun nth_bit_of_num_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_bit_of_num_nat x n  = (if x = 0 then (if n = 0 then 1 else 0) else
                            if n = 0 then (if hd_nat x = 0 then 0 else 1) else
                            nth_bit_of_num_nat (tl_nat x) (n-1)) "

lemma sub_nth_bit_of_num: "nth_bit_of_num_nat (num_encode x) n = bit_encode (nth_bit_of_num x n)"
     apply (subst nth_bit_of_num_nat.simps)
  apply (induct x n rule:nth_bit_of_num.induct)
       apply (simp_all (no_asm_simp)  only:sub_hd sub_tl num_encode_def
       num_to_list.simps nth_bit_of_num.simps list_encode.simps tail.simps head.simps list_encode_eq
   del: nth_bit_of_num_nat.simps   flip:list_encode.simps )
     apply (simp_all only: flip: nth_bit_of_num_nat.simps num_encode_def)
   apply auto
  done

lemma dom_nth_bit_nat:"nth_bit_nat a n = 0 \<or> nth_bit_nat a n = Suc 0"
  apply (induction n arbitrary: a)
   apply auto
  done

lemma sub_nth_bit : "nth_bit_nat a n = bit_encode (nth_bit a n)"
  apply (cases "nth_bit_nat a n") 
  apply (auto simp add: nth_bit_def )
   using  dom_nth_bit_nat
   by (metis Suc_inject old.nat.distinct(2))



fun nth_carry_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"nth_carry_nat n a b = (if n = 0 then (if (nth_bit_nat a 0 = 1 \<and> nth_bit_nat b 0 = 1) then 1 else 0)
 else (if (nth_bit_nat a n = 1 \<and> nth_bit_nat b n = 1) 
  \<or> ((nth_bit_nat a n = 1 \<or> nth_bit_nat b n = 1) \<and> nth_carry_nat (n-1) a b = 1) 
  then 1 else 0) )"

lemma sub_nth_carry: "nth_carry_nat n a b = bit_encode (nth_carry n a b)"
  apply (induct n)
  apply (auto simp add: sub_nth_bit)
  done



fun nth_carry_sub_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nth_carry_sub_nat n a b = (if n =0 then (if (nth_bit_nat a 0 = 0 \<and> nth_bit_nat b 0 = 1) then 1 else 0)
else (if (nth_bit_nat a n = 0 \<and> ( nth_bit_nat b n = 1 \<or> nth_carry_sub_nat (n-1) a b = 1))
    \<or> (nth_bit_nat a n = 1 \<and> (nth_bit_nat b n) = 1 \<and> nth_carry_sub_nat (n-1) a b = 1) then 1
  else 0))"

lemma sub_nth_carry_sub :"nth_carry_sub_nat n a b = bit_encode (nth_carry_sub n a b)"
 apply (induct n)
  apply (auto simp add: sub_nth_bit)
  done



fun bit_list_to_nat_nat:: "nat \<Rightarrow> nat" where
"bit_list_to_nat_nat n = (if n =0 then 0 else if hd_nat n =0 then 2 *bit_list_to_nat_nat (tl_nat n)
   else  2*bit_list_to_nat_nat (tl_nat n) + 1)" 

lemma sub_bit_list_to_nat: "bit_list_to_nat_nat (list_encode (map bit_encode x)) = bit_list_to_nat x"
  apply (induct x)
   apply (simp)
  apply (subst bit_list_to_nat_nat.simps)
  apply (auto simp only: sub_hd sub_tl sub_tail_map tl_def 
          sub_head_map bit_list_to_nat.simps split:bit.splits)
   apply (auto)
  done


end