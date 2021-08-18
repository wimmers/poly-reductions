theory IMP_Minus_Max_Constant_Nat
  imports "HOL-Library.Nat_Bijection"
  "IMP-_To_IMP--/Primitives"  IMP_Minus_Max_Constant 
begin


fun atomExp_to_constant:: "atomExp \<Rightarrow> nat" where
"atomExp_to_constant (V var) = 0" |
"atomExp_to_constant (N val) = val"

definition atomExp_to_constant_nat:: "nat \<Rightarrow> nat" where 
"atomExp_to_constant_nat n = (if fst_nat n = 0 then 0 else snd_nat n)"

lemma sub_atomExp_to_constant[simp]: "atomExp_to_constant_nat (atomExp_encode x) = atomExp_to_constant x"
  apply (cases x)
  apply (auto simp add: atomExp_to_constant_nat_def sub_fst sub_snd)
  done


fun aexp_max_constant:: "AExp.aexp \<Rightarrow> nat" where
"aexp_max_constant (A a) = atomExp_to_constant a" |
"aexp_max_constant (Plus a b) = max (atomExp_to_constant a) (atomExp_to_constant b)" |
"aexp_max_constant (Sub a b) = max (atomExp_to_constant a) (atomExp_to_constant b)" |
"aexp_max_constant (Parity a) = atomExp_to_constant a" | 
"aexp_max_constant (RightShift a) = atomExp_to_constant a"

fun aexp_max_constant_nat:: "nat \<Rightarrow> nat" where
"aexp_max_constant_nat n = (if hd_nat n \<le>2 \<and> 1 \<le> hd_nat n 
then max (atomExp_to_constant_nat (nth_nat (Suc 0) n)) (atomExp_to_constant_nat (nth_nat (Suc (Suc 0)) n))
else atomExp_to_constant_nat (nth_nat (Suc 0) n))"

lemma sub_aexp_max_constant:"aexp_max_constant_nat (aexp_encode x) = aexp_max_constant x"
  apply (cases x)
      apply (auto simp only: aexp_max_constant_nat.simps aexp_encode.simps
                sub_nth  sub_hd head.simps nth.simps
              sub_snd sub_fst snd_def fst_def sub_atomExp_to_constant)
      apply auto
  done

  
      
fun max_constant :: "Com.com \<Rightarrow> nat" where
"max_constant (Com.com.SKIP) = 0" |
"max_constant (Com.com.Assign vname aexp) = aexp_max_constant aexp" |
"max_constant (Com.com.Seq c1  c2) = max (max_constant c1) (max_constant c2)" |         
"max_constant (Com.com.If  _ c1 c2) = max (max_constant c1) (max_constant c2)"  |   
"max_constant (Com.com.While _ c) = max_constant c"

lemma fst_less [simp]: "n >0 \<Longrightarrow>fst_nat n < n"
  apply (auto simp add:fst_nat_def)
  by (metis fst_conv leI le_add1 le_less_trans prod_decode_aux.cases prod_sum_less)

lemma snd_less [simp]: "n >0 \<Longrightarrow> fst_nat n > 0 \<Longrightarrow>snd_nat n < n"
  by (auto simp add:snd_nat_def fst_nat_def prod_snd_less)
    
lemma sum_less [simp]: "fst_nat n + snd_nat n \<le> n"
  apply (simp add: fst_nat_def snd_nat_def)
  by (simp add: prod_sum_less2)
    

declare nth_nat.simps [simp del]
fun max_constant_nat :: "nat \<Rightarrow> nat" where 
"max_constant_nat n = (if n=0 \<or> hd_nat n = 0 then 0 else if hd_nat n = 1 
          then aexp_max_constant_nat (nth_nat (Suc (Suc 0)) n ) else (if hd_nat n =2 then 
          max (max_constant_nat (nth_nat (Suc 0) n)) (max_constant_nat (nth_nat (Suc (Suc 0)) n)) 
          else (if hd_nat n =3 then 
       max (max_constant_nat (nth_nat (Suc (Suc 0)) n)) (max_constant_nat (nth_nat (Suc (Suc (Suc 0))) n))
        else max_constant_nat (nth_nat (Suc (Suc 0)) n ) )))"
declare nth_nat.simps [simp]

lemma [simp]: "fst_nat 0 =0" 
  by (simp add: fst_nat_def fst_def prod_decode_aux.simps prod_decode_def)
    
lemma sub_max_constant:"max_constant_nat (com_encode c) = max_constant c"
  apply (subst max_constant_nat.simps)
  apply (induction c)
      apply (simp_all split:if_splits only: com_encode.simps sub_nth sub_hd nth.simps 
        sub_aexp_max_constant  max_constant.simps head.simps)
      apply auto
  done

fun atomExp_var:: "atomExp \<Rightarrow> vname list" where
"atomExp_var (V var) = [ var ]" |
"atomExp_var (N val) = []"

fun atomExp_var_nat:: "nat \<Rightarrow> nat" where
"atomExp_var_nat n = (if fst_nat n = 0 then cons (snd_nat n) 0 else 0)"


lemma sub_atomExp_var: "atomExp_var_nat (atomExp_encode x) = vname_list_encode (atomExp_var x)"
  apply (cases x)
  apply (auto simp only: atomExp_encode.simps atomExp_var_nat.simps)
   apply (auto simp add:vname_list_encode_def cons_def sub_fst sub_snd prod_encode_eq)
  done

fun aexp_vars:: "AExp.aexp \<Rightarrow> vname list" where
"aexp_vars (A a) = atomExp_var a" |
"aexp_vars (Plus a b) = (atomExp_var a) @ (atomExp_var b)" |
"aexp_vars (Sub a b) = (atomExp_var a) @ (atomExp_var b)" |
"aexp_vars (Parity a) = atomExp_var a" |
"aexp_vars (RightShift a) = atomExp_var a"

definition aexp_vars_nat:: "nat \<Rightarrow> nat" where
"aexp_vars_nat n =  ( if hd_nat n = 1 \<or> hd_nat n = 2 then
             append_nat (atomExp_var_nat (nth_nat (Suc 0) n)) (atomExp_var_nat(nth_nat (Suc (Suc 0)) n))
                    else atomExp_var_nat (nth_nat (Suc 0) n))"

lemma sub_aexp_vars : "aexp_vars_nat (aexp_encode x) = vname_list_encode (aexp_vars x)"
  apply (cases x)
      apply (auto simp only: aexp_vars_nat_def aexp_encode.simps sub_hd head.simps sub_nth nth.simps
 sub_append sub_atomExp_var aexp_vars.simps vname_list_encode_def)
      apply auto
  done

fun all_variables :: "Com.com \<Rightarrow> vname list" where
"all_variables (Com.com.SKIP) = []" |
"all_variables (Com.com.Assign v aexp) = v # aexp_vars aexp" |
"all_variables (Com.com.Seq c1 c2) = all_variables c1 @ all_variables c2" |
"all_variables (Com.com.If v c1 c2) = [ v ] @ all_variables c1 @ all_variables c2" |
"all_variables (Com.com.While v c) = [ v ] @ all_variables c"

declare nth_nat.simps[simp del]
fun all_variables_nat :: "nat \<Rightarrow> nat" where
"all_variables_nat n = (if n=0 \<or> hd_nat n =0 then 0 else if hd_nat n = 1 then cons (nth_nat (Suc 0) n) 
(aexp_vars_nat (nth_nat (Suc (Suc 0)) n )) else if hd_nat n = 2
then append_nat (all_variables_nat (nth_nat (Suc 0) n)) (all_variables_nat (nth_nat (Suc (Suc 0)) n))
else if hd_nat n = 3 then
 append_nat (append_nat (cons (nth_nat (Suc 0) n) 0) (all_variables_nat (nth_nat (Suc (Suc 0)) n)))
 (all_variables_nat(nth_nat (Suc (Suc (Suc 0))) n))
else append_nat (cons (nth_nat (Suc 0) n) 0)  (all_variables_nat (nth_nat (Suc (Suc 0)) n)) )"
declare nth_nat.simps[simp]

lemma sub_cons_vname: "cons (vname_encode x) (vname_list_encode xs) = vname_list_encode (x#xs)"
  apply (auto simp add:cons_def vname_list_encode_def) done
lemma sub_append_vname: "append_nat (vname_list_encode x) (vname_list_encode xs) = vname_list_encode (x@xs)"
  apply (induction x)
   apply (auto simp add: vname_list_encode_def sub_append simp flip: list_encode.simps)
  done

lemma sub_all_variables: "all_variables_nat (com_encode x ) = vname_list_encode (all_variables x)"
  apply (induct x)
  apply (subst all_variables_nat.simps)
      apply (auto simp only: com_encode.simps)
      apply (auto simp only:sub_hd sub_nth head.simps nth.simps sub_aexp_vars 
              vname_list_encode_def sub_append sub_cons cons0)
      apply simp
 apply (subst all_variables_nat.simps)
      apply (auto simp only:sub_hd sub_nth head.simps nth.simps sub_aexp_vars 
              vname_list_encode_def sub_append sub_cons cons0)
     apply simp
 apply (subst all_variables_nat.simps)
      apply (auto simp only:sub_hd sub_nth head.simps nth.simps sub_aexp_vars 
              vname_list_encode_def sub_append sub_cons cons0)
    apply simp
 apply (subst all_variables_nat.simps)
      apply (auto simp only:sub_hd sub_nth head.simps nth.simps sub_aexp_vars 
              vname_list_encode_def sub_append sub_cons cons0)
   apply simp
 apply (subst all_variables_nat.simps)
      apply (auto simp only:sub_hd sub_nth head.simps nth.simps sub_aexp_vars 
              vname_list_encode_def sub_append sub_cons cons0)
  apply simp
  done



    
   
definition num_variables:: "Com.com \<Rightarrow> nat" where
"num_variables c = length (remdups (all_variables c))" 

definition num_variables_nat :: "nat \<Rightarrow> nat" where 
"num_variables_nat n = length_nat (remdups_nat (all_variables_nat n))"

lemma vname_encode_eq: "vname_encode x = vname_encode y \<Longrightarrow> x=y"
  apply (auto simp add:vname_encode_def list_encode_eq idchar)
  by (metis vname_encode_def vname_id)
lemma [simp]: "remdups (map (vname_encode) x) = map vname_encode (remdups x)"
  apply (induction x)
  using vname_encode_eq by auto
   
lemma "num_variables_nat (com_encode c) = num_variables c"
  apply (auto simp only:num_variables_nat_def sub_all_variables sub_remdups vname_list_encode_def
        sub_length num_variables_def)
  apply (induct "all_variables c"  arbitrary:c)
  by (auto simp add:map_def)
      
    
   

               
end