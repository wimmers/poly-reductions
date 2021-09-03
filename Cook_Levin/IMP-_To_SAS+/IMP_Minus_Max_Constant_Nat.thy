theory IMP_Minus_Max_Constant_Nat
  imports "HOL-Library.Nat_Bijection"
  "IMP-_To_IMP--/Primitives"  IMP_Minus.Max_Constant 
begin



definition atomExp_to_constant_nat:: "nat \<Rightarrow> nat" where 
"atomExp_to_constant_nat n = (if fst_nat n = 0 then 0 else snd_nat n)"

definition atomExp_to_constant_tail:: "nat \<Rightarrow> nat" where 
"atomExp_to_constant_tail n = atomExp_to_constant_nat n"

lemma subtail_atomExp_to_constant:
"atomExp_to_constant_tail n = atomExp_to_constant_nat n"
  using atomExp_to_constant_tail_def by presburger

lemma sub_atomExp_to_constant[simp]: "atomExp_to_constant_nat (atomExp_encode x) = atomExp_to_constant x"
  apply (cases x)
  apply (auto simp add: atomExp_to_constant_nat_def sub_fst sub_snd)
  done


fun aexp_max_constant_nat:: "nat \<Rightarrow> nat" where
"aexp_max_constant_nat n = (if hd_nat n \<le>2 \<and> 1 \<le> hd_nat n 
then max (atomExp_to_constant_nat (nth_nat (Suc 0) n)) (atomExp_to_constant_nat (nth_nat (Suc (Suc 0)) n))
else atomExp_to_constant_nat (nth_nat (Suc 0) n))"

fun aexp_max_constant_tail:: "nat \<Rightarrow> nat" where
"aexp_max_constant_tail n = (if hd_nat n \<le>2 \<and> 1 \<le> hd_nat n 
then max (atomExp_to_constant_tail (nth_nat (Suc 0) n)) (atomExp_to_constant_tail (nth_nat (Suc (Suc 0)) n))
else atomExp_to_constant_tail (nth_nat (Suc 0) n))"

lemma subtail_aexp_max_constant:
"aexp_max_constant_tail n = aexp_max_constant_nat n"
  using aexp_max_constant_nat.simps aexp_max_constant_tail.simps 
atomExp_to_constant_tail_def by presburger


lemma sub_aexp_max_constant:"aexp_max_constant_nat (aexp_encode x) = aexp_max_constant x"
  apply (cases x)
      apply (auto simp only: aexp_max_constant_nat.simps aexp_encode.simps
                sub_nth  sub_hd head.simps nth.simps
              sub_snd sub_fst snd_def fst_def sub_atomExp_to_constant)
      apply auto
  done

  
lemma fst_less [simp]: "n >0 \<Longrightarrow>fst_nat n < n"
  apply (auto simp add:fst_nat_def)
  by (metis fst_conv leI le_add1 le_less_trans prod_decode_aux.cases prod_sum_less)

lemma snd_less [simp]: "n >0 \<Longrightarrow> fst_nat n > 0 \<Longrightarrow>snd_nat n < n"
  by (auto simp add:snd_nat_def fst_nat_def prod_snd_less)
    
lemma sum_less [simp]: "fst_nat n + snd_nat n \<le> n"
  apply (simp add: fst_nat_def snd_nat_def)
  by (simp add: prod_sum_less2)
    

lemma [simp]: "fst_nat 0 =0" 
  by (simp add: fst_nat_def fst_def prod_decode_aux.simps prod_decode_def)

datatype max_con = Bot nat|
                   SKIP |
                   Assign  aexp|
                   Seq_0 "Com.com" "Com.com" |
                   Seq_m "Com.com" "Com.com" nat|
                   Seq_f "Com.com" "Com.com" nat nat|
                   While_0 "Com.com"|
                   While_f "Com.com" nat

fun max_con_encode :: "max_con \<Rightarrow> nat" where 
"max_con_encode SKIP = list_encode [0]"|
"max_con_encode (Assign aexp) = list_encode [1,aexp_encode aexp]"|
"max_con_encode (Seq_0 c1 c2) = list_encode [2, com_encode c1 , com_encode c2]"|
"max_con_encode (Seq_m c1 c2 n) = list_encode [3, com_encode c1 , com_encode c2,n] "|
"max_con_encode (Seq_f c1 c2 n m) = list_encode [4, com_encode c1 , com_encode c2,n,m] "|
"max_con_encode (While_0 c) = list_encode [5, com_encode c]"|
"max_con_encode (While_f c n) = list_encode[6, com_encode c ,n]"|
"max_con_encode (Bot n) = list_encode[7,n]"


fun push_con :: "Com.com \<Rightarrow> max_con list \<Rightarrow> max_con list " where 
"push_con Com.com.SKIP s = SKIP # s"|
"push_con (Com.com.Assign v a) s = Assign a # s "|
"push_con (Com.com.Seq c1 c2) s = Seq_0 c1 c2 # s"|
"push_con (Com.com.If _ c1 c2) s = Seq_0 c1 c2 # s"|
"push_con (Com.com.While _ c ) s = While_0 c # s"

lemma push_con_Nil:
"push_con c s \<noteq> []"
  apply(cases c)
  apply auto
  done

fun push_con_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"push_con_nat c s = (let con = hd_nat c; e1 = nth_nat (Suc 0) c; e2 =nth_nat (Suc (Suc 0)) c;
    e3 = nth_nat (Suc (Suc (Suc 0))) c in
     if con = 0 then (0##0) ## s else 
     if con = 1 then (1##e2##0)## s else 
     if con = 2 then c ## s else 
     if con = 3 then (2 ## e2 ## e3 ## 0) ## s else 
     (5 ## e2 ## 0) ## s
)"


lemma sub_push_con :
"push_con_nat (com_encode c) (list_encode (map max_con_encode s))
= list_encode (map max_con_encode (push_con c s)) "
  apply(cases c)
  apply (auto simp add: sub_hd sub_cons sub_tl cons0  simp del: list_encode.simps)
  done

fun add_res :: "nat \<Rightarrow> max_con list \<Rightarrow> max_con list" where 
"add_res n [] = [Bot n]"|
"add_res n (Seq_0 c1 c2 # s) = Seq_m c1 c2 n # s"|
"add_res n (Seq_m c1 c2 n0 #s) = Seq_f c1 c2 n0 n # s "|
"add_res n (While_0 c #s) = While_f c n # s"|
"add_res n s = [Bot n]"

lemma add_res_Nil:
"add_res n s \<noteq> []"
  apply (cases s)
   apply auto
  subgoal for a xs 
    apply(cases a)
           apply auto
    done
  done


fun add_res_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add_res_nat n s = (
  if s = 0 then  (7##n##0) ## 0
else (let h =hd_nat s; t =tl_nat s; c = hd_nat h; e1 = nth_nat (Suc 0) h ; e2 = nth_nat (Suc (Suc 0)) h;
e3 = nth_nat (Suc (Suc (Suc 0))) h in
if c = 2 then (3##e1##e2##n##0)##t else 
if c = 3 then (4##e1##e2##e3##n##0)##t else 
if c = 5 then (6##e1##n##0)##t else  (7##n##0) ## 0  )

)"

lemma sub_add_res:
"add_res_nat n (list_encode (map max_con_encode s))
= list_encode (map max_con_encode (add_res n s))"
  apply (cases s)
   apply (auto simp add:cons0 sub_cons non_empty_not_zero sub_hd sub_tl
           simp del: list_encode.simps(2))
  subgoal for a xs
    apply(cases a)
           apply( auto simp add: Let_def sub_hd cons0 sub_cons sub_tl  simp del: list_encode.simps(2))
    done
  done

fun size_root :: "max_con \<Rightarrow> nat" where 
"size_root (Seq_0 c1 c2) = Suc (size c1) + (size c2)"|
"size_root (Seq_m c1 c2 _ ) = Suc (size c1) + (size c2) "|
"size_root (Seq_f c1 c2 _ _ ) = Suc (size c1) + (size c2)"|
"size_root (While_0 c) = Suc (size c)"|
"size_root (While_f c _) = Suc(size c) "|
"size_root (Bot _ ) = 0"|
"size_root s = 1"

fun size_out :: "max_con \<Rightarrow> nat" where
"size_out (Seq_m c1 _ _) = size c1 "|
"size_out (Seq_f c1 c2 _ _) =  size c1 + size c2"|
"size_out (While_f c _) = size c"|
"size_out c = 0"

fun size_e :: "Com.com \<Rightarrow> nat" where 
"size_e Com.com.SKIP = 1 "|
"size_e (Com.com.Assign v a)  = 1"|
"size_e (Com.com.Seq c1 c2) = Suc (size_e c1 + size_e c2)"|
"size_e (Com.com.If v c1 c2) = Suc (size_e c1 + size_e c2)"|
"size_e (Com.com.While v c) = Suc (size_e c)"

fun size_stack_rev :: "max_con list \<Rightarrow> nat" where
"size_stack_rev (Seq_0 c1 c2# s) =  (if s = [] then Suc (2* (size_e c1 + size_e c2)) else  Suc (2 * size_e c2) + size_stack_rev s )  "|
"size_stack_rev (Seq_m c1 c2 n#s) = (if s = [] then  Suc (2 * size_e c2) else  Suc (size_stack_rev s)) "|
"size_stack_rev (While_0 c #s)  = (if s = [] then Suc (2* size_e c) else Suc (size_stack_rev s) )"|
"size_stack_rev (Bot x # s) = size_stack_rev s"|
"size_stack_rev (_#s) = Suc (size_stack_rev s)"|
"size_stack_rev [] = 0"

fun size_stack :: "max_con list \<Rightarrow> nat" where 
"size_stack s = size_stack_rev (rev s)"

fun compare :: "max_con list \<Rightarrow> max_con list \<Rightarrow> bool" where 
"compare (Bot _ # _) _  = True"|
"compare [] _ = True"|
"compare (push_con c1 (Seq_0 c1 c2 # s) )  (Seq_0 c1 c2 # s) = True"|
"compare (push_con c2 (Seq_m c1 c2 n # s) )  (Seq_m c1 c2 n # s) = True"|
"compare (push_con c (While_0  c # s))   (While_0  c # s)  = True"
lemma size_pos:"size_e c >0"
  apply(induct c)
      apply auto
  done
lemma 
size_stack_mono :" x \<noteq> [] \<Longrightarrow>y \<noteq>  [] \<Longrightarrow> size_stack_rev y < size_stack_rev x
 \<Longrightarrow> size_stack_rev (s @ y) < size_stack_rev (s @ x) "
  apply(induct s )
   apply auto
  subgoal for a xs
    apply (cases a)
           apply (auto)
    done
  done

lemma " (s = Seq_0 c1 c2 # s' \<or> s = Seq_m c1 c2 n # s' \<or> s = While_0 c # s') 
  \<Longrightarrow> size_stack (add_res r s) < size_stack s "
  using size_stack_mono size_pos
  apply auto
  done


    

function max_constant_stack :: "max_con list \<Rightarrow> nat" where 
"max_constant_stack (Bot x # s) = x"|
"max_constant_stack (SKIP # s) = max_constant_stack (add_res 0 s)"|
"max_constant_stack (Assign v # s) = max_constant_stack (add_res (aexp_max_constant v) s)"|
"max_constant_stack (Seq_0 c1 c2 # s) = max_constant_stack (push_con c1 (Seq_0 c1 c2 # s)) "|
"max_constant_stack (Seq_m c1 c2 n0 # s) = max_constant_stack (push_con c2  (Seq_m c1 c2 n0 # s))"|
"max_constant_stack (Seq_f _ _ n m #s) = max_constant_stack (add_res (max n m) s)"|
"max_constant_stack (While_0 c# s) = max_constant_stack (push_con c (While_0 c# s)) "|
"max_constant_stack (While_f _  n# s) = max_constant_stack (add_res n s)"
  by pat_completeness auto
termination 
  apply (relation "measure size_stack")
         apply auto
  subgoal for s
    apply (cases s)
     apply auto
    subgoal for a xs
      apply (cases a)
      apply auto




fun compare_max_con::  "max_con list \<Rightarrow> max_con list \<Rightarrow> bool" where
"compare_max_con x y = compare_max_con' (rev x) (rev y)"

lemma "s\<noteq> [] \<Longrightarrow> compare_max_con (a#s) s"
  nitpick
  apply (auto)
  apply(induct s)
   apply auto
    

function max_constant_stack_nat :: "nat \<Rightarrow> nat" where 
" max_constant_stack_nat s = (let h = hd_nat s; t = tl_nat s;
  c = hd_nat h; e1 = nth_nat (Suc 0) h; e2 = nth_nat (Suc (Suc 0)) h;
 e3 = nth_nat (Suc (Suc (Suc 0))) h ; e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h in 
 if c = 0 then  max_constant_stack_nat (add_res_nat 0 t) 
else if c = 1 then max_constant_stack_nat (add_res_nat (aexp_max_constant_tail e1) t)
else if c = 2 then  max_constant_stack_nat (push_con_nat e1 s) 
else if c = 3 then   max_constant_stack_nat (push_con_nat e2 s)
else if c = 4 then   max_constant_stack_nat (add_res_nat (max e3 e4) t)
else if c = 5 then   max_constant_stack_nat (push_con_nat e1 s) 
else if c = 6 then  max_constant_stack_nat (add_res_nat e2 t)
else e1)"
  sorry
termination sorry

lemma list_encode_0:"(list_encode xs = 0) =  (xs = [])"
  by (metis list_encode.simps(1) list_encode_inverse)

thm "accp.simps"
find_theorems "wf"
lemma sub_max_constant_stack:
"s \<noteq> [] \<Longrightarrow> max_constant_stack_nat (list_encode (map max_con_encode s))
= max_constant_stack s "
  apply(induct s rule:max_constant_stack.induct)
         apply(subst max_constant_stack_nat.simps)
         apply( simp add: Let_def sub_hd sub_tl 
          del: list_encode.simps(2) max_constant_stack_nat.simps )
 apply(subst max_constant_stack_nat.simps)
        apply( simp add: sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps  )
 apply(subst max_constant_stack_nat.simps)
        apply( simp add: subtail_aexp_max_constant sub_aexp_max_constant  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps aexp_max_constant.simps
                    aexp_max_constant_nat.simps aexp_max_constant_tail.simps )
 apply(subst max_constant_stack_nat.simps)
      apply( simp add: sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps aexp_max_constant.simps
                    aexp_max_constant_nat.simps aexp_max_constant_tail.simps )
      apply (simp only: sub_push_con  flip: max_con_encode.simps list.map)
 apply(subst max_constant_stack_nat.simps)
      apply( simp add: sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps aexp_max_constant.simps
                    aexp_max_constant_nat.simps aexp_max_constant_tail.simps )
     apply (simp only: sub_push_con  flip: max_con_encode.simps list.map)
 apply(subst max_constant_stack_nat.simps)
        apply( simp add: subtail_aexp_max_constant sub_aexp_max_constant  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps aexp_max_constant.simps
                    aexp_max_constant_nat.simps aexp_max_constant_tail.simps )
 apply(subst max_constant_stack_nat.simps)
      apply( simp add: sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps aexp_max_constant.simps
                    aexp_max_constant_nat.simps aexp_max_constant_tail.simps )
     apply (simp only: sub_push_con  flip: max_con_encode.simps list.map)
 apply(subst max_constant_stack_nat.simps)
        apply( simp add: subtail_aexp_max_constant sub_aexp_max_constant  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps max_constant_stack_nat.simps
                add_res.simps add_res_nat.simps push_con_nat.simps push_con.simps aexp_max_constant.simps
                    aexp_max_constant_nat.simps aexp_max_constant_tail.simps )
  done


lemma max_constant_stack_correct:
"max_constant_stack (push_con c s) = max_constant_stack (add_res (max_constant c) s)"
  apply(induct c arbitrary: s)
  apply auto
  done





fun atomExp_var_nat:: "nat \<Rightarrow> nat" where
"atomExp_var_nat n = (if fst_nat n = 0 then cons (snd_nat n) 0 else 0)"

definition atomExp_var_tail :: "nat \<Rightarrow> nat" where 
"atomExp_var_tail n = atomExp_var_nat n"

lemma subtail_atomExp_var:
"atomExp_var_tail n = atomExp_var_nat n"
  using atomExp_var_tail_def by auto

lemma sub_atomExp_var: "atomExp_var_nat (atomExp_encode x) = vname_list_encode (atomExp_var x)"
  apply (cases x)
  apply (auto simp only: atomExp_encode.simps atomExp_var_nat.simps)
   apply (auto simp add:vname_list_encode_def cons_def sub_fst sub_snd prod_encode_eq)
  done


definition aexp_vars_nat:: "nat \<Rightarrow> nat" where
"aexp_vars_nat n =  ( if hd_nat n = 1 \<or> hd_nat n = 2 then
             append_nat (atomExp_var_nat (nth_nat (Suc 0) n)) (atomExp_var_nat(nth_nat (Suc (Suc 0)) n))
                    else atomExp_var_nat (nth_nat (Suc 0) n))"

definition aexp_vars_tail:: "nat \<Rightarrow> nat" where
"aexp_vars_tail n =  ( if hd_nat n = 1 \<or> hd_nat n = 2 then
             append_tail (atomExp_var_tail (nth_nat (Suc 0) n)) (atomExp_var_tail(nth_nat (Suc (Suc 0)) n))
                    else atomExp_var_tail (nth_nat (Suc 0) n))"

lemma subtail_aexp_vars:
"aexp_vars_tail n = aexp_vars_nat n"
  apply (auto simp only: aexp_vars_tail_def aexp_vars_nat_def
            subtail_append subtail_atomExp_var )
  done

lemma sub_aexp_vars : "aexp_vars_nat (aexp_encode x) = vname_list_encode (aexp_vars x)"
  apply (cases x)
      apply (auto simp only: aexp_vars_nat_def aexp_encode.simps sub_hd head.simps sub_nth nth.simps
 sub_append sub_atomExp_var aexp_vars.simps vname_list_encode_def)
      apply auto
  done

datatype all_var = Bot "vname list"|
                   SKIP |
                   Assign vname  aexp  |
                   If_0  vname  "Com.com" "Com.com" |
                   If_m  vname "Com.com" "Com.com" "vname list"|
                   If_f  vname "Com.com" "Com.com" "vname list" "vname list"|
                   Seq_0 "Com.com" "Com.com" |
                   Seq_m  "Com.com" "Com.com" "vname list"|
                   Seq_f  "Com.com" "Com.com" "vname list" "vname list"|
                   While_0 vname "Com.com"|
                   While_f vname "Com.com" "vname list"

fun all_var_encode :: "all_var  \<Rightarrow> nat" where 
"all_var_encode SKIP = list_encode [0]"|
"all_var_encode (Assign v aexp) = list_encode [1,vname_encode v,aexp_encode aexp]"|
"all_var_encode (Seq_0 c1 c2) = list_encode [2, com_encode c1 , com_encode c2]"|
"all_var_encode (Seq_m c1 c2 n) = list_encode [3, com_encode c1 , com_encode c2, vname_list_encode n] "|
"all_var_encode (Seq_f c1 c2 n m) = list_encode [4, com_encode c1 , com_encode c2,vname_list_encode n, vname_list_encode m] "|
"all_var_encode (If_0  v c1 c2) = list_encode [5, vname_encode v, com_encode c1 , com_encode c2]"|
"all_var_encode (If_m  v c1 c2 n) = list_encode [6, vname_encode v,  com_encode c1 , com_encode c2,vname_list_encode n] "|
"all_var_encode (If_f  v c1 c2 n m) = list_encode [7, vname_encode v, com_encode c1 , com_encode c2,vname_list_encode n, vname_list_encode m] "|
"all_var_encode (While_0 v c) = list_encode [8,vname_encode v, com_encode c]"|
"all_var_encode (While_f v c n) = list_encode[9, vname_encode v, com_encode c ,vname_list_encode n]"|
"all_var_encode (Bot n) = list_encode[10, vname_list_encode n]"



fun push_var :: "Com.com \<Rightarrow> all_var list \<Rightarrow> all_var list " where 
"push_var Com.com.SKIP s = SKIP # s"|
"push_var (Com.com.Assign v a) s = Assign v a # s "|
"push_var (Com.com.Seq c1 c2) s = Seq_0 c1 c2 # s"|
"push_var (Com.com.If v c1 c2) s = If_0 v c1 c2 # s"|
"push_var (Com.com.While v c ) s = While_0 v c # s"

lemma push_var_Nil:
"push_var c s \<noteq> []"
  apply(cases c)
  apply auto
  done

fun push_var_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"push_var_nat c s = (let con = hd_nat c; e1 = nth_nat (Suc 0) c; e2 =nth_nat (Suc (Suc 0)) c;
    e3 = nth_nat (Suc (Suc (Suc 0))) c in
     if con = 0 then (0##0) ## s else 
     if con = 1 then c ## s else 
     if con = 2 then c ## s else 
     if con = 3 then (5 ##e1 ## e2 ## e3 ## 0) ## s else 
     (8 ## e1 ## e2 ## 0) ## s
)"


lemma sub_push_var :
"push_var_nat (com_encode c) (list_encode (map all_var_encode s))
= list_encode (map all_var_encode (push_var c s)) "
  apply(cases c)
  apply (auto simp add: sub_hd sub_cons sub_tl cons0  simp del: list_encode.simps)
  done

fun add_var :: " vname list \<Rightarrow> all_var list \<Rightarrow> all_var list" where 
"add_var n [] = [Bot n]"|
"add_var vs (Seq_0 c1 c2 # s) = Seq_m c1 c2 vs # s"|
"add_var vs' (Seq_m c1 c2 vs #s) = Seq_f c1 c2 vs vs' # s "|
"add_var vs  (If_0 v c1 c2 # s) = If_m v c1 c2 vs # s"|
"add_var vs' (If_m v c1 c2 vs #s) = If_f v c1 c2 vs vs' # s "|
"add_var vs' (While_0 v c #s) = While_f v c vs'  # s"|
"add_var vs' s = s"

lemma add_var_Nil:
"add_var n s \<noteq> []"
  apply (cases s)
   apply auto
  subgoal for a xs 
    apply(cases a)
           apply auto
    done
  done


fun add_var_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add_var_nat n s = (
  if s = 0 then  (10##n##0) ## 0
else (let h =hd_nat s; t =tl_nat s; c = hd_nat h; e1 = nth_nat (Suc 0) h ; e2 = nth_nat (Suc (Suc 0)) h;
e3 = nth_nat (Suc (Suc (Suc 0))) h; e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h  in
if c = 2 then (3##e1##e2##n##0)##t else 
if c = 3 then (4##e1##e2##e3##n##0)##t else 
if c = 5 then (6##e1##e2##e3##n ##0)##t else 
if c = 6 then (7##e1##e2##e3##e4 ## n ##0)##t else 
if c = 8 then (9##e1##e2##n##0)##t else s   )

)"

lemma sub_add_var:
"add_var_nat (vname_list_encode n) (list_encode (map all_var_encode s))
= list_encode (map all_var_encode (add_var n s))"
  apply (cases s)
   apply (auto simp add:cons0 sub_cons non_empty_not_zero sub_hd sub_tl
           simp del: list_encode.simps(2))
  subgoal for a xs
    apply(cases a)
           apply( auto simp add: Let_def sub_hd cons0 sub_cons sub_tl  simp del: list_encode.simps(2))
    done
  done

function all_variables_stack :: "all_var list \<Rightarrow>vname list" where 
"all_variables_stack (Bot x # s) = x"|
"all_variables_stack (SKIP # s) = all_variables_stack (add_var [] s)"|
"all_variables_stack (Assign v a # s) = all_variables_stack (add_var (v # aexp_vars a) s)"|
"all_variables_stack (Seq_0 c1 c2 # s) = all_variables_stack (push_var c1 (Seq_0 c1 c2 # s)) "|
"all_variables_stack (Seq_m c1 c2 n0 # s) =all_variables_stack (push_var c2  (Seq_m c1 c2 n0 # s))"|
"all_variables_stack (Seq_f _ _ n m #s) = all_variables_stack (add_var (n @ m) s)"|
"all_variables_stack (If_0 v c1 c2 # s) = all_variables_stack (push_var c1 (If_0  v c1 c2 # s)) "|
"all_variables_stack (If_m v c1 c2 n0 # s) =all_variables_stack (push_var c2  (If_m v c1 c2 n0 # s))"|
"all_variables_stack (If_f v _ _ n m #s) = all_variables_stack (add_var (v # n @ m) s)"|
"all_variables_stack (While_0 v c# s) = all_variables_stack (push_var c (While_0 v c# s)) "|
"all_variables_stack (While_f v _  n# s) = all_variables_stack (add_var (v#n) s)"
  sorry
termination sorry

function all_variables_stack_nat :: "nat \<Rightarrow> nat" where 
"  all_variables_stack_nat s = (let h = hd_nat s; t = tl_nat s;
  c = hd_nat h; e1 = nth_nat (Suc 0) h; e2 = nth_nat (Suc (Suc 0)) h;
 e3 = nth_nat (Suc (Suc (Suc 0))) h ; e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h; e5 = 
  nth_nat (Suc (Suc (Suc (Suc (Suc  0))))) h in 
 if c = 0 then all_variables_stack_nat (add_var_nat 0 t) 
else if c = 1 then all_variables_stack_nat (add_var_nat (e1 ## aexp_vars_tail e2) t)
else if c = 2 then  all_variables_stack_nat (push_var_nat e1 s) 
else if c = 3 then   all_variables_stack_nat (push_var_nat e2 s)
else if c = 4 then   all_variables_stack_nat (add_var_nat (append_nat e3 e4) t)
else if c = 5 then   all_variables_stack_nat (push_var_nat e2 s)
else if c = 6 then   all_variables_stack_nat (push_var_nat e3 s)  
else if c = 7 then   all_variables_stack_nat (add_var_nat (e1 ## append_nat e4 e5) t)
else if c = 8 then   all_variables_stack_nat (push_var_nat e2 s)
else if c = 9 then  all_variables_stack_nat (add_var_nat (e1 ## e3) t)
else e1)"
  sorry
termination sorry


lemma all_variables_stack_correct:
"all_variables_stack (push_var c s) = all_variables_stack (add_var(all_variables c) s)"
  apply(induct c arbitrary: s)
  apply auto
  done
lemma vname_list_encode_Nil: "vname_list_encode [] = 0" 
  apply (auto simp add: vname_list_encode_def)
  done

lemma sub_all_variables_stack:
"s \<noteq> [] \<Longrightarrow> all_variables_stack_nat (list_encode (map all_var_encode s))
= vname_list_encode (all_variables_stack s) "
  apply(induct s rule: all_variables_stack.induct)
         apply(subst all_variables_stack_nat.simps)
         apply( simp add: Let_def sub_hd sub_tl 
          del: list_encode.simps(2) all_variables_stack_nat.simps )
 apply(subst all_variables_stack_nat.simps)
           apply( simp add: sub_add_var Let_def sub_hd sub_tl add_var_Nil push_var_Nil list_encode_0
                  flip: vname_list_encode_Nil
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps  )
 apply(subst all_variables_stack_nat.simps)
        apply( simp add: subtail_aexp_vars sub_cons vname_list_encode_def  sub_aexp_vars  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
  apply(simp add: sub_add_var add_var_Nil flip:list.map vname_list_encode_def  del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
 apply(subst all_variables_stack_nat.simps)
      apply(simp add: sub_add_res Let_def sub_hd sub_tl add_var_Nil push_var_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
      apply (simp only: sub_push_var  flip: all_var_encode.simps list.map)
 apply(subst all_variables_stack_nat.simps)
      apply(simp add: sub_add_res Let_def sub_hd sub_tl add_var_Nil push_var_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
        apply (simp only: sub_push_var  flip: all_var_encode.simps list.map)
 apply(subst all_variables_stack_nat.simps)
        apply( simp add: subtail_aexp_vars sub_cons vname_list_encode_def sub_append  sub_aexp_vars  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
  apply(simp add: sub_add_var add_var_Nil flip:list.map vname_list_encode_def map_append  del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
apply(subst all_variables_stack_nat.simps)
      apply(simp add: sub_add_res Let_def sub_hd sub_tl add_var_Nil push_var_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
      apply (simp only: sub_push_var  flip: all_var_encode.simps list.map)
 apply(subst all_variables_stack_nat.simps)
      apply(simp add: sub_add_res Let_def sub_hd sub_tl add_var_Nil push_var_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
        apply (simp only: sub_push_var  flip: all_var_encode.simps list.map)
 apply(subst all_variables_stack_nat.simps)
        apply( simp add: subtail_aexp_vars sub_cons vname_list_encode_def sub_append  sub_aexp_vars  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
  apply(simp add: sub_add_var add_var_Nil flip:list.map vname_list_encode_def map_append  del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
 apply(subst all_variables_stack_nat.simps)
      apply(simp add: sub_add_res Let_def sub_hd sub_tl add_var_Nil push_var_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
        apply (simp only: sub_push_var  flip: all_var_encode.simps list.map)
 apply(subst all_variables_stack_nat.simps)
        apply( simp add: subtail_aexp_vars sub_cons vname_list_encode_def sub_append  sub_aexp_vars  sub_add_res Let_def sub_hd sub_tl add_res_Nil push_con_Nil list_encode_0
          del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
  apply(simp add: sub_add_var add_var_Nil flip:list.map vname_list_encode_def map_append  del: list_encode.simps all_variables_stack_nat.simps
                add_var.simps add_var_nat.simps push_var_nat.simps push_var.simps )
  done

definition all_variables_t :: "Com.com \<Rightarrow> vname list" where 
" all_variables_t c =  all_variables_stack (push_var c [])"

definition  all_variables_nat :: "nat \<Rightarrow> nat" where 
" all_variables_nat c =  all_variables_stack_nat (push_var_nat c 0)"

lemma subtailnat_all_variables:
" all_variables_nat (com_encode c) =  vname_list_encode (all_variables_t c)"
  by (metis all_variables_nat_def all_variables_t_def list.map(1) list_encode.simps(1) 
push_var_Nil sub_all_variables_stack sub_push_var)


lemma subt_all_variables:
"all_variables_t c = all_variables c"
  using all_variables_t_def  all_variables_stack_correct push_var_Nil
  by simp 


lemma sub_all_variables:"all_variables_nat (com_encode c) = vname_list_encode (all_variables c)"
  by (simp add: subt_all_variables subtailnat_all_variables)

definition all_variables_tail :: "nat \<Rightarrow> nat" where 
"all_variables_tail  c = all_variables_nat c"

lemma subtail_all_variables:
"all_variables_tail  c = all_variables_nat c"
  by (simp add: all_variables_tail_def)

definition max_constant_t :: "Com.com \<Rightarrow>nat" where 
" max_constant_t c =  max_constant_stack (push_con c [])"

definition  max_constant_nat :: "nat \<Rightarrow> nat" where 
" max_constant_nat c =  max_constant_stack_nat (push_con_nat c 0)"

lemma subtailnat_max_constant:
" max_constant_nat (com_encode c) =   (max_constant_t c)"
  by (metis max_constant_nat_def max_constant_t_def list.map(1) list_encode.simps(1) 
push_con_Nil sub_max_constant_stack sub_push_con)


lemma subt_max_constant:
"max_constant_t c = max_constant c"
  using max_constant_t_def  max_constant_stack_correct push_var_Nil
  by simp 


lemma sub_max_constant:"max_constant_nat (com_encode c) = (max_constant c)"
  by (simp add: subt_max_constant subtailnat_max_constant)

definition max_constant_tail :: "nat \<Rightarrow> nat" where 
"max_constant_tail  c = max_constant_nat c"

lemma subtail_max_constant:
"max_constant_tail  c = max_constant_nat c"
  by (simp add: max_constant_tail_def)


lemma sub_cons_vname: "cons (vname_encode x) (vname_list_encode xs) = vname_list_encode (x#xs)"
  apply (auto simp add:cons_def vname_list_encode_def) done
lemma sub_append_vname: "append_nat (vname_list_encode x) (vname_list_encode xs) = vname_list_encode (x@xs)"
  apply (induction x)
   apply (auto simp add: vname_list_encode_def sub_append simp flip: list_encode.simps)
  done





definition num_variables_nat :: "nat \<Rightarrow> nat" where 
"num_variables_nat n = length_nat (remdups_nat (all_variables_nat n))"

definition num_variables_tail :: "nat \<Rightarrow> nat" where 
"num_variables_tail n = length_tail (remdups_tail (all_variables_tail n))"

lemma subtail_num_variables:
"num_variables_tail n = num_variables_nat n"
  by (simp add: all_variables_tail_def num_variables_nat_def 
num_variables_tail_def subtail_length subtail_remdups)

lemma vname_encode_eq: "vname_encode x = vname_encode y \<Longrightarrow> x=y"
  apply (auto simp add:vname_encode_def list_encode_eq idchar)
  by (metis vname_encode_def vname_id)
lemma [simp]: "remdups (map (vname_encode) x) = map vname_encode (remdups x)"
  apply (induction x)
  using vname_encode_eq by auto
   
lemma sub_num_variables:"num_variables_nat (com_encode c) = num_variables c"
  apply (auto simp only:num_variables_nat_def sub_all_variables sub_remdups vname_list_encode_def
        sub_length num_variables_def)
  apply (induct "all_variables c"  arbitrary:c)
  by (auto simp add:map_def)
      
    
   

               
end