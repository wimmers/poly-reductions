theory IMP_Minus_Minus_To_SAS_Plus_Plus_Reduction_Nat
  imports "../IMP-_To_IMP--/Primitives" IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations_Nat  IMP_Minus_Minus_Subprograms_Nat
 IMP_Minus_Minus_To_SAS_Plus_Plus_Reduction  
begin                               
definition domain_nat :: "nat" where
"domain_nat = list_encode [prod_encode(0,0), prod_encode(0,1)]"

lemma sub_domain: "domain_nat = list_encode (map domain_element_encode domain)"
  apply (auto simp add:domain_nat_def)
  done

definition pc_to_com_nat :: "nat\<Rightarrow> nat" where
"pc_to_com_nat l =(if fst_nat(snd_nat(hd_nat l)) = 1 then snd_nat (snd_nat (hd_nat l)) 
                  else  0##0)"

lemma sub_pc_to_com :
  "pc_to_com_nat (sas_assignment_list_encode l) = comm_encode (pc_to_com l)"
  apply (cases l)
  apply (auto simp only: pc_to_com_nat_def sas_assignment_list_encode_def sub_hd 
              pc_to_com_def list.map head.simps sas_assignment_encode.simps
                    sub_snd snd_def nth.simps 
                  split:list.splits)
  apply(simp add:fst_nat_def snd_nat_def prod_decode_def prod_decode_aux.simps cons_def)
      
  subgoal for a b l
    apply (cases b)
     apply (auto simp only: domain_element_encode.simps sub_snd snd_def sub_fst cons0)
     apply auto
    done
  done

declare nth_nat.simps[simp del]

fun map_com_to_operators:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_com_to_operators c c2 n = (if n = 0 then 0 else 
 (let c1' = pc_to_com_nat (nth_nat (Suc 0) (hd_nat n)) in  
        (list_update_nat (nth_nat 0 (hd_nat n)) 0 (prod_encode (0,prod_encode(1,c))))##
        (list_update_nat (nth_nat (Suc 0) (hd_nat n)) 0 (prod_encode(0, prod_encode(1, 2 ##c1'##c2##0))))##0 )
## map_com_to_operators c c2 (tl_nat n)
)"

lemma submap_com_to_operators:
"map_com_to_operators c c2 n =
 map_nat (\<lambda> op. 
    (let c1' = pc_to_com_nat (nth_nat (Suc 0) op) in  
        (list_update_nat (nth_nat 0 op) 0 (prod_encode (0,prod_encode(1,c))))##
        (list_update_nat (nth_nat (Suc 0) op) 0 (prod_encode(0, prod_encode(1, 2 ##c1'##c2##0))))##0 )) n
 "
  apply (induct c c2 n rule:map_com_to_operators.induct)
  apply auto
  done
fun map_com_to_operators2 :: "nat \<Rightarrow> nat" where 
" map_com_to_operators2 n = (if n = 0 then 0 else (prod_encode(Suc (hd_nat n), prod_encode(0,0)))##  map_com_to_operators2 (tl_nat n))"

lemma submap_com_to_operators2: 
" map_com_to_operators2 n =  map_nat (\<lambda>v. prod_encode(Suc v, prod_encode(0,0))) n"
  apply (induct n rule:map_com_to_operators2.induct)
  apply auto
  done

fun  map_com_to_operators3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"map_com_to_operators3 i c1 n  = (if n =0 then 0 else ((((prod_encode(0, i))## (prod_encode(Suc (hd_nat n), prod_encode(0,1)))##0)## 
         ((prod_encode(0, prod_encode(1, c1)))##0)## 0)) ##map_com_to_operators3 i c1 (tl_nat n))"

lemma submap_com_to_operators3:
"map_com_to_operators3 i c1 n = map_nat (\<lambda> v. 
      ( ((prod_encode(0, i))## (prod_encode(Suc v, prod_encode(0,1)))##0)## 
         ((prod_encode(0, prod_encode(1, c1)))##0)## 0)) n"
  apply (induct i c1 n rule:map_com_to_operators3.induct)
  apply auto
  done

fun  map_com_to_operators4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>nat" where 
"map_com_to_operators4 i j n = (if n=0 then 0 else (( (((prod_encode(0, i)) ## (prod_encode (Suc (hd_nat n), prod_encode(0,1) )) ##0)) ## 
         (((prod_encode(0, j))##0) ## 0 ))) ## map_com_to_operators4 i j (tl_nat n))"

lemma submap_com_to_operators4:
"map_com_to_operators4 i j n =  map_nat (\<lambda> v. 
      ( (((prod_encode(0, i)) ## (prod_encode (Suc v, prod_encode(0,1) )) ##0)) ## 
         (((prod_encode(0, j))##0) ## 0 ))) n "
  apply (induct i j n rule:map_com_to_operators4.induct)
  apply auto
  done

fun com_to_operators_nat :: "nat \<Rightarrow> nat" where
"com_to_operators_nat c = (if c = 0 \<or> hd_nat c = 0 then 0 else 
if hd_nat c = 1 then (
                        ((prod_encode(0,prod_encode(1,c)))##0)
                        ##
                          (
                              (prod_encode(0,prod_encode(1,0##0)))
                                ##
                              (prod_encode(Suc (nth_nat (Suc 0) c),prod_encode(0,nth_nat (Suc (Suc 0)) c)))
                               ##0
                          )
                        ##0)##0
else if hd_nat c = 2 then (let c1 = nth_nat (Suc 0) c; c2= nth_nat (Suc (Suc 0)) c in 
  (if c1 = 0##0 then (((prod_encode(0,prod_encode(1,c)))##0)##((prod_encode(0,prod_encode(1,c2)))##0)##0)##0
else  (let ops = com_to_operators_nat c1 in map_com_to_operators c c2 ops)))
else if hd_nat c = 3 then 
(let i = prod_encode (1, c); vs = nth_nat (Suc 0) c ; c1 = nth_nat (Suc (Suc 0)) c ; c2 = nth_nat (Suc (Suc (Suc 0))) c
   in  ( ((prod_encode(0, i)) ## map_com_to_operators2 (remdups_nat vs))## 
        ((prod_encode(0, prod_encode(1, c2)))##0)## 0)
      ## map_com_to_operators3 i c1 vs)
else (let i = prod_encode(1,c) ;  vs = nth_nat (Suc 0) c ; c' = nth_nat (Suc (Suc 0)) c ; 
  j = prod_encode(1, (2##c'## c##0)); k = prod_encode(1, 0##0) in 
    ( ((prod_encode(0, i)) ##  map_com_to_operators2 (remdups_nat vs))## 
        (((prod_encode(0, k))##0))##0) 
      ## map_com_to_operators4 i j vs))
"
declare nth_nat.simps[simp]

lemma com_to_operators_inv: 
  "\<lbrakk> c \<noteq> SKIP ; L = com_to_operators c; l \<in>set L \<rbrakk> \<Longrightarrow> effect_of l \<noteq>[] \<and> (\<exists>x y. effect_of l!0 = (y,PCV x))"
  apply (induct c arbitrary:l L rule: com_to_operators.induct )
      apply (auto simp add:  Let_def split:if_splits  )
  done
  
lemma sub_map_dec: "map_nat P xs = list_encode (map P (list_decode xs))"
  using sub_map list_decode_inverse by metis


lemma comm_encode_eq : "(comm_encode c1 = comm_encode c2) = (c1 = c2)"
  apply (cases c2)
  apply (induct c1 arbitrary:c2)
          apply (auto simp add:prod_encode_eq)
  apply (metis One_nat_def comm_encode.simps(2) comm_id list_encode.simps(1) list_encode.simps(2))
  apply (metis comm_encode.simps(3) comm_id list_encode.simps(1) list_encode.simps(2))
   apply (metis comm_encode.simps(4) comm_id list_encode.simps(1) list_encode.simps(2))
  by (metis comm_encode.simps(5) comm_id cons0 cons_def list_encode.simps(2))


  
lemma list_encode_empty:"(list_encode l = 0) =(l = [])"
  apply (auto)
  using list_encode_eq by force

lemma suc_eq: "(Suc i = Suc j) = (i=j) "
  by simp

lemma list_update_nat_zero: "list_update_nat 0 0 n = 0"
  apply auto
  done

lemma sub_com_to_operators:
"com_to_operators_nat (comm_encode c) = list_encode (map operator_encode (com_to_operators c))"
  apply (induct rule:com_to_operators.induct)
      apply (subst com_to_operators_nat.simps)
      apply (auto simp only:sub_hd comm_encode.simps head.simps sub_cons cons0 sub_map )
      apply simp
       apply (subst com_to_operators_nat.simps)
     apply (auto simp only:sub_hd comm_encode.simps head.simps sub_cons cons0 sub_map sub_nth com_to_operators.simps
                                      nth.simps simp flip: domain_element_encode.simps  variable_encode.simps(2) sas_assignment_encode.simps comm_encode.simps(1) imp_assignment_encode.simps)
     apply (auto simp add: operator_encode_def sas_assignment_list_encode_def 
            sub_map list_encode_eq )[1]
      apply (subst com_to_operators_nat.simps)
     apply (auto simp only: sub_hd list_encode_eq suc_eq list_encode_empty comm_encode_eq head.simps sub_cons cons0 sub_map sub_map_dec sub_nth com_to_operators.simps
                         sub_list_update sas_plus_operator.simps sas_assignment_list_encode_def list.map prod_encode_eq  nth.simps sub_pc_to_com Let_def comp_def operator_encode_def
  domain_element_encode.simps  variable_encode.simps  sas_assignment_encode.simps
    map_map list_encode_inverse sub_remdups  comm_encode.simps submap_com_to_operators
  simp flip: comm_encode.simps(1) 
                          del: list_encode.simps hd_nat_def cons_def pc_to_com_nat_def map_nat.simps nth_nat.simps list_update_nat.simps  com_to_operators_nat.simps split:if_splits)
  apply (auto simp only:sub_pc_to_com simp flip:  sas_assignment_list_encode_def )
    apply (auto simp only: sas_assignment_list_encode_def list.simps map_update 
            sas_assignment_encode.simps variable_encode.simps domain_element_encode.simps comm_encode.simps)
   apply (subst com_to_operators_nat.simps)
  using vname_inj
   apply (auto simp only:sub_hd head.simps Let_def cons0 sub_cons sub_nth nth.simps sub_map_dec  bit_encode.simps 
        vname_list_encode_def sub_remdups list_encode_inverse map_map comp_def
sas_assignment_encode.simps variable_encode.simps domain_element_encode.simps comm_encode.simps list.simps
    remdups_map submap_com_to_operators2  submap_com_to_operators3
   )
   apply simp
   apply (subst com_to_operators_nat.simps)
  using vname_inj
   apply (auto simp only:sub_hd  submap_com_to_operators2 head.simps Let_def cons0 sub_cons sub_nth nth.simps sub_map_dec  bit_encode.simps 
        vname_list_encode_def sub_remdups list_encode_inverse map_map comp_def
sas_assignment_encode.simps variable_encode.simps domain_element_encode.simps comm_encode.simps list.simps
    remdups_map submap_com_to_operators4
   )
  apply simp
  done

fun map_coms_to_operators :: "nat \<Rightarrow> nat" where 
"map_coms_to_operators n = (if n = 0 then 0 else (com_to_operators_nat (hd_nat n)) ## map_coms_to_operators (tl_nat n))"
 
lemma submap_coms_to_operators : 
"map_coms_to_operators n  = map_nat com_to_operators_nat n "
  apply (induct n rule:map_coms_to_operators.induct)
  apply auto
  done
definition coms_to_operators_nat :: "nat \<Rightarrow> nat" where
"coms_to_operators_nat cs = concat_nat (map_coms_to_operators cs)"

lemma sub_coms_to_operators:
    "coms_to_operators_nat (list_encode( map comm_encode cs)) = 
          list_encode (map operator_encode (coms_to_operators cs)) "
  apply (auto simp only: coms_to_operators_nat_def sub_map map_map comp_def
        sub_com_to_operators submap_coms_to_operators )
  apply (auto simp only: coms_to_operators_def sub_concat map_concat simp flip: comp_def[of "list_encode" "%x.(map operator_encode (com_to_operators x))"]
            map_map)
  apply (auto simp add: comp_def)
  done



definition imp_minus_minus_to_sas_plus_list::
"com \<Rightarrow> (vname,bit) assignment list  \<Rightarrow> (vname,bit) assignment list \<Rightarrow> 
      (variable,domain_element) sas_plus_list_problem" where 
"imp_minus_minus_to_sas_plus_list c I G = (let cs = enumerate_subprograms c ; 
  initial_vs = restrict_list I (enumerate_variables c) ;
  goal_vs = restrict_list G (enumerate_variables c) ;
  pc_d = map (\<lambda> i. PCV i) cs in
    \<lparr> variables_ofl = PC # (map VN (enumerate_variables c)),
      operators_ofl = coms_to_operators cs, 
      initial_ofl = imp_minus_state_to_sas_plus_list (c, initial_vs),
      goal_ofl = imp_minus_state_to_sas_plus_list (SKIP, goal_vs),
      range_ofl = (PC, pc_d)#(map (\<lambda> v. (VN v, domain)) (enumerate_variables c))\<rparr>)"

lemma sublist_imp_minus_minus_to_sas_plus:
"list_problem_to_problem (imp_minus_minus_to_sas_plus_list c I G) = 
    imp_minus_minus_to_sas_plus c (map_of I) (map_of G)"
  apply (auto simp add:
          imp_minus_minus_to_sas_plus_list_def list_problem_to_problem.simps
          sub_restrict_list Let_def sas_plus_problem.simps sas_plus_list_problem.simps
            sublist_imp_minus_state_to_sas_plus 
            imp_minus_minus_to_sas_plus_def  )
  done
fun map_PCV :: "nat \<Rightarrow> nat" where 
"map_PCV n = (if n = 0 then 0 else  (prod_encode(1, hd_nat n))## map_PCV (tl_nat n))"

lemma submap_PCV : 
"map_PCV n =  map_nat (\<lambda> i. prod_encode(1, i)) n "
  apply (induct n rule: map_PCV.induct)
  apply (auto)
  done

fun map_Suc :: "nat \<Rightarrow> nat" where 
"map_Suc n = (if n = 0 then 0 else (Suc(hd_nat n)) ## (map_Suc (tl_nat n)))"

lemma submap_Suc :
"map_Suc n = map_nat Suc n"
  apply (induct n rule:map_Suc.induct)
  apply auto
  done

fun map_domain :: "nat\<Rightarrow> nat" where 
"map_domain n = (if n = 0 then 0 else (prod_encode(Suc (hd_nat n), domain_nat)) ## map_domain (tl_nat n))"

lemma submap_domain :
"map_domain n = map_nat (\<lambda> v. (prod_encode(Suc v, domain_nat))) n"
  apply (induct n rule:map_domain.induct)
  apply auto
  done

definition imp_minus_minus_to_sas_plus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"imp_minus_minus_to_sas_plus_nat c I G = (let cs = enumerate_subprograms_nat c ; 
  initial_vs = restrict_nat I (enumerate_variables_nat c) ;
  goal_vs = restrict_nat G (enumerate_variables_nat c) ;
  pc_d = map_PCV cs in
   (0 ## (map_Suc (enumerate_variables_nat c)))## 
      (coms_to_operators_nat cs) ## 
      (imp_minus_state_to_sas_plus_nat (prod_encode (c, initial_vs)))##
      (imp_minus_state_to_sas_plus_nat (prod_encode (0##0, goal_vs)))##
      ((prod_encode(0, pc_d))##(map_domain (enumerate_variables_nat c)))##0 )"

lemma subnat_imp_minus_minus_to_sas_plus:
"imp_minus_minus_to_sas_plus_nat (comm_encode c) 
            (imp_assignment_list_encode I) (imp_assignment_list_encode G) =
 list_problem_encode (imp_minus_minus_to_sas_plus_list c I G)"
  apply (auto simp only: imp_minus_minus_to_sas_plus_nat_def
      sub_enumerate_subprograms sub_restrict_nat sub_enumerate_variables sub_map
      sub_cons cons0 Let_def submap_PCV submap_Suc submap_domain
)
  apply (auto simp only: vname_list_encode_def sub_map sub_cons
      sub_coms_to_operators sub_domain
   subnat_imp_minus_state_to_sas_plus map_map comp_def
        simp flip: comm_encode.simps(1) cilist_encode.simps variable_encode.simps(2))
  apply (auto simp only: subnat_imp_minus_state_to_sas_plus list_problem_encode_def  sas_plus_list_problem.simps 
              imp_minus_minus_to_sas_plus_list_def Let_def list.simps simp flip: comp_def map_map )
  apply (auto simp only: domain_element_encode.simps sas_assignment_list_encode_def map_map[of "vdlist_encode"] map_map[of "domain_element_encode"] comp_def vdlist_encode.simps variable_encode.simps)
  done

lemma sub_imp_minus_minus_to_sas:
"list_problem_to_problem (list_problem_decode (imp_minus_minus_to_sas_plus_nat (comm_encode c) 
            (imp_assignment_list_encode I) (imp_assignment_list_encode G)))
= imp_minus_minus_to_sas_plus c (map_of I) (map_of G)"
  apply (auto simp only: subnat_imp_minus_minus_to_sas_plus sublist_imp_minus_minus_to_sas_plus list_problem_id)
  done

   
  


      
        
        


    
end