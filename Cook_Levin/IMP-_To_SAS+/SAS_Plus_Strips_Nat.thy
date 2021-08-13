theory SAS_Plus_Strips_Nat 
  imports "Verified_SAT_Based_AI_Planning.SAS_Plus_STRIPS" "IMP-_To_IMP--/Primitives"
begin

definition possible_assignments_for_list
  :: "('variable, 'domain) sas_plus_list_problem \<Rightarrow> 'variable \<Rightarrow> ('variable \<times> 'domain) list" 
  where "possible_assignments_for_list \<Psi> v \<equiv> [(v, a). a \<leftarrow> the (map_list_find (range_ofl \<Psi>) v)]"

lemma sublist_possible_assignments_for:
"possible_assignments_for_list P v =
 possible_assignments_for (list_problem_to_problem P) v"
  apply (auto simp add: sub_map_list_find possible_assignments_for_list_def possible_assignments_for_def )
  done

definition possible_assignments_for_nat
  :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
  where "possible_assignments_for_nat P v \<equiv> map_nat (\<lambda>a. prod_encode(v, a)) (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) P) v))"

lemma vdlist_plus_simp:"vdlist_plus_encode = prod_encode o (\<lambda>(v,d). (var_encode v, list_encode (map dom_encode d)))"
  apply auto
  done
lemma subnat_possible_assignments_for_pre:
  assumes "v \<in> set (variables_ofl P)"
  assumes " v \<in> set (variables_ofl P ) \<Longrightarrow> map_list_find  (range_ofl P)  v \<noteq> None"
  shows
"possible_assignments_for_nat (list_problem_plus_encode P) (var_encode v)
= sas_plus_assignment_list_encode (possible_assignments_for_list P v)"
  using inj_var assms
  apply auto
  apply (auto simp only: possible_assignments_for_nat_def
              list_problem_plus_encode_def sub_nth nth.simps
sub_map_list_find_nat  inj_map_list_find[of var_encode]
            option_encode.simps the_nat.simps diff_Suc_1
 map_list_find_map  sub_map
possible_assignments_for_list_def
sas_plus_assignment_list_encode_def
vdlist_plus_simp simp flip:map_map 
)
  apply (auto simp add:comp_def)
  done

lemma inv_possible_assignments_for:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  assumes "v \<in> set (variables_ofl P)"
  shows "map_list_find  (range_ofl P)  v \<noteq> None"
proof -
  have "v \<in> set (sas_plus_problem.variables_of (list_problem_to_problem P))"
    using assms by auto
  hence "range_of (list_problem_to_problem P) v \<noteq> None" using assms apply (auto simp add:
    is_valid_problem_sas_plus_def ) 
    by (smt Ball_set_list_all)
  thus ?thesis by (auto simp add: sub_map_list_find)
qed

lemma subnat_possible_assignments_for:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  assumes "v \<in> set (variables_ofl P)"
  shows "possible_assignments_for_nat (list_problem_plus_encode P) (var_encode v)
= sas_plus_assignment_list_encode (possible_assignments_for_list P v)"
  using  subnat_possible_assignments_for_pre inv_possible_assignments_for assms by fastforce

definition all_possible_assignments_for_list
  :: "('variable, 'domain) sas_plus_list_problem \<Rightarrow> ('variable \<times> 'domain) list"
  where "all_possible_assignments_for_list \<Psi> 
    \<equiv> concat [possible_assignments_for_list \<Psi> v. v \<leftarrow> variables_ofl \<Psi>]" 

lemma sublist_all_possible_assignments_for:
" all_possible_assignments_for_list P =
all_possible_assignments_for (list_problem_to_problem P)"
  apply (auto simp add: all_possible_assignments_for_list_def all_possible_assignments_for_def
  sublist_possible_assignments_for)
  done

definition all_possible_assignments_for_nat::
   "nat \<Rightarrow> nat"
  where "all_possible_assignments_for_nat \<Psi> 
    \<equiv> concat_nat (map_nat (possible_assignments_for_nat \<Psi>) (nth_nat 0 \<Psi>))" 

lemma subnat_all_possible_assignments_for_map:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows " map (\<lambda>x. possible_assignments_for_nat (list_problem_plus_encode P) (var_encode x))
         (variables_ofl P) =
 map sas_plus_assignment_list_encode (map (\<lambda>x. possible_assignments_for_list P x)  (variables_ofl P))"
  apply (induct "variables_ofl P")
   apply simp
  using assms apply (auto simp del: list_problem_to_problem.simps)
  apply (auto simp add:subnat_possible_assignments_for simp del: list_problem_to_problem.simps)
  done

lemma subnat_all_possible_assignments_for:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows "all_possible_assignments_for_nat (list_problem_plus_encode P)
= sas_plus_assignment_list_encode (all_possible_assignments_for_list P)"
  using assms
  apply (auto simp only:all_possible_assignments_for_nat_def list_problem_plus_encode_def
            sub_nth nth.simps sas_plus_assignment_list_encode_def[of "all_possible_assignments_for_list P"] )
  apply (auto simp only: sub_map map_map comp_def all_possible_assignments_for_list_def 
    subnat_all_possible_assignments_for_map
 simp flip:list_problem_plus_encode_def)
  apply (auto simp only: sas_plus_assignment_list_encode_def sub_concat map_concat simp flip: map_map comp_def[of _ "\<lambda>x. map sas_plus_assignment_encode (possible_assignments_for_list P x)"] )
  apply (auto simp only:map_map comp_def)
  done

definition state_to_strips_state_list
  :: "('variable, 'domain) sas_plus_list_problem 
    \<Rightarrow> ('variable, 'domain) assignment list 
    \<Rightarrow> (('variable, 'domain) assignment ,bool) assignment list" 
  where "state_to_strips_state_list \<Psi> s 
    \<equiv> let defined = filter (\<lambda>v. map_list_find s v \<noteq> None) (variables_ofl \<Psi>) in
      map (\<lambda>(v, a). ((v, a), the (map_list_find s v) = a)) 
        (concat [possible_assignments_for_list \<Psi> v. v \<leftarrow> defined])"

lemma sublist_state_to_strips_state:
"map_of (state_to_strips_state_list P s) =
state_to_strips_state (list_problem_to_problem P) (map_of s)"
  apply (auto simp add:state_to_strips_state_list_def sub_map_list_find
state_to_strips_state_def sublist_possible_assignments_for)
  done

definition state_to_strips_state_nat
  :: "nat \<Rightarrow>nat \<Rightarrow>nat" 
  where "state_to_strips_state_nat \<Psi> s 
    \<equiv> let defined = filter_nat (\<lambda>v. map_list_find_nat s v \<noteq> 0) (nth_nat 0 \<Psi>) in
      map_nat (\<lambda>va. prod_encode(va, if the_nat (map_list_find_nat s (fst_nat va)) = snd_nat va then 1 else 0)) 
        (concat_nat (map_nat (possible_assignments_for_nat \<Psi>)  defined))"


lemma subnat_state_to_strips_state_map:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
shows
"map (\<lambda>x. possible_assignments_for_nat (list_problem_plus_encode P) (var_encode x))
           (filter (\<lambda>x. map_list_find s x \<noteq> None) (variables_ofl P))
= map  sas_plus_assignment_list_encode  ( map (possible_assignments_for_list P)
 (filter (\<lambda>x. map_list_find s x \<noteq> None) (variables_ofl P)) )"
  using assms apply (auto simp add: subnat_possible_assignments_for)
  done

lemma  possible_assignments_fst: "(x, b) \<in> set (possible_assignments_for_list P y) \<Longrightarrow> x = y"
  apply (auto simp add:possible_assignments_for_list_def)
  done

lemma subnat_state_to_strips_state:
  assumes "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows "state_to_strips_state_nat (list_problem_plus_encode P) (sas_plus_assignment_list_encode s)
= strips_assignment_list_encode (state_to_strips_state_list P s)"
  apply (auto simp only:state_to_strips_state_nat_def list_problem_plus_encode_def sub_nth nth.simps)
  apply (auto simp only: simp flip: list_problem_plus_encode_def)
  apply (auto simp only:       sub_filter  sas_plus_assignment_list_encode_def sas_plus_simp sub_map_list_find_nat option_encode_0
                    filter_map
            simp flip: map_map )
  using inj_var  apply (auto simp only:comp_def  inj_map_list_find  map_list_find_map_none 
subnat_possible_assignments_for Let_def sub_map map_map
)
  using assms apply(auto simp only:sub_map
state_to_strips_state_list_def
 sub_concat subnat_state_to_strips_state_map  sas_plus_list_simp simp flip:map_map map_concat)
  apply (auto simp only:map_map comp_def fst_sas_simp snd_sas_simp  inj_map_list_find
 strips_assignment_list_encode_def list_encode_eq Let_def
 )
  apply (induct "variables_ofl P")
   apply (auto simp del:list_problem_to_problem.simps)
  subgoal for a x y aa b ya
    apply (cases "map_list_find (map (\<lambda>(v, d). (v, dom_encode d)) s) aa")
    using possible_assignments_fst[of aa b P y] 
     apply (auto simp add: map_list_find_map_none map_list_find_map dom_inj_simp
          simp del:list_problem_to_problem.simps)
    done
 subgoal for a x y aa b ya
    apply (cases "map_list_find (map (\<lambda>(v, d). (v, dom_encode d)) s) aa")
    using possible_assignments_fst[of aa b P y] 
     apply (auto simp add: map_list_find_map_none map_list_find_map dom_inj_simp
          simp del:list_problem_to_problem.simps)
    done
  done

definition sasp_op_to_strips_list
  :: "('variable, 'domain) sas_plus_list_problem
    \<Rightarrow> ('variable, 'domain) sas_plus_operator
    \<Rightarrow> ('variable, 'domain) assignment strips_operator" 
  ("\<phi>\<^sub>O _ _" 99)
  where "sasp_op_to_strips_list \<Psi> op \<equiv> let
      pre = precondition_of op
      ; add = effect_of op
      ; delete = concat (map (\<lambda>(v,a). map (\<lambda>a'. (v, a')) (filter ((\<noteq>) a) (the (map_list_find (range_ofl \<Psi> )v)))) (effect_of op))
    in STRIPS_Representation.operator_for pre add delete"

lemma sublist_sasp_op_to_strips:
"sasp_op_to_strips_list P op = sasp_op_to_strips (list_problem_to_problem P) op"
  apply (auto simp add:sasp_op_to_strips_list_def  sasp_op_to_strips_def sub_map_list_find)
  done

fun operator_for_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"operator_for_nat pre add delete = pre ## add ## delete ##0 "

lemma sub_operator_for : "operator_for_nat (sas_plus_assignment_list_encode pre) (sas_plus_assignment_list_encode add) (sas_plus_assignment_list_encode delete)
= strips_operator_encode (operator_for pre add delete)"
  apply (auto simp add: sub_cons cons0 simp del: list_encode.simps)
  done


definition sasp_op_to_strips_nat
  :: "nat \<Rightarrow>nat \<Rightarrow> nat " 
  where "sasp_op_to_strips_nat \<Psi> op \<equiv> let
      pre = nth_nat 0 op
      ; add = nth_nat (Suc 0)  op
      ; delete = concat_nat (map_nat (\<lambda>n. map_nat (\<lambda>a'. prod_encode(fst_nat n, a')) (filter_nat ((\<noteq>) (snd_nat n)) (the_nat (map_list_find_nat (nth_nat (Suc (Suc (Suc (Suc 0)))) \<Psi> ) (fst_nat n))))) (nth_nat (Suc 0) op))
    in operator_for_nat pre add delete"




lemma subnat_sasp_op_to_strips_map:
  assumes "\<forall>(v,d)\<in> set (effect_of op). map_list_find (range_ofl P) v \<noteq> None"
  shows
"map (\<lambda>x. map_nat (\<lambda>a'. prod_encode (var_encode (fst x), a'))
                            (filter_nat ((\<noteq>) (dom_encode (snd x)))
                              (the_nat
                                (option_encode
                                  (map_list_find
                                    (map (\<lambda>(v, d).
                                             (var_encode v, list_encode (map dom_encode d)))
                                      (range_ofl P))
                                    (var_encode (fst x)))))))
                  (effect_of op) =
map (\<lambda>(v,d). map_nat (\<lambda>a'. prod_encode (var_encode v, a'))
                            (filter_nat ((\<noteq>) (dom_encode d))
                             (list_encode (map dom_encode (the (map_list_find (range_ofl P)  v))))))
                  (effect_of op)

"
  apply (induct "effect_of op")
  using inj_var
   apply  (auto simp del:map_nat.simps filter_nat.simps the_nat.simps )
  apply (auto simp only: inj_map_list_find[of var_encode])
  subgoal for a b x ax bx
    apply (cases "map_list_find (range_ofl P) ax")
    using assms apply 
(auto simp add:  map_list_find_map_none   simp del:map_nat.simps filter_nat.simps the_nat.simps
)
    subgoal for y
    apply (auto simp add:  map_list_find_map)
      done
    done
  done

lemma subnat_sasp_op_to_strips_map2: 
 "(\<lambda>(v, d).
                         list_encode
                          (map (\<lambda>a'. prod_encode (var_encode v, a'))
                            (filter ((\<noteq>) (dom_encode d))
                              (map dom_encode (the (map_list_find (range_ofl P) v))))))
= list_encode o (\<lambda>(v,d). map (\<lambda>a'. prod_encode (var_encode v, a'))
                            (filter ((\<noteq>) (dom_encode d))
                              (map dom_encode (the (map_list_find (range_ofl P) v)))))"
  apply (auto)
  done
lemma subnat_sasp_op_to_strips_map3:
"(\<lambda>(v, d).
                         map sas_plus_assignment_encode
                          (map (Pair v) (filter ((\<noteq>) d) (the (map_list_find (range_ofl P) v)))))
= map sas_plus_assignment_encode o (\<lambda>(v,d). map (Pair v) (filter ((\<noteq>) d) (the (map_list_find (range_ofl P) v))) )"
  apply auto
  done
lemma subnat_sasp_op_to_strips_inv:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"  "op \<in> set (operators_ofl P)"
  shows  "\<forall>(v,d)\<in> set (effect_of op). map_list_find (range_ofl P) v \<noteq> None"
  using assms
  apply (auto simp add: is_valid_problem_sas_plus_def is_valid_operator_sas_plus_def)
  by (smt case_prodD is_valid_operator_sas_plus_then(3) list_all_iff sas_plus_problem.select_convs(1) sub_map_list_find)

lemma subnat_sasp_op_to_strips_pre:
  assumes "\<forall>(v,d)\<in> set (effect_of op). map_list_find (range_ofl P) v \<noteq> None"
  shows   "sasp_op_to_strips_nat (list_problem_plus_encode P) (operator_plus_encode op) 
= 
strips_operator_encode (sasp_op_to_strips_list P op)"
  apply (auto simp only:sasp_op_to_strips_nat_def operator_plus_encode_def sub_nth nth.simps
          list_problem_plus_encode_def sub_map_list_find_nat vdlist_plus_simp
sas_plus_assignment_list_encode_def sub_map 

 simp flip: map_map )
  using inj_var apply (auto simp only: map_map comp_def fst_sas_simp snd_sas_simp

)
  using assms apply (auto simp only:subnat_sasp_op_to_strips_map sub_filter sub_map 
subnat_sasp_op_to_strips_map2  sub_concat simp flip: map_map
)
  apply (auto simp only:filter_map comp_def dom_inj_simp map_map simp flip:
sas_plus_assignment_encode.simps)
  apply (auto simp only: simp flip: comp_def map_map)
  apply (auto simp only: comp_def)
  apply (auto simp only: subnat_sasp_op_to_strips_map3
sasp_op_to_strips_list_def
  Let_def sub_operator_for simp flip: map_map map_concat
sas_plus_assignment_list_encode_def
)
  done

lemma subnat_sasp_op_to_strips:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"  "op \<in> set (operators_ofl P)"
  shows   "sasp_op_to_strips_nat (list_problem_plus_encode P) (operator_plus_encode op)
= 
strips_operator_encode (sasp_op_to_strips_list P op)"
  using assms  subnat_sasp_op_to_strips_pre  subnat_sasp_op_to_strips_inv by blast

definition problem_for_list
  :: "'variable list 
  \<Rightarrow> 'variable strips_operator list 
  \<Rightarrow> ('variable,bool) assignment list  
  \<Rightarrow> ('variable,bool) assignment list
  \<Rightarrow> ('variable) strips_list_problem"
  where "problem_for_list vs ops I gs \<equiv> \<lparr> 
    variables_of = vs
    , operators_of = ops
    , initial_of = I
    , goal_of = gs \<rparr>" 

lemma sublist_problem_for :
"strips_list_problem_to_problem (problem_for_list vs ops I gs) = 
problem_for vs ops (map_of I) (map_of gs)"
  apply (auto simp add:problem_for_list_def)
  done

definition sas_plus_problem_to_strips_problem_list
  :: "('variable, 'domain) sas_plus_list_problem \<Rightarrow> ('variable, 'domain) assignment strips_list_problem" 
  ("\<phi> _ " 99)
  where "sas_plus_problem_to_strips_problem_list \<Psi> \<equiv> let 
      vs =  concat (map (possible_assignments_for_list \<Psi>)(variables_ofl \<Psi>))
      ; ops = map (sasp_op_to_strips_list \<Psi>) (operators_ofl \<Psi>)
      ; I = state_to_strips_state_list \<Psi> (initial_ofl \<Psi>)
      ; G = state_to_strips_state_list \<Psi> (goal_ofl \<Psi>)
    in problem_for_list vs ops I G"

lemma sublist_sas_plus_problem_to_strips_problem:
"strips_list_problem_to_problem (sas_plus_problem_to_strips_problem_list P) =
sas_plus_problem_to_strips_problem (list_problem_to_problem P)"
  apply (auto simp only: Let_def
sublist_possible_assignments_for
sas_plus_problem_to_strips_problem_def
list_problem_to_problem.simps
sas_plus_list_problem.simps
sas_plus_problem.simps

  sas_plus_problem_to_strips_problem_list_def   
sublist_problem_for sublist_sasp_op_to_strips sublist_state_to_strips_state )
  apply (auto simp add:sublist_sasp_op_to_strips sublist_possible_assignments_for simp flip: list_problem_to_problem.simps)
  apply (meson sublist_possible_assignments_for)
  done
definition problem_for_nat
  :: "nat 
  \<Rightarrow> nat 
  \<Rightarrow> nat  
  \<Rightarrow> nat
  \<Rightarrow> nat"
  where "problem_for_nat vs ops I gs \<equiv> vs ## ops ## I ## gs ## 0 "

lemma subnat_problem_for: 
"problem_for_nat (sas_plus_assignment_list_encode vs) (strips_operator_list_encode ops)
(strips_assignment_list_encode I) (strips_assignment_list_encode gs)
= 
 strips_list_problem_encode(problem_for_list vs ops I gs)
 "
  apply (auto simp only: problem_for_nat_def sub_cons cons0 problem_for_list_def
strips_list_problem_encode.simps strips_list_problem.simps) done

definition sas_plus_problem_to_strips_problem_nat
  :: "nat\<Rightarrow>nat" 
  ("\<phi> _ " 99)
  where "sas_plus_problem_to_strips_problem_nat \<Psi> \<equiv> let 
      vs =  concat_nat (map_nat (possible_assignments_for_nat \<Psi>)(nth_nat 0 \<Psi>))
      ; ops = map_nat (sasp_op_to_strips_nat \<Psi>) (nth_nat (Suc 0) \<Psi>)
      ; I = state_to_strips_state_nat \<Psi> (nth_nat (Suc (Suc 0)) \<Psi>)
      ; G = state_to_strips_state_nat \<Psi> (nth_nat (Suc (Suc (Suc 0))) \<Psi>)
    in problem_for_nat vs ops I G"


lemma  subnat_sas_plus_problem_to_strips_problem_map:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows  "map (\<lambda>x. possible_assignments_for_nat (list_problem_plus_encode P)
                             (var_encode x))
                   (variables_ofl P)
  = map sas_plus_assignment_list_encode (map (possible_assignments_for_list P) (variables_ofl P))"
  using subnat_all_possible_assignments_for_map assms by blast

lemma  subnat_sas_plus_problem_to_strips_problem_map2:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows  "map (\<lambda>x. sasp_op_to_strips_nat (list_problem_plus_encode P)
                        (operator_plus_encode x))
              (operators_ofl P)
  = map strips_operator_encode (map (sasp_op_to_strips_list P) (operators_ofl P))"
  using assms subnat_sasp_op_to_strips
  by auto

lemma subnat_sas_plus_problem_to_strips_problem:
  assumes  "is_valid_problem_sas_plus (list_problem_to_problem P)"
  shows "sas_plus_problem_to_strips_problem_nat (list_problem_plus_encode P)
 =  strips_list_problem_encode (sas_plus_problem_to_strips_problem_list P)"
  apply (auto simp only: sas_plus_problem_to_strips_problem_nat_def
list_problem_plus_encode_def sub_nth nth.simps 
)
  using assms  apply (auto simp only: sub_map
              subnat_possible_assignments_for map_map comp_def 
              subnat_sasp_op_to_strips
subnat_state_to_strips_state 
 simp flip: list_problem_plus_encode_def)
  apply (auto simp only:subnat_sas_plus_problem_to_strips_problem_map sas_plus_list_simp 
sub_concat 
simp flip: map_map map_concat )
  apply (auto simp only: 
 simp flip: sas_plus_assignment_list_encode_def)
  apply (auto simp only:  subnat_sas_plus_problem_to_strips_problem_map2 simp flip: strips_operator_list_encode_def)
  apply (auto simp only: Let_def  subnat_problem_for sas_plus_problem_to_strips_problem_list_def )
  done



      
end