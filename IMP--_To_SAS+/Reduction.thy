\<^marker>\<open>creator Florian Keßler\<close>

section "Reduction"

theory Reduction imports Domains "Verified_SAT_Based_AI_Planning.SAS_Plus_Representation"
begin

datatype variable = VN vname | PC

type_synonym operator = "(variable, domain_element) sas_plus_operator"
type_synonym state = "(variable, domain_element) state"
type_synonym problem = "(variable, domain_element) sas_plus_problem"

fun all_variables :: "com \<Rightarrow> vname list" where
"all_variables (SKIP) = []" |
"all_variables (Assign v aexp) = [ v ] @ (case aexp of 
  A a \<Rightarrow> (case a of V v2 \<Rightarrow> [ v2 ] | N _ \<Rightarrow> []) |
  Plus a b \<Rightarrow> [ a ] |
  Sub a b \<Rightarrow> [ a ])" |
"all_variables (c1 ;; c2) = all_variables c1 @ all_variables c2" |
"all_variables (If v c1 c2) = [ v ] @ all_variables c1 @ all_variables c2" |
"all_variables (While v c) = [ v ] @ all_variables c"

definition enumerate_variables :: "com \<Rightarrow> vname list" where
"enumerate_variables c = remdups (all_variables c)"

fun all_subprograms :: "com \<Rightarrow> com list" where
"all_subprograms (SKIP) = [SKIP]" |
"all_subprograms (Assign v aexp) = [(Assign v aexp), SKIP]" |
"all_subprograms (c1 ;; c2) = (map (\<lambda> c. c ;; c2) (all_subprograms c1)) @ all_subprograms c1 
  @ all_subprograms c2" |
"all_subprograms (If v c1 c2) = [(If v c1 c2)] @ all_subprograms c1 @ all_subprograms c2" |
"all_subprograms (While v c) = [(While v c), SKIP] @ all_subprograms c @ 
  (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))"

definition enumerate_subprograms :: "com \<Rightarrow> com list" where
"enumerate_subprograms c = remdups (all_subprograms c)"

declare enumerate_subprograms_def[simp] 

lemma c_in_all_subprograms_c: "c \<in> set (enumerate_subprograms c)" 
  by (induction c) auto

lemma enumerate_subprograms_complete_step: "(c1, s1) \<rightarrow> (c2, s2) 
  \<Longrightarrow> c2 \<in> set (enumerate_subprograms c1)"
apply (induction c1 s1 c2 s2 rule: small_step_induct)
  using c_in_all_subprograms_c apply(auto)
done

lemma enumerate_subprograms_transitive: "c2 \<in> set (enumerate_subprograms c1) \<Longrightarrow> 
  c3 \<in> set (enumerate_subprograms c2) \<Longrightarrow> c3 \<in> set (enumerate_subprograms c1)"
proof (induction c1 arbitrary: c2 c3 rule: all_subprograms.induct)
  case (4 v c4 c5)
  then have "(c2 = (If v c4 c5)) \<or> (c2 \<in> set (all_subprograms c4)) 
              \<or> (c2 \<in> set (all_subprograms c5))"
      by (metis Un_iff all_subprograms.simps append.simps append.simps enumerate_subprograms_def set_ConsD set_append set_remdups)
  then show ?case
  proof (elim disjE)
    assume "c2 \<in> set (all_subprograms c5)" 
    then show ?thesis using 4 by auto
  next
    assume "c2 \<in> set (all_subprograms c4)"
    then show ?thesis using 4 by auto
  next
    assume "c2 = (If v c4 c5)"
    then show ?thesis using 4 by auto
  qed
next
  case (5 v c)
  then have "c2 \<in> set (all_subprograms (While v c))" by (metis enumerate_subprograms_def set_remdups)
  then have "c2 \<in> set ([While v c, SKIP] @ all_subprograms c @ map (\<lambda> x. x ;; (While v c)) (all_subprograms c))" 
    by (metis all_subprograms.simps enumerate_subprograms_def map_eq_conv set_append set_remdups) 
  then have "(c2 = (While v c)) \<or> c2 = SKIP \<or> (c2 \<in> set (all_subprograms c)) 
              \<or> (c2 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c)))" by simp
  then show ?case
  proof (elim disjE)
    assume "c2 = (While v c)"
    then show ?thesis using 5 by auto
  next
    assume "c2 = SKIP"
    then show ?thesis using 5 by auto
  next
    assume "c2 \<in> set (all_subprograms c)"
    then show ?thesis using 5 
      by (metis Un_iff all_subprograms.simps enumerate_subprograms_def set_append set_remdups)
  next
    assume "c2 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))"
    then obtain c' where *: "c2 = c' ;; (While v c) \<and> c' \<in> set (all_subprograms c)" by auto
    then have "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c')) \<or> c3 \<in> set (all_subprograms c')
      \<or> c3 \<in> set (all_subprograms (While v c))" using 5 by auto
    then show ?thesis
    proof (elim disjE)
      assume "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c'))"
      then have "c3 \<in> set (map (\<lambda> x. x ;; (While v c)) (all_subprograms c))" using * 5 by auto
      then show ?thesis by auto
    next
      assume "c3 \<in> set (all_subprograms c')"
      then have "c3 \<in> set (all_subprograms c)" using * 5 by auto
      then show ?thesis by auto
    next
      assume "c3 \<in> set (all_subprograms (While v c))"
      then show ?thesis using 5 by (metis enumerate_subprograms_def set_remdups)
    qed
  qed
qed auto

lemma enumerate_subprograms_complete: "(c1, s1)\<rightarrow>\<^bsup>t\<^esup> (c2, s2)
  \<Longrightarrow>  c2 \<in> set (enumerate_subprograms c1)"
proof(induction t arbitrary: c1 s1 c2 s2)
  case 0
  then show ?case using c_in_all_subprograms_c by auto
next
  case (Suc t)
  then obtain c1' s1' where "((c1, s1) \<rightarrow> (c1', s1')) \<and> ((c1', s1')\<rightarrow>\<^bsup>t\<^esup> (c2, s2))" by auto
  then show ?case using enumerate_subprograms_transitive Suc enumerate_subprograms_complete_step 
    by blast
qed

definition pc_to_com :: "com list \<Rightarrow> (variable \<times> domain_element) list \<Rightarrow> com" where
"pc_to_com cs as = cs ! (case snd (the (find (\<lambda> i. fst i = PC) as)) of Num x \<Rightarrow> x | \<omega> \<Rightarrow> 0)" 


definition index_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"index_of cs c = snd (the (find (\<lambda> i. fst i = c) (zip cs [0..<(length cs)])))"

definition index_of2 :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> nat" where
"index_of2 cs c = snd (the (find (\<lambda> i. fst (fst i) = c) (zip cs [0..<(length cs)])))"

fun com_to_operators :: "com list \<Rightarrow> com \<Rightarrow> domain_element list \<Rightarrow> operator list" where
"com_to_operators cs (SKIP) d = []" |
"com_to_operators cs (v ::= aexp) d = (let i = index_of cs (v ::= aexp) ; j = index_of cs SKIP in
  (case aexp of
    A a \<Rightarrow> (case a of
      N val \<Rightarrow> [\<lparr> precondition_of = [(PC, Num i)], 
                  effect_of = [(PC, Num j), (VN v, Num val)]\<rparr>] |
      V var \<Rightarrow> map (\<lambda> x. \<lparr> precondition_of = [(PC, Num i), (VN var, x)], 
                           effect_of = [(PC, Num j), (VN v, x)]\<rparr>) d) |
    Plus a b \<Rightarrow> map (\<lambda> x.  \<lparr> precondition_of = [(PC, Num i), (VN a, x)], 
                             effect_of = [(PC, Num j), (VN v, (case x of Num y \<Rightarrow> Num (y + b) | \<omega> \<Rightarrow> \<omega>))]\<rparr>) d | 
    Sub a b \<Rightarrow> map (\<lambda> x.  \<lparr> precondition_of = [(PC, Num i), (VN a, x)], 
                            effect_of = [(PC, Num j), (VN v, (case x of Num y \<Rightarrow> Num (y - b) | \<omega> \<Rightarrow> \<omega>))]\<rparr>) d))" |
"com_to_operators cs (c1;; c2) d = (let i = index_of cs (c1 ;; c2) in 
  (if c1 = SKIP then (let j = index_of cs c2 in [\<lparr> precondition_of = [(PC, Num i)],
                                                  effect_of = [(PC, Num j)]\<rparr>])
   else (let ops = com_to_operators cs c1 d in map (\<lambda> op. 
    (let j = index_of cs (pc_to_com cs (sas_plus_operator.effect_of op)) in 
      \<lparr> precondition_of = 
        list_update (sas_plus_operator.precondition_of op) 
                    (index_of2 (sas_plus_operator.precondition_of op) PC) (PC, Num i),
        effect_of = 
        list_update (sas_plus_operator.effect_of op) 
                    (index_of2 (sas_plus_operator.effect_of op) PC) (PC, Num j)\<rparr>)) ops)))" |
"com_to_operators cs (IF v\<noteq>0 THEN c1 ELSE c2) d = (let i = index_of cs (IF v\<noteq>0 THEN c1 ELSE c2) ;
  j = index_of cs c1 ; k = index_of cs c2 in map (\<lambda> x. 
    \<lparr> precondition_of = [(PC, Num i), (VN v, x)], 
      effect_of = [(PC, (if x = Num 0 then Num k else Num j))]\<rparr>) d)" |
"com_to_operators cs (WHILE v\<noteq>0 DO c) d = (let i = index_of cs (WHILE v\<noteq>0 DO c) ;
  j = index_of cs (c ;; (WHILE v\<noteq>0 DO c)); k = index_of cs SKIP in map (\<lambda> x. 
    \<lparr> precondition_of = [(PC, Num i), (VN v, x)], 
      effect_of = [(PC, (if x = Num 0 then Num k else Num j))]\<rparr>) d)"

definition coms_to_operators :: "com list \<Rightarrow> domain_element list \<Rightarrow> operator list" where
"coms_to_operators cs d = concat (map (\<lambda> c. com_to_operators cs c d) cs)"

definition state_by_pc_and_vars :: 
  "com list \<Rightarrow> com  \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> domain_element list \<Rightarrow> state" where
"state_by_pc_and_vars cs c vs d =  (\<lambda> v. (case v of 
  VN vn \<Rightarrow> (case vs vn of Some x \<Rightarrow> (if Num x \<in> set d then Some (Num x) else Some \<omega>) |
                          None \<Rightarrow> None) |
  PC \<Rightarrow> Some (Num (index_of cs c))))"

definition imp_minus_minus_to_sas_plus :: "com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> problem" where
"imp_minus_minus_to_sas_plus c vs t = (let cs = enumerate_subprograms c ; 
  d = domain c t ; 
  pc_d = map (\<lambda> i. Num i) [0..<(length cs + 1)] in
    \<lparr> variables_of = PC # (map (\<lambda> v. VN v) (enumerate_variables c)),
      operators_of = coms_to_operators cs d, 
      initial_of = state_by_pc_and_vars cs c vs d,
      goal_of = state_by_pc_and_vars cs SKIP Map.empty d,
      range_of = map_of ((PC, pc_d) # map (\<lambda> v. (VN v, d)) (enumerate_variables c))\<rparr>)"

end