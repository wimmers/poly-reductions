\<^marker>\<open>creator Florian Keßler\<close>

section "Reduction"

theory Reduction imports Domains "Verified_SAT_Based_AI_Planning.SAS_Plus_Representation"
begin

datatype variable = VN vname | PC

type_synonym operator = "(variable, domain_element) sas_plus_operator"
type_synonym state = "(variable, domain_element) state"
type_synonym problem = "(variable, domain_element) sas_plus_problem"

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

fun all_variables :: "com \<Rightarrow> vname list" where
"all_variables (SKIP) = []" |
"all_variables (Assign v aexp) = [ v ] @ (case aexp of 
  A a \<Rightarrow> (case a of V v2 \<Rightarrow> [ v2 ] | N _ \<Rightarrow> []) |
  Plus a b \<Rightarrow> [ a ] |
  Sub a b \<Rightarrow> [ a ])" |
"all_variables (c1 ;; c2) = []" |
"all_variables (If v c1 c2) = [ v ]" |
"all_variables (While v c) = [ v ]"

definition enumerate_variables :: "com \<Rightarrow> vname list" where
"enumerate_variables c = remdups (concat (map all_variables (enumerate_subprograms c)))"

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

lemma SKIP_in_enumerate_subprograms[simp]: "SKIP \<in> set (enumerate_subprograms c)" 
  by (induction c rule: all_subprograms.induct) auto

lemma enumerate_subprogams_enumerate_variables: "c' \<in> set (enumerate_subprograms c) 
  \<Longrightarrow> set (all_variables c') \<subseteq> set (enumerate_variables c)" 
  by (auto simp: enumerate_variables_def)

fun index_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"index_of [] c = 0" |
"index_of (d # cs) c = (if d = c then 0 else Suc (index_of cs c))"

lemma index_of_element_in_list:
  "x \<in> set l \<Longrightarrow> index_of l x < length l"
  by (induction l) auto

lemma index_of_identity[simp]:
  "x \<in> set l \<Longrightarrow> (l ! (index_of l x) = x)"
  by (induction l) auto

fun index_of2 :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> nat" where
"index_of2 [] c = 0" |
"index_of2 ((d,_) # cs) c = (if d = c then 0 else Suc (index_of2 cs c))" 

lemma index_of2_in_list: "x \<in> set (map fst l) \<Longrightarrow> (\<forall>y. (x, y) \<in> set l \<longrightarrow> P y) 
  \<Longrightarrow> P (snd (l ! (index_of2 l x)))"
  apply (induction l) 
   apply auto
  by force

lemma index_of2_distinct: "(x, y) \<in> set l \<Longrightarrow> distinct (map fst l) 
  \<Longrightarrow> l ! (index_of2 l x) = (x, y)"
  apply(induction l)
   apply(auto)
  by force

definition pc_to_com :: "com list \<Rightarrow> (variable \<times> domain_element) list \<Rightarrow> com" where
"pc_to_com cs as = cs ! (case snd (as ! (index_of2 as PC)) of Num x \<Rightarrow> x)"

lemma index_of2_index_of2[simp]: "x \<in> set (map fst l) 
  \<Longrightarrow> l[index_of2 l x := (x, y)] ! index_of2 (l[index_of2 l x := (x, y)]) x = (x, y)"
proof (induction l)
  case (Cons a l)
  then have "fst a = x \<or> fst a \<noteq> x" by simp
  then show ?case
  proof (elim disjE)
    assume "fst a = x"
    then show ?thesis using Cons 
      by (metis eq_fst_iff index_of2.simps length_map length_pos_if_in_set list_update_code nth_list_update)
  next
    assume "fst a \<noteq> x"
    then show ?thesis using Cons 
      by (metis index_of2.simps list.simps(9) list_update_code nth_Cons_Suc prod.collapse set_ConsD)
  qed
qed auto

lemma pc_to_com_of_subprogram: "c1 \<in> set cs \<Longrightarrow> PC \<in> set (map fst as) 
  \<Longrightarrow> pc_to_com cs
    (as [index_of2 as PC := (PC, Num (index_of cs c1))]) = c1"
  by (induction cs) (auto simp: pc_to_com_def)


fun com_to_operators :: "com list \<Rightarrow> com \<Rightarrow> domain_element list \<Rightarrow> operator list" where
"com_to_operators cs (SKIP) d = []" |
"com_to_operators cs (v ::= aexp) d = (let i = index_of cs (v ::= aexp) ; j = index_of cs SKIP in
  (case aexp of
    A a \<Rightarrow> (case a of
      N val \<Rightarrow> [\<lparr> precondition_of = [(PC, Num i)], 
                  effect_of = [(PC, Num j), (VN v, (if (Num val) \<in> set d then Num val else \<omega>))]\<rparr>] |
      V var \<Rightarrow> map (\<lambda> x. \<lparr> precondition_of = [(PC, Num i), (VN var, x)], 
                           effect_of = [(PC, Num j), (VN v, x)]\<rparr>) d) |
    Plus a b \<Rightarrow> map (\<lambda> x.  \<lparr> precondition_of = [(PC, Num i), (VN a, x)], 
                             effect_of = [(PC, Num j), (VN v, (case x of 
      Num y \<Rightarrow> if Num (y + b) \<in> set d then Num (y + b) else \<omega> | 
      \<omega> \<Rightarrow> \<omega>))]\<rparr>) d | 
    Sub a b \<Rightarrow> map (\<lambda> x.  \<lparr> precondition_of = [(PC, Num i), (VN a, x)], 
                            effect_of = [(PC, Num j), (VN v, (case x of 
      Num y \<Rightarrow> if Num (y - b) \<in> set d then Num (y - b) else \<omega> | 
      \<omega> \<Rightarrow> \<omega>))]\<rparr>) d))" |
"com_to_operators cs (c1;; c2) d = (let i = index_of cs (c1 ;; c2) in 
  (if c1 = SKIP then (let j = index_of cs c2 in [\<lparr> precondition_of = [(PC, Num i)],
                                                   effect_of = [(PC, Num j)]\<rparr>])
   else (let ops = com_to_operators cs c1 d in map (\<lambda> op. 
    (let j = index_of cs ((pc_to_com cs (effect_of op) ;; c2)) in 
      \<lparr> precondition_of = 
        list_update (precondition_of op) 
                    (index_of2 (precondition_of op) PC) (PC, Num i),
        effect_of = 
        list_update (effect_of op) 
                    (index_of2 (effect_of op) PC) (PC, Num j)\<rparr>)) ops)))" |
"com_to_operators cs (IF v\<noteq>0 THEN c1 ELSE c2) d = (let i = index_of cs (IF v\<noteq>0 THEN c1 ELSE c2) ;
  j = index_of cs c1 ; k = index_of cs c2 in map (\<lambda> x. 
    \<lparr> precondition_of = [(PC, Num i), (VN v, x)], 
      effect_of = [(PC, (if x = Num 0 then Num k else Num j))]\<rparr>) d)" |
"com_to_operators cs (WHILE v\<noteq>0 DO c) d = (let i = index_of cs (WHILE v\<noteq>0 DO c) ;
  j = index_of cs (c ;; (WHILE v\<noteq>0 DO c)); k = index_of cs SKIP in map (\<lambda> x. 
    \<lparr> precondition_of = [(PC, Num i), (VN v, x)], 
      effect_of = [(PC, (if x = Num 0 then Num k else Num j))]\<rparr>) d)"

lemma PC_in_update: 
"(PC, y1) \<in> set l \<Longrightarrow> (\<exists>y2. (PC, y2) \<in> set (list_update l (index_of2 l PC) (PC, y3)))" 
proof (induction l)
  case (Cons a l)
  then show ?case 
    by (metis index_of2.simps list.set_intros list.set_intros list_update_code list_update_code prod.collapse set_ConsD)
qed auto

lemma PC_in_effect_precondition: "op \<in> set (com_to_operators cs c d) 
  \<Longrightarrow> (\<exists>y1 y2. (PC, y1) \<in> set (precondition_of op) \<and> (PC, y2) \<in> set (effect_of op))"
proof(induction cs c d arbitrary: op rule: com_to_operators.induct)
  case (2 cs v aexp d)
  then show ?case by (cases aexp) (auto simp: Let_def split: atomExp.splits)
next
  case (3 cs c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case using 3 PC_in_update by fastforce
qed auto

lemma update_PC_registers_unchanged: 
    "{x \<in> set l. fst x \<noteq> PC} =  {x \<in> set (list_update l (index_of2 l PC) (PC, y)). fst x \<noteq> PC}"
proof (induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  have "fst a = PC \<or> fst a \<noteq> PC" by auto
  then show ?case
  proof (elim disjE)
    assume "fst a = PC" 
    then show ?thesis 
      by (metis (no_types, lifting) Collect_cong fst_conv index_of2.simps list.set_intros 
         list_update_code prod.collapse set_ConsD)
  next
    assume "fst a \<noteq> PC"
    then have "index_of2 (a#l) PC \<noteq> 0" by (metis index_of2.simps old.nat.distinct prod.collapse)
    then show ?thesis using Cons 
      by (smt Collect_cong index_of2.elims insert_iff list.inject list.set list_update_code mem_Collect_eq)
  qed
qed

lemma com_to_operators_seq_registers:
  assumes "c1 \<noteq> SKIP" and  "op \<in> set (com_to_operators cs (c1 ;; c2) d)" 
    and "(VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op)"
  shows "\<exists>op'. op' \<in> set (com_to_operators cs c1 d) 
          \<and> ((VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op'))"
proof -
  let ?i = "index_of cs (c1 ;; c2)"
  obtain op' where "op' \<in> set (com_to_operators cs c1 d) 
    \<and> op = (let j = index_of cs ((pc_to_com cs (effect_of op') ;; c2)) in 
      \<lparr> precondition_of = 
        list_update (precondition_of op') 
                    (index_of2 (precondition_of op') PC) (PC, Num ?i),
        effect_of = 
        list_update (effect_of op') 
                    (index_of2 (effect_of op') PC) (PC, Num j)\<rparr>)" using assms by auto
  moreover then have "(VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op')" 
    using assms update_PC_registers_unchanged by fastforce
  ultimately show ?thesis by auto
qed

lemma com_to_operators_registers_in_d: 
  "op \<in> set (com_to_operators cs c d) 
  \<Longrightarrow> ((VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op)) \<Longrightarrow> \<omega> \<in> set d 
  \<Longrightarrow> y \<in> set d"
proof (induction cs c d arbitrary: op rule: com_to_operators.induct)
  case (2 cs v aexp d)
  then show ?case by (auto simp: Let_def split: aexp.splits atomExp.splits if_splits domain_element.splits)
next
  case (3 cs c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case
  proof (elim disjE)
    assume "c1 \<noteq> SKIP"
    then show ?thesis using 3 com_to_operators_seq_registers by metis
  next
    assume "c1 = SKIP" 
    then show ?thesis using 3 by auto
  qed
qed (auto simp: Let_def split: aexp.splits atomExp.splits if_splits)

lemma update_index_of2_preserve_set:
  "set (map fst l) = set (map fst (list_update l (index_of2 l x) (x, y)))"
proof (induction l)
  case (Cons a l)
  then show ?case
    by (metis eq_fst_iff index_of2.simps list.set list.simps list_update_code list_update_code surjective_pairing)
qed auto

lemma update_index_of2_preserve_distinct: "distinct (map fst l)
  \<Longrightarrow> distinct (map fst (list_update l (index_of2 l x) (x, y)))"
proof (induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  let ?l' = "list_update l (index_of2 l x) (x, y)"
  have "fst a = x \<or> fst a \<noteq> x" by auto
  then show ?case
  proof(elim disjE)
    assume "fst a = x"
    then show ?thesis using Cons 
      by (metis (no_types, lifting) eq_fst_iff index_of2.simps list_update_code map_update)
  next
    assume "fst a \<noteq> x"
    then show ?thesis using Cons update_index_of2_preserve_set 
      by (metis card_distinct distinct_card length_list_update length_map)
  qed
qed

lemma com_to_operators_variables_distinct: 
  "op \<in> set (com_to_operators cs c d) \<Longrightarrow> (l = precondition_of op \<or> l = effect_of op)
  \<Longrightarrow> distinct (map fst l)"
proof(induction cs c d arbitrary: op l rule: com_to_operators.induct)
  case (3 cs c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by simp
  then show ?case using 3 update_index_of2_preserve_distinct by fastforce
qed (auto simp: Let_def split: aexp.splits atomExp.splits if_splits)

lemma com_to_operators_PC_is_subprogram: 
  "cs = enumerate_subprograms c \<Longrightarrow> c1 \<in> set cs \<Longrightarrow> op \<in> set (com_to_operators cs c1 d)
  \<Longrightarrow> ((PC, y) \<in> set (precondition_of op) \<or> (PC, y) \<in> set (effect_of op))
  \<Longrightarrow>  (pc_to_com cs (precondition_of op) \<in> set (enumerate_subprograms c1)
      \<and> pc_to_com cs (effect_of op) \<in> set (enumerate_subprograms c1)
      \<and> y \<in> set (map (\<lambda> i. Num i) [0..<(length cs)]))"
proof (induction cs c1 d arbitrary: y op rule: com_to_operators.induct)
  case (2 cs v aexp d)
  moreover then have "v ::= aexp \<in> set cs" and "SKIP \<in> set cs" 
    using SKIP_in_enumerate_subprograms by blast+
  ultimately show ?case 
    by (auto simp: Let_def pc_to_com_def index_of_element_in_list split: aexp.splits atomExp.splits)
next
  case (3 cs c1 c2 d)
  then have c1c2_in_cs: "c1 ;; c2 \<in> set (enumerate_subprograms c) 
    \<and> c1 \<in> set (enumerate_subprograms (c1 ;; c2)) \<and> c2 \<in> set (enumerate_subprograms (c1 ;; c2))" 
    using c_in_all_subprograms_c by auto
  then have "c1 \<in> set (enumerate_subprograms c) \<and> c2 \<in> set (enumerate_subprograms c)" 
    using enumerate_subprograms_transitive by blast
  then have c1_in_cs: "c1 \<in> set cs" and c2_in_cs: "c2 \<in> set cs" using 3 by auto
  then have "c1 = SKIP \<or> c1 \<noteq> SKIP" by auto
  then show ?case
  proof (elim disjE)
    assume "c1 = SKIP"
    then show ?thesis
      using 3 c2_in_cs c_in_all_subprograms_c c1c2_in_cs 
      by (auto simp: Let_def pc_to_com_def index_of_element_in_list)
  next
    assume a: "c1 \<noteq> SKIP"
    moreover then obtain op' where op'_def: "op' \<in> set (com_to_operators cs c1 d)
      \<and> precondition_of op = list_update (precondition_of op') 
                    (index_of2 (precondition_of op') PC) (PC, Num (index_of cs (c1 ;; c2)))
      \<and> effect_of op = list_update (effect_of op') 
                      (index_of2 (effect_of op') PC) (PC, Num (index_of cs (pc_to_com cs (effect_of op') ;; c2)))"
      using 3 a by (auto simp: Let_def)
    moreover then obtain c3 where c3_def: "c3 = pc_to_com cs (effect_of op')" by auto
    ultimately have "c3 \<in> set (enumerate_subprograms c1)" using 3 c1_in_cs
      by (meson PC_in_effect_precondition)
    then have "c3 ;; c2 \<in> set (enumerate_subprograms (c1 ;; c2))" by auto
    then have *: "c3 ;; c2 \<in> set cs" and **: "c1 ;; c2 \<in> set cs" using enumerate_subprograms_transitive 
      using 3 "3.prems"(1) c1c2_in_cs by (meson PC_in_effect_precondition)+
    have ***: "PC \<in> set (map fst (precondition_of op'))" and ****: "PC \<in> set (map fst (effect_of op'))"
      using PC_in_effect_precondition 3 op'_def by (metis in_set_zipE zip_map_fst_snd)+
    have "pc_to_com cs (precondition_of op) = c1 ;; c2" 
      using op'_def pc_to_com_of_subprogram[OF ** ***] by auto 
    moreover have "pc_to_com cs (effect_of op) = c3 ;; c2"
      using op'_def pc_to_com_of_subprogram[OF * ****] using c3_def by auto
    moreover have "y = Num (index_of cs (c1 ;; c2)) \<or> y = Num (index_of cs (c3 ;; c2))" 
      using 3 op'_def c3_def com_to_operators_variables_distinct *** ****
      by (metis Pair_inject index_of2_distinct index_of2_index_of2)
    ultimately show ?thesis 
      using c_in_all_subprograms_c \<open>c3;; c2 \<in> set (enumerate_subprograms (c1;; c2))\<close> 3 *
      by (auto simp: index_of_element_in_list)
  qed
next
  case (4 cs v c1 c2 d)
  let ?i = "IF v \<noteq>0 THEN c1 ELSE c2"
  have "?i \<in> set (enumerate_subprograms c) \<and> c1 \<in> set (enumerate_subprograms ?i) \<and> c2 \<in> set (enumerate_subprograms ?i)" 
    using 4 c_in_all_subprograms_c by auto
  moreover then have "c1 \<in> set (enumerate_subprograms c) \<and> c2 \<in> set (enumerate_subprograms c)"
    using enumerate_subprograms_transitive by blast
  ultimately have "?i \<in> set cs \<and> c1 \<in> set cs \<and> c2 \<in> set cs" using 4 by auto
  then show ?case using 4 c_in_all_subprograms_c 
    by (auto simp: Let_def pc_to_com_def index_of_element_in_list) 
next
  case (5 cs v c1 d)
  let ?w = "WHILE v \<noteq>0 DO c1"
  have "?w \<in> set (enumerate_subprograms c) \<and> c1 ;; ?w \<in> set (enumerate_subprograms ?w)" 
    using 5 c_in_all_subprograms_c by auto
  moreover then have "c1 ;; ?w \<in> set (enumerate_subprograms c)"
    using enumerate_subprograms_transitive by blast
  ultimately have "?w \<in> set cs \<and> c1 ;; ?w \<in> set cs \<and> SKIP \<in> set cs" 
    using 5 SKIP_in_enumerate_subprograms by auto
  then show ?case using 5 c_in_all_subprograms_c 
    by (auto simp: Let_def pc_to_com_def index_of_element_in_list) 
qed auto

lemma com_to_operators_variables_in_enumerate_variables: "cs = (enumerate_subprograms c) ==> c1 \<in> set cs
  \<Longrightarrow> op \<in> set (com_to_operators cs c1 d)
  \<Longrightarrow> ((VN x, y) \<in> set (precondition_of op) \<or> (VN x, y) \<in> set (effect_of op))
  \<Longrightarrow> x \<in> set (enumerate_variables c)"
proof (induction cs c1 d arbitrary: op rule: com_to_operators.induct)
  case (1 cs d)
  then show ?case by auto
next
  case (2 cs v aexp d)
  then have "set (all_variables (v ::= aexp)) \<subseteq> set (enumerate_variables c)" 
    using enumerate_subprogams_enumerate_variables by blast 
  then show ?case using 2 by (auto simp: Let_def split: aexp.splits atomExp.splits if_splits) 
next
  case (3 cs c1 c2 d)
  have "c1 = SKIP \<or> c1 \<noteq> SKIP" by auto
  then show ?case
  proof (elim disjE)
    assume "c1 = SKIP"
    then show ?thesis using 3 by auto
  next
    assume "c1 \<noteq> SKIP"
    then obtain op' where "op' \<in> set (com_to_operators cs c1 d) 
          \<and> ((VN x, y) \<in> set (precondition_of op') \<or> (VN x, y) \<in> set (effect_of op'))"
      using 3 com_to_operators_seq_registers by presburger
    moreover have "c1 ;; c2 \<in> set (enumerate_subprograms c) \<and> c1 \<in> set (enumerate_subprograms (c1 ;; c2))" 
      using 3 c_in_all_subprograms_c by simp
    moreover then have "c1 \<in> set (enumerate_subprograms c)" 
      using 3 enumerate_subprograms_transitive by blast
    ultimately show ?thesis using 3 \<open>c1 \<noteq> SKIP\<close> by blast
  qed
next
  case (4 cs v c1 c2 d)
  then have "set (all_variables (IF v \<noteq>0 THEN c1 ELSE c2)) \<subseteq> set (enumerate_variables c)" 
    using enumerate_subprogams_enumerate_variables by blast 
  then show ?case using 4 by (auto simp: Let_def split: aexp.splits atomExp.splits if_splits)
next
  case (5 cs v c' d)
  then have "set (all_variables (WHILE v \<noteq>0 DO c')) \<subseteq> set (enumerate_variables c)" 
    using enumerate_subprogams_enumerate_variables by blast
  then show ?case using 5 by (auto simp: Let_def split: aexp.splits atomExp.splits if_splits)
qed

definition coms_to_operators :: "com list \<Rightarrow> domain_element list \<Rightarrow> operator list" where
"coms_to_operators cs d = concat (map (\<lambda> c. com_to_operators cs c d) cs)"

definition state_by_pc_and_vars :: 
  "com list \<Rightarrow> com  \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> domain_element list \<Rightarrow> state" where
"state_by_pc_and_vars cs c vs d =  (\<lambda> v. (case v of 
  VN vn \<Rightarrow> (case vs vn of Some x \<Rightarrow> (if Num x \<in> set d then Some (Num x) else Some \<omega>) |
                          None \<Rightarrow> None) |
  PC \<Rightarrow> Some (Num (index_of cs c))))"

lemma state_by_pc_and_vars_variables_in_d: 
  "x \<noteq> PC \<Longrightarrow> (state_by_pc_and_vars cs c vs d) x = Some y 
  \<Longrightarrow> (y = \<omega> \<or> y \<in> set d)"
  by (auto simp: state_by_pc_and_vars_def split: variable.splits option.splits if_splits)

lemma state_by_pc_and_vars_PC_in_d:
  "c \<in> set cs \<Longrightarrow> (state_by_pc_and_vars cs c vs d) PC = Some y
  \<Longrightarrow> y \<in> set (map (\<lambda> i. Num i) [0..<(length cs)])"
  by (auto simp: state_by_pc_and_vars_def index_of_element_in_list split: variable.splits option.splits if_splits)

definition imp_minus_minus_to_sas_plus :: "com \<Rightarrow> (vname \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> problem" where
"imp_minus_minus_to_sas_plus c vs t = (let cs = enumerate_subprograms c ; 
  d = domain c t ; 
  initial_vs = (\<lambda>x. (if x \<in> set (enumerate_variables c) then Some (case vs x of Some y \<Rightarrow> y | None \<Rightarrow> 0)
    else None)) ;
  pc_d = map (\<lambda> i. Num i) [0..<(length cs)] in
    \<lparr> variables_of = PC # (map (\<lambda> v. VN v) (enumerate_variables c)),
      operators_of = coms_to_operators cs d, 
      initial_of = state_by_pc_and_vars cs c initial_vs d,
      goal_of = state_by_pc_and_vars cs SKIP Map.empty d,
      range_of = (map_of (map (\<lambda> v. (VN v, d)) (enumerate_variables c)))(PC \<mapsto> pc_d)\<rparr>)"

lemma range_defined: 
  assumes "v \<in> set (variables_of (imp_minus_minus_to_sas_plus c vs t))" 
  shows "(\<exists>y. range_of (imp_minus_minus_to_sas_plus c vs t) v = Some y)"
proof(cases v)
  case (VN x)
  then have *: "(VN x, domain c t) \<in> set (map (\<lambda> v. (VN v, domain c t)) (enumerate_variables c))" 
    using assms by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)    
  then show ?thesis using VN by (simp add: Let_def imp_minus_minus_to_sas_plus_def) 
       (smt Pair_inject * ex_map_conv map_of_SomeD weak_map_of_SomeI)
next
  case PC
  then show ?thesis by (auto simp: imp_minus_minus_to_sas_plus_def Let_def)
qed

lemma range_non_empty: 
  assumes "v \<in> set (variables_of (imp_minus_minus_to_sas_plus c vs t))" 
  shows "(\<exists>y. y \<in> range_of' (imp_minus_minus_to_sas_plus c vs t) v)"
proof (cases v)
  case (VN x)
  then have *: "(VN x, domain c t) \<in> set (map (\<lambda> v. (VN v, domain c t)) (enumerate_variables c))" 
    using assms by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)
  then have "range_of (imp_minus_minus_to_sas_plus c vs t) v = Some (domain c t)" 
    using VN by (simp add: Let_def imp_minus_minus_to_sas_plus_def) 
       (smt Pair_inject * ex_map_conv map_of_SomeD weak_map_of_SomeI)
  then have "\<omega> \<in> range_of' (imp_minus_minus_to_sas_plus c vs t) v" 
    by (auto simp: domain_def range_of'_def)
  then show ?thesis by auto
next
  case PC
  let ?pc_d = "(map (\<lambda> i. Num i) [0..<(length (enumerate_subprograms c))])"
  have "range_of (imp_minus_minus_to_sas_plus c vs t) v 
    = Some ?pc_d"
    using assms PC by (auto simp: Let_def imp_minus_minus_to_sas_plus_def)
  then have "range_of (imp_minus_minus_to_sas_plus c vs t) v = Some ?pc_d" using PC by simp
  moreover have "Num 0 \<in> set ?pc_d" using SKIP_in_enumerate_subprograms 
    by (metis (no_types, lifting) add.left_neutral in_set_conv_nth length_map length_pos_if_in_set map_nth nth_map nth_upt)
  ultimately have "Num 0 \<in> range_of' (imp_minus_minus_to_sas_plus c vs t) v"
    by (auto simp: domain_def range_of'_def)
  then show ?thesis by auto
qed

lemma map_of_variables: "x \<in> set l \<Longrightarrow> (map_of (map (\<lambda>v. (VN v, d)) l) (VN x)) = Some d"
  by (induction l) auto

lemma distinct_list_all: 
  assumes "distinct (map fst l)" 
  shows "list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') l) l"
proof -
  have "(v1, a1) \<in> set l \<Longrightarrow> list_all (\<lambda>(v', a'). v1 \<noteq> v' \<or> a1 = a') l" for v1 a1
  proof -
    assume "(v1, a1) \<in> set l"
    then have "(v2, a2) \<in> set l \<Longrightarrow> v1 \<noteq> v2 \<or> a1 = a2" for v2 a2 
      using assms by (meson eq_key_imp_eq_value)
    then show ?thesis using Ball_set_list_all by blast
  qed
  then show ?thesis
    by (metis (no_types, lifting) case_prodI2 list.pred_set)
qed 
  

lemma operators_valid: 
  assumes "cs = enumerate_subprograms c" and "c1 \<in> set cs" and "d = domain c t"
         and  "op \<in> set (com_to_operators cs c1 d)"
  shows "is_valid_operator_sas_plus (imp_minus_minus_to_sas_plus c vs t) op" 
proof -                   
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c vs t"
  let ?pre = "precondition_of op" and ?eff = "effect_of op" and ?vs = "variables_of ?\<Psi>" 
      and ?D = "range_of ?\<Psi>" and ?pc_d = "(map (\<lambda> i. Num i) [0..<(length (enumerate_subprograms c))])"

  have *: "((VN x, a) \<in> set ?pre \<or> (VN x, a) \<in> set ?eff) \<Longrightarrow> x \<in> set (enumerate_variables c)" for x a 
    using com_to_operators_variables_in_enumerate_variables[OF assms(1) assms(2) assms(4)] by auto
  then have "((VN x, a) \<in> set ?pre \<or> (VN x, a) \<in> set ?eff) \<Longrightarrow> ListMem (VN x) ?vs" for x a 
    by (auto simp: imp_minus_minus_to_sas_plus_def Let_def ListMem_iff)
  moreover have "ListMem PC ?vs" by (auto simp: imp_minus_minus_to_sas_plus_def Let_def ListMem_iff)
  ultimately have "((v, a) \<in> set ?pre \<or> (v, a) \<in> set ?eff) \<Longrightarrow> ListMem v ?vs" for v a by (cases v) auto
  then have pre_in_range: "list_all (\<lambda>(v, a). ListMem v ?vs) ?pre" 
    and eff_in_range: "list_all (\<lambda>(v, a). ListMem v ?vs) ?eff"  
    by (metis (mono_tags, lifting) case_prodI2 list.pred_set)+

  have "x \<in> set (enumerate_variables c) \<Longrightarrow> ?D (VN x) = Some d" for x
    using assms(3) map_of_variables by (simp add: imp_minus_minus_to_sas_plus_def Let_def) fast
  then have "((VN x, a) \<in> set ?pre \<or> (VN x, a) \<in> set ?eff) \<Longrightarrow> ?D (VN x) = Some d" for x a 
    using * by (auto simp: imp_minus_minus_to_sas_plus_def Let_def)
  then have "((VN x, a) \<in> set ?pre \<or> (VN x, a) \<in> set ?eff) \<Longrightarrow> ?D (VN x) = Some d \<and> a \<in> set d" for x a
    by (metis assms(3) assms(4) com_to_operators_registers_in_d domain_def in_set_conv_decomp)
  moreover have "((PC, a) \<in> set ?pre \<or> (PC, a) \<in> set ?eff) \<Longrightarrow> ?D PC = Some ?pc_d \<and> a \<in> set ?pc_d" for a
    using com_to_operators_PC_is_subprogram assms
    by (metis (no_types, lifting) fun_upd_apply imp_minus_minus_to_sas_plus_def sas_plus_problem.select_convs)
  ultimately have "((v, a) \<in> set ?pre \<or> (v, a) \<in> set ?eff) \<Longrightarrow> (?D v \<noteq> None \<and> a \<in> set (the (?D v)))" for v a
    by (cases v) auto
  then have "((v, a) \<in> set ?pre \<or> (v, a) \<in> set ?eff) \<Longrightarrow> (?D v \<noteq> None \<and> ListMem a (the (?D v)))" for v a
    by (simp add: ListMem_iff)
  then have "list_all (\<lambda>(v, a). (?D v \<noteq> None) \<and> ListMem a (the (?D v))) ?pre" 
    and "list_all (\<lambda>(v, a). (?D v \<noteq> None) \<and> ListMem a (the (?D v))) ?eff" 
    using Ball_set_list_all by blast+

  then show ?thesis 
    using com_to_operators_variables_distinct assms distinct_list_all pre_in_range eff_in_range 
    apply (auto simp: is_valid_operator_sas_plus_def Let_def) 
    by blast+ 
qed

lemma SKIP_in_pcs[simp]:  "ListMem (Num (index_of (enumerate_subprograms c) SKIP))
     (map Num [0..<length (enumerate_subprograms c)])"
proof -
  have "index_of (enumerate_subprograms c) SKIP < length (enumerate_subprograms c)"
    using SKIP_in_enumerate_subprograms index_of_element_in_list by fastforce
  then show ?thesis by (simp add: ListMem_iff)
qed

lemma imp_minus_minus_to_sas_plus_valid: 
  "is_valid_problem_sas_plus (imp_minus_minus_to_sas_plus c vs t)"
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c vs t"
  let ?ops = "operators_of ?\<Psi>"
      and ?vs = "variables_of ?\<Psi>"
      and ?I = "initial_of ?\<Psi>"
      and ?G = "goal_of ?\<Psi>"
      and ?D = "range_of ?\<Psi>"
  have "x \<in> set ?ops \<Longrightarrow> is_valid_operator_sas_plus ?\<Psi> x" for x 
  proof -
    assume "x \<in> set ?ops"
    then have "\<exists>c1 \<in> set (enumerate_subprograms c). 
      x \<in> set (com_to_operators (enumerate_subprograms c) c1 (domain c t))"
      by (auto simp: imp_minus_minus_to_sas_plus_def Let_def coms_to_operators_def)
    then show ?thesis using operators_valid by auto
  qed
  moreover have "\<forall>v. ?I v \<noteq> None \<longleftrightarrow> ListMem v ?vs"
  proof
    fix v
    show "?I v \<noteq> None \<longleftrightarrow> ListMem v ?vs" 
      by (cases v) (auto simp: imp_minus_minus_to_sas_plus_def Let_def state_by_pc_and_vars_def ListMem.elem ListMem_iff)
  qed
  moreover have "?I v \<noteq> None \<Longrightarrow> ListMem (the (?I v)) (the (?D v))" for v
  proof -
    assume assm: "?I v \<noteq> None" 
    then show ?thesis
    proof(cases v)
      case (VN x1)
      then have "x1 \<in> set (enumerate_variables c)" 
        using VN assm by (auto simp: imp_minus_minus_to_sas_plus_def Let_def state_by_pc_and_vars_def split: option.splits if_splits)
      then have "the (?D v) = domain c t" 
        using VN by (auto simp: imp_minus_minus_to_sas_plus_def Let_def map_of_variables)
      then show ?thesis 
        using VN assm 
        apply (auto simp: imp_minus_minus_to_sas_plus_def Let_def state_by_pc_and_vars_def elem ListMem_iff split: option.splits)
        by (meson ListMem_iff omega_in_domain)+
    next
      case PC
      have "c \<in> set (enumerate_subprograms c)" using c_in_all_subprograms_c by auto
      then show ?thesis using PC 
        by (auto simp: imp_minus_minus_to_sas_plus_def Let_def state_by_pc_and_vars_def index_of_element_in_list ListMem_iff)
    qed
  qed
  moreover have "\<forall>v. ?G v \<noteq> None \<longrightarrow> ListMem v ?vs"
    by (auto simp: imp_minus_minus_to_sas_plus_def Let_def state_by_pc_and_vars_def ListMem.elem split: variable.splits)
  moreover have "\<forall>v. ?G v \<noteq> None \<longrightarrow> ListMem (the (?G v)) (the (?D v))"
    using SKIP_in_pcs by (auto simp: imp_minus_minus_to_sas_plus_def Let_def state_by_pc_and_vars_def ListMem.elem split: variable.splits)

  ultimately show ?thesis 
    by (auto simp: is_valid_problem_sas_plus_def Let_def range_defined list_all_def state_by_pc_and_vars_variables_in_d state_by_pc_and_vars_PC_in_d)
qed

end