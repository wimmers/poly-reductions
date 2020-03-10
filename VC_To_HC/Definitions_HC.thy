theory Definitions_HC
  imports Main "../Three_Sat_To_Set_Cover"  "../Auxiliaries/List_Auxiliaries" 
    "../Auxiliaries/Set_Auxiliaries" "../Auxiliaries/Graph_Auxiliaries" 
    "../VC_Set_to_VC_List/VC_Set_to_VC_List"
    Graph_Theory.Digraph  Graph_Theory.Arc_Walk Graph_Theory.Vertex_Walk
begin

subsection\<open>Definitions\<close>

datatype ('a, 'b) hc_node = Cover nat | Edge 'a 'b nat

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_hc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    ((pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1)
    \<and> set c \<subseteq> verts G \<and> distinct (tl c)"

definition
  "hc \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}) 
    \<and> finite (verts G)}"

definition
  "vc_hc \<equiv> \<lambda>(E, k).
    if ugraph (set E) \<and>  k \<le> card (\<Union> (set E)) \<and> distinct E
        then  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> 
            {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e \<and> u \<noteq> v} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E 
              \<and>  e1 = E!i\<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k} \<union>
            {(Cover i, Cover j) |i j.  i < k \<and> j < k},
          tail = fst, head = snd \<rparr>
        else \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"

definition get_second where
  "get_second e \<equiv> SOME v. v \<in> e"

definition next_edge where
  "next_edge v E e1 e2 \<equiv> \<exists>i j. i<length E \<and> j<length E \<and>  e1 = E!i \<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 \<and> i<j \<and>
              \<not> (\<exists>k < size E. v \<in> E!k \<and> i < k \<and> k < j)"

definition first_edge where
  "first_edge v e E \<equiv> (\<exists>i<length E. e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i))"

definition last_edge where
  "last_edge v e E \<equiv> \<exists>i<length E. e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j)"


subsection\<open>Proofs for Definitions\<close>

lemma else_not_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<notin> hc"
proof 
  assume "G \<in> hc"
  then have "\<exists> c. pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c) 
    \<and> set c \<subseteq> verts G \<and> distinct (tl c)" 
    using assms hc_def 
    by (simp add: hc_def doubleton_eq_iff is_hc_def)
  then obtain c where c_def: "pre_digraph.cycle G (vwalk_arcs c)" "(\<forall>x\<in> verts G. x \<in> set c)" 
    by blast
  with pre_digraph.cycle_def have not_empty: "vwalk_arcs c \<noteq> []"  
    by fastforce
  from pre_digraph.cycle_def pre_digraph.awalk_def c_def have subset: "set (vwalk_arcs c) \<subseteq> arcs G" 
    by metis
  have "arcs G = {}" 
    using assms 
    by(auto)
  with subset  have "set (vwalk_arcs c) = {}" 
    by auto
  then show "False" 
    using not_empty 
    by(auto)
qed


lemma else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)


lemma if_else_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<in> hc" 
  apply(auto simp add: hc_def wf_digraph_def is_hc_def assms) 
  using set_replicate_conv_if 
  by fastforce 


lemma if_else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)


lemma get_second_in_edge:
  assumes "u = get_second e" "e \<noteq> {}"
  shows "u \<in> e"
  using assms 
  unfolding  get_second_def 
  by(auto simp add: some_in_eq) 


lemma first_not_next: 
  assumes "first_edge v e1 E" "next_edge v E e2 e1" "distinct E" 
  shows False
proof -
  obtain i where 1: "i<length E \<and> e1 = E!i \<and> v \<in> e1 \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i)"
    using assms first_edge_def 
    by metis
  obtain i' j' where 2: "i'<length E \<and> j'<length E \<and>  e2 = E!i' \<and> e1 = E!j' 
      \<and> v \<in> e2 \<and> v \<in> e1 \<and> i'<j' \<and>
      \<not> (\<exists>k < size E. v \<in> E!k \<and> i' < k \<and> k < j')"
    using assms next_edge_def 
    by metis 
  then have "i = j'" using 1 2 
    by (simp add: "1" assms(3) nth_eq_iff_index_eq)  
  then have "i' < i"
    using 2 
    by simp
  then show ?thesis 
    using 1 2 
    by blast 
qed


lemma last_not_next:
  assumes "last_edge v e1 E" "next_edge v E e1 e2" "distinct E"
  shows False
proof -
  obtain i where 1: "i<length E \<and> e1 = E!i\<and> v \<in> e1 \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j)"
    using assms last_edge_def 
    by metis
  obtain i' j' where 2: "i'<length E \<and> j'<length E \<and>  e1 = E!i' \<and> e2 = E!j' \<and> v \<in> e1 \<and> v \<in> e2 
      \<and> i'<j' \<and> \<not>(\<exists>k < size E. v \<in> E!k \<and> i' < k \<and> k < j')"
    using assms next_edge_def 
    by metis
  then have "i = i'"
    using 1 2 
    by (simp add: "1" assms(3) nth_eq_iff_index_eq)  
  then have "i < j'" 
    using 2 
    by simp
  then show ?thesis 
    using 1 2 
    by blast 
qed


lemma hd_is_first_edge:
  assumes "e = hd E" "v\<in> e" "E \<noteq> []"
  shows "first_edge v e E"
proof -
  have 1: "e = E!0" "0 < length E" 
    by (simp add: assms hd_conv_nth)+
  have 2: "\<not> (\<exists>j < size E. v \<in> E!j \<and> j < 0)"
    by simp
  then show ?thesis 
    using first_edge_def 1 2 assms  
    by fast 
qed


lemma next_edge_cons: 
  assumes "(\<exists>e1. next_edge v E e1 e2)"
  shows "(\<exists>e1. next_edge v (a#E) e1 e2)"
proof -
  obtain e1 where e1_def: "next_edge v E e1 e2"
    using assms 
    by auto
  then obtain i j where ij_def: "i<length E \<and> j<length E \<and>  e1 = E!i \<and> e2 = E!j \<and> v \<in> e1 \<and> v \<in> e2 
      \<and> i<j \<and> \<not> (\<exists>k < size E. v \<in> E!k \<and> i < k \<and> k < j)"
    using next_edge_def 
    by metis
  then have 1: "i+1<length (a#E) \<and> (j+1)<length (a#E) \<and>  e1 = (a#E)!(i+1) 
      \<and> e2 = (a#E)!(j+1) \<and> v \<in> e1 \<and> v \<in> e2 \<and> (i+1)<(j+1)"
    by auto
  have "\<not> (\<exists>k < size (a#E). v \<in> (a#E)!k \<and> (i+1) < k \<and> k < (j+1))"
  proof(rule ccontr) 
    assume "\<not> \<not> (\<exists>k<length (a # E). v \<in> (a # E) ! k \<and> i + 1 < k \<and> k < j + 1)"
    then have "(\<exists>k<length (a # E). v \<in> (a # E) ! k \<and> i + 1 < k \<and> k < j + 1)"
      by auto
    then obtain k where k_def: "k<length (a # E)\<and> v \<in> (a # E) ! k \<and> i + 1 < k \<and> k < j + 1"
      by blast
    then have 0: "k \<noteq> 0" 
      by simp 
    then have 1: "k-1 < length E \<and> v \<in> E!(k-1)" 
      using k_def 
      by force 
    have "i  < k-1 \<and> k-1 < j" 
      using k_def 0 
      by linarith
    then have "(\<exists>k < size (E). v \<in> (E)!k \<and> i < k \<and> k < j)"
      using 1 by blast
    then show False 
      using ij_def
      by auto
  qed
  then have "next_edge v (a#E) e1 e2"
    using next_edge_def 1 
    by metis 
  then show ?thesis 
    by auto
qed


lemma first_edge_cons_not_in: 
  assumes "first_edge v e E" "v \<notin> a"
  shows "first_edge v e (a#E)"
proof -
  obtain i where i_def:  "i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i)" 
    using assms first_edge_def 
    by metis
  then have 1: "i+1 < length (a#E) \<and> e = (a#E)!(i+1) \<and> v \<in> e"
    by auto
  have 2: "\<not> (\<exists>j < size (a#E). v \<in> (a#E)!j \<and> j < (i+1))" 
  proof (rule ccontr)
    assume "\<not> \<not> (\<exists>j < size (a#E). v \<in> (a#E)!j \<and> j < (i+1))"
    then have "(\<exists>j < size (a#E). v \<in> (a#E)!j \<and> j < (i+1))"
      by auto
    then obtain j where j_def: "j < size (a#E) \<and> v \<in> (a#E)!j \<and> j < (i+1)"
      by auto
    then show False proof(cases "j = 0")
      case True
      then have "v \<in> a"
        using j_def 
        by auto
      then show ?thesis 
        using assms 
        by simp
    next
      case False
      then have "(j-1) < length E \<and> v \<in> E!(j-1) \<and> j-1 < i"
        using j_def 
        by fastforce  
      then show ?thesis 
        using i_def 
        by blast 
    qed
  qed
  then show ?thesis 
    using 1 2 first_edge_def 
    by metis
qed


lemma first_edge_cons_in: 
  assumes "first_edge v e E" "v \<in> a"
  shows "next_edge v (a#E) a e"
proof -
  obtain i where i_def:  "i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i)" 
    using assms first_edge_def by metis
  then have 1: "i+1 < length (a#E) \<and> e = (a#E)!(i+1) \<and> v \<in> e" 
    by auto
  then have 2: "0 < length (a#E) \<and> a = (a#E) ! 0 \<and> v \<in> a \<and> 0 < i+1"
    using assms 
    by simp
  then have 3: "0 < length (a#E) \<and>
          i+1 < length (a#E) \<and> a = (a#E) ! 0 \<and> e = (a#E) ! (i+1)  \<and> v \<in> a \<and> v \<in> e \<and> 0 < (i+1)" 
    using 1 2
    by argo
  have "\<not> (\<exists>k < size (a#E). v \<in> (a#E)!k \<and> 0 < k \<and> k < i+1)" proof(rule ccontr)
    assume "\<not> \<not> (\<exists>k<length (a # E). v \<in> (a # E) ! k \<and> 0 < k \<and> k < i + 1)"
    then obtain k where k_def: "k<length (a # E)\<and> v \<in> (a # E) ! k \<and> 0 < k \<and> k < i + 1"
      by auto
    then have "k > 0" 
      by simp
    then have "k-1<length (E)\<and> v \<in> (E) ! (k-1) \<and> k-1 < i "
      using k_def
      by fastforce
    then show False 
      using i_def 
      by blast
  qed
  then have "0 < length (a#E) \<and>
          i+1 < length (a#E) \<and> a = (a#E) ! 0 \<and> e = (a#E) ! (i+1)  \<and> v \<in> a \<and> v \<in> e \<and> 0 < (i+1)
      \<and> \<not> (\<exists>k < size (a#E). v \<in> (a#E)!k \<and> 0 < k \<and> k < i+1)" 
    using 3 
    by auto  
  then have "\<exists>i j. i < length (a#E) \<and>
          j < length (a#E) \<and> a = (a#E) ! i \<and> e = (a#E) ! j  \<and> v \<in> a \<and> v \<in> e \<and> i < j
      \<and> \<not> (\<exists>k < size (a#E). v \<in> (a#E)!k \<and> i < k \<and> k < j)" 
    by metis
  then show ?thesis
    using next_edge_def 
    by metis 
qed


lemma first_Edge_or_next_edge: 
  assumes "e \<in> set E" "v \<in> e"
  shows "first_edge v e E \<or> (\<exists>e1. next_edge v E e1 e)"
  using assms 
proof(induction E)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a E)
  then show ?case 
  proof(cases "e = a")
    case True
    then have "e = hd (a#E)" by simp
    then have "first_edge v e (a#E)" 
      using assms 
      by (simp add: hd_is_first_edge) 
    then show ?thesis 
      by simp
  next
    case False
    then have "e \<in> set E" 
      using Cons 
      by simp
    then have 1: "first_edge v e E \<or> (\<exists>e1. next_edge v E e1 e)" 
      using Cons 
      by auto
    then show ?thesis proof
      assume a1: "first_edge v e E"
      then show ?thesis proof(cases "v \<in> a")
        case True
        then have "next_edge v (a#E) a e"
          using first_edge_cons_in a1
          by fast 
        then show ?thesis 
          by auto
      next
        case False
        then have "first_edge v e (a#E)"
          using 1 first_edge_cons_not_in a1  
          by metis  
        then show ?thesis 
          by simp
      qed
    next
      assume "(\<exists>e1. next_edge v E e1 e)"
      then have "(\<exists>e1. next_edge v (a#E) e1 e)" 
        using next_edge_cons 
        by fast
      then show ?thesis 
        by auto
    qed
  qed
qed 


subsection\<open>Auxiliary lemmas\<close>

lemma ugraph_implies_smaller_set_ugraph:
  assumes "ugraph (insert a (set E'))"
  shows "ugraph (set E')"
  using assms by (simp add: ugraph_def)


lemma edge_contains_minus_one_not_empty: 
  assumes "e \<in> set E'" "ugraph (set E')" "u \<in> e"
  shows "e-{u} \<noteq> {}"
  using subset_singletonD assms ugraph_def by fastforce


end