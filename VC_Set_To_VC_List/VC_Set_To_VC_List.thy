theory VC_Set_To_VC_List
  imports Main "../VC_To_HC/Definitions_HC"
begin

section\<open>VC Set to VC List\<close>

subsection\<open>Preliminaries\<close>

definition set_to_list::"'a set \<Rightarrow> 'a list" where
  "set_to_list S = (SOME L. (set L = S  \<and> distinct L))" 

definition " vc_set_to_vc_list \<equiv>
  \<lambda>(E, k). (if ugraph E \<and> k \<le> card (\<Union> E) then (set_to_list E, k) else ([], 1))"


fun get_elements:: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "get_elements 0 S = {}" |
  "get_elements n S = (let e = (SOME e. e \<in> S) in {e} \<union> (get_elements (n-1) (S-{e})))"


lemma get_some_simps: 
  assumes "e = (SOME e. e \<in> S)"
  shows "get_elements (Suc n) S = {e}\<union> (get_elements n (S - {e}))"
proof -
  have "get_elements (Suc n) S =  (let e = (SOME e. e \<in> S) in {e} \<union> (get_elements (n) (S-{e})))" 
    by auto
  then show ?thesis 
    using assms 
    by meson
qed


lemma get_some_in_set: 
  assumes "S \<noteq> {}" "e = (SOME e. e \<in> S)"
  shows "e \<in> S" 
  using assms 
  by (meson all_not_in_conv tfl_some) 


lemma get_elements_subset:
  assumes  "n \<le> card S" 
  shows "get_elements n S \<subseteq> S"
  using assms
proof(induction n arbitrary: S)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  then obtain e where e_def: "e = (SOME e. e \<in> S)" 
    by auto
  then have 2: "get_elements (Suc n) S = {e}\<union> (get_elements n (S - {e}))" 
    using get_some_simps 
    by fast  
  then have "S \<noteq> {}"  
    using Suc
    by auto
  then have 1: "{e} \<subseteq> S" 
    using e_def 
    by (metis bot.extremum_unique empty_subsetI insert_subsetI someI subsetI)  
  then have "n\<le> card (S-{e})" 
    using Suc e_def
    by (metis (no_types, lifting) Diff_empty Diff_insert0 Suc_leD Suc_le_mono antisym card_insert_le_m1 diff_Suc_1 insert_Diff linear zero_less_Suc) 
  then have "get_elements n (S-{e}) \<subseteq> S" 
    using Suc  
    by auto 
  then show ?case 
    using 1 2 
    by auto   
qed


lemma card_get_elements:
  assumes "n\<le> card S"
  shows "card (get_elements n S) = n"
  using assms 
proof(induction n arbitrary: S)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  then obtain e where e_def: "e = (SOME e. e \<in> S)" 
    by auto
  then have 2: "get_elements (Suc n) S = {e} \<union> (get_elements n (S -{e}))" 
    using get_some_simps 
    by fast
  then have 3: "n\<le> card (S-{e})" 
    using Suc e_def
    by (metis (no_types, lifting) Diff_empty Diff_insert0 Suc_leD Suc_le_mono antisym card_insert_le_m1 diff_Suc_1 insert_Diff linear zero_less_Suc) 
  then have 1: "card (get_elements (n) (S -{e})) = n"
    using Suc 
    by auto 
  have "get_elements n (S-{e}) \<subseteq> (S-{e})" 
    using get_elements_subset Suc 3 
    by auto
  then have "e \<notin> get_elements n (S-{e})"
    by auto
  then show ?case 
    using 1 2 Suc  
    by (metis Diff_eq_empty_iff Suc_diff_le \<open>get_elements n (S - {e}) \<subseteq> S - {e}\<close> card_0_eq card_Suc_eq card_infinite diff_is_0_eq' finite.emptyI finite_Diff2 finite_insert insert_is_Un le_numeral_extra(3)) 
qed


lemma set_set_to_list: "finite S \<Longrightarrow> set (set_to_list S) = S" 
  unfolding set_to_list_def 
  by (metis (mono_tags, lifting) finite_distinct_list tfl_some) 


lemma distinct_set_to_list: "finite S \<Longrightarrow> distinct (set_to_list S)" 
  unfolding set_to_list_def
  by (metis (mono_tags, lifting) finite_distinct_list tfl_some)


lemma distinct_size:
  assumes "distinct L"
  shows "size L = card (set L)"
  using assms 
  by (simp add: distinct_card) 


lemma is_vertex_cover:
  assumes "is_vertex_cover (set E') (set V')" 
  shows "is_vertex_cover_list E' V'"
  using assms is_vertex_cover_list_def is_vertex_cover_def
  by blast 


lemma is_vertex_cover_super_set:
  assumes "is_vertex_cover E' V" "V\<subseteq> V'"
  shows "is_vertex_cover E' V'" 
  using is_vertex_cover_def assms
  by (smt Collect_mem_eq in_mono mem_Collect_eq order_refl)


context
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover"
begin


lemma make_card_equal: 
  assumes "ugraph (set E')" "set V' \<subseteq> \<Union> (set E')" "k \<le> card (\<Union> (set E'))" "size V' \<le> k" "is_vertex_cover (set E') (set V')" "distinct V'"
  shows "\<exists>V. ugraph (set E') \<and> set V \<subseteq> \<Union> (set E') \<and> k \<le> card (\<Union> (set E')) \<and> size V = k \<and> is_vertex_cover (set E') (set V) \<and> distinct V"
proof -
  define k' where k'_def: "k' = k - (size V')"
  define leftNodes where leftNodes_def: "leftNodes = ((\<Union> (set E')) - (set V'))"  
  then have "leftNodes \<subseteq> \<Union> (set E')" 
    by simp
  have 1: "k' \<le> card leftNodes" 
  proof -
    have "k = k' + size V'" 
      using k'_def by (simp add: assms(4))  
    with \<open>leftNodes \<subseteq> \<Union> (set E')\<close> assms(2,3,6) show ?thesis
      unfolding k'_def
      by (metis (full_types) Diff_partition Diff_subset_conv Un_Diff_cancel card_Un_le distinct_size
            double_diff le_diff_conv leftNodes_def order_trans) 
  qed
proof -
  obtain k' where k'_def: "k' = k - (size V')" 
    by simp
  then obtain leftNodes where leftNodes_def: "leftNodes = ((\<Union> (set E')) - (set V'))"  
    by simp
  then have "leftNodes \<subseteq> \<Union> (set E')" 
    by simp
  then obtain setV where setV_def: "setV= (set V') \<union> get_elements k' leftNodes" 
    by simp
  have 1: "k' \<le> card leftNodes" 
    using assms k'_def leftNodes_def 
  proof -
    have "k = k' + size V'" 
      using k'_def 
      by (simp add: assms(4))  
    then show ?thesis 
      by (metis (full_types) Diff_partition Diff_subset_conv Un_Diff_cancel \<open>leftNodes \<subseteq> \<Union> (set E')\<close> assms(2) assms(3) assms(6) card_Un_le distinct_size double_diff k'_def le_diff_conv leftNodes_def order_trans) 
  qed
  then have 2: "setV \<subseteq> \<Union> (set E')"  
    using \<open>leftNodes \<subseteq> \<Union> (set E')\<close> get_elements_subset setV_def assms 
    by blast
  have 4: "finite setV" 
    using 2 assms ugraph_def
    by (meson rev_finite_subset ugraph_vertex_set_finite) 
  have 3: "card setV = k" 
    using assms setV_def k'_def 1 
  proof -
    have "card (get_elements k' leftNodes) = k'" 
      by (simp add: "1" card_get_elements) 
    have a: "(get_elements k' leftNodes) \<subseteq> leftNodes" 
      by (simp add: "1" get_elements_subset)  
    have "leftNodes \<inter> set V' = {}" 
      using leftNodes_def 
      by auto
    then have "set V' \<inter> (get_elements k' leftNodes) = {}" 
      using a 
      by auto
    then have "card setV = card (set V') + card (get_elements k' leftNodes)" 
      using setV_def 4 
      by (simp add: card_Un_disjoint)   
    then show ?thesis 
      using k'_def setV_def assms \<open>card (get_elements k' leftNodes) = k'\<close> distinct_size 
      by force 
  qed
  then obtain V where V_def: "V = set_to_list setV" 
    by auto
  then have 5: "set V = setV" 
    using 4 
    by (simp add: set_set_to_list) 
  then have 6: "distinct V" 
    using 4 
    by (simp add: V_def distinct_set_to_list) 
  then have 7: "set V \<subseteq> \<Union> (set E')" "size V = k" 
    using 5 2 
     apply(simp) 
    using 5 3 6 
    by (simp add: distinct_size) 
  have "set V' \<subseteq> set V" 
    using 5 setV_def
    by simp 
  then have "is_vertex_cover (set E') (set V)" 
    using is_vertex_cover_super_set assms 
    by auto  
  then show ?thesis 
    using assms 2 3 4 V_def 5 6 7 
    by blast
qed


lemma in_vc_list: "vc_set_to_vc_list (E, k) \<in> vertex_cover_list"
proof -
  have "\<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> k \<le> card (\<Union> E) \<and> card V \<le> k \<and> is_vertex_cover E V" 
    using in_vc
    by(auto simp add: vertex_cover_def)
  then obtain V where V_def: "ugraph E" "V \<subseteq> \<Union> E" "k \<le> card (\<Union> E)" 
    "card V \<le> k" "is_vertex_cover E V"
    by auto
  then have finite_V: "finite V" 
    using finite_subset ugraph_vertex_set_finite 
    by auto 
  have "vc_set_to_vc_list (E, k) = (set_to_list E, k)" 
    using V_def
    by (simp add: vc_set_to_vc_list_def)
  then obtain E' where  E'_def: "E' = (set_to_list E)" 
    by auto
  have finite_E: "finite E" 
    using V_def ugraph_def 
    by blast
  then have 2: "set E' = E" 
    using set_set_to_list E'_def 
    by fast
  then have 3: "ugraph (set E')" "V \<subseteq> \<Union> (set E')" "k \<le> card (\<Union> (set E'))" "card V \<le> k" "is_vertex_cover (set E') V"
    using V_def E'_def 
    by metis+
  then obtain V' where V'_def: "V' = set_to_list V" 
    by simp
  then have 4: "set V' = V" 
    using set_set_to_list finite_V 
    by auto
  then have distinct_V': "distinct V'" 
    using V'_def finite_V distinct_set_to_list
    by auto
  then have 5: "ugraph (set E')" "set V' \<subseteq> \<Union> (set E')" "k \<le> card (\<Union> (set E'))" 
    "size V' \<le> k" "is_vertex_cover (set E') (set V')"
    using 3 finite_V V_def V'_def 4 
    by(auto simp add: distinct_size)
  then have is_vertex_cover_list: "is_vertex_cover_list ( E') ( V')" 
    using is_vertex_cover 
    by auto
  have distinct_E': "distinct E'" 
    using E'_def finite_E distinct_set_to_list 
    by auto
  have "\<exists>V. ugraph (set E') \<and> set V \<subseteq> \<Union> (set E') \<and> k \<le> card (\<Union> (set E')) \<and> size V = k 
    \<and> is_vertex_cover (set E') (set V) \<and> distinct V"
    using make_card_equal 5 distinct_V' 
    by blast 
  then show ?thesis 
    using distinct_E' vertex_cover_list_def E'_def \<open>vc_set_to_vc_list (E, k) = (set_to_list E, k)\<close> 
      is_vertex_cover 
    by fastforce    
qed
end


lemma else_not_in_vc_list:
  shows "([], 1) \<notin> vertex_cover_list" 
proof -
  have "card (set []) = 0" 
    by simp
  then have "1 > card (set [])" 
    by simp
  then have "([], 1) \<notin> vertex_cover_list"
    using vertex_cover_list_def
    by force
  then show ?thesis .
qed


context
  fixes E k assumes in_vc_list: "vc_set_to_vc_list (E,k) \<in> vertex_cover_list"
  fixes E' k' assumes E'_def: "vc_set_to_vc_list (E,k) = (E',k')" 
begin 


lemma is_vc_list_is_vc:
  assumes "is_vertex_cover_list A B"
  shows "is_vertex_cover (set A) (set B)" 
  using is_vertex_cover_list_def is_vertex_cover_def assms 
  by fast


lemma in_vc:
  shows "(E,k) \<in> vertex_cover"
proof - 
  have "(E', k') = (set_to_list E, k)" 
    using E'_def in_vc_list else_not_in_vc_list vc_set_to_vc_list_def 
    by (smt old.prod.case)
  then have 2: "k' = k" "E' = set_to_list E" 
    by simp+
  then have 3: "(E', k) \<in> vertex_cover_list" 
    using in_vc_list E'_def 
    by auto   
  then have 4: "ugraph E" "k \<le> card (\<Union> E)"  
  proof -
    show "ugraph E" proof (rule ccontr)
      assume "\<not> ugraph E" 
      then have "(E',k') = ([], 1)" 
        using E'_def 
        by (simp add: vc_set_to_vc_list_def)
      then have "vc_set_to_vc_list (E,k) \<notin> vertex_cover_list" 
        using E'_def else_not_in_vc_list 
        by auto 
      then show False 
        using in_vc_list 
        by simp
    qed
  next 
    show "k \<le> card (\<Union> E)" 
    proof (rule ccontr)
      assume "\<not> k \<le> card (\<Union> E)" 
      then have "(E',k') = ([], 1)" 
        using E'_def 
        by (simp add: vc_set_to_vc_list_def)
      then have "vc_set_to_vc_list (E,k) \<notin> vertex_cover_list" 
        using E'_def else_not_in_vc_list 
        by auto 
      then show False 
        using in_vc_list 
        by simp
    qed
  qed
  then have "finite E" 
    using ugraph_def 
    by auto
  then have 6: "set E' = E" 
    using 2 
    by (simp add: set_set_to_list) 
  have "\<exists>V. ugraph (set E') \<and> set V \<subseteq> \<Union> (set E') \<and> k \<le> card (\<Union> (set E')) \<and> length V = k
     \<and> is_vertex_cover_list E' V \<and> distinct E' \<and> distinct V"
    using 3  
    by (simp add: vertex_cover_list_def)  
  then obtain V where V_def:
    "ugraph (set E')" "set V \<subseteq> \<Union> (set E')" "k \<le> card (\<Union> (set E'))" "length V = k" 
    "is_vertex_cover_list E' V" "distinct E'" "distinct V" 
    by auto
  then obtain setV where setV_def: "setV = set V" 
    by auto
  then have 7: "setV \<subseteq> \<Union> E" "k \<le> card (\<Union> E)" "card setV \<le> k" 
    using V_def 6 card_length 
    by(auto) 
  have "is_vertex_cover E setV" 
    using 6 setV_def is_vc_list_is_vc V_def 
    by auto 
  then show ?thesis 
    using 4 7 vertex_cover_def 
    by blast    
qed


end



subsection\<open> Main theorem \<close>

(*Just some help for Isabelle, since she was not able to figure that out herself*)
lemma vc_set_implies_vc_list: "(E,k) \<in> vertex_cover  \<Longrightarrow> vc_set_to_vc_list (E,k) \<in> vertex_cover_list"
  using in_vc_list by auto


lemma in_vc_list_implies_in_vc_set: 
  assumes "vc_set_to_vc_list (E,k) \<in> vertex_cover_list"
  shows "(E,k) \<in> vertex_cover"
  using in_vc assms 
proof -
  have 1: "vc_set_to_vc_list (E,k) =  
    (if ugraph E \<and> k \<le> card (\<Union> E) then (set_to_list E, k) else ([], 1))"  
    by (simp add: vc_set_to_vc_list_def) 
  then have "vc_set_to_vc_list (E,k) = (set_to_list E, k)" 
    using 1 assms else_not_in_vc_list
    by auto 
  then show ?thesis 
    using assms in_vc 
    by blast 
qed


theorem is_reduction_vc: 
  "is_reduction vc_set_to_vc_list vertex_cover vertex_cover_list"
  unfolding is_reduction_def
  using vc_set_implies_vc_list in_vc_list_implies_in_vc_set by auto

end
