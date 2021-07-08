section \<open>\<open>3CNF-SAT\<close> To \<open>Set Cover\<close>\<close>

theory Three_Sat_To_Set_Cover
  imports Reductions "Poly_Reductions_Lib.SAT_Definition"
begin

subsection \<open>Preliminaries\<close>


type_synonym 'a ugraph = "'a set set"

definition
  "ugraph E \<equiv> finite E \<and> (\<forall>e \<in> E. card e = 2)" \<comment> \<open>Allow self-loops?\<close>

definition
  "is_independent_set E V \<equiv> \<forall>u \<in> V. \<forall>v \<in> V. {u, v} \<notin> E"

definition
  "independent_set \<equiv> {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> card V \<ge> k \<and> is_independent_set E V}"

definition
  "is_vertex_cover E V \<equiv> \<forall> e \<in> E. \<exists> v \<in> V. v \<in> e"

definition
  "vertex_cover \<equiv>
  {(E, k). \<exists>V. ugraph E \<and> V \<subseteq> \<Union> E \<and> k \<le> card (\<Union> E) \<and> card V \<le> k \<and> is_vertex_cover E V}"

definition
  (* "set_cover \<equiv> {(T, k). \<exists> S \<subseteq> T. \<Union> S = \<Union> T \<and> card S \<le> k \<and> finite T \<and> finite (\<Union> T)}" *)
  "set_cover \<equiv> {(T, k). \<exists> S \<subseteq> T. \<Union> S = \<Union> T \<and> card S \<le> k}"

definition
  "is_vc \<equiv> \<lambda>(E, k). if k > card (\<Union> E) then (E, k) else (E, card (\<Union> E) - k)"

definition
  "vc_sc \<equiv> \<lambda>(E, k).
    if ugraph E \<and> k \<le> card (\<Union> E) then ({{e. e \<in> E \<and> v \<in> e} | v. v \<in> \<Union>E}, k)
    else ({{undefined}}, 0)"

lemma is_independent_set_is_vertex_cover:
  "is_independent_set E V \<longleftrightarrow> is_vertex_cover E ((\<Union>E) - V)" if "ugraph E"
  using that unfolding is_independent_set_def is_vertex_cover_def
proof safe
  fix e
  assume A: "ugraph E" "\<forall>u\<in>V. \<forall>v\<in>V. {u, v} \<notin> E" "e \<in> E"
  then obtain u v where "e = {u, v}"
    unfolding ugraph_def by (metis card_eq_SucD numeral_2_eq_2)
  with A(2,3) consider "u \<notin> V" "v \<notin> V" | "u \<in> V" "v \<in> \<Union> E - V" | "v \<in> V" "u \<in> \<Union> E - V"
    by auto
  then show "\<exists>v\<in>\<Union> E - V. v \<in> e"
    using \<open>e \<in> E\<close> unfolding \<open>e = _\<close> by cases auto
next
  fix u v
  assume "\<forall>e\<in>E. \<exists>v\<in>\<Union> E - V. v \<in> e" "u \<in> V" "v \<in> V" "{u, v} \<in> E"
  then show False
    by force
qed

lemma ugraph_vertex_set_finite:
  assumes "ugraph E"
  shows "finite (\<Union>E)"
  using assms by (auto 4 3 intro: card_ge_0_finite simp: ugraph_def)


subsection \<open>Independent Set to Set Cover\<close>
theorem is_reduction_is_vc:
  "is_reduction is_vc independent_set vertex_cover"
  unfolding is_reduction_def is_vc_def independent_set_def vertex_cover_def
proof (simp add: is_independent_set_is_vertex_cover , safe)
  show False if "card (\<Union> E) < k" "ugraph E" "k \<le> card V" "V \<subseteq> \<Union> E" for E k and V :: "'a set"
    using that by (auto 4 4 intro: card_ge_0_finite simp: ugraph_def dest: card_mono[rotated])
next
  show "\<exists>V. V \<subseteq> \<Union> E \<and> card V \<le> card (\<Union> E) - k \<and> is_vertex_cover E V"
    if "ugraph E" "V \<subseteq> \<Union> E" "k \<le> card V" "is_independent_set E V" for E k and V :: "'a set"
    using that
    by (subst (asm) is_independent_set_is_vertex_cover, (simp; fail))
      (intro exI conjI,
        auto simp: card_Diff_subset[OF finite_subset] dest: ugraph_vertex_set_finite)
next
  fix E :: "'a set set" and k :: nat and V :: "'a set"
  assume A: "\<not> card (\<Union>E) < k" "ugraph E" "V \<subseteq> \<Union> E" "card V \<le> card (\<Union>E) - k" "is_vertex_cover E V"
  then have "\<Union> E - (\<Union> E - V) = V"
    by auto
  with A show "\<exists>V. V \<subseteq> \<Union> E \<and> k \<le> card V \<and> is_independent_set E V"
    by (auto simp: is_independent_set_is_vertex_cover card_Diff_subset[OF finite_subset]
        dest: ugraph_vertex_set_finite intro!: exI[where x = "\<Union> E - V"])
qed


subsection \<open>Three Sat to Independent Set\<close>

definition
  "conflict l1 l2 \<equiv> \<exists>a. l1 = Pos a \<and> l2 = Neg a \<or> l1 = Neg a \<and> l2 = Pos a"

definition
  "sat_is F \<equiv> if (\<forall>cls \<in> set F. card cls = 3) then (
    {{(l1, i), (l2, i)} | l1 l2 i. i < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! i \<and> l1 \<noteq> l2}
  \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> conflict l1 l2}, length F)
  else ({}, 1)"

lemma conflict_models_ccontr:
  assumes "(\<sigma>\<up>) x" "(\<sigma>\<up>) y" "conflict x y"
  shows "False"
  using assms unfolding conflict_def lift_def by auto

lemma conflict_same[simp]:
  "conflict l l \<longleftrightarrow> False"
  unfolding conflict_def by simp

theorem is_reduction_sat_is:
  "is_reduction sat_is three_cnf_sat independent_set"
  unfolding is_reduction_def
proof safe
  fix F :: "'a lit set list"
  assume "F \<in> three_cnf_sat"
  then obtain \<sigma> where "\<sigma> \<Turnstile> F"
    unfolding three_cnf_sat_def sat_def by auto
  from \<open>F \<in> _\<close> have fin_1: "finite (\<Union> (set F))"
    unfolding three_cnf_sat_def by (auto 4 3 intro: card_ge_0_finite)
  let ?m = "length F"
  let ?l = "\<lambda>i. SOME l. (\<sigma>\<up>) l \<and> l \<in> F ! i"
  define V where "V \<equiv> {(?l i, i) | i. i < ?m}"
  have select: "(\<sigma>\<up>) (?l i) \<and> (?l i) \<in> F ! i" if "i < length F" for i
    using \<open>\<sigma> \<Turnstile> F\<close> that unfolding models_def by - (rule someI_ex, auto)
  { fix l i assume "l \<in> F ! i" "i < length F"
    have "card (F ! i) = 3"
      using \<open>F \<in> _\<close> \<open>i < _\<close> unfolding three_cnf_sat_def by auto
    with \<open>l \<in> _\<close> consider l' where "l \<noteq> l'" "l' \<in> F ! i"
      unfolding numeral_3_eq_3 by (force dest: card_eq_SucD)
  } note pair = this
  obtain E k where "sat_is F = (E, k)"
    by force
  let ?S = "((\<Union> (set F)) \<times> {0..<length F}) \<times> ((\<Union> (set F)) \<times> {0..<length F})"
  from \<open>F \<in> _\<close> have wf: "\<forall>cls \<in> set F. card cls = 3"
    unfolding three_cnf_sat_def by auto
  with \<open>sat_is F = _\<close> have "length F = k"
    unfolding sat_is_def by simp
  have "card V = length F"
    unfolding V_def setcompr_eq_image by (subst card_image) (auto intro: inj_onI)
  moreover have "is_independent_set E V"
    using \<open>sat_is F = (E, k)\<close> wf unfolding sat_is_def is_independent_set_def V_def
    by (auto intro: conflict_models_ccontr dest: select simp: doubleton_eq_iff)
  moreover have "ugraph E"
    using \<open>sat_is F = (E, k)\<close> wf unfolding sat_is_def is_independent_set_def ugraph_def
    apply safe
    subgoal
      using fin_1 by (fastforce intro: finite_surj[where A = "?S"])
    by (force simp: card_insert_if)+
  moreover have "V \<subseteq> \<Union> E"
    using \<open>sat_is F = (E, k)\<close> wf unfolding V_def sat_is_def is_independent_set_def ugraph_def
    apply simp
    apply (elim conjE)
    apply (drule sym)
    apply simp
    apply (rule subsetI)
    apply (rule UnI1)
    apply clarsimp
    apply (frule select)
    apply (rule pair)
    apply auto
    done
  ultimately show "sat_is F \<in> independent_set"
    unfolding independent_set_def by (auto simp: \<open>sat_is _ = _\<close> \<open>length F = _\<close>)
next
  fix F :: "'a lit set list"
  assume "sat_is F \<in> independent_set"
  obtain E k where "sat_is F = (E, k)"
    by force
  show "F \<in> three_cnf_sat"
  proof (cases "\<forall>cls \<in> set F. card cls = 3")
    case wf: True
    with \<open>sat_is F = _\<close> have "length F = k"
      unfolding sat_is_def by simp
    from \<open>sat_is F \<in> _\<close> obtain V where V:
      "ugraph E" "V \<subseteq> \<Union> E" "card V \<ge> k" "is_independent_set E V"
      unfolding independent_set_def \<open>sat_is _ = _\<close> by auto
    define \<sigma> where "\<sigma> \<equiv> \<lambda>x. (\<exists>i. (Pos x, i) \<in> V)"
    have V_inj: "l = l'" if "(l, i) \<in> V" "(l', i) \<in> V" for l l' i
    proof (rule ccontr)
      from that V(2) have "i < length F"
        using \<open>sat_is _ = _\<close> wf unfolding sat_is_def by auto
      from that V(2) have "l \<in> F ! i" "l' \<in> F ! i"
        using \<open>sat_is _ = _\<close> wf unfolding sat_is_def by fastforce+
      assume "l \<noteq> l'"
      with \<open>l \<in> _\<close> \<open>l' \<in> _\<close> \<open>i < _\<close> have "{(l, i), (l', i)} \<in> E"
        using \<open>sat_is _ = _\<close> wf unfolding sat_is_def by auto
      with V(4) that show False
        unfolding is_independent_set_def by auto
    qed
    have 1: "i < length F \<and> l \<in> F ! i" if "(l, i) \<in> V" for l i
      using that V(2) using \<open>sat_is _ = _\<close> wf unfolding sat_is_def by auto
    then have V_sub: "V \<subseteq> (\<lambda>i. (SOME l. (l, i) \<in> V, i)) ` {0..<length F}"
      by (auto 4 3 intro: someI V_inj)
    have 2: "\<exists>l. (l, i) \<in> V" if "i < length F" for i
    proof (rule ccontr)
      assume "\<nexists>l. (l, i) \<in> V"
      with that V_sub have "V \<subset> (\<lambda>i. (SOME l. (l, i) \<in> V, i)) ` {0..<length F}"
        by fastforce
      then have "card V < length F"
        apply -
        apply (drule psubset_card_mono[rotated])
        using card_image_le[of "{0..<length F}" "\<lambda>i. (SOME l. (l, i) \<in> V, i)"]
        by auto
      with \<open>card V \<ge> _\<close> \<open>length F = _\<close> show False
        by simp
    qed
    have no_conflict: False if "(l, i) \<in> V" "(l', j) \<in> V" "conflict l l'" for l l' i j
      using \<open>sat_is F = (E, k)\<close> that unfolding sat_is_def
      by (simp add: wf) (smt 1 UnCI V(4) is_independent_set_def mem_Collect_eq prod.sel(1))
    have "\<exists>l\<in>cls. (\<sigma>\<up>) l" if "cls \<in> set F" for cls
    proof -
      from that obtain i where "F ! i = cls" "i < length F"
        by (meson in_set_conv_nth)
      then obtain l where "(l, i) \<in> V"
        by (blast dest: 2)
      then have "(\<sigma>\<up>) l"
        unfolding \<sigma>_def lift_def by (cases l) (auto simp: conflict_def dest: no_conflict)
      moreover from \<open>_ \<in> V\<close> have "l \<in> cls"
        using \<open>F ! i = _\<close> by (auto dest: 1)
      ultimately show ?thesis
        by auto
    qed
    then have "\<sigma> \<Turnstile> F"
      unfolding models_def by auto
    with wf show "F \<in> three_cnf_sat"
      unfolding three_cnf_sat_def by (auto simp: sat_def)
  next
    case False
    with \<open>sat_is F \<in> _\<close> show "F \<in> three_cnf_sat"
      unfolding sat_is_def independent_set_def by simp
  qed
qed

subsection \<open>Vertex Cover to Set Cover\<close>
theorem is_reduction_vc_sc:
  "is_reduction vc_sc vertex_cover set_cover"
  unfolding is_reduction_def vc_sc_def vertex_cover_def set_cover_def
  apply clarsimp
  apply safe
  subgoal for E k V
    apply (rule exI[where x = "{{e \<in> E. v \<in> e} |v. v \<in> V}"])
    apply (intro conjI)
    subgoal
      by fastforce
    subgoal
      apply safe
      subgoal for e _ v
        by auto
      subgoal for e _ v e'
        unfolding is_vertex_cover_def by simp (metis mem_Collect_eq)
      done
    subgoal
      unfolding setcompr_eq_image
      by (rule order.trans, rule card_image_le) (auto dest: ugraph_vertex_set_finite finite_subset)
    done
  subgoal premises prems for E k S
  proof -
    define vv where "vv \<equiv> \<lambda>X. SOME v. X = {e \<in> E. v \<in> e}"
    let ?S = "vv ` S"
    have *: "{e \<in> E. v \<in> e} = {e \<in> E. vv {e \<in> E. v \<in> e} \<in> e}" for v
      unfolding vv_def by (rule someI) auto
    then have "vv {e \<in> E. v \<in> e} \<in> \<Union>E" if "{e \<in> E. v \<in> e} \<noteq> {}" for v
      using that by auto
    then have 1: "vv X \<in> \<Union>E" if "X \<in> S" for X
      using \<open>S \<subseteq> _\<close> that by blast
    from \<open>ugraph _\<close> have "finite E"
      unfolding ugraph_def by auto
    moreover have "S \<subseteq> Pow E"
      by (rule order.trans, rule prems) auto
    ultimately have "finite S"
      using \<open>finite E\<close> finite_subset by auto
    have "is_vertex_cover E ?S"
      unfolding is_vertex_cover_def
    proof safe
      fix e :: "'a set" assume "e \<in> E"
      from \<open>e \<in> E\<close> \<open>ugraph E\<close> have "card e = 2"
        unfolding ugraph_def by auto
      then obtain v where "v \<in> e"
        by force
      with \<open>\<Union> S = _\<close> \<open>e \<in> E\<close> have "e \<in> \<Union> S"
        by auto
      with \<open>S \<subseteq> {_ | _. _}\<close> obtain v where "{e \<in> E. v \<in> e} \<in> S" "v \<in> e"
        by auto
      with *[of v] \<open>e \<in> E\<close> show "\<exists>v\<in>vv ` S. v \<in> e"
        by auto
    qed
    have "?S \<subseteq> \<Union> E"
      by (auto dest: 1)
    moreover have "card ?S \<le> k"
      using \<open>card S \<le> _\<close> \<open>finite S\<close> by (auto intro: card_image_le order.trans)
    moreover have "is_vertex_cover E ?S"
      using prems
      unfolding is_vertex_cover_def
      apply auto
      subgoal premises prems for e
      proof -
        from \<open>e \<in> E\<close> \<open>ugraph E\<close> have "card e = 2"
          unfolding ugraph_def by auto
        then obtain v where "v \<in> e"
          by force
        with \<open>\<Union> S = _\<close> \<open>e \<in> E\<close> have "e \<in> \<Union> S"
          by auto
        with \<open>S \<subseteq> {_ | _. _}\<close> obtain v where "{e \<in> E. v \<in> e} \<in> S" "v \<in> e"
          by auto
        with *[of v] \<open>e \<in> E\<close> show ?thesis
          by auto
      qed
      done
    ultimately show ?thesis
      by auto
  qed
  by (simp add: finite_subset)+

theorem sat_sc:
  "is_reduction (vc_sc o is_vc o sat_is) three_cnf_sat set_cover"
  by (rule is_reduction_trans is_reduction_sat_is is_reduction_is_vc is_reduction_vc_sc)+

end