theory List_Auxiliaries
  imports Main Graph_Theory.Stuff
begin

lemma sublist_implies_in_set:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = C"
  shows "v1 \<in> set C" "v2 \<in> set C"
  using assms 
  by auto

lemma sublist_implies_in_set_a:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = C" "distinct C"
  shows "v1 \<noteq> v2"
  using assms 
  by auto

lemma sublist3_hd_lists:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = l1"
  shows "v2 = hd (ls1 @ ls2)"
  using assms apply(induction L) apply(auto) 
  by (metis assms(1) assms(2) distinct_append hd_append hd_in_set list.sel(1) list.sel(3) not_distinct_conv_prefix self_append_conv2)

lemma sublist_set_ls2_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows "v2 \<in> set ls2"
  using assms proof(induction L arbitrary: ls2 ls1)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "ls1 = []" using assms Cons 
      by (metis (no_types, hide_lams) Nil_is_append_conv append.assoc append_Cons_eq_iff append_self_conv2 distinct.simps(2) in_set_conv_decomp in_set_conv_decomp_first list.distinct(1) split_list)
    then have "a#L = ls2" using Cons by auto
    then have "v2 \<in> set ls2"
      using Cons.prems(3) sublist_implies_in_set(2) by force 
    then show ?thesis .
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then show ?thesis using Cons 
      by (metis L_def_2 append_self_conv2 sublist_implies_in_set(2) distinct_tl p_def tl_append2)
  qed
qed 

lemma sublist_set_ls2_2:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows "v2 \<in> set ls2"
  using assms sublist_set_ls2_1 
  by (metis Cons_eq_appendI)

lemma sublist_set_ls2_3:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2"
  using assms proof(induction L arbitrary: ls2 ls1)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "ls1 = []" using assms Cons 
      by (metis (no_types, hide_lams) Nil_is_append_conv append.assoc append_Cons_eq_iff append_self_conv2 distinct.simps(2) in_set_conv_decomp in_set_conv_decomp_first list.distinct(1) split_list)
    then have "a#L = ls2" using Cons by auto
    then show ?thesis 
      using Cons by blast
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then show ?thesis using Cons 
      by (metis L_def_2 append_self_conv2 distinct_tl p_def tl_append2)
  qed
qed 

lemma sublist_set_ls2_4:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2" "ls3 = l1#ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2"
proof -
  have 1: "L = ls3 @ ls2" 
    using assms by simp
  then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2" 
    using sublist_set_ls2_3 assms 1  by fast 
  then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 = ls2" by blast
  then show ?thesis by auto
qed

lemma sublist_set_ls2:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls2"
  shows  "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls2"
  using assms sublist_set_ls2_4 
  by fast 

lemma sublist_set_ls1_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "v2 \<in> set ls1"
  using assms proof(induction L arbitrary: ls1 ls2 )
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd ls1" 
      using Cons by (metis distinct.simps(2) distinct_singleton hd_append2 list.sel(1))
    with Cons have "v1 \<noteq> last ls1" 
      by auto
    then have "tl ls1 \<noteq> []" 
      by (metis Cons.prems(4) \<open>v1 = hd ls1\<close> distinct.simps(2) distinct_singleton last_ConsL list.collapse)
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" 
      using Cons assms by  argo
    then obtain p1 p2 where "p1@ [v1, v2] @ p2 = (a#L)" by auto
    then have "p1 = []" 
      using Cons \<open>v1 = a\<close> by (metis sublist_implies_in_set(1) distinct.simps(2) list.sel(3) tl_append2)
    then have "v2 = hd L" 
      using Cons by (metis Cons_eq_appendI True \<open>p1 @ [v1, v2] @ p2 = a # L\<close> eq_Nil_appendI list.sel(1) list.sel(3))
    then have "v2 = hd (tl ls1)" 
      using Cons \<open>tl ls1 \<noteq> []\<close> by (metis Nil_tl \<open>p1 = []\<close> hd_append2 list.sel(3) tl_append2) 
    then show ?thesis 
      by (simp add: \<open>tl ls1 \<noteq> []\<close> list_set_tl)
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" 
      using False Cons p_def 
      by (metis hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 self_append_conv2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" 
      by auto
    have 2: "distinct L" 
      using Cons by (meson distinct.simps(2))
    have 3: "L = tl ls1 @ ls2" 
      using Cons 
      by (metis distinct.simps(2) distinct_singleton list.sel(3) tl_append2) 
    have 4: "v1 \<in> set (tl ls1)" 
      using Cons False by (metis hd_Cons_tl hd_append2 list.sel(1) set_ConsD tl_Nil)
    have 5: "v1 \<noteq> last (tl ls1)" 
      using Cons 
      by (metis "4" last_tl list.set_cases neq_Nil_conv) 
    then show ?thesis
      using Cons 1 2 3 4 5 list_set_tl 
      by metis   
  qed
qed  

lemma sublist_set_ls1_2:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1" "ls3 = l1#ls1"
  shows "v2 \<in> set ls1"
proof -
  have "L = ls3 @ ls2" 
    using assms by simp
  have "v1 \<in> set ls3" using assms by simp
  then have 1: "v2 \<in> set ls3" using sublist_set_ls1_1 assms 
    by (metis \<open>L = ls3 @ ls2\<close> last.simps list.distinct(1) list.set_cases)
  have "v2 \<noteq> l1" using assms 
    by (metis append_self_conv2 sublist_implies_in_set(2) distinct.simps(2) hd_append2 list.sel(1) list.sel(2) list.sel(3) list.set_sel(1) tl_append2)
  then have "v2 \<in> (set ls1)" 
    using 1 assms by simp
  then show ?thesis  .
qed

lemma sublist_set_ls1_3:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "v2 \<in> set ls1"
  using assms sublist_set_ls1_2 
  by fast

lemma sublist_set_ls1_4:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1"
  using assms proof(induction L arbitrary: ls1 ls2 )
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd ls1" 
      using Cons by (metis distinct.simps(2) distinct_singleton hd_append2 list.sel(1))
    with Cons have "v1 \<noteq> last ls1" 
      by auto
    then have "tl ls1 \<noteq> []" 
      by (metis Cons.prems(4) \<open>v1 = hd ls1\<close> distinct.simps(2) distinct_singleton last_ConsL list.collapse)
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" 
      using Cons assms by  argo
    then obtain p1 p2 where "p1@ [v1, v2] @ p2 = (a#L)" by auto
    then have "p1 = []" 
      using Cons \<open>v1 = a\<close> by (metis sublist_implies_in_set(1) distinct.simps(2) list.sel(3) tl_append2)
    then have "v2 = hd L" 
      using Cons by (metis Cons_eq_appendI True \<open>p1 @ [v1, v2] @ p2 = a # L\<close> eq_Nil_appendI list.sel(1) list.sel(3))
    then have "v2 = hd (tl ls1)" 
      using Cons \<open>tl ls1 \<noteq> []\<close> by (metis Nil_tl \<open>p1 = []\<close> hd_append2 list.sel(3) tl_append2) 
    then show ?thesis 
      by (metis Cons.prems(4) \<open>p1 = []\<close> \<open>tl ls1 \<noteq> []\<close> \<open>v1 = hd ls1\<close> append_Cons eq_Nil_appendI in_set_replicate list.exhaust_sel replicate_empty)
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" 
      using False Cons p_def 
      by (metis hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 self_append_conv2)
    then have "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" 
      by auto
    have 2: "distinct L" 
      using Cons by (meson distinct.simps(2))
    have 3: "L = tl ls1 @ ls2" 
      using Cons 
      by (metis distinct.simps(2) distinct_singleton list.sel(3) tl_append2) 
    have 4: "v1 \<in> set (tl ls1)" 
      using Cons False by (metis hd_Cons_tl hd_append2 list.sel(1) set_ConsD tl_Nil)
    have 5: "v1 \<noteq> last (tl ls1)" 
      using Cons 
      by (metis "4" last_tl list.set_cases neq_Nil_conv) 
    then have "\<exists>p1 p2. p1@[v1, v2]@p2 = tl(ls1)" 
      using Cons 1 2 3 4 5 by blast
    then obtain p1' p2' where "p1'@[v1, v2]@p2' = tl(ls1)" by auto
    then have "(a#p1')@[v1, v2]@p2' = ls1" 
      using Cons by (simp add: "3")
    then show ?thesis
      by blast 
  qed
qed  

lemma sublist_set_ls1_5:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1" "ls3 = l1#ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1"
proof -
  have 1: "L = ls3 @ ls2" 
    using assms by simp
  have 2: "v1 \<in> set ls3" using assms by simp
  have 3: "v1 \<noteq> last ls3" using assms by auto
  then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls3" 
    using sublist_set_ls1_4 assms 1 2 by fast 
  then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 = ls3" by blast
  have "v2 \<noteq> l1" using assms 
    by (metis append_self_conv2 sublist_implies_in_set(2) distinct.simps(2) hd_append2 list.sel(1) list.sel(2) list.sel(3) list.set_sel(1) tl_append2)
  have 1: "v1 \<noteq> l1" 
    using assms by force
  then have 2: "p1@ [v1, v2] @ p2 = (l1 # ls1)" using assms p_def by auto
  then have "hd p1 = l1" using 1 p_def  
    by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
  then have "(tl p1)@[v1, v2] @ p2 = ls1" 
    using 2 1 by (metis hd_append list.sel(1) list.sel(3) tl_append2) 
  then show ?thesis by auto
qed

lemma sublist_set_ls1:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1"
  using assms sublist_set_ls1_5 by fast

lemma sublist_set_last_ls1_2: 
  assumes "x = hd L" "x = last ls1" "L = ls1 @ ls2" "x \<in> set ls1" "distinct L"
  shows "ls1 = [x]"
  using assms proof(induction L)
  case Nil
  then show ?case by(auto)
next
  case (Cons a L)
  then have "x = a" 
    by (meson list.sel(1))
  then show ?case using Cons 
    by (metis append.assoc append_Cons append_Cons_eq_iff append_Nil append_butlast_last_id distinct.simps(2) distinct_singleton)
qed

lemma sublist_set_last_ls1_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 = hd ls2"
  using assms proof(induction L arbitrary: ls1 ls2)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd (a#L)" 
      by simp  
    then have "ls1 = [a]" using assms Cons sublist_set_last_ls1_2 True 
      by fast 
    then have "L = ls2" using Cons by auto
    then have "v2 = hd ls2"
      using Cons by (metis (mono_tags, lifting) Cons_eq_appendI True \<open>ls1 = [a]\<close> sublist3_hd_lists  list.sel(3)) 
    then show ?thesis .
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def 
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2) 
    then have L_exists: "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    have "ls1 \<noteq> []" using False Cons by auto
    then have "L = tl ls1 @ ls2" using Cons 
      by (metis list.sel(3) tl_append2)
    then show ?thesis using Cons L_exists 
      by (metis False distinct.simps(2) distinct_singleton hd_append2 last_tl list.collapse list.sel(1) set_ConsD)
  qed
qed

lemma sublist_set_last_ls1_1_1:
  assumes "distinct L" "L = ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 \<in> set ls2"
  using assms proof(induction L arbitrary: ls1 ls2)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "v1 = hd (a#L)" 
      by simp  
    then have "ls1 = [a]" using assms Cons sublist_set_last_ls1_2 True 
      by fast 
    then have 1: "L = ls2" using Cons by auto
    have 2: "v2 \<in> set (a#L)" 
      using assms Cons.prems(3) sublist_implies_in_set(2) by force 
    have "v2 \<noteq> a" using True assms sublist_implies_in_set_a by fastforce
    then have "v2 \<in> set L" using 2 by simp
    then have "v2 \<in> set ls2" using 1 by simp
    then show ?thesis by(auto)
  next
    case False
    have "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" using Cons by auto
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L" by fast
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)" by auto
    have "p1 \<noteq> []" using False Cons p_def 
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2) 
    then have L_exists: "L = (tl p1) @[v1, v2] @ p2" 
      using L_def_2 by simp
    have "ls1 \<noteq> []" using False Cons 
      by auto 
    then have "L = tl ls1 @ ls2" using Cons 
      by (metis list.sel(3) tl_append2)
    then show ?thesis using Cons L_exists 
      by (metis False distinct.simps(2) distinct_singleton hd_append2 last_tl list.collapse list.sel(1) set_ConsD)
  qed
qed

lemma sublist_set_last_ls1_3:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1" "ls3 = l1 # ls1"
  shows "v2 = hd ls2"
proof -
  have L_def_2: "L = ls3 @ ls2" using assms by auto
  then have last: "v1 = last ls3" using assms by auto
  then have "v1 \<in> set ls3" using assms by auto
  then have "v2 = hd ls2" 
    using assms(1) assms(3) last sublist_set_last_ls1_1 L_def_2 by fast
  then show ?thesis .
qed

lemma sublist_set_last_ls1:
  assumes "distinct L" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 = hd ls2"
  using assms sublist_set_last_ls1_3 by fast

lemma sublist_set_noteq_l1:
  assumes "distinct (tl L)" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v1 \<noteq> l1"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1@ls2" 
  using assms proof(induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then have "l1 = a" by auto
  then show ?case using Cons
    by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(3) tl_append2)
qed

lemma sublist_set_v2_noteq_hd_lists:
  assumes "distinct (tl L)" "L = l1#ls1 @ ls2" "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "v2 \<noteq> hd (ls1@ls2)"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = ls1@ls2" 
  using assms proof(induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then have 1: "l1 = a" by auto
  obtain p1 p2 where p1p2_def: "p1@ [v1, v2] @ p2 = (a#L)" using Cons by blast 
  then show ?case using Cons proof(cases "v1 = l1")
    case True
    then show ?thesis proof(cases "p1 = []")
      case True
      then have "v1 = a" using p1p2_def by auto
      then have "v1 = hd (l1#ls1@ls2)" by (simp add: "1") 
      then have "v2 = hd (tl (l1#ls1@ls2))" using True p1p2_def 
        by (metis "1" Cons.prems(2) Cons_eq_append_conv \<open>v1 = a\<close> assms(2) list.sel(1) list.sel(3) self_append_conv2)
      then have "v2 = hd (ls1@ls2)" by simp
      then show ?thesis using Cons by auto
    next
      case False
      then have "hd p1 = a" using p1p2_def 
        by (metis hd_append2 list.sel(1)) 
      then have "(tl p1) @[v1, v2]@p2 = ls1 @ ls2" using p1p2_def Cons 
        by (metis False list.sel(3) tl_append2)  
      then show ?thesis by auto
    qed
  next
    case False
    then show ?thesis using Cons sublist_set_noteq_l1 
      by metis  
  qed
qed

lemma sublist_v1_in_subsets: 
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "L = l1@l2" 
  shows "v1 \<in> set l1 \<or> v1 \<in> set l2"
  using assms apply(induction L arbitrary: l1 l2) apply(auto) 
  by (metis hd_append2 in_set_conv_decomp list.sel(1) list.sel(3) list.set_sel(1) list_set_tl self_append_conv2 tl_append2)

lemma sublist_v1_hd_v2_hd_tl:  
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L" "distinct L" "v1 = hd L"
  shows "v2 = hd(tl L)"
  using assms apply(induction L arbitrary: v1) apply(auto) 
  by (metis in_set_conv_decomp list.sel(1) list.sel(3) self_append_conv2 tl_append2) 

lemma indices_length_set_ls2:
  assumes "\<exists>i. l = (ls1@ls2)!i \<and> i\<ge> length ls1 \<and> i< length (ls1@ls2)"
  shows "l \<in> set ls2"  
  using assms apply(induction "ls1@ls2") apply(auto)  
  by (metis add_less_imp_less_left le_iff_add nth_append_length_plus nth_mem) 

lemma indices_length_set_ls2_only_append: 
  assumes "\<exists>i. l = (l1#ls2)!i \<and> i\<ge> 1 \<and> i< length (l1#ls2)"
  shows "l \<in> set ls2"
proof -
  have "l1#ls2 = [l1]@ls2" by simp
  then show ?thesis using indices_length_set_ls2 assms by auto
qed 

lemma sublist_append_not_eq:
  assumes "\<exists>p1 p2. p1@ [v1, v2] @ p2 = (a#L)" "v1 \<noteq> a"
  shows "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L"
  using assms 
  by (metis Cons_eq_append_conv append_self_conv2 list.sel(1) list.sel(3) tl_append2) 

lemma x_in_implies_exist_index:
  assumes "x \<in> set L" 
  shows "\<exists>i. x = L!i \<and> i<length L"
  using assms by (metis in_set_conv_nth)

lemma distinct_same_indices:
  assumes "distinct L" "L!i = L!j" "i<length L" "j<length L"
  shows "i = j"
  using assms apply(induction L) apply(auto)
  by (simp add: nth_eq_iff_index_eq)


lemma length_1_set_L:
  assumes "length L = 1" "l \<in> set L"
  shows "L = [l]" 
  using assms 
  by (metis append_butlast_last_id butlast.simps(2) diff_is_0_eq' in_set_conv_nth last.simps last_conv_nth le_numeral_extra(4) length_0_conv length_butlast less_one list.distinct(1) zero_neq_one)  


lemma last_in_set_tl: 
  assumes "l = last L" "length L \<ge> 2" 
  shows "l \<in> set (tl L)"
using assms proof(induction L)
case Nil
then show ?case by auto
next
  case (Cons a L)
  then have "length L \<ge> 1" 
    by auto
  then have "L \<noteq> []" 
    by auto
  then show ?case using Cons 
    by force 
qed


lemma card_subset: 
  assumes "s \<subseteq> set L"
  shows "card s \<le> card (set L)"
proof -
  have 1: "finite (set L)" by simp
  then have 2: "finite s" 
    using assms finite_subset by auto 
  then show ?thesis using assms 1 2 
    by (simp add: card_mono) 
qed


lemma length_2_hd_last: 
  assumes "length L = 2" 
  shows "L = [hd L, last L]"
  using assms apply(induction L) apply(auto) 
  by (metis append_butlast_last_id append_eq_append_conv append_self_conv2 length_Cons list.size(3))


lemma length_2_exits: 
  assumes "length L = 2" 
  shows "\<exists>l1 l2. L = [l1, l2]" 
  using assms apply(induction L) apply(auto) 
  by (metis Suc_length_conv length_0_conv) 


subsubsection\<open>Definitions for VC_HC_2\<close>

definition "sublist l ls \<equiv> \<exists>p1 p2. p1@l@p2 = ls"

lemma sublist_transitiv:
  assumes "sublist l1 l2" "sublist l2 l3" 
  shows "sublist l1 l3" 
  using assms sublist_def 
  by (metis append.assoc) 

lemma sublist_append:
  assumes "sublist l1 l2" 
  shows "sublist l1 (l3@l2)" 
proof -
  have "\<exists>p1 p2. p1@l1@p2 = l2" 
    using sublist_def assms by auto
  then obtain p1 p2 where "p1@l1@p2 = l2"
    by auto 
  then have "(l3@p1)@l1@p2 = l3@l2" 
    by simp
  then show ?thesis 
    using sublist_def by blast
qed

lemma sublist_cons:
  assumes "sublist l1 l2" 
  shows "sublist l1 (l#l2)"
  using assms 
  by (metis Cons_eq_appendI sublist_def) 


lemma two_sublist_distinct_same_first: 
  assumes "sublist [x, a] L" "sublist [y, a] L" "distinct (tl L)"
  shows "x = y"
  using assms proof(induction L)
  case Nil
  then show ?case 
    by (simp add: sublist_def) 
next
  case (Cons l L)
  then have distinct: "distinct L"
    by simp
  then have 1: "distinct (tl L)" 
    by (simp add: distinct_tl) 
  then show ?case proof(cases "sublist [x, a] L")
    case True
    then have a1: "sublist [x, a] L"
      by simp
    then show ?thesis proof(cases "sublist [y, a] L")
      case True
      then show ?thesis 
        using a1 1 Cons by simp  
    next
      case False
      then have 2: "\<exists>p1 p2. p1@[y, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[y, a] @ p2 = (L))"
        using sublist_def Cons by blast+
      then have "y = l" 
        using Cons 
        by (meson sublist_append_not_eq)
      then have hd: "a = hd L" 
        by (metis 2 append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) tl_append2)
      have tl: "a \<in> set (tl L)" using a1 sublist_def 
        by (smt append_Cons list.sel(3) list.set_intros(1) self_append_conv2 sublist_implies_in_set(2) tl_append2) 
      then have False using hd tl distinct 
        by (metis distinct.simps(2) distinct_singleton list.collapse list_set_tl)         
      then show ?thesis by simp
    qed
  next
    case False
    then have 2: "\<exists>p1 p2. p1@[x, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[x, a] @ p2 = (L))"
      using sublist_def Cons by blast+
    then have 3: "x = l" 
      using Cons 
      by (meson sublist_append_not_eq)
    then show ?thesis proof(cases "sublist [y, a] L")
      case True
      then have hd: "a = hd L" 
        by (metis 2 append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) tl_append2)
      have tl: "a \<in> set (tl L)" using 3 True sublist_def 
        by (smt append_Cons list.sel(3) list.set_intros(1) self_append_conv2 sublist_implies_in_set(2) tl_append2) 
      then have False using hd tl distinct 
        by (metis distinct.simps(2) distinct_singleton list.collapse list_set_tl)
      then show ?thesis by simp
    next
      case False
      then have 2: "\<exists>p1 p2. p1@[y, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[y, a] @ p2 = (L))"
        using sublist_def Cons by blast+
      then have "y = l" 
        using Cons 
        by (meson sublist_append_not_eq)
      then show ?thesis using 3 by simp
    qed
  qed
qed


lemma sublist_cons_impl_sublist: 
  assumes "sublist [a, b] (c#cs)" "a\<noteq> c"
  shows "sublist [a, b] cs"
proof -
  obtain p1 p2 where p_def: "p1@[a, b] @ p2 = (c#cs)" 
    using sublist_def assms 
    by blast
  then have 1: "p1 \<noteq> []" 
    using assms 
    by fastforce
  then have "c = hd p1" 
    using p_def 
    by (metis hd_append2 list.sel(1))
  then have "tl p1 @ [a, b] @ p2 = cs"
    using 1 p_def 
    by (metis list.sel(3) tl_append2) 
  then show ?thesis using sublist_def 
    by blast
qed


lemma sublist_not_cyclic_for_distinct: 
  assumes "sublist [a, b] Cy" "sublist [b, a] Cy" "distinct Cy"
  shows False
  using assms proof (induction Cy)
  case Nil
  then show ?case 
    using sublist_def 
    by fast  
next
  case (Cons c Cy)
  then show ?case proof(cases "a = c")
    case a: True
    then have b_hd: "b = hd Cy" 
      using sublist_def Cons 
      by (metis list.sel(1) list.sel(3) sublist_v1_hd_v2_hd_tl)  
    then show ?thesis proof(cases "b = c")
      case b: True
      then have "b = a" using a by simp
      then have "sublist [a, a] (c#Cy)" 
        using Cons by auto
      then have "\<not> distinct Cy" 
        using sublist_def Cons sublist_implies_in_set_a by metis 
      then show ?thesis 
        using Cons by auto
    next
      case b: False
      then have "b \<noteq> a" 
        using a by simp
      have "sublist [b, a] Cy" 
        using b Cons sublist_cons_impl_sublist
        by metis
      then have "a \<in> set Cy"
        by (simp add: sublist_def sublist_implies_in_set) 
      then show ?thesis 
        using a Cons by simp
    qed
  next
    case a: False
    then show ?thesis proof(cases "b = c")
      case True
      then have "b \<noteq> a" 
        using a by simp
      have "sublist [a, b] Cy" 
        using a Cons sublist_cons_impl_sublist
        by metis
      then have "b \<in> set Cy"
        by (simp add: sublist_def sublist_implies_in_set) 
      then show ?thesis 
        using True Cons by simp
    next
      case False
      then have "sublist [a, b] Cy" "sublist [b, a] Cy"
        using a sublist_cons_impl_sublist Cons
        by metis+  
      then show ?thesis 
        using Cons by auto 
    qed
  qed
qed


lemma distinct_sublist_last_first_of_sublist_false: 
  assumes "distinct cs" "sublist [a, b] cs" "a = last cs" 
  shows False
  using assms proof(induction cs)
  case Nil
  then  have "[] \<noteq>  []" 
    by (simp add: sublist_def)  
  then show ?thesis by auto
next
  case (Cons c cs)
  then show ?thesis proof(cases "a = c")
    case True
    then have "hd (a#cs) = last (a#cs)" 
      using Cons by auto 
    then have "(a#cs) = [a]" 
      using Cons 
      by (metis True distinct.simps(2) last.simps last_in_set) 
    then show ?thesis using Cons 
      by (simp add: sublist_def) 
  next
    case False
    then have 1: "sublist [a,b] cs" 
      using Cons 
      by (meson sublist_cons_impl_sublist) 
    then have "cs \<noteq> []"
      using Cons.prems False by auto 
    then have 2: "last (c#cs) = last cs" by simp
    then show ?thesis using Cons 1  2 by simp
  qed
qed


lemma sublist_hd_tl_equal_b_hd_tl: 
  assumes "sublist [a, b] cs" "a = hd cs" "distinct (tl cs)" 
    "a = last cs"
  shows "b = hd (tl cs)" 
proof -
  obtain p1 p2 where p_def: "p1 @ [a, b] @ p2 = cs"
    using sublist_def assms by blast
  show ?thesis proof(cases "p1 =[]")
    case True
    then show ?thesis 
      using p_def by auto  
  next
    case False
    then have 1: "sublist [a, b](tl cs)" 
      using assms 
      by (metis p_def sublist_def tl_append2) 
    then have "tl cs \<noteq> []"
      using sublist_def by fastforce
    then have "last cs = last (tl cs)"
      by (simp add: last_tl)  
    then show ?thesis 
      using 1 assms p_def distinct_sublist_last_first_of_sublist_false 
      by metis 
  qed
qed


lemma sublist_hd_last_only_2_elems: 
  assumes "sublist [a,b] cs" "a = hd cs" "b = last cs" "distinct cs"
  shows "cs = [a, b]" 
  using assms proof(induction cs)
  case Nil
  then show ?case 
    by (simp add: sublist_def) 
next
  case (Cons c cs)
  then have 0: "a = c" 
    using Cons by auto
  then have 1: "b = hd (cs)" 
    using Cons 
    by (metis list.sel(3) sublist_def sublist_v1_hd_v2_hd_tl) 
  then have "hd cs = last cs" 
    using Cons 
    by (metis \<open>a = c\<close> distinct_sublist_last_first_of_sublist_false last_ConsL last_ConsR) 
  then have "cs = [b]" using 1 Cons 
    by (metis \<open>a = c\<close> append_Nil2 distinct_tl hd_in_set last.simps list.sel(3) sublist_not_cyclic_for_distinct sublist_set_last_ls1_2)
  then have "c#cs = [a, b]" 
    using 0 by simp
  then show ?case by auto
qed


lemma two_sublist_distinct_same_last: 
  assumes "sublist [x, a] L" "sublist [x, b] L" "distinct (L)"
  shows "a = b"
  using assms proof(induction L)
  case Nil
  then show ?case by (simp add: sublist_def)
next
  case (Cons c L)
  then show ?case proof(cases "x = c")
    case True
    then have "a = hd L" "b = hd L"
      using Cons 
      by (metis list.sel(1) list.sel(3) sublist_def sublist_v1_hd_v2_hd_tl)+
    then show ?thesis by simp
  next
    case False
    then have "sublist [x, a] L" "sublist [x, b] L"
      using Cons 
      by (meson sublist_cons_impl_sublist)+
    then show ?thesis using Cons by auto
  qed
qed 



lemma sublist_append_not_in_first: 
  assumes "sublist [v1, v2] (l1 @ l2)" "v1 \<notin> set l1"
  shows "sublist [v1, v2] l2" 
using assms proof(induction l1)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case 
    by (simp add: Cons sublist_cons_impl_sublist) 
qed 


end
