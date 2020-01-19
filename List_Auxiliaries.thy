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


lemma sublist_v1_hd_v2_hd_tl_lists:  
  assumes "p1@ (v#vs) @ p2 = L" "distinct L" "v = hd L"
  shows "vs @ p2 = tl L"
  using assms apply(induction L arbitrary: v vs) apply(auto) 
  by (metis append_self_conv2 in_set_conv_decomp list.sel(3) tl_append2) 


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


lemma length_geq_2_tt_not_empty: 
  assumes "length C \<ge> 2"
  shows "tl C \<noteq> []"
  using assms apply(induction C)
  by(auto)


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


lemma sublist_cons_impl_sublist_list: 
  assumes "sublist (a#as) (c#cs)" "a\<noteq> c"
  shows "sublist (a#as) cs"
proof -
  obtain p1 p2 where p_def: "p1@ (a#as) @ p2 = (c#cs)" 
    using sublist_def assms 
    by blast
  then have 1: "p1 \<noteq> []" 
    using assms 
    by fastforce
  then have "c = hd p1" 
    using p_def 
    by (metis hd_append2 list.sel(1))
  then have "tl p1 @ (a#as) @ p2 = cs"
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


lemma distinct_sublist_last_first_of_sublist_false_2: 
  assumes "distinct cs" "sublist [a, b, b2] cs" "a = last cs" 
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
    then have 1: "sublist [a,b, b2] cs" 
      using Cons 
      by (meson sublist_cons_impl_sublist_list) 
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


lemma sublist_hd_tl_equal_b_hd_tl_2: 
  assumes "sublist [a, b, c] cs" "a = hd cs" "distinct (tl cs)" 
    "a = last cs"
  shows "b = hd (tl cs) \<and> c = hd(tl (tl cs))" 
proof -
  obtain p1 p2 where p_def: "p1 @ [a, b, c] @ p2 = cs"
    using sublist_def assms by blast
  show ?thesis proof(cases "p1 =[]")
    case True
    then show ?thesis 
      using p_def by auto  
  next
    case False
    then have 1: "sublist [a, b, c](tl cs)" 
      using assms 
      by (metis p_def sublist_def tl_append2) 
    then have "tl cs \<noteq> []"
      using sublist_def by fastforce
    then have "last cs = last (tl cs)"
      by (simp add: last_tl)  
    then show ?thesis 
      using 1 assms p_def distinct_sublist_last_first_of_sublist_false_2 
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


lemma sublist_append_using_or: 
  assumes "sublist [a, b] (l1@l2)" "distinct (l1@l2)" "l1 \<noteq> []"
  shows "sublist [a, b] l1 \<or> sublist [a, b] l2 \<or> (a = last l1 \<and> b = hd l2)"
  using assms proof(induction l1)
  case Nil
  then show ?case using sublist_def by simp 
next
  case (Cons l l1)
  then have "a= l \<or> sublist [a, b] (l1@l2)"
    using sublist_cons_impl_sublist 
    by fastforce
  then show ?case proof
    assume a1: "a = l"
    then have "a = hd (l#l1@l2)"
      by simp
    then have b1: "b = hd (tl(l#l1@l2))" 
      using Cons sublist_def 
      by (smt append_Cons sublist_v1_hd_v2_hd_tl) 
    then have b2: "b = hd (l1@l2)" 
      by auto
    then have "sublist [a, b] (l#l1) \<or> (a = last (l#l1) \<and> b = hd l2)"
    proof(cases "l1 = []")
      case True
      then have a2: "a = last (l#l1)" 
        using a1 by simp
      then have "b = hd l2" 
        using b2 True by simp
      then show ?thesis using a2 by auto
    next
      case False
      then have "b = hd l1" 
        using b2 by simp
      then have "(l#l1) = []@[a, b] @ (tl l1)" 
        using a1 False by simp
      then have "sublist [a, b] (l#l1)"
        using sublist_def by metis
      then show ?thesis using sublist_def by simp
    qed
    then show ?thesis by auto
  next
    assume "sublist [a, b] (l1@l2)"
    then show ?thesis using Cons 
      by (metis append_self_conv2 distinct_tl last_ConsR list.sel(3) sublist_cons tl_append2) 
  qed
qed


lemma distinct_tl_rev_C: 
  assumes "distinct (tl C)" "hd C = last C \<or> distinct C"
  shows "distinct (tl (rev C))"
  using assms proof (induction C)
  case Nil
  then show ?case by auto
next
  case (Cons a C)
  have 1: "distinct C" 
    using Cons by simp
  then have 2: "distinct (tl (rev C))" 
    using Cons 
    by (simp add: distinct_tl) 
  have 3: "rev (a#C) = rev C @[a]"
    by simp
  have "a = last (a#C) \<or> a \<notin> set C" 
    using Cons by simp
  then show ?case proof 
    assume "a = last (a#C)"
    show ?thesis proof(cases "C = []")
      case True
      then show ?thesis by simp
    next
      case False
      then have 4: "a = last C" 
        using \<open>a = last (a # C)\<close> by auto 
      then have "a =  hd (rev C)" 
        by (simp add: False hd_rev) 
      then have "a \<notin> set (tl (rev C))" 
        by (metis "1" False distinct.simps(2) distinct_rev list.collapse rev.simps(1) rev_rev_ident)
      then show ?thesis 
        using 2 False by auto 
    qed
  next
    assume "a \<notin> set C"
    then have "a \<notin> set (rev C)" 
      by auto
    then show ?thesis 
      by (simp add: 1 distinct_tl) 
  qed
qed


lemma b_in_set_cy_exists_sublist: 
  assumes "b \<in> set Cy" "b \<in> set (tl Cy)" "length Cy \<ge> 2"
  shows "\<exists>a. sublist [a, b] Cy"
  using assms proof(induction Cy)
  case Nil
  then show ?case by auto
next
  case (Cons c Cy)
  then have 1: "b \<in> set Cy" 
    by simp
  then show ?case proof(cases "b = hd Cy")
    case True
    then have "(c#Cy) = c#b#tl Cy" 
      by (metis 1 hd_Cons_tl list.distinct(1) list.set_cases) 
    then have "[]@[c,b]@tl Cy = c#Cy" 
      by simp
    then have "sublist [c, b] (c#Cy)" 
      using Cons sublist_def by blast 
    then show ?thesis 
      by auto 
  next
    case False
    have 2: "length Cy \<ge> 2"
    proof (rule ccontr)
      assume "\<not> 2 \<le> length Cy"
      then have "2 > length Cy" 
        by auto
      then have "length Cy = 0 \<or> length Cy = 1" 
        by linarith
      then show False proof 
        assume "length Cy = 0" 
        then have "Cy = []" by simp
        then show False using 1 by simp
      next 
        assume "length Cy = 1" 
        then have "Cy = [b]" 
          using 1 length_1_set_L 
          by metis 
        then have "hd Cy = b" by simp
        then show False using False by simp
      qed
    qed
    then have 3: "b \<in> set (tl Cy)" 
      using False 
      by (metis "1" list.sel(1) list.sel(3) list.set_cases) 
    then have "\<exists>a. sublist [a, b] Cy" 
      using Cons 1 2 3 False by blast
    then show ?thesis using 2 sublist_cons 
      by fast
  qed
qed


lemma a_in_set_cy_exists_sublist: 
  assumes "a \<in> set Cy" "a\<noteq> last Cy" "length Cy \<ge> 2"
  shows "\<exists>b. sublist [a, b] Cy"
  using assms proof(induction Cy)
  case Nil
  then show ?case by auto
next
  case (Cons c Cy)
  then have not_empty: "Cy \<noteq> []"
    using in_set_insert by auto  
  then show ?case proof(cases "a = c")
    case True
    then have "[]@ [a, hd Cy] @ (tl Cy) = (c#Cy)"
      using not_empty by simp 
    then show ?thesis using sublist_def 
      by blast
  next
    case False
    then have in_Cy: "a \<in> set Cy" 
      using Cons by simp
    have not_last: "a\<noteq> last Cy" 
      using Cons not_empty by force  
    then show ?thesis proof(cases "length Cy \<ge> 2")
      case True
      then show ?thesis 
        using Cons not_last in_Cy sublist_cons 
        by fast  
    next
      case False
      then have "length Cy = 1 \<or> length Cy = 0" 
        by linarith 
      then have "length Cy = 1" 
        using not_empty by simp
      then have "Cy = [a]" 
        using in_Cy 
        by (simp add: length_1_set_L) 
      then have "a = last Cy"
        by simp
      then show ?thesis using not_last by simp
    qed
  qed
qed


lemma b_in_Cycle_exists_sublist:
  assumes "b \<in> set Cycle" "length Cycle \<ge> 2" "hd Cycle = last Cycle"
  shows "\<exists>a. sublist [a, b] Cycle"
  using assms proof(cases "b = hd Cycle")
  case True
  then have "b = last Cycle"
    using assms by simp
  then have "b \<in> set (tl Cycle)" 
    using assms last_in_set_tl
    by fast 
  then show ?thesis 
    using b_in_set_cy_exists_sublist assms  by metis 
next
  case False
  then have "b \<in> set (tl Cycle)" 
    using assms 
    by (metis hd_Cons_tl list.sel(2) set_ConsD)   
  then show ?thesis 
    using b_in_set_cy_exists_sublist assms by metis
qed


lemma a_in_Cycle_exists_sublist:
  assumes "a \<in> set Cycle" "length Cycle \<ge> 2" "hd Cycle = last Cycle"
  shows "\<exists>b. sublist [a, b] Cycle"
  using assms proof(cases "a = last Cycle")
  case True
  then have 1: "a = hd Cycle"
    using assms by simp 
  then obtain b where "b = hd (tl Cycle)" 
    by simp
  then have 2: "a # tl Cycle = Cycle" 
    using 1 
    by (metis assms(1) hd_Cons_tl list.discI list.set_cases) 
  have "tl Cycle \<noteq> []"
    using last_in_set_tl assms  by fastforce 
  then have "[]@[a, b] @ (tl (tl Cycle)) = Cycle"
    using 2 
    by (simp add: \<open>b = hd (tl Cycle)\<close>) 
  then have "sublist [a, b] Cycle" 
    using sublist_def by blast 
  then show ?thesis 
    by auto 
next
  case False   
  then show ?thesis 
    using a_in_set_cy_exists_sublist assms by metis
qed


lemma two_sublist_same_first_distinct_tl: 
  assumes "distinct (tl cs)" "sublist [x, a] cs" "sublist [x, b] cs" "hd cs = last cs" 
  shows "b = a"
proof(cases "x = hd cs")
case True
  then show ?thesis using assms 
    by (metis sublist_hd_tl_equal_b_hd_tl) 
next
case False
  then show ?thesis using assms 
    by (metis distinct.simps(1) list.collapse sublist_cons_impl_sublist two_sublist_distinct_same_last) 
qed


lemma distinct_tl_cyclic_sublist_cs_explisit: 
  assumes "distinct (tl cs)" "sublist [a, b] cs" "sublist [b, a] cs" "hd cs = last cs" "b \<noteq> a"
  shows "cs = [a, b, a] \<or> cs = [b, a, b]" 
proof(cases "a = hd cs")
  case True
  then have 1: "b = hd (tl cs)" 
    using assms sublist_hd_tl_equal_b_hd_tl by fastforce 
  then have 2: "a = hd (tl (tl cs))" 
    by (metis True assms distinct.simps(1) distinct_singleton hd_Cons_tl last_tl list.sel(1) list.sel(3) sublist_cons_impl_sublist sublist_hd_last_only_2_elems sublist_not_cyclic_for_distinct) 
  then have "cs = [a, b, a]@ (tl (tl (tl cs)))" 
    using 1 2 True 
    by (metis append_Nil2 assms(1) assms(3) assms(4) assms(5) last_tl list.collapse list.sel(2) list.sel(3) sublist_cons_impl_sublist sublist_hd_last_only_2_elems) 
  have "a = last cs" 
    using assms True by simp
  then show ?thesis using assms 
    by (metis "1" \<open>cs = [a, b, a] @ tl (tl (tl cs))\<close> last_tl list.collapse self_append_conv sublist_cons_impl_sublist sublist_hd_last_only_2_elems tl_Nil) 
next
  case False
  then have 1: "sublist [a, b] (tl cs)"
    using assms 
    by (metis distinct.simps(1) hd_Cons_tl sublist_cons_impl_sublist sublist_not_cyclic_for_distinct) 
  then show ?thesis proof(cases "b = hd cs")
    case True
    then have 1: "a = hd (tl cs)" 
    using assms sublist_hd_tl_equal_b_hd_tl by fastforce 
  then have 2: "b = hd (tl (tl cs))" 
    by (metis True assms distinct.simps(1) distinct_singleton hd_Cons_tl last_tl list.sel(1) list.sel(3) sublist_cons_impl_sublist sublist_hd_last_only_2_elems sublist_not_cyclic_for_distinct) 
  then have "cs = [b, a, b]@ (tl (tl (tl cs)))" 
    using 1 2 True 
    by (metis append_Nil2 assms(1) assms(2) assms(4) assms(5) last_tl list.collapse list.sel(2) list.sel(3) sublist_cons_impl_sublist sublist_hd_last_only_2_elems) 
  have "b = last cs" 
    using assms True by simp
  then show ?thesis using assms 
    by (metis "1" \<open>cs = [b, a, b] @ tl (tl (tl cs))\<close> last_tl list.collapse self_append_conv sublist_cons_impl_sublist sublist_hd_last_only_2_elems tl_Nil) 
  next
    case False
    then have 2: "sublist [b, a] (tl cs)"
    using assms 
    by (metis distinct.simps(1) hd_Cons_tl sublist_cons_impl_sublist sublist_not_cyclic_for_distinct) 
    then show ?thesis using 1 2 assms 
      by (meson sublist_not_cyclic_for_distinct) 
  qed
qed


lemma sublist_rev: 
  assumes "sublist as bs" 
  shows "sublist (rev as) (rev bs)"
  using assms sublist_def 
  by (metis append.assoc rev_append) 


lemma sublist_ab_bc_b_not_head: 
  assumes "sublist [a, b] ds" "sublist [b, c] ds" "b \<noteq> hd ds""distinct (tl ds)"
  shows "sublist [a, b, c] ds"
  using assms proof(induction ds)
  case Nil
  then have "[] \<noteq> []"  
    by (simp add: sublist_def) 
  then show ?case by simp
next
  case (Cons d ds)
  then show ?case proof(cases "b = hd ds")
    case True
    have "distinct ds" using Cons by auto
    then have 1: "c = hd (tl ds)" 
      using True Cons 
      by (smt hd_append list.distinct(1) list.sel(1) list.sel(3) sublist_def sublist_v1_hd_v2_hd_tl tl_append2) 
    have 2: "a = d"
      using True Cons 
      by (metis (no_types, lifting) Cons_eq_appendI \<open>distinct ds\<close> append_self_conv2 distinct_rev distinct_sublist_last_first_of_sublist_false last_rev rev.simps(1) rev.simps(2) sublist_cons_impl_sublist sublist_not_cyclic_for_distinct sublist_rev) 
    then have "ds = b # c # tl(tl ds)"
      using 1 2 True
      by (metis Cons.prems(1) Cons.prems(2) Cons.prems(3) True distinct_length_2_or_more distinct_singleton distinct_sublist_last_first_of_sublist_false last_ConsL last_ConsR list.collapse list.sel(1))
    then have "d#ds = a # b #c #(tl (tl ds))"
      using 2 by simp
    then have "d#ds = [] @ [a, b, c] @ (tl (tl ds))"
      by simp
    then show ?thesis using sublist_def by metis
  next
    case False
    then have 1: "sublist [a, b] ds" using Cons 
      by (metis append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) sublist_def tl_append2) 
    then have 2: "sublist [b, c] ds" using Cons 
      using list.sel(1) sublist_cons_impl_sublist 
      by metis 
    then show ?thesis using 1 2 Cons 
      by (simp add: False distinct_tl sublist_cons) 
  qed
qed


lemma sublist_ab_bcs_b_not_head: 
  assumes "sublist [a, b] ds" "sublist (b#cs) ds" "b \<noteq> hd ds""distinct (tl ds)"
  shows "sublist (a#b#cs) ds"
  using assms proof(induction ds)
  case Nil
  then have "[] \<noteq> []"  
    by (simp add: sublist_def) 
  then show ?case by simp
next
  case (Cons d ds)
  then obtain p1 p2 where p_def: "p1 @ (b#cs) @ p2 = d#ds"
    using sublist_def by blast
  then show ?case proof(cases "b = hd ds")
    case True
    have "distinct ds" using Cons by auto
    then have 1: "cs@p2 = tl ds" 
      using True Cons p_def sublist_v1_hd_v2_hd_tl_lists 
      by (metis hd_append list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 tl_append2) 
    have 2: "a = d"
      using True Cons 
      by (metis (no_types, lifting) Cons_eq_appendI \<open>distinct ds\<close> append_self_conv2 distinct_rev distinct_sublist_last_first_of_sublist_false last_rev rev.simps(1) rev.simps(2) sublist_cons_impl_sublist sublist_not_cyclic_for_distinct sublist_rev) 
    then have "ds = b # cs @ p2"
      using 1 2 True
      by (metis Cons.prems(1) True distinct_singleton distinct_sublist_last_first_of_sublist_false last_ConsL list.collapse)
    then have "d#ds = a # b #cs @p2"
      using 2 by simp
    then have "d#ds = [] @ (a# b#cs) @ p2"
      by simp
    then show ?thesis using sublist_def by metis
  next
    case False
    then have 1: "sublist [a, b] ds" using Cons 
      by (metis append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) sublist_def tl_append2) 
    then have 2: "sublist (b#cs) ds" using Cons 
      using list.sel(1) sublist_cons_impl_sublist_list 
      by metis 
    then show ?thesis using 1 2 Cons 
      by (simp add: False distinct_tl sublist_cons) 
  qed
qed


lemma sublist_indixes: 
  assumes "Suc i < length cs"
  shows "sublist [cs!i, cs!Suc i] cs"
  using assms proof(induction cs arbitrary: i)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a cs)
  then show ?case proof(cases "Suc i = 1")
    case True
    then have "i = 0"
      by simp
    then have "(a#cs)!i = a"
      using Cons.prems hd_conv_nth by fastforce 
    then have "(a#cs)!Suc i = hd (cs)"
      using Cons 
      by (simp add: \<open>i = 0\<close> hd_conv_nth) 
    then have "(a#cs) = [(a#cs)!i, (a#cs)!Suc i] @ tl cs" 
      using Cons.prems \<open>i = 0\<close> by auto
    then have "(a#cs) = [] @ [(a#cs)!i, (a#cs)!Suc i] @ tl cs" 
      using Cons.prems \<open>i = 0\<close> by auto
    then show ?thesis using sublist_def 
      by metis   
  next
    case False
    then have "Suc i > 1"
      by simp
    then have "Suc i -1 < length cs"
      using Cons by fastforce
    then have "sublist [cs!(i-1), cs!i] cs" 
      using Cons 
      using \<open>1 < Suc i\<close> gr0_conv_Suc by auto
    then show ?thesis 
      by (metis One_nat_def Suc_less_SucD \<open>1 < Suc i\<close> nth_Cons_Suc nth_Cons_pos sublist_cons) 
  qed
qed


end
