theory Kleene
  imports Concat
begin

primrec lang_pow :: "'a timed_word set => nat => 'a timed_word set" where
  "lang_pow L 0 = {[]}"
| "lang_pow L (Suc n) = concat_lang L (lang_pow L n)"

definition lang_star :: "'a timed_word set => 'a timed_word set" where
  "lang_star L = (\<Union>n. lang_pow L n)"

definition lang_plus :: "'a timed_word set => 'a timed_word set" where
  "lang_plus L = (\<Union>n. lang_pow L (Suc n))"

definition plus_ta :: "(nat, 'a) automaton => (nat, 'a) automaton" where
  "plus_ta A =
    \<lparr> ta_locations = ta_locations A,
      ta_initial = ta_initial A,
      ta_accepting = ta_accepting A,
      ta_clocks = ta_clocks A,
      ta_transitions = ta_transitions A \<union> concat_switches A A \<rparr>"

definition star_ta :: "(nat, 'a) automaton => (nat, 'a) automaton" where
  "star_ta A = union_ta epsilon_ta (plus_ta A)"

fun compile_kleene_fragment :: "'a tre => (nat, 'a) automaton option" where
  "compile_kleene_fragment Empty = Some empty_ta"
| "compile_kleene_fragment Epsilon = Some epsilon_ta"
| "compile_kleene_fragment (Atom a) = Some (atom_ta a)"
| "compile_kleene_fragment (Union r s) =
    (case compile_kleene_fragment r of
       None => None
     | Some A =>
         (case compile_kleene_fragment s of
            None => None
          | Some B => Some (union_ta A B)))"
| "compile_kleene_fragment (Concat r s) =
    (case compile_kleene_fragment r of
       None => None
     | Some A =>
         (case compile_kleene_fragment s of
            None => None
          | Some B => Some (concat_ta A B)))"
| "compile_kleene_fragment (KleeneStar r) =
    (case compile_kleene_fragment r of
       None => None
     | Some A => Some (star_ta A))"
| "compile_kleene_fragment (KleenePlus r) =
    (case compile_kleene_fragment r of
       None => None
     | Some A => Some (plus_ta A))"
| "compile_kleene_fragment (Within r I) =
    (case compile_kleene_fragment r of
       None => None
     | Some A => Some (time_restrict_ta A I))"
| "compile_kleene_fragment (Intersection r s) = None"

lemma lang_pow_list_iff:
  "w \<in> lang_pow L n \<longleftrightarrow>
    (\<exists>ws. length ws = n \<and> set ws \<subseteq> L \<and> w = concat ws)"
proof (induction n arbitrary: w)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  show ?case
  proof
    assume "w \<in> lang_pow L (Suc n)"
    then obtain u v ws where
      u_in: "u \<in> L" and
      v_pow: "v \<in> lang_pow L n" and
      w_def: "w = u @ v" and
      len: "length ws = n" and
      set_ws: "set ws \<subseteq> L" and
      v_def: "v = concat ws"
      using Suc.IH by auto
    then have "length (u # ws) = Suc n \<and>
      set (u # ws) \<subseteq> L \<and> w = concat (u # ws)"
      by simp
    then show "\<exists>ws. length ws = Suc n \<and> set ws \<subseteq> L \<and>
      w = concat ws"
      by blast
  next
    assume "\<exists>ws. length ws = Suc n \<and> set ws \<subseteq> L \<and>
      w = concat ws"
    then obtain zs where
      len_zs: "length zs = Suc n" and
      set_zs: "set zs \<subseteq> L" and
      w_zs: "w = concat zs"
      by auto
    then obtain u ws where zs_def: "zs = u # ws"
      by (cases zs) auto
    have len: "length ws = n"
      using len_zs zs_def by simp
    have u_in: "u \<in> L"
      using set_zs zs_def by auto
    have set_ws: "set ws \<subseteq> L"
      using set_zs zs_def by auto
    have w_def: "w = u @ concat ws"
      using w_zs zs_def by simp
    have "concat ws \<in> lang_pow L n"
      using Suc.IH len set_ws by auto
    then show "w \<in> lang_pow L (Suc n)"
      using u_in w_def by auto
  qed
qed

lemma lang_plus_iff [simp]:
  "w \<in> lang_plus L \<longleftrightarrow>
    (\<exists>ws. w = concat ws \<and> ws \<noteq> [] \<and> set ws \<subseteq> L)"
proof
  assume "w \<in> lang_plus L"
  then obtain n where "w \<in> lang_pow L (Suc n)"
    by (auto simp: lang_plus_def)
  then obtain ws where
    "length ws = Suc n" and "set ws \<subseteq> L" and "w = concat ws"
    using lang_pow_list_iff by blast
  then show "\<exists>ws. w = concat ws \<and> ws \<noteq> [] \<and> set ws \<subseteq> L"
    by auto
next
  assume "\<exists>ws. w = concat ws \<and> ws \<noteq> [] \<and> set ws \<subseteq> L"
  then obtain ws where
    w_def: "w = concat ws" and
    nonempty: "ws \<noteq> []" and
    set_ws: "set ws \<subseteq> L"
    by auto
  then obtain n where len: "length ws = Suc n"
    by (cases ws) auto
  then have "w \<in> lang_pow L (Suc n)"
    using lang_pow_list_iff w_def set_ws by blast
  then show "w \<in> lang_plus L"
    by (auto simp: lang_plus_def)
qed

lemma lang_star_iff [simp]:
  "w \<in> lang_star L \<longleftrightarrow>
    (\<exists>ws. w = concat ws \<and> set ws \<subseteq> L)"
  by (auto simp: lang_star_def lang_pow_list_iff)

lemma lang_plus_eq_plus_lang:
  "lang_plus L = plus_lang L"
  by auto

lemma lang_star_eq_star_lang:
  "lang_star L = star_lang L"
  by auto

lemma lang_star_empty_union_plus:
  "lang_star L = {[]} \<union> lang_plus L"
proof
  show "lang_star L \<subseteq> {[]} \<union> lang_plus L"
  proof
    fix w
    assume "w \<in> lang_star L"
    then obtain ws where w_def: "w = concat ws" and set_ws: "set ws \<subseteq> L"
      by auto
    show "w \<in> {[]} \<union> lang_plus L"
    proof (cases ws)
      case Nil
      then show ?thesis
        using w_def by simp
    next
      case (Cons x xs)
      then have "w \<in> lang_plus L"
        using w_def set_ws
        by (intro iffD2[OF lang_plus_iff] exI[of _ "x # xs"]) auto
      then show ?thesis by simp
    qed
  qed
next
  show "{[]} \<union> lang_plus L \<subseteq> lang_star L"
  proof
    fix w
    assume "w \<in> {[]} \<union> lang_plus L"
    then show "w \<in> lang_star L"
    proof
      assume "w \<in> {[]}"
      then have w_def: "w = []"
        by simp
      have "w \<in> lang_pow L 0"
        using w_def by simp
      then show ?thesis
        unfolding lang_star_def by blast
    next
      assume "w \<in> lang_plus L"
      then show ?thesis
        by auto
    qed
  qed
qed

lemma lang_subset_plus:
  "L \<subseteq> lang_plus L"
proof
  fix w
  assume "w \<in> L"
  then have "w \<in> lang_pow L (Suc 0)"
    by (auto simp: concat_lang_def)
  then show "w \<in> lang_plus L"
    unfolding lang_plus_def by blast
qed

lemma lang_plus_subset_star:
  "lang_plus L \<subseteq> lang_star L"
  by auto

lemma plus_ta_simps [simp]:
  "ta_locations (plus_ta A) = ta_locations A"
  "ta_initial (plus_ta A) = ta_initial A"
  "ta_accepting (plus_ta A) = ta_accepting A"
  "ta_clocks (plus_ta A) = ta_clocks A"
  by (simp_all add: plus_ta_def)

lemma plus_ta_transitions:
  "ta_transitions (plus_ta A) =
    ta_transitions A \<union> concat_switches A A"
  by (simp add: plus_ta_def)

lemma original_transition_in_plus_ta:
  assumes "t \<in> ta_transitions A"
  shows "t \<in> ta_transitions (plus_ta A)"
  using assms by (auto simp: plus_ta_transitions)

lemma loop_transition_in_plus_ta:
  assumes "t \<in> ta_transitions A"
  assumes "trans_target t \<in> ta_accepting A"
  assumes "q \<in> ta_initial A"
  shows "concat_transition A t q \<in> ta_transitions (plus_ta A)"
  using assms by (auto simp: plus_ta_transitions concat_switches_def)

lemma plus_switchesE:
  assumes "u \<in> concat_switches A A"
  obtains t q where
    "t \<in> ta_transitions A"
    "trans_target t \<in> ta_accepting A"
    "q \<in> ta_initial A"
    "u = concat_transition A t q"
  using assms by (auto elim: concat_switchesE)

lemma run_from_plus_oldI:
  assumes "run_from A q v w qf vf"
  shows "run_from (plus_ta A) q v w qf vf"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by (rule run_from.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  have t_in: "t \<in> ta_transitions (plus_ta A)"
    using original_transition_in_plus_ta[OF Run_Cons.hyps(1)] .
  then show ?case
    using Run_Cons
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma accepts_plus_oldI:
  assumes "w \<in> ta_lang A"
  shows "w \<in> ta_lang (plus_ta A)"
proof -
  obtain q0 qf vf where
    q0: "q0 \<in> ta_initial A" and
    qf: "qf \<in> ta_accepting A" and
    run: "run_from A q0 zero_val w qf vf"
    using assms by (auto simp: ta_lang_def accepts_def)
  have "run_from (plus_ta A) q0 zero_val w qf vf"
    using run_from_plus_oldI[OF run] .
  then show ?thesis
    using q0 qf by (auto simp: ta_lang_def accepts_def)
qed

lemma automaton_wf_plus_ta:
  assumes wf: "automaton_wf A"
  shows "automaton_wf (plus_ta A)"
proof -
  have transition_endpoints:
    "trans_source t \<in> ta_locations A \<and> trans_target t \<in> ta_locations A"
    if t_in: "t \<in> ta_transitions (plus_ta A)"
    for t
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using wf by (auto simp: automaton_wf_def)
  next
    case False
    then have "t \<in> concat_switches A A"
      using t_in by (auto simp: plus_ta_transitions)
    then obtain t0 q where
      t0_in: "t0 \<in> ta_transitions A" and
      q_init: "q \<in> ta_initial A" and
      t_def: "t = concat_transition A t0 q"
      by (auto elim: plus_switchesE)
    have "trans_source t0 \<in> ta_locations A"
      using wf t0_in by (auto simp: automaton_wf_def)
    moreover have "q \<in> ta_locations A"
      using wf q_init by (auto simp: automaton_wf_def)
    ultimately show ?thesis
      using t_def by simp
  qed
  show ?thesis
    using wf transition_endpoints by (auto simp: automaton_wf_def)
qed

lemma clock_wf_plus_ta:
  assumes cwf: "clock_wf A"
  shows "clock_wf (plus_ta A)"
proof -
  have transition_clocks:
    "trans_resets t \<subseteq> ta_clocks A \<and>
     guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
    if t_in: "t \<in> ta_transitions (plus_ta A)"
    for t
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using cwf by (auto simp: clock_wf_def)
  next
    case False
    then have "t \<in> concat_switches A A"
      using t_in by (auto simp: plus_ta_transitions)
    then obtain t0 q where
      t0_in: "t0 \<in> ta_transitions A" and
      t_def: "t = concat_transition A t0 q"
      by (auto elim: plus_switchesE)
    have "trans_resets t0 \<subseteq> ta_clocks A"
      "guards_clocks (trans_guards t0) \<subseteq> ta_clocks A"
      using cwf t0_in by (auto simp: clock_wf_def)
    then show ?thesis
      using t_def by auto
  qed
  show ?thesis
    using cwf transition_clocks by (auto simp: clock_wf_def)
qed

lemma run_from_plus_decompose_aux:
  assumes cwf: "clock_wf A"
  assumes pref_run: "run_from A p0 zero_val pref q v"
  assumes p0_init: "p0 \<in> ta_initial A"
  assumes run: "run_from (plus_ta A) q v w qf vf"
  assumes qf_acc: "qf \<in> ta_accepting A"
  shows "\<exists>ws. ws \<noteq> [] \<and> set ws \<subseteq> ta_lang A \<and>
    pref @ w = concat ws"
  using run pref_run p0_init
proof (induction w arbitrary: pref p0 q v vf)
  case Nil
  then have q_eq: "qf = q"
    by (cases rule: run_from.cases) auto
  have v_eq: "vf = v"
    using Nil.prems(1) by (cases rule: run_from.cases) auto
  have run_acc: "run_from A p0 zero_val pref qf v"
    using Nil.prems(2) q_eq by (simp add: zero_val_def)
  have "accepts A pref"
    unfolding accepts_def
    apply (rule exI[where x=p0])
    apply (rule exI[where x=qf])
    apply (rule exI[where x=v])
    apply (rule conjI)
     apply (fact Nil.prems(3))
    apply (rule conjI)
     apply (fact qf_acc)
    apply (fact run_acc)
    done
  then have pref_in: "pref \<in> ta_lang A"
    by (simp add: ta_lang_def)
  show ?case
  proof (rule exI[of _ "[pref]"], intro conjI)
    show "[pref] \<noteq> []" by simp
  next
    show "set [pref] \<subseteq> ta_lang A"
      using pref_in by simp
  next
    show "pref @ [] = concat [pref]"
      by simp
  qed
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t where
    t_plus: "t \<in> ta_transitions (plus_ta A)" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from (plus_ta A)
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf"
    using Cons.prems(1) x_def by (auto elim: run_from_ConsE)
  show ?case
  proof (cases "t \<in> ta_transitions A")
    case True
    have step:
      "run_from A q v [(d, a)] (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))"
      using True source label nonneg guards
      by (auto intro!: run_from.Run_Cons[of t] run_from.Run_Nil
          simp: reset_val_def)
    have pref_run':
      "run_from A p0 zero_val (pref @ [(d, a)]) (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))"
      using run_from_appendI[OF Cons.prems(2) step]
      by (simp add: zero_val_def)
    obtain ws where
      ws_nonempty: "ws \<noteq> []" and
      ws_set: "set ws \<subseteq> ta_lang A" and
      word: "(pref @ [(d, a)]) @ xs = concat ws"
      using Cons.IH[OF tail_run pref_run' Cons.prems(3)] by auto
    have "pref @ (x # xs) = concat ws"
      using x_def word by simp
    then show ?thesis
      using ws_nonempty ws_set by blast
  next
    case not_old: False
    then have "t \<in> concat_switches A A"
      using t_plus by (auto simp: plus_ta_transitions)
    then obtain t0 q0 where
      t0_in: "t0 \<in> ta_transitions A" and
      t0_acc: "trans_target t0 \<in> ta_accepting A" and
      q0_init: "q0 \<in> ta_initial A" and
      t_def: "t = concat_transition A t0 q0"
      by (auto elim: plus_switchesE)
    have step:
      "run_from A q v [(d, a)] (trans_target t0)
        (reset_val (trans_resets t0) (delay_val d v))"
      using t0_in source label nonneg guards t_def
      by (auto intro!: run_from.Run_Cons[of t0] run_from.Run_Nil
          simp: reset_val_def)
    have first_run:
      "run_from A p0 zero_val (pref @ [(d, a)]) (trans_target t0)
        (reset_val (trans_resets t0) (delay_val d v))"
      using run_from_appendI[OF Cons.prems(2) step]
      by (simp add: zero_val_def)
    have first_in: "pref @ [(d, a)] \<in> ta_lang A"
      using Cons.prems(3) t0_acc first_run
      by (auto simp: ta_lang_def accepts_def)
    have start_agree:
      "agree_on (ta_clocks (plus_ta A))
        (reset_val (trans_resets t) (delay_val d v))
        zero_val"
      using t_def by (auto simp: agree_on_def)
    have plus_cwf: "clock_wf (plus_ta A)"
      using clock_wf_plus_ta[OF cwf] .
    obtain vf' where tail_zero_raw:
      "run_from (plus_ta A) (trans_target t) zero_val xs qf vf'"
      using run_from_agree_on[OF plus_cwf tail_run start_agree]
      by auto
    have tail_zero:
      "run_from (plus_ta A) q0 zero_val xs qf vf'"
      using tail_zero_raw t_def by simp
    have empty_pref: "run_from A q0 zero_val [] q0 zero_val"
      by (rule run_from.Run_Nil)
    obtain ws where
      ws_nonempty: "ws \<noteq> []" and
      ws_set: "set ws \<subseteq> ta_lang A" and
      xs_def: "xs = concat ws"
      using Cons.IH[OF tail_zero empty_pref q0_init] by auto
    have "pref @ (x # xs) = concat ((pref @ [(d, a)]) # ws)"
      using x_def xs_def by simp
    moreover have "set ((pref @ [(d, a)]) # ws) \<subseteq> ta_lang A"
      using first_in ws_set by auto
    show ?thesis
    proof (rule exI[of _ "(pref @ [(d, a)]) # ws"], intro conjI)
      show "(pref @ [(d, a)]) # ws \<noteq> []"
        by simp
    next
      show "set ((pref @ [(d, a)]) # ws) \<subseteq> ta_lang A"
        using first_in ws_set by auto
    next
      show "pref @ (x # xs) = concat ((pref @ [(d, a)]) # ws)"
        using x_def xs_def by simp
    qed
  qed
qed

lemma plus_ta_sound:
  assumes cwf: "clock_wf A"
  assumes "w \<in> ta_lang (plus_ta A)"
  shows "w \<in> lang_plus (ta_lang A)"
proof -
  obtain q0 qf vf where
    q0_init: "q0 \<in> ta_initial A" and
    qf_acc: "qf \<in> ta_accepting A" and
    run: "run_from (plus_ta A) q0 zero_val w qf vf"
    using assms(2) by (auto simp: ta_lang_def accepts_def)
  have empty_pref: "run_from A q0 zero_val [] q0 zero_val"
    by (rule run_from.Run_Nil)
  obtain ws where
    "ws \<noteq> []" and "set ws \<subseteq> ta_lang A" and "w = concat ws"
    using run_from_plus_decompose_aux[
        OF cwf empty_pref q0_init run qf_acc]
    by auto
  then show ?thesis
    by auto
qed

lemma run_from_snoc_decomp:
  assumes run: "run_from A q v w qf vf"
  assumes nonempty: "w \<noteq> []"
  shows "\<exists>u d a t vu.
    w = u @ [(d, a)] \<and>
    run_from A q v u (trans_source t) vu \<and>
    t \<in> ta_transitions A \<and>
    trans_label t = a \<and>
    0 <= d \<and>
    guards_sat (delay_val d vu) (trans_guards t) \<and>
    trans_target t = qf \<and>
    vf = reset_val (trans_resets t) (delay_val d vu)"
  using run nonempty
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t where
    t_in: "t \<in> ta_transitions A" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf"
    using Cons.prems(1) x_def by (auto elim: run_from_ConsE)
  show ?case
  proof (cases "xs = []")
    case True
    have qf_def: "qf = trans_target t"
      using tail_run True by (cases rule: run_from.cases) auto
    have vf_def: "vf = reset_val (trans_resets t) (delay_val d v)"
      using tail_run True by (cases rule: run_from.cases) auto
    have prefix: "run_from A q v [] (trans_source t) v"
      using source by (simp add: run_from.Run_Nil)
    show ?thesis
      using x_def True prefix t_in label nonneg guards qf_def vf_def
      by (intro exI[of _ "[]"] exI[of _ d] exI[of _ a] exI[of _ t]
          exI[of _ v]) (simp add: delay_val_def reset_val_def)
  next
    case False
    obtain u d2 a2 t2 vu where
      xs_def: "xs = u @ [(d2, a2)]" and
      prefix_tail: "run_from A
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        u (trans_source t2) vu" and
      t2_in: "t2 \<in> ta_transitions A" and
      label2: "trans_label t2 = a2" and
      nonneg2: "0 <= d2" and
      guards2: "guards_sat (delay_val d2 vu) (trans_guards t2)" and
      target2: "trans_target t2 = qf" and
      vf_def: "vf = reset_val (trans_resets t2) (delay_val d2 vu)"
      using Cons.IH[OF tail_run False]
      by (auto simp: delay_val_def reset_val_def)
    have first_step:
      "run_from A q v [(d, a)] (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))"
      using t_in source label nonneg guards
      by (auto intro!: run_from.Run_Cons[of t] run_from.Run_Nil
          simp: reset_val_def)
    have prefix:
      "run_from A q v ((d, a) # u) (trans_source t2) vu"
      using run_from_appendI[OF first_step prefix_tail] by simp
    show ?thesis
      using x_def xs_def prefix t2_in label2 nonneg2 guards2 target2 vf_def
      by (intro exI[of _ "((d, a) # u)"] exI[of _ d2]
          exI[of _ a2] exI[of _ t2] exI[of _ vu])
         (simp add: delay_val_def reset_val_def)
  qed
qed

lemma plus_ta_appendI:
  assumes cwf: "clock_wf A"
  assumes w1_in: "w1 \<in> ta_lang A"
  assumes nonempty: "w1 \<noteq> []"
  assumes w2_in: "w2 \<in> ta_lang (plus_ta A)"
  shows "w1 @ w2 \<in> ta_lang (plus_ta A)"
proof -
  obtain q10 q1f v1f where
    q10_init: "q10 \<in> ta_initial A" and
    q1f_acc: "q1f \<in> ta_accepting A" and
    run1: "run_from A q10 zero_val w1 q1f v1f"
    using w1_in by (auto simp: ta_lang_def accepts_def)
  obtain q20 q2f v2f where
    q20_init: "q20 \<in> ta_initial A" and
    q2f_acc: "q2f \<in> ta_accepting A" and
    run2: "run_from (plus_ta A) q20 zero_val w2 q2f v2f"
    using w2_in by (auto simp: ta_lang_def accepts_def)
  have plus_cwf: "clock_wf (plus_ta A)"
    using clock_wf_plus_ta[OF cwf] .
  obtain u d a t vu where
    w1_def: "w1 = u @ [(d, a)]" and
    prefix_run: "run_from A q10 zero_val u (trans_source t) vu" and
    t_in: "t \<in> ta_transitions A" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d vu) (trans_guards t)" and
    target: "trans_target t = q1f"
    using run_from_snoc_decomp[OF run1 nonempty] by auto
  have target_acc: "trans_target t \<in> ta_accepting A"
    using q1f_acc target by simp
  have loop_in: "concat_transition A t q20 \<in> ta_transitions (plus_ta A)"
  proof -
    have "concat_transition A t q20 \<in> ta_transitions (concat_ta_raw A A)"
      by (rule concat_switchI) (use t_in target_acc q20_init in simp_all)
    then show ?thesis
      by (auto simp: concat_ta_raw_transitions plus_ta_transitions)
  qed
  have start_agree:
    "agree_on (ta_clocks (plus_ta A))
      (reset_val (trans_resets t \<union> ta_clocks A) (delay_val d vu))
      zero_val"
    by (auto simp: agree_on_def)
  obtain vf_tail where tail:
    "run_from (plus_ta A) q20
      (reset_val (trans_resets t \<union> ta_clocks A) (delay_val d vu))
      w2 q2f vf_tail"
    using run_from_agree_on[OF plus_cwf run2 agree_on_sym[OF start_agree]]
    by auto
  have prefix_plus:
    "run_from (plus_ta A) q10 zero_val u (trans_source t) vu"
    using run_from_plus_oldI[OF prefix_run] .
  have loop_tail:
    "run_from (plus_ta A) (trans_source t) vu ((d, a) # w2) q2f vf_tail"
    using loop_in label nonneg guards tail
    by (auto intro!: run_from.Run_Cons[of "concat_transition A t q20"]
        simp: reset_val_def)
  have run: "run_from (plus_ta A) q10 zero_val (w1 @ w2) q2f vf_tail"
    using run_from_appendI[OF prefix_plus loop_tail] w1_def by simp
  then show ?thesis
    using q10_init q2f_acc by (auto simp: ta_lang_def accepts_def)
qed

lemma plus_ta_complete_list:
  assumes cwf: "clock_wf A"
  assumes "ws \<noteq> []"
  assumes "set ws \<subseteq> ta_lang A"
  shows "concat ws \<in> ta_lang (plus_ta A)"
  using assms
proof (induction ws)
  case Nil
  then show ?case by simp
next
  case (Cons w ws)
  have w_in: "w \<in> ta_lang A"
    using Cons.prems by auto
  show ?case
  proof (cases ws)
    case Nil
    then show ?thesis
      using accepts_plus_oldI[OF w_in] by simp
  next
    case Cons_tail: (Cons u us)
    have tail_nonempty: "ws \<noteq> []"
      using Cons_tail by simp
    have tail_set: "set ws \<subseteq> ta_lang A"
      using Cons.prems by auto
    have tail_in: "concat ws \<in> ta_lang (plus_ta A)"
      using Cons.IH[OF cwf tail_nonempty tail_set] .
    show ?thesis
    proof (cases "w = []")
      case True
      then show ?thesis
        using tail_in by simp
    next
      case False
      show ?thesis
        using plus_ta_appendI[OF cwf w_in False tail_in] by simp
    qed
  qed
qed

lemma plus_ta_complete:
  assumes cwf: "clock_wf A"
  assumes "w \<in> lang_plus (ta_lang A)"
  shows "w \<in> ta_lang (plus_ta A)"
  using assms plus_ta_complete_list by auto

theorem plus_ta_correct:
  assumes cwf: "clock_wf A"
  shows "ta_lang (plus_ta A) = lang_plus (ta_lang A)"
proof
  show "ta_lang (plus_ta A) \<subseteq> lang_plus (ta_lang A)"
    using plus_ta_sound[OF cwf] by blast
next
  show "lang_plus (ta_lang A) \<subseteq> ta_lang (plus_ta A)"
    using plus_ta_complete[OF cwf] by blast
qed

theorem star_ta_correct:
  assumes wf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  shows "ta_lang (star_ta A) = lang_star (ta_lang A)"
proof -
  have plus_wf: "automaton_wf (plus_ta A)"
    using automaton_wf_plus_ta[OF wf] .
  have "ta_lang (star_ta A) =
    ta_lang epsilon_ta \<union> ta_lang (plus_ta A)"
    unfolding star_ta_def
    using ta_lang_union_ta[OF automaton_wf_epsilon_ta plus_wf] .
  also have "... = {[]} \<union> lang_plus (ta_lang A)"
    using plus_ta_correct[OF cwf] by simp
  also have "... = lang_star (ta_lang A)"
    using lang_star_empty_union_plus[of "ta_lang A"] by simp
  finally show ?thesis .
qed

lemma automaton_wf_star_ta:
  assumes wf: "automaton_wf A"
  shows "automaton_wf (star_ta A)"
  unfolding star_ta_def
  using automaton_wf_union_ta[
      OF automaton_wf_epsilon_ta automaton_wf_plus_ta[OF wf]] .

lemma clock_wf_star_ta:
  assumes cwf: "clock_wf A"
  shows "clock_wf (star_ta A)"
  unfolding star_ta_def
  using clock_wf_union_ta[
      OF clock_wf_epsilon_ta clock_wf_plus_ta[OF cwf]] .

lemma compile_kleene_fragment_wf:
  assumes "compile_kleene_fragment r = Some A"
  shows "automaton_wf A \<and> clock_wf A"
  using assms
proof (induction r arbitrary: A)
  case Empty
  then show ?case by simp
next
  case Epsilon
  then show ?case by simp
next
  case (Atom x)
  then show ?case by auto
next
  case (Union r s)
  then obtain A1 A2 where
    r_def: "compile_kleene_fragment r = Some A1" and
    s_def: "compile_kleene_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1 \<and> clock_wf A1"
    using Union.IH(1)[OF r_def] .
  have wf2: "automaton_wf A2 \<and> clock_wf A2"
    using Union.IH(2)[OF s_def] .
  then show ?case
    using wf1 by (simp add: A_def automaton_wf_union_ta clock_wf_union_ta)
next
  case (Concat r s)
  then obtain A1 A2 where
    r_def: "compile_kleene_fragment r = Some A1" and
    s_def: "compile_kleene_fragment s = Some A2" and
    A_def: "A = concat_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1 \<and> clock_wf A1"
    using Concat.IH(1)[OF r_def] .
  have wf2: "automaton_wf A2 \<and> clock_wf A2"
    using Concat.IH(2)[OF s_def] .
  then show ?case
    using wf1 by (simp add: A_def automaton_wf_concat_ta clock_wf_concat_ta)
next
  case (KleeneStar r)
  then obtain A0 where
    r_def: "compile_kleene_fragment r = Some A0" and
    A_def: "A = star_ta A0"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using KleeneStar.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_star_ta clock_wf_star_ta)
next
  case (KleenePlus r)
  then obtain A0 where
    r_def: "compile_kleene_fragment r = Some A0" and
    A_def: "A = plus_ta A0"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using KleenePlus.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_plus_ta clock_wf_plus_ta)
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_kleene_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using Within.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_time_restrict_ta clock_wf_time_restrict_ta)
qed auto

theorem compile_kleene_fragment_correct:
  assumes "compile_kleene_fragment r = Some A"
  shows "ta_lang A = tre_lang r"
  using assms
proof (induction r arbitrary: A)
  case Empty
  then show ?case by simp
next
  case Epsilon
  then show ?case by simp
next
  case (Atom x)
  then show ?case by auto
next
  case (Union r s)
  then obtain A1 A2 where
    r_def: "compile_kleene_fragment r = Some A1" and
    s_def: "compile_kleene_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_kleene_fragment_wf[OF s_def] by simp
  have "ta_lang A = ta_lang A1 \<union> ta_lang A2"
    using ta_lang_union_ta[OF wf1 wf2] by (simp add: A_def)
  also have "... = tre_lang r \<union> tre_lang s"
    using Union.IH(1)[OF r_def] Union.IH(2)[OF s_def] by simp
  also have "... = tre_lang (Union r s)"
    by simp
  finally show ?case .
next
  case (Concat r s)
  then obtain A1 A2 where
    r_def: "compile_kleene_fragment r = Some A1" and
    s_def: "compile_kleene_fragment s = Some A2" and
    A_def: "A = concat_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_kleene_fragment_wf[OF s_def] by simp
  have cwf2: "clock_wf A2"
    using compile_kleene_fragment_wf[OF s_def] by simp
  have "ta_lang A = concat_lang (ta_lang A1) (ta_lang A2)"
    using concat_ta_correct[OF wf1 wf2 cwf2] by (simp add: A_def)
  also have "... = concat_lang (tre_lang r) (tre_lang s)"
    using Concat.IH(1)[OF r_def] Concat.IH(2)[OF s_def] by simp
  also have "... = tre_lang (Concat r s)"
    by simp
  finally show ?case .
next
  case (KleeneStar r)
  then obtain A0 where
    r_def: "compile_kleene_fragment r = Some A0" and
    A_def: "A = star_ta A0"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have cwf0: "clock_wf A0"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have "ta_lang A = lang_star (ta_lang A0)"
    using star_ta_correct[OF wf0 cwf0] by (simp add: A_def)
  also have "... = star_lang (ta_lang A0)"
    by (simp add: lang_star_eq_star_lang)
  also have "... = star_lang (tre_lang r)"
    using KleeneStar.IH[OF r_def] by simp
  also have "... = tre_lang (KleeneStar r)"
    by simp
  finally show ?case .
next
  case (KleenePlus r)
  then obtain A0 where
    r_def: "compile_kleene_fragment r = Some A0" and
    A_def: "A = plus_ta A0"
    by (auto split: option.splits)
  have cwf0: "clock_wf A0"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have "ta_lang A = lang_plus (ta_lang A0)"
    using plus_ta_correct[OF cwf0] by (simp add: A_def)
  also have "... = plus_lang (ta_lang A0)"
    by (simp add: lang_plus_eq_plus_lang)
  also have "... = plus_lang (tre_lang r)"
    using KleenePlus.IH[OF r_def] by simp
  also have "... = tre_lang (KleenePlus r)"
    by simp
  finally show ?case .
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_kleene_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have cwf0: "clock_wf A0"
    using compile_kleene_fragment_wf[OF r_def] by simp
  have "ta_lang A = {w \<in> ta_lang A0. interval_mem (duration w) I}"
    using time_restrict_ta_correct[OF wf0 cwf0] by (simp add: A_def)
  also have "... = {w \<in> tre_lang r. interval_mem (duration w) I}"
    using Within.IH[OF r_def] by simp
  also have "... = tre_lang (Within r I)"
    by simp
  finally show ?case .
qed auto

theorem compile_kleene_fragment_trim_correct:
  assumes "compile_kleene_fragment r = Some A"
  shows "ta_lang (trim_to_accepting A) = tre_lang r"
  using compile_kleene_fragment_correct[OF assms] ta_lang_trim_to_accepting[of A]
  by simp

end
