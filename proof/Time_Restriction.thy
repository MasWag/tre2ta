theory Time_Restriction
  imports Trim
begin

fun guard_clocks :: "guard => clock set" where
  "guard_clocks (Clock_In x I) = {x}"

definition guards_clocks :: "guard list => clock set" where
  "guards_clocks gs = \<Union>(guard_clocks ` set gs)"

definition clock_wf :: "('q, 'a) automaton => bool" where
  "clock_wf A \<longleftrightarrow>
    finite (ta_clocks A) \<and>
    (\<forall>t \<in> ta_transitions A.
      trans_resets t \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards t) \<subseteq> ta_clocks A)"

definition fresh_clock :: "clock => ('q, 'a) automaton => bool" where
  "fresh_clock x A \<longleftrightarrow> x \<notin> ta_clocks A"

definition fresh_clock_for :: "('q, 'a) automaton => clock" where
  "fresh_clock_for A = Suc (Max (ta_clocks A))"

definition add_clock :: "clock => ('q, 'a) automaton => ('q, 'a) automaton" where
  "add_clock x A = A\<lparr>ta_clocks := insert x (ta_clocks A)\<rparr>"

definition sink_location :: "(nat, 'a) automaton => nat" where
  "sink_location A = Suc (Max (ta_locations A))"

definition restrict_transition ::
  "clock => nat => interval => (nat, 'a) transition => (nat, 'a) transition"
where
  "restrict_transition x sink I t =
    t\<lparr> trans_guards := trans_guards t @ [Clock_In x I],
       trans_target := sink \<rparr>"

definition time_restrict_ta_with ::
  "clock => nat => (nat, 'a) automaton => interval => (nat, 'a) automaton"
where
  "time_restrict_ta_with x sink A I =
    \<lparr> ta_locations = insert sink (ta_locations A),
      ta_initial =
        ta_initial A \<union>
        (if accepts A [] \<and> interval_mem 0 I then {sink} else {}),
      ta_accepting = {sink},
      ta_clocks = insert x (ta_clocks A),
      ta_transitions =
        ta_transitions A \<union>
        restrict_transition x sink I `
          {t \<in> ta_transitions A. trans_target t \<in> ta_accepting A} \<rparr>"

definition time_restrict_ta ::
  "(nat, 'a) automaton => interval => (nat, 'a) automaton"
where
  "time_restrict_ta A I =
    time_restrict_ta_with (fresh_clock_for A) (sink_location A) A I"

fun compile_time_fragment :: "'a tre => (nat, 'a) automaton option" where
  "compile_time_fragment Empty = Some empty_ta"
| "compile_time_fragment Epsilon = Some epsilon_ta"
| "compile_time_fragment (Atom a) = Some (atom_ta a)"
| "compile_time_fragment (Union r s) =
    (case compile_time_fragment r of
       None => None
     | Some A =>
         (case compile_time_fragment s of
            None => None
          | Some B => Some (union_ta A B)))"
| "compile_time_fragment (Within r I) =
    (case compile_time_fragment r of
       None => None
     | Some A => Some (time_restrict_ta A I))"
| "compile_time_fragment (Intersection r s) = None"
| "compile_time_fragment (Concat r s) = None"
| "compile_time_fragment (KleeneStar r) = None"
| "compile_time_fragment (KleenePlus r) = None"

lemma guard_clocks_append [simp]:
  "guards_clocks (xs @ ys) = guards_clocks xs \<union> guards_clocks ys"
  by (auto simp: guards_clocks_def)

lemma guards_clocks_Clock_In [simp]:
  "guards_clocks [Clock_In x I] = {x}"
  by (simp add: guards_clocks_def)

lemma fresh_clock_for_fresh:
  assumes "clock_wf A"
  shows "fresh_clock (fresh_clock_for A) A"
proof -
  have finite_clocks: "finite (ta_clocks A)"
    using assms by (simp add: clock_wf_def)
  have "fresh_clock_for A \<notin> ta_clocks A"
  proof
    assume in_clocks: "fresh_clock_for A \<in> ta_clocks A"
    have "fresh_clock_for A <= Max (ta_clocks A)"
      using Max_ge[OF finite_clocks in_clocks] .
    then show False
      by (simp add: fresh_clock_for_def)
  qed
  then show ?thesis
    by (simp add: fresh_clock_def)
qed

lemma sink_location_fresh:
  assumes "automaton_wf A"
  shows "sink_location A \<notin> ta_locations A"
proof
  assume in_locs: "sink_location A \<in> ta_locations A"
  have finite_locs: "finite (ta_locations A)"
    using assms by (simp add: automaton_wf_def)
  have "sink_location A <= Max (ta_locations A)"
    using Max_ge[OF finite_locs in_locs] .
  then show False
    by (simp add: sink_location_def)
qed

lemma run_from_add_clock_iff [simp]:
  "run_from (add_clock x A) q v w qf vf \<longleftrightarrow> run_from A q v w qf vf"
proof
  assume "run_from (add_clock x A) q v w qf vf"
  then show "run_from A q v w qf vf"
    by (rule run_from_transition_subset) (simp add: add_clock_def)
next
  assume "run_from A q v w qf vf"
  then show "run_from (add_clock x A) q v w qf vf"
    by (rule run_from_transition_subset) (simp add: add_clock_def)
qed

lemma add_clock_simps [simp]:
  "ta_locations (add_clock x A) = ta_locations A"
  "ta_initial (add_clock x A) = ta_initial A"
  "ta_accepting (add_clock x A) = ta_accepting A"
  "ta_clocks (add_clock x A) = insert x (ta_clocks A)"
  "ta_transitions (add_clock x A) = ta_transitions A"
  by (simp_all add: add_clock_def)

lemma add_clock_language [simp]:
  "ta_lang (add_clock x A) = ta_lang A"
  by (auto simp: ta_lang_def accepts_def)

lemma run_from_NilD:
  assumes "run_from A p v [] q vf"
  shows "q = p \<and> vf = v"
  using assms by (cases rule: run_from.cases) auto

lemma restrict_transition_simps [simp]:
  "trans_source (restrict_transition x sink I t) = trans_source t"
  "trans_label (restrict_transition x sink I t) = trans_label t"
  "trans_guards (restrict_transition x sink I t) =
    trans_guards t @ [Clock_In x I]"
  "trans_resets (restrict_transition x sink I t) = trans_resets t"
  "trans_target (restrict_transition x sink I t) = sink"
  by (simp_all add: restrict_transition_def)

lemma time_restrict_locations [simp]:
  "ta_locations (time_restrict_ta_with x sink A I) =
    insert sink (ta_locations A)"
  by (simp add: time_restrict_ta_with_def)

lemma time_restrict_initial [simp]:
  "ta_initial (time_restrict_ta_with x sink A I) =
    ta_initial A \<union>
      (if accepts A [] \<and> interval_mem 0 I then {sink} else {})"
  by (simp add: time_restrict_ta_with_def)

lemma time_restrict_accepting [simp]:
  "ta_accepting (time_restrict_ta_with x sink A I) = {sink}"
  by (simp add: time_restrict_ta_with_def)

lemma time_restrict_clocks [simp]:
  "ta_clocks (time_restrict_ta_with x sink A I) = insert x (ta_clocks A)"
  by (simp add: time_restrict_ta_with_def)

lemma time_restrict_transitions:
  "ta_transitions (time_restrict_ta_with x sink A I) =
    ta_transitions A \<union>
    restrict_transition x sink I `
      {t \<in> ta_transitions A. trans_target t \<in> ta_accepting A}"
  by (simp add: time_restrict_ta_with_def)

lemma clock_wf_empty_ta [simp]:
  "clock_wf empty_ta"
  by (simp add: clock_wf_def)

lemma clock_wf_epsilon_ta [simp]:
  "clock_wf epsilon_ta"
  by (simp add: clock_wf_def)

lemma clock_wf_atom_ta [simp]:
  "clock_wf (atom_ta a)"
  by (simp add: clock_wf_def guards_clocks_def)

lemma clock_wf_shift_locations:
  assumes "clock_wf A"
  shows "clock_wf (shift_locations k A)"
  using assms
  by (auto simp: clock_wf_def shift_locations_def)

lemma clock_wf_union_ta_raw:
  assumes "clock_wf A"
  assumes "clock_wf B"
  shows "clock_wf (union_ta_raw A B)"
  using assms by (auto simp: clock_wf_def)

lemma clock_wf_union_ta:
  assumes "clock_wf A"
  assumes "clock_wf B"
  shows "clock_wf (union_ta A B)"
  using assms
  by (simp add: union_ta_def clock_wf_union_ta_raw clock_wf_shift_locations)

lemma run_fresh_clock_duration:
  assumes wf: "clock_wf A"
  assumes fresh: "fresh_clock x A"
  assumes run: "run_from A p v w q vf"
  shows "vf x = v x + duration w"
  using run wf fresh
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by simp
next
  case (Run_Cons t A q a d v w qf vf)
  have all_trans:
    "\<forall>t \<in> ta_transitions A.
      trans_resets t \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
    using Run_Cons.prems(1) by (simp add: clock_wf_def)
  have resets_subset: "trans_resets t \<subseteq> ta_clocks A"
    using all_trans Run_Cons.hyps(1) by blast
  have no_reset: "x \<notin> trans_resets t"
    using resets_subset Run_Cons.prems(2) by (auto simp: fresh_clock_def)
  have start_x:
    "reset_val (trans_resets t) (delay_val d v) x = v x + d"
    using no_reset by simp
  have "vf x =
    reset_val (trans_resets t) (delay_val d v) x + duration w"
    using Run_Cons.IH[OF Run_Cons.prems] .
  then show ?case
    using start_x by (simp add: algebra_simps)
qed

lemma original_transition_in_time_restrict:
  assumes "t \<in> ta_transitions A"
  shows "t \<in> ta_transitions (time_restrict_ta_with x sink A I)"
  using assms by (auto simp: time_restrict_transitions)

lemma restricted_transition_in_time_restrict:
  assumes "t \<in> ta_transitions A"
  assumes "trans_target t \<in> ta_accepting A"
  shows "restrict_transition x sink I t
    \<in> ta_transitions (time_restrict_ta_with x sink A I)"
  using assms by (auto simp: time_restrict_transitions)

lemma no_transition_from_fresh_sink:
  assumes wf: "automaton_wf A"
  assumes sink_fresh: "sink \<notin> ta_locations A"
  assumes t_in: "t \<in> ta_transitions (time_restrict_ta_with x sink A I)"
  shows "trans_source t \<noteq> sink"
proof -
  have source_in: "trans_source t \<in> ta_locations A"
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using wf by (auto simp: automaton_wf_def)
  next
    case False
    then obtain t0 where
      "t0 \<in> ta_transitions A" and
      "t = restrict_transition x sink I t0"
      using t_in by (auto simp: time_restrict_transitions)
    then show ?thesis
      using wf by (auto simp: automaton_wf_def)
  qed
  then show ?thesis
    using sink_fresh by auto
qed

lemma run_from_fresh_sink_iff:
  assumes wf: "automaton_wf A"
  assumes sink_fresh: "sink \<notin> ta_locations A"
  shows "run_from (time_restrict_ta_with x sink A I) sink v w q vf \<longleftrightarrow>
    w = [] \<and> q = sink \<and> vf = v"
  by (rule run_from_no_transition_from_source_iff)
     (use no_transition_from_fresh_sink[OF wf sink_fresh] in auto)

lemma run_original_lift_to_time_restrict:
  assumes awf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  assumes fresh: "fresh_clock x A"
  assumes run: "run_from A q v w qf vf"
  assumes acc: "qf \<in> ta_accepting A"
  assumes in_interval: "interval_mem (v x + duration w) I"
  assumes nonempty: "w \<noteq> []"
  shows "\<exists>vf'. run_from (time_restrict_ta_with x sink A I) q v w sink vf'"
  using run acc in_interval nonempty
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case by simp
next
  case (Cons e w)
  obtain d a where e_def: "e = (d, a)"
    by (cases e)
  obtain t where
    t_in: "t \<in> ta_transitions A" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      w qf vf"
    using Cons.prems(1) e_def by (auto elim: run_from_ConsE)
  have no_reset: "x \<notin> trans_resets t"
    using cwf fresh t_in by (auto simp: clock_wf_def fresh_clock_def)
  have reset_x:
    "reset_val (trans_resets t) (delay_val d v) x = v x + d"
    using no_reset by simp
  show ?case
  proof (cases w)
    case Nil
    then have target_acc: "trans_target t \<in> ta_accepting A"
      using run_from_NilD[OF tail_run[unfolded Nil]] Cons.prems(2) by simp
    have x_guard:
      "guard_sat (delay_val d v) (Clock_In x I)"
      using Cons.prems(3) Nil e_def by simp
    have rt_in:
      "restrict_transition x sink I t
        \<in> ta_transitions (time_restrict_ta_with x sink A I)"
      using restricted_transition_in_time_restrict[OF t_in target_acc] .
    have rt_guards:
      "guards_sat (delay_val d v)
        (trans_guards (restrict_transition x sink I t))"
      using guards x_guard
      by (simp add: guards_sat_def)
    have step:
      "run_from (time_restrict_ta_with x sink A I) q v [(d, a)] sink
        (reset_val (trans_resets t) (delay_val d v))"
      by (rule run_from.Run_Cons[of "restrict_transition x sink I t"])
         (use rt_in source label nonneg rt_guards in
          \<open>simp_all add: run_from.Run_Nil reset_val_def\<close>)
    then show ?thesis
      using Nil e_def by auto
  next
    case (Cons w_head w_tail)
    have interval_tail:
      "interval_mem
        (reset_val (trans_resets t) (delay_val d v) x + duration w) I"
      using Cons.prems(3) reset_x e_def
      by (simp add: algebra_simps)
    have ex_tail:
      "\<exists>vf'. run_from (time_restrict_ta_with x sink A I)
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        w sink vf'"
      using Cons.IH[OF tail_run Cons.prems(2) interval_tail]
      by (simp add: Cons reset_val_def delay_val_def)
    then obtain vf' where tail_lift:
      "run_from (time_restrict_ta_with x sink A I)
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        w sink vf'"
      by blast
    have step:
      "run_from (time_restrict_ta_with x sink A I) q v ((d, a) # w) sink vf'"
      by (rule run_from.Run_Cons[of t])
         (use original_transition_in_time_restrict[OF t_in]
            source label nonneg guards tail_lift in
          \<open>auto simp: reset_val_def\<close>)
    then show ?thesis
      using e_def by auto
  qed
qed

lemma time_restrict_complete_with:
  assumes awf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  assumes fresh: "fresh_clock x A"
  assumes "w \<in> ta_lang A"
  assumes "interval_mem (duration w) I"
  shows "w \<in> ta_lang (time_restrict_ta_with x sink A I)"
proof -
  obtain q0 qf vf where
    q0_in: "q0 \<in> ta_initial A" and
    qf_in: "qf \<in> ta_accepting A" and
    run: "run_from A q0 zero_val w qf vf"
    using assms(4) by (auto simp: ta_lang_def accepts_def)
  show ?thesis
  proof (cases w)
    case Nil
    then have "accepts A []"
      using q0_in qf_in run by (auto simp: accepts_def)
    then have "sink \<in> ta_initial (time_restrict_ta_with x sink A I)"
      using assms(5) Nil by auto
    moreover have "run_from (time_restrict_ta_with x sink A I)
      sink zero_val [] sink zero_val"
      by (rule run_from.Run_Nil)
    moreover have "sink \<in> ta_accepting (time_restrict_ta_with x sink A I)"
      by simp
    ultimately have "accepts (time_restrict_ta_with x sink A I) []"
      unfolding accepts_def by blast
    then show ?thesis
      by (simp add: ta_lang_def Nil)
  next
    case (Cons e es)
    have interval_start: "interval_mem (zero_val x + duration w) I"
      using assms(5) by simp
    have ex_lift:
      "\<exists>vf'. run_from (time_restrict_ta_with x sink A I) q0 zero_val w sink vf'"
      using run_original_lift_to_time_restrict[
          where sink=sink, OF awf cwf fresh run qf_in interval_start]
        Cons by (auto simp: zero_val_def)
    then obtain vf' where
      run_lift: "run_from (time_restrict_ta_with x sink A I) q0 zero_val w sink vf'"
      by blast
    then show ?thesis
      using q0_in run_lift by (auto simp: ta_lang_def accepts_def)
  qed
qed

lemma time_restrict_project_run:
  assumes awf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  assumes fresh: "fresh_clock x A"
  assumes sink_fresh: "sink \<notin> ta_locations A"
  assumes run: "run_from (time_restrict_ta_with x sink A I) q v w sink vf"
  assumes q_in: "q \<in> ta_locations A"
  shows "\<exists>qf vf0.
    qf \<in> ta_accepting A \<and>
    run_from A q v w qf vf0 \<and>
    interval_mem (v x + duration w) I"
  using run q_in
proof (induction w arbitrary: q v vf)
  case Nil
  then show ?case
    using run_from_NilD[OF Nil.prems(1)] Nil.prems(2) sink_fresh by auto
next
  case (Cons e w)
  obtain d a where e_def: "e = (d, a)"
    by (cases e)
  obtain tr where
    tr_in: "tr \<in> ta_transitions (time_restrict_ta_with x sink A I)" and
    source: "trans_source tr = q" and
    label: "trans_label tr = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards tr)" and
    tail_run: "run_from (time_restrict_ta_with x sink A I)
      (trans_target tr)
      (reset_val (trans_resets tr) (delay_val d v))
      w sink vf"
    using Cons.prems(1) e_def by (auto elim: run_from_ConsE)
  show ?case
  proof (cases "tr \<in> ta_transitions A")
    case True
    have target_in: "trans_target tr \<in> ta_locations A"
      using awf True by (auto simp: automaton_wf_def)
    have tail_project:
      "\<exists>qf vf0.
        qf \<in> ta_accepting A \<and>
        run_from A
          (trans_target tr)
          (reset_val (trans_resets tr) (delay_val d v))
          w qf vf0 \<and>
        interval_mem
          (reset_val (trans_resets tr) (delay_val d v) x + duration w) I"
      using Cons.IH[OF tail_run target_in] by blast
    then obtain qf vf0 where
      qf_acc: "qf \<in> ta_accepting A" and
      tail_old: "run_from A
        (trans_target tr)
        (reset_val (trans_resets tr) (delay_val d v))
        w qf vf0" and
      tail_interval:
        "interval_mem
          (reset_val (trans_resets tr) (delay_val d v) x + duration w) I"
      by blast
    have no_reset: "x \<notin> trans_resets tr"
      using cwf fresh True by (auto simp: clock_wf_def fresh_clock_def)
    have reset_x:
      "reset_val (trans_resets tr) (delay_val d v) x = v x + d"
      using no_reset by simp
    have old_run:
      "run_from A q v ((d, a) # w) qf vf0"
      by (rule run_from.Run_Cons[of tr])
         (use True source label nonneg guards tail_old in
          \<open>auto simp: reset_val_def\<close>)
    have interval_full:
      "interval_mem (v x + duration (e # w)) I"
    proof -
      have "v x + duration (e # w) =
        reset_val (trans_resets tr) (delay_val d v) x + duration w"
        using reset_x e_def by (simp add: algebra_simps)
      then show ?thesis
        using tail_interval by simp
    qed
    show ?thesis
      using qf_acc old_run interval_full e_def by blast
  next
    case False
    then obtain t where
      t_in: "t \<in> ta_transitions A" and
      target_acc: "trans_target t \<in> ta_accepting A" and
      tr_def: "tr = restrict_transition x sink I t"
      using tr_in by (auto simp: time_restrict_transitions)
    have tail_empty: "w = []"
      using tail_run run_from_fresh_sink_iff[OF awf sink_fresh,
          of x I "reset_val (trans_resets tr) (delay_val d v)" w sink vf]
      by (simp add: tr_def)
    have x_guard: "interval_mem (delay_val d v x) I"
      using guards tr_def by (simp add: guards_sat_def)
    have old_run:
      "run_from A q v [(d, a)] (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))"
      by (rule run_from.Run_Cons[of t])
         (use t_in source label nonneg guards tr_def in
          \<open>auto intro: run_from.Run_Nil simp: guards_sat_def reset_val_def\<close>)
    show ?thesis
      using target_acc old_run x_guard tail_empty e_def
      by auto
  qed
qed

lemma time_restrict_sound_with:
  assumes awf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  assumes fresh: "fresh_clock x A"
  assumes sink_fresh: "sink \<notin> ta_locations A"
  assumes "w \<in> ta_lang (time_restrict_ta_with x sink A I)"
  shows "w \<in> ta_lang A \<and> interval_mem (duration w) I"
proof -
  obtain q0 qf vf where
    q0_in: "q0 \<in> ta_initial (time_restrict_ta_with x sink A I)" and
    qf_in: "qf \<in> ta_accepting (time_restrict_ta_with x sink A I)" and
    run: "run_from (time_restrict_ta_with x sink A I) q0 zero_val w qf vf"
    using assms(5) by (auto simp: ta_lang_def accepts_def)
  have qf_sink: "qf = sink"
    using qf_in by simp
  show ?thesis
  proof (cases "q0 = sink")
    case True
    then have "w = []"
      using run qf_sink run_from_fresh_sink_iff[OF awf sink_fresh, of x I zero_val w qf vf]
      by simp
    moreover have sink_not_initial: "sink \<notin> ta_initial A"
      using awf sink_fresh by (auto simp: automaton_wf_def)
    moreover have empty_ok: "accepts A [] \<and> interval_mem 0 I"
    proof -
      have "sink \<in>
        ta_initial A \<union>
          (if accepts A [] \<and> interval_mem 0 I then {sink} else {})"
        using q0_in True by (simp only: time_restrict_initial)
      then have "sink \<in>
          (if accepts A [] \<and> interval_mem 0 I then {sink} else {})"
        using sink_not_initial by blast
      then show ?thesis
        by (cases "accepts A [] \<and> interval_mem 0 I") auto
    qed
    ultimately show ?thesis
      by (auto simp: ta_lang_def)
  next
    case False
    then have q0_old: "q0 \<in> ta_initial A"
    proof -
      have "q0 \<in> ta_initial A \<union>
        (if accepts A [] \<and> interval_mem 0 I then {sink} else {})"
        using q0_in by (simp only: time_restrict_initial)
      then show ?thesis
      proof
        assume "q0 \<in> ta_initial A"
        then show ?thesis .
      next
        assume "q0 \<in> (if accepts A [] \<and> interval_mem 0 I then {sink} else {})"
        then have "q0 = sink"
          by (simp split: if_splits)
        then show ?thesis
          using False by simp
      qed
    qed
    have q0_loc: "q0 \<in> ta_locations A"
      using awf q0_old by (auto simp: automaton_wf_def)
    have run_sink: "run_from (time_restrict_ta_with x sink A I) q0 zero_val w sink vf"
      using run qf_sink by simp
    have projected:
      "\<exists>q_old vf_old.
        q_old \<in> ta_accepting A \<and>
        run_from A q0 zero_val w q_old vf_old \<and>
        interval_mem (zero_val x + duration w) I"
      using time_restrict_project_run[
          OF awf cwf fresh sink_fresh run_sink q0_loc]
      by blast
    obtain q_old vf_old where
      q_acc: "q_old \<in> ta_accepting A" and
      old_run: "run_from A q0 zero_val w q_old vf_old" and
      interval: "interval_mem (zero_val x + duration w) I"
      using projected by blast
    then have "w \<in> ta_lang A"
      using q0_old by (auto simp: ta_lang_def accepts_def)
    then show ?thesis
      using interval by simp
  qed
qed

theorem time_restrict_ta_with_correct:
  assumes awf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  assumes fresh: "fresh_clock x A"
  assumes sink_fresh: "sink \<notin> ta_locations A"
  shows "ta_lang (time_restrict_ta_with x sink A I) =
    {w \<in> ta_lang A. interval_mem (duration w) I}"
proof
  show "ta_lang (time_restrict_ta_with x sink A I)
    \<subseteq> {w \<in> ta_lang A. interval_mem (duration w) I}"
  proof
    fix w
    assume w_in: "w \<in> ta_lang (time_restrict_ta_with x sink A I)"
    have "w \<in> ta_lang A \<and> interval_mem (duration w) I"
      using time_restrict_sound_with[OF awf cwf fresh sink_fresh w_in] .
    then show "w \<in> {w \<in> ta_lang A. interval_mem (duration w) I}"
      by simp
  qed
next
  show "{w \<in> ta_lang A. interval_mem (duration w) I}
    \<subseteq> ta_lang (time_restrict_ta_with x sink A I)"
  proof
    fix w
    assume "w \<in> {w \<in> ta_lang A. interval_mem (duration w) I}"
    then have w_A: "w \<in> ta_lang A" and interval: "interval_mem (duration w) I"
      by simp_all
    show "w \<in> ta_lang (time_restrict_ta_with x sink A I)"
      using time_restrict_complete_with[OF awf cwf fresh w_A interval] .
  qed
qed

lemma automaton_wf_time_restrict_ta_with:
  assumes awf: "automaton_wf A"
  assumes sink_fresh: "sink \<notin> ta_locations A"
  shows "automaton_wf (time_restrict_ta_with x sink A I)"
proof -
  have finite_locations: "finite (ta_locations A)"
    using awf by (simp add: automaton_wf_def)
  have initial_subset: "ta_initial A \<subseteq> ta_locations A"
    using awf by (simp add: automaton_wf_def)
  have transition_endpoints:
    "trans_source t \<in> insert sink (ta_locations A) \<and>
     trans_target t \<in> insert sink (ta_locations A)"
    if t_in: "t \<in> ta_transitions (time_restrict_ta_with x sink A I)"
    for t
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using awf by (auto simp: automaton_wf_def)
  next
    case False
    then obtain t0 where
      t0_in: "t0 \<in> ta_transitions A" and
      t_def: "t = restrict_transition x sink I t0"
      using t_in by (auto simp: time_restrict_transitions)
    have "trans_source t0 \<in> ta_locations A"
      using awf t0_in by (auto simp: automaton_wf_def)
    then show ?thesis
      using t_def by simp
  qed
  show ?thesis
    using finite_locations initial_subset transition_endpoints
    by (auto simp: automaton_wf_def)
qed

lemma clock_wf_time_restrict_ta_with:
  assumes cwf: "clock_wf A"
  shows "clock_wf (time_restrict_ta_with x sink A I)"
proof -
  have finite_clocks: "finite (ta_clocks A)"
    using cwf by (simp add: clock_wf_def)
  have old_transition_clocks:
    "trans_resets t \<subseteq> ta_clocks A \<and>
     guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
    if "t \<in> ta_transitions A"
    for t
    using cwf that by (simp add: clock_wf_def)
  have transition_clocks:
    "trans_resets t \<subseteq> insert x (ta_clocks A) \<and>
     guards_clocks (trans_guards t) \<subseteq> insert x (ta_clocks A)"
    if t_in: "t \<in> ta_transitions (time_restrict_ta_with x sink A I)"
    for t
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using old_transition_clocks[of t] by auto
  next
    case False
    then obtain t0 where
      t0_in: "t0 \<in> ta_transitions A" and
      t_def: "t = restrict_transition x sink I t0"
      using t_in by (auto simp: time_restrict_transitions)
    have "trans_resets t0 \<subseteq> ta_clocks A"
      "guards_clocks (trans_guards t0) \<subseteq> ta_clocks A"
      using old_transition_clocks[OF t0_in] by simp_all
    then show ?thesis
      using t_def by auto
  qed
  show ?thesis
    using finite_clocks transition_clocks
    by (auto simp: clock_wf_def)
qed

theorem time_restrict_ta_correct:
  assumes awf: "automaton_wf A"
  assumes cwf: "clock_wf A"
  shows "ta_lang (time_restrict_ta A I) =
    {w \<in> ta_lang A. interval_mem (duration w) I}"
proof -
  have fresh: "fresh_clock (fresh_clock_for A) A"
    using fresh_clock_for_fresh[OF cwf] .
  have sink_fresh: "sink_location A \<notin> ta_locations A"
    using sink_location_fresh[OF awf] .
  show ?thesis
    unfolding time_restrict_ta_def
    by (rule time_restrict_ta_with_correct[OF awf cwf fresh sink_fresh])
qed

lemma automaton_wf_time_restrict_ta:
  assumes awf: "automaton_wf A"
  shows "automaton_wf (time_restrict_ta A I)"
  using automaton_wf_time_restrict_ta_with[OF awf sink_location_fresh[OF awf],
      of "fresh_clock_for A" I]
  by (simp add: time_restrict_ta_def)

lemma clock_wf_time_restrict_ta:
  assumes cwf: "clock_wf A"
  shows "clock_wf (time_restrict_ta A I)"
  using clock_wf_time_restrict_ta_with[OF cwf,
      of "fresh_clock_for A" "sink_location A" I]
  by (simp add: time_restrict_ta_def)

lemma compile_time_fragment_wf:
  assumes "compile_time_fragment r = Some A"
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
    r_def: "compile_time_fragment r = Some A1" and
    s_def: "compile_time_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1 \<and> clock_wf A1"
    using Union.IH(1)[OF r_def] .
  have wf2: "automaton_wf A2 \<and> clock_wf A2"
    using Union.IH(2)[OF s_def] .
  then show ?case
    using wf1 by (simp add: A_def automaton_wf_union_ta clock_wf_union_ta)
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_time_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using Within.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_time_restrict_ta clock_wf_time_restrict_ta)
qed auto

theorem compile_time_fragment_correct:
  assumes "compile_time_fragment r = Some A"
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
    r_def: "compile_time_fragment r = Some A1" and
    s_def: "compile_time_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_time_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_time_fragment_wf[OF s_def] by simp
  have "ta_lang A = ta_lang A1 \<union> ta_lang A2"
    using ta_lang_union_ta[OF wf1 wf2] by (simp add: A_def)
  also have "... = tre_lang r \<union> tre_lang s"
    using Union.IH(1)[OF r_def] Union.IH(2)[OF s_def] by simp
  also have "... = tre_lang (Union r s)"
    by simp
  finally show ?case .
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_time_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0"
    using compile_time_fragment_wf[OF r_def] by simp
  have cwf0: "clock_wf A0"
    using compile_time_fragment_wf[OF r_def] by simp
  have "ta_lang A = {w \<in> ta_lang A0. interval_mem (duration w) I}"
    using time_restrict_ta_correct[OF wf0 cwf0] by (simp add: A_def)
  also have "... = {w \<in> tre_lang r. interval_mem (duration w) I}"
    using Within.IH[OF r_def] by simp
  also have "... = tre_lang (Within r I)"
    by simp
  finally show ?case .
qed auto

theorem compile_time_fragment_trim_correct:
  assumes "compile_time_fragment r = Some A"
  shows "ta_lang (trim_to_accepting A) = tre_lang r"
  using compile_time_fragment_correct[OF assms] ta_lang_trim_to_accepting[of A]
  by simp

end
