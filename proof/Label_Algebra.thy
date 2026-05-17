theory Label_Algebra
  imports Kleene
begin

locale label_algebra =
  fixes lab_sem :: "'label => 'event set"
  fixes label_intersect :: "'label => 'label => 'label option"
  assumes label_intersect_Some:
    "label_intersect l1 l2 = Some l \<Longrightarrow>
      lab_sem l = lab_sem l1 \<inter> lab_sem l2"
  assumes label_intersect_None:
    "label_intersect l1 l2 = None \<Longrightarrow>
      lab_sem l1 \<inter> lab_sem l2 = {}"
begin

definition event_matches :: "'label => 'event => bool" where
  "event_matches l e \<longleftrightarrow> e \<in> lab_sem l"

inductive run_from_l ::
  "('q, 'label) automaton => 'q => valuation =>
    'event timed_word => 'q => valuation => bool"
where
  Run_Nil:
    "run_from_l A q v [] q v"
| Run_Cons:
    "t \<in> ta_transitions A \<Longrightarrow>
     trans_source t = q \<Longrightarrow>
     event_matches (trans_label t) a \<Longrightarrow>
     0 <= d \<Longrightarrow>
     guards_sat (delay_val d v) (trans_guards t) \<Longrightarrow>
     run_from_l A
       (trans_target t)
       (reset_val (trans_resets t) (delay_val d v))
       w qf vf \<Longrightarrow>
     run_from_l A q v ((d, a) # w) qf vf"

definition accepts_l ::
  "('q, 'label) automaton => 'event timed_word => bool"
where
  "accepts_l A w \<longleftrightarrow>
    (\<exists>q0 qf vf.
      q0 \<in> ta_initial A \<and>
      qf \<in> ta_accepting A \<and>
      run_from_l A q0 zero_val w qf vf)"

definition ta_lang_l ::
  "('q, 'label) automaton => 'event timed_word set"
where
  "ta_lang_l A = {w. accepts_l A w}"

lemma accepts_l_iff [simp]:
  "w \<in> ta_lang_l A \<longleftrightarrow> accepts_l A w"
  by (simp add: ta_lang_l_def)

lemma label_intersect_complete:
  assumes "event_matches l1 e"
  assumes "event_matches l2 e"
  shows "\<exists>l. label_intersect l1 l2 = Some l \<and> event_matches l e"
proof (cases "label_intersect l1 l2")
  case None
  then have "lab_sem l1 \<inter> lab_sem l2 = {}"
    by (rule label_intersect_None)
  then show ?thesis
    using assms by (auto simp: event_matches_def)
next
  case (Some l)
  then have "lab_sem l = lab_sem l1 \<inter> lab_sem l2"
    by (rule label_intersect_Some)
  then show ?thesis
    using Some assms by (auto simp: event_matches_def)
qed

lemma run_from_l_ConsE:
  assumes "run_from_l A q v ((d, a) # w) qf vf"
  obtains t where
    "t \<in> ta_transitions A"
    "trans_source t = q"
    "event_matches (trans_label t) a"
    "0 <= d"
    "guards_sat (delay_val d v) (trans_guards t)"
    "run_from_l A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      w qf vf"
  using assms
  by (cases rule: run_from_l.cases) auto

lemma run_from_l_transition_subset:
  assumes "run_from_l B q v w qf vf"
  assumes "ta_transitions B \<subseteq> ta_transitions A"
  shows "run_from_l A q v w qf vf"
  using assms
proof (induction arbitrary: A rule: run_from_l.induct)
  case (Run_Nil B q v)
  show ?case by (rule run_from_l.Run_Nil)
next
  case (Run_Cons t B q a d v w qf vf)
  have t_in: "t \<in> ta_transitions A"
    using Run_Cons.prems Run_Cons.hyps(1) by blast
  have tail:
    "run_from_l A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      w qf vf"
    using Run_Cons.IH[OF Run_Cons.prems] .
  then show ?case
    using Run_Cons.hyps t_in
    by (auto intro!: run_from_l.Run_Cons[of t])
qed

lemma run_from_l_wellformed:
  assumes "run_from_l A q v w qf vf"
  shows "wellformed_timed_word w"
  using assms by (induction rule: run_from_l.induct) simp_all

lemma accepts_l_wellformed:
  assumes "accepts_l A w"
  shows "wellformed_timed_word w"
  using assms run_from_l_wellformed by (auto simp: accepts_l_def)

lemma run_from_l_agree_on:
  assumes cwf: "clock_wf A"
  assumes run: "run_from_l A p v w q vf"
  assumes agree: "agree_on (ta_clocks A) v v'"
  shows "\<exists>vf'. run_from_l A p v' w q vf' \<and>
    agree_on (ta_clocks A) vf vf'"
  using run cwf agree
proof (induction arbitrary: v' rule: run_from_l.induct)
  case (Run_Nil A q v)
  show ?case
    using Run_Nil.prems(2)
    by (auto intro: run_from_l.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  have trans_bounds:
    "trans_resets t \<subseteq> ta_clocks A"
    "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
    using Run_Cons.prems(1) Run_Cons.hyps(1)
    by (auto simp: clock_wf_def)
  have delayed_agree:
    "agree_on (ta_clocks A) (delay_val d v) (delay_val d v')"
    using agree_on_delay[OF Run_Cons.prems(2)] .
  have guards':
    "guards_sat (delay_val d v') (trans_guards t)"
    using guards_sat_agree[OF trans_bounds(2) delayed_agree]
      Run_Cons.hyps(5)
    by simp
  have reset_agree:
    "agree_on (ta_clocks A)
      (reset_val (trans_resets t) (delay_val d v))
      (reset_val (trans_resets t) (delay_val d v'))"
    using agree_on_reset[OF delayed_agree trans_bounds(1)] .
  obtain vf' where
    tail: "run_from_l A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v'))
      w qf vf'" and
    final_agree: "agree_on (ta_clocks A) vf vf'"
    using Run_Cons.IH[OF Run_Cons.prems(1) reset_agree] by blast
  have run':
    "run_from_l A q v' ((d, a) # w) qf vf'"
    using Run_Cons.hyps tail guards'
    by (auto intro!: run_from_l.Run_Cons[of t])
  then show ?case
    using final_agree by auto
qed

end

definition eq_label_intersect :: "'a => 'a => 'a option" where
  "eq_label_intersect l1 l2 = (if l1 = l2 then Some l1 else None)"

interpretation equality_label_algebra:
  label_algebra "\<lambda>l. {l}" eq_label_intersect
  by standard (auto simp: eq_label_intersect_def split: if_splits)

lemma equality_event_matches [simp]:
  "equality_label_algebra.event_matches l e \<longleftrightarrow> e = l"
  by (simp add: equality_label_algebra.event_matches_def)

lemma equality_run_from_l_iff:
  "equality_label_algebra.run_from_l A q v w qf vf \<longleftrightarrow>
    run_from A q v w qf vf"
proof
  assume "equality_label_algebra.run_from_l A q v w qf vf"
  then show "run_from A q v w qf vf"
  proof (induction rule: equality_label_algebra.run_from_l.induct)
    case (Run_Nil A q v)
    then show ?case by (rule run_from.Run_Nil)
  next
    case (Run_Cons t A q a d v w qf vf)
    then show ?case
      by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
  qed
next
  assume "run_from A q v w qf vf"
  then show "equality_label_algebra.run_from_l A q v w qf vf"
  proof (induction rule: run_from.induct)
    case (Run_Nil A q v)
    then show ?case
      by (rule equality_label_algebra.Run_Nil)
  next
    case (Run_Cons t A q a d v w qf vf)
    then show ?case
      by (auto intro!: equality_label_algebra.Run_Cons[of t]
          simp: reset_val_def)
  qed
qed

lemma equality_accepts_l_iff:
  "equality_label_algebra.accepts_l A w \<longleftrightarrow> accepts A w"
  by (auto simp: equality_label_algebra.accepts_l_def accepts_def
      equality_run_from_l_iff)

lemma equality_ta_lang_l:
  "equality_label_algebra.ta_lang_l A = ta_lang A"
  by (auto simp: equality_label_algebra.ta_lang_l_def ta_lang_def
      equality_accepts_l_iff)

end
