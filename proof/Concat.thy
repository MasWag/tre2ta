theory Concat
  imports Time_Restriction
begin

definition agree_on :: "clock set => valuation => valuation => bool" where
  "agree_on C v v' \<longleftrightarrow> (\<forall>c \<in> C. v c = v' c)"

definition concat_transition ::
  "(nat, 'a) automaton => (nat, 'a) transition => nat => (nat, 'a) transition"
where
  "concat_transition B t q =
    t\<lparr> trans_resets := trans_resets t \<union> ta_clocks B,
       trans_target := q \<rparr>"

definition concat_switches ::
  "(nat, 'a) automaton => (nat, 'a) automaton => (nat, 'a) transition set"
where
  "concat_switches A B =
    {concat_transition B t q | t q.
      t \<in> ta_transitions A \<and>
      trans_target t \<in> ta_accepting A \<and>
      q \<in> ta_initial B}"

definition concat_ta_raw ::
  "(nat, 'a) automaton => (nat, 'a) automaton => (nat, 'a) automaton"
where
  "concat_ta_raw A B =
    \<lparr> ta_locations = ta_locations A \<union> ta_locations B,
      ta_initial =
        ta_initial A \<union> (if accepts A [] then ta_initial B else {}),
      ta_accepting = ta_accepting B,
      ta_clocks = ta_clocks A \<union> ta_clocks B,
      ta_transitions =
        ta_transitions A \<union> ta_transitions B \<union> concat_switches A B \<rparr>"

definition concat_ta ::
  "(nat, 'a) automaton => (nat, 'a) automaton => (nat, 'a) automaton"
where
  "concat_ta A B =
    concat_ta_raw A (shift_locations (shift_offset A) B)"

fun compile_concat_fragment :: "'a tre => (nat, 'a) automaton option" where
  "compile_concat_fragment Empty = Some empty_ta"
| "compile_concat_fragment Epsilon = Some epsilon_ta"
| "compile_concat_fragment (Atom a) = Some (atom_ta a)"
| "compile_concat_fragment (Union r s) =
    (case compile_concat_fragment r of
       None => None
     | Some A =>
         (case compile_concat_fragment s of
            None => None
          | Some B => Some (union_ta A B)))"
| "compile_concat_fragment (Concat r s) =
    (case compile_concat_fragment r of
       None => None
     | Some A =>
         (case compile_concat_fragment s of
            None => None
          | Some B => Some (concat_ta A B)))"
| "compile_concat_fragment (Within r I) =
    (case compile_concat_fragment r of
       None => None
     | Some A => Some (time_restrict_ta A I))"
| "compile_concat_fragment (Intersection r s) = None"
| "compile_concat_fragment (KleeneStar r) = None"
| "compile_concat_fragment (KleenePlus r) = None"

lemma concat_langI:
  assumes "u \<in> A"
  assumes "v \<in> B"
  shows "u @ v \<in> concat_lang A B"
  using assms by auto

lemma append_assoc_timed_word:
  "(u @ v) @ w = (u @ v @ w :: 'a timed_word)"
  by simp

lemma agree_on_refl [simp]:
  "agree_on C v v"
  by (simp add: agree_on_def)

lemma agree_on_sym:
  assumes "agree_on C v v'"
  shows "agree_on C v' v"
  using assms by (auto simp: agree_on_def)

lemma agree_on_zero:
  assumes "\<And>c. c \<in> C \<Longrightarrow> v c = 0"
  shows "agree_on C v zero_val"
  using assms by (simp add: agree_on_def)

lemma agree_on_delay:
  assumes "agree_on C v v'"
  shows "agree_on C (delay_val d v) (delay_val d v')"
  using assms by (auto simp: agree_on_def)

lemma agree_on_reset:
  assumes "agree_on C v v'"
  assumes "R \<subseteq> C"
  shows "agree_on C (reset_val R v) (reset_val R v')"
  using assms by (auto simp: agree_on_def)

lemma guard_sat_agree:
  assumes "guard_clocks g \<subseteq> C"
  assumes "agree_on C v v'"
  shows "guard_sat v g \<longleftrightarrow> guard_sat v' g"
  using assms by (cases g) (auto simp: agree_on_def)

lemma guards_sat_agree:
  assumes "guards_clocks gs \<subseteq> C"
  assumes "agree_on C v v'"
  shows "guards_sat v gs \<longleftrightarrow> guards_sat v' gs"
  using assms
proof (induction gs)
  case Nil
  then show ?case by simp
next
  case (Cons g gs)
  have g_subset: "guard_clocks g \<subseteq> C"
    using Cons.prems(1) by (auto simp: guards_clocks_def)
  have gs_subset: "guards_clocks gs \<subseteq> C"
    using Cons.prems(1) by (auto simp: guards_clocks_def)
  show ?case
    using guard_sat_agree[OF g_subset Cons.prems(2)]
      Cons.IH[OF gs_subset Cons.prems(2)]
    by simp
qed

lemma run_from_appendI:
  assumes "run_from A p v u q vq"
  assumes "run_from A q vq w r vr"
  shows "run_from A p v (u @ w) r vr"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by simp
next
  case (Run_Cons t A q a d v u qf vf)
  then show ?case
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma run_from_agree_on:
  assumes cwf: "clock_wf A"
  assumes run: "run_from A p v w q vf"
  assumes agree: "agree_on (ta_clocks A) v v'"
  shows "\<exists>vf'. run_from A p v' w q vf' \<and>
    agree_on (ta_clocks A) vf vf'"
  using run cwf agree
proof (induction arbitrary: v' rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case
    by (auto intro: run_from.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  have transition_clock_bounds:
    "\<And>u. u \<in> ta_transitions A \<Longrightarrow>
      trans_resets u \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards u) \<subseteq> ta_clocks A"
  proof -
    fix u
    assume u_in: "u \<in> ta_transitions A"
    have wf_unfolded:
      "finite (ta_clocks A) \<and>
       (\<forall>u \<in> ta_transitions A.
        trans_resets u \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards u) \<subseteq> ta_clocks A)"
      using Run_Cons.prems(1) by (simp add: clock_wf_def)
    then have all_trans:
      "\<forall>u \<in> ta_transitions A.
        trans_resets u \<subseteq> ta_clocks A \<and>
        guards_clocks (trans_guards u) \<subseteq> ta_clocks A"
      by simp
    show "trans_resets u \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards u) \<subseteq> ta_clocks A"
      using all_trans u_in by simp
  qed
  have resets_subset: "trans_resets t \<subseteq> ta_clocks A"
    using transition_clock_bounds[OF Run_Cons.hyps(1)] by simp
  have guards_subset: "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
    using transition_clock_bounds[OF Run_Cons.hyps(1)] by simp
  have delayed_agree:
    "agree_on (ta_clocks A) (delay_val d v) (delay_val d v')"
    using agree_on_delay[OF Run_Cons.prems(2)] .
  have guards':
    "guards_sat (delay_val d v') (trans_guards t)"
    using guards_sat_agree[OF guards_subset delayed_agree]
      Run_Cons.hyps(5)
    by simp
  have reset_agree:
    "agree_on (ta_clocks A)
      (reset_val (trans_resets t) (delay_val d v))
      (reset_val (trans_resets t) (delay_val d v'))"
    using agree_on_reset[OF delayed_agree resets_subset] .
  obtain vf' where
    tail: "run_from A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v'))
      w qf vf'" and
    final_agree: "agree_on (ta_clocks A) vf vf'"
    using Run_Cons.IH[OF Run_Cons.prems(1) reset_agree] by blast
  have run':
    "run_from A q v' ((d, a) # w) qf vf'"
    using Run_Cons.hyps tail guards'
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
  then show ?case
    using final_agree by auto
qed

lemma concat_transition_simps [simp]:
  "trans_source (concat_transition B t q) = trans_source t"
  "trans_label (concat_transition B t q) = trans_label t"
  "trans_guards (concat_transition B t q) = trans_guards t"
  "trans_resets (concat_transition B t q) =
    trans_resets t \<union> ta_clocks B"
  "trans_target (concat_transition B t q) = q"
  by (simp_all add: concat_transition_def)

lemma concat_ta_raw_simps [simp]:
  "ta_locations (concat_ta_raw A B) = ta_locations A \<union> ta_locations B"
  "ta_initial (concat_ta_raw A B) =
    ta_initial A \<union> (if accepts A [] then ta_initial B else {})"
  "ta_accepting (concat_ta_raw A B) = ta_accepting B"
  "ta_clocks (concat_ta_raw A B) = ta_clocks A \<union> ta_clocks B"
  by (simp_all add: concat_ta_raw_def)

lemma concat_ta_raw_transitions:
  "ta_transitions (concat_ta_raw A B) =
    ta_transitions A \<union> ta_transitions B \<union> concat_switches A B"
  by (simp add: concat_ta_raw_def)

lemma concat_switchesE:
  assumes "u \<in> concat_switches A B"
  obtains t q where
    "t \<in> ta_transitions A"
    "trans_target t \<in> ta_accepting A"
    "q \<in> ta_initial B"
    "u = concat_transition B t q"
  using assms by (auto simp: concat_switches_def)

lemma concat_switchI:
  assumes "t \<in> ta_transitions A"
  assumes "trans_target t \<in> ta_accepting A"
  assumes "q \<in> ta_initial B"
  shows "concat_transition B t q \<in> ta_transitions (concat_ta_raw A B)"
  using assms by (auto simp: concat_ta_raw_transitions concat_switches_def)

lemma run_from_concat_raw_rightI:
  assumes "run_from B q v w qf vf"
  shows "run_from (concat_ta_raw A B) q v w qf vf"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by (rule run_from.Run_Nil)
next
  case (Run_Cons t B q a d v w qf vf)
  have t_in: "t \<in> ta_transitions (concat_ta_raw A B)"
    using Run_Cons.hyps(1) by (auto simp: concat_ta_raw_transitions)
  then show ?case
    using Run_Cons
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma run_from_concat_raw_rightD:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  assumes q_in: "q \<in> ta_locations B"
  assumes run: "run_from (concat_ta_raw A B) q v w qf vf"
  shows "qf \<in> ta_locations B \<and> run_from B q v w qf vf"
  using run q_in
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case
    by (cases rule: run_from.cases) (auto intro: run_from.Run_Nil)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t where
    t_concat: "t \<in> ta_transitions (concat_ta_raw A B)" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from (concat_ta_raw A B)
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf"
    using Cons.prems(1) x_def by (auto elim: run_from_ConsE)
  show ?case
  proof (cases "t \<in> ta_transitions B")
    case True
    then have target_in: "trans_target t \<in> ta_locations B"
      using wfB by (auto simp: automaton_wf_def)
    have tail: "qf \<in> ta_locations B \<and>
      run_from B
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        xs qf vf"
      using Cons.IH[OF tail_run target_in] .
    then show ?thesis
      using True source label nonneg guards x_def
      by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
  next
    case False
    show ?thesis
    proof (cases "t \<in> ta_transitions A")
      case True
      then have "trans_source t \<in> ta_locations A"
        using wfA by (auto simp: automaton_wf_def)
      then show ?thesis
        using source Cons.prems(2) disj by auto
    next
      case False_A: False
      have "t \<in> concat_switches A B"
        using t_concat False False_A
        by (auto simp: concat_ta_raw_transitions)
      then obtain tA q0 where
        tA_in: "tA \<in> ta_transitions A" and
        t_def: "t = concat_transition B tA q0"
        by (auto elim: concat_switchesE)
      have "trans_source tA \<in> ta_locations A"
        using wfA tA_in by (auto simp: automaton_wf_def)
      then show ?thesis
        using source Cons.prems(2) disj t_def by auto
    qed
  qed
qed

lemma run_from_concat_raw_left_to_rightD:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  assumes q_in: "q \<in> ta_locations A"
  assumes qf_in: "qf \<in> ta_locations B"
  assumes run: "run_from (concat_ta_raw A B) q v w qf vf"
  shows "\<exists>w1 w2 qa q0 vb.
    w = w1 @ w2 \<and>
    qa \<in> ta_accepting A \<and>
    q0 \<in> ta_initial B \<and>
    run_from A q v w1 qa vb \<and>
    (\<exists>vfB. run_from B q0 zero_val w2 qf vfB)"
  using run q_in qf_in
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case
    by (cases rule: run_from.cases) (use disj in auto)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t where
    t_concat: "t \<in> ta_transitions (concat_ta_raw A B)" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from (concat_ta_raw A B)
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf"
    using Cons.prems(1) x_def by (auto elim: run_from_ConsE)
  show ?case
  proof (cases "t \<in> ta_transitions A")
    case True
    then have target_A: "trans_target t \<in> ta_locations A"
      using wfA by (auto simp: automaton_wf_def)
    obtain w1 w2 qa q0 vb vfB where
      xs_def: "xs = w1 @ w2" and
      qa_acc: "qa \<in> ta_accepting A" and
      q0_init: "q0 \<in> ta_initial B" and
      runA_tail: "run_from A
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        w1 qa vb" and
      runB: "run_from B q0 zero_val w2 qf vfB"
      using Cons.IH[OF tail_run target_A Cons.prems(3)] by blast
    have runA:
      "run_from A q v ((d, a) # w1) qa vb"
      using True source label nonneg guards runA_tail
      by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
    show ?thesis
    proof -
      have word: "x # xs = ((d, a) # w1) @ w2"
        using x_def xs_def by simp
      show ?thesis
        using word qa_acc q0_init runA runB by blast
    qed
  next
    case not_A: False
    show ?thesis
    proof (cases "t \<in> ta_transitions B")
      case True
      then have "trans_source t \<in> ta_locations B"
        using wfB by (auto simp: automaton_wf_def)
      then show ?thesis
        using source Cons.prems(2) disj by auto
    next
      case not_B: False
      have t_switch: "t \<in> concat_switches A B"
        using t_concat not_A not_B by (auto simp: concat_ta_raw_transitions)
      then obtain tA q0 where
        tA_in: "tA \<in> ta_transitions A" and
        tA_acc: "trans_target tA \<in> ta_accepting A" and
        q0_init: "q0 \<in> ta_initial B" and
        t_def: "t = concat_transition B tA q0"
        by (auto elim: concat_switchesE)
      have q0_loc: "q0 \<in> ta_locations B"
        using wfB q0_init by (auto simp: automaton_wf_def)
      have right_run:
        "qf \<in> ta_locations B \<and>
         run_from B q0
          (reset_val (trans_resets tA \<union> ta_clocks B) (delay_val d v))
          xs qf vf"
        using run_from_concat_raw_rightD[OF wfA wfB disj q0_loc]
          tail_run t_def
        by simp
      have start_agree:
        "agree_on (ta_clocks B)
          (reset_val (trans_resets tA \<union> ta_clocks B) (delay_val d v))
          zero_val"
        by (auto simp: agree_on_def)
      obtain vfB where runB:
        "run_from B q0 zero_val xs qf vfB"
        using run_from_agree_on[OF cwfB conjunct2[OF right_run] start_agree]
        by auto
      have runA:
        "run_from A q v [(d, a)] (trans_target tA)
          (reset_val (trans_resets tA) (delay_val d v))"
        using tA_in source label nonneg guards t_def
        by (auto intro!: run_from.Run_Cons[of tA] run_from.Run_Nil
            simp: reset_val_def)
      show ?thesis
      proof -
        have word: "x # xs = [(d, a)] @ xs"
          using x_def by simp
        show ?thesis
          using word tA_acc q0_init runA runB by blast
      qed
    qed
  qed
qed

lemma run_from_concat_raw_left_then_rightI:
  assumes cwfB: "clock_wf B"
  assumes runA: "run_from A q v w1 qa va"
  assumes qa_acc: "qa \<in> ta_accepting A"
  assumes nonempty: "w1 \<noteq> []"
  assumes q0_init: "q0 \<in> ta_initial B"
  assumes runB: "run_from B q0 zero_val w2 qf vfB"
  shows "\<exists>vf. run_from (concat_ta_raw A B) q v (w1 @ w2) qf vf"
  using runA qa_acc nonempty q0_init runB
proof (induction arbitrary: w2 q0 qf vfB rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by simp
next
  case (Run_Cons t A q a d v w qa va)
  show ?case
  proof (cases "w = []")
    case True
    have target_acc: "trans_target t \<in> ta_accepting A"
      using Run_Cons.hyps(6) Run_Cons.prems(1) True
      by (cases rule: run_from.cases) auto
    have switch_in:
      "concat_transition B t q0 \<in> ta_transitions (concat_ta_raw A B)"
      using concat_switchI[OF Run_Cons.hyps(1) target_acc Run_Cons.prems(3)] .
    have start_agree:
      "agree_on (ta_clocks B)
        (reset_val (trans_resets t \<union> ta_clocks B) (delay_val d v))
        zero_val"
      by (auto simp: agree_on_def)
    obtain vf where runB':
      "run_from B q0
        (reset_val (trans_resets t \<union> ta_clocks B) (delay_val d v))
        w2 qf vf"
      using run_from_agree_on[
          OF cwfB Run_Cons.prems(4) agree_on_sym[OF start_agree]]
      by auto
    have tail:
      "run_from (concat_ta_raw A B) q0
        (reset_val (trans_resets t \<union> ta_clocks B) (delay_val d v))
        w2 qf vf"
      using run_from_concat_raw_rightI[OF runB'] .
    have run:
      "run_from (concat_ta_raw A B) q v (((d, a) # w) @ w2) qf vf"
      using switch_in Run_Cons.hyps(2,3,4,5) tail True
      by (auto intro!: run_from.Run_Cons[of "concat_transition B t q0"]
          simp: reset_val_def)
    then show ?thesis by auto
  next
    case False
    obtain vf where tail:
      "run_from (concat_ta_raw A B)
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        (w @ w2) qf vf"
      using Run_Cons.IH[OF Run_Cons.prems(1) False
          Run_Cons.prems(3) Run_Cons.prems(4)]
      by blast
    have t_in: "t \<in> ta_transitions (concat_ta_raw A B)"
      using Run_Cons.hyps(1) by (auto simp: concat_ta_raw_transitions)
    have run:
      "run_from (concat_ta_raw A B) q v (((d, a) # w) @ w2) qf vf"
      using t_in Run_Cons.hyps tail
      by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
    then show ?thesis by auto
  qed
qed

lemma concat_ta_raw_sound:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  assumes "w \<in> ta_lang (concat_ta_raw A B)"
  shows "w \<in> concat_lang (ta_lang A) (ta_lang B)"
proof -
  obtain q0 qf vf where
    q0_init: "q0 \<in> ta_initial (concat_ta_raw A B)" and
    qf_acc: "qf \<in> ta_accepting (concat_ta_raw A B)" and
    run: "run_from (concat_ta_raw A B) q0 zero_val w qf vf"
    using assms(5) by (auto simp: ta_lang_def accepts_def)
  have qf_B: "qf \<in> ta_locations B"
    using qf_acc wfB by (auto simp: automaton_wf_def)
  show ?thesis
  proof (cases "q0 \<in> ta_initial A")
    case True
    then have q0_A: "q0 \<in> ta_locations A"
      using wfA by (auto simp: automaton_wf_def)
    obtain w1 w2 qa qB0 va vfB where
      w_def: "w = w1 @ w2" and
      qa_acc: "qa \<in> ta_accepting A" and
      qB0_init: "qB0 \<in> ta_initial B" and
      runA: "run_from A q0 zero_val w1 qa va" and
      runB: "run_from B qB0 zero_val w2 qf vfB"
      using run_from_concat_raw_left_to_rightD[
          OF wfA wfB cwfB disj q0_A qf_B run]
      by auto
    have "w1 \<in> ta_lang A"
      using True qa_acc runA by (auto simp: ta_lang_def accepts_def)
    moreover have "w2 \<in> ta_lang B"
      using qB0_init qf_acc runB by (auto simp: ta_lang_def accepts_def)
    ultimately show ?thesis
      using w_def by auto
  next
    case False
    then have q0_B: "q0 \<in> ta_initial B"
      using q0_init by (auto split: if_splits)
    have A_empty: "[] \<in> ta_lang A"
      using q0_init False by (auto simp: ta_lang_def split: if_splits)
    have q0_B_loc: "q0 \<in> ta_locations B"
      using wfB q0_B by (auto simp: automaton_wf_def)
    have right:
      "qf \<in> ta_locations B \<and> run_from B q0 zero_val w qf vf"
      using run_from_concat_raw_rightD[OF wfA wfB disj q0_B_loc run] .
    have "w \<in> ta_lang B"
      using q0_B qf_acc right by (auto simp: ta_lang_def accepts_def)
    then show ?thesis
      using A_empty by auto
  qed
qed

lemma concat_ta_raw_complete:
  assumes cwfB: "clock_wf B"
  assumes "w1 \<in> ta_lang A"
  assumes "w2 \<in> ta_lang B"
  shows "w1 @ w2 \<in> ta_lang (concat_ta_raw A B)"
proof -
  obtain qA0 qAf vAf where
    qA0_init: "qA0 \<in> ta_initial A" and
    qAf_acc: "qAf \<in> ta_accepting A" and
    runA: "run_from A qA0 zero_val w1 qAf vAf"
    using assms(2) by (auto simp: ta_lang_def accepts_def)
  obtain qB0 qBf vBf where
    qB0_init: "qB0 \<in> ta_initial B" and
    qBf_acc: "qBf \<in> ta_accepting B" and
    runB: "run_from B qB0 zero_val w2 qBf vBf"
    using assms(3) by (auto simp: ta_lang_def accepts_def)
  show ?thesis
  proof (cases "w1 = []")
    case True
    have A_empty: "accepts A []"
      using assms(2) True by simp
    have qB0_init_concat:
      "qB0 \<in> ta_initial (concat_ta_raw A B)"
      using qB0_init A_empty by simp
    have run_concat:
      "run_from (concat_ta_raw A B) qB0 zero_val w2 qBf vBf"
      using run_from_concat_raw_rightI[OF runB] .
    have qBf_acc_concat:
      "qBf \<in> ta_accepting (concat_ta_raw A B)"
      using qBf_acc by simp
    have "accepts (concat_ta_raw A B) w2"
      using qB0_init_concat qBf_acc_concat run_concat
      unfolding accepts_def by blast
    then show ?thesis
      using True by (simp add: ta_lang_def)
  next
    case False
    obtain vf where run_concat:
      "run_from (concat_ta_raw A B) qA0 zero_val (w1 @ w2) qBf vf"
      using run_from_concat_raw_left_then_rightI[
          OF cwfB runA qAf_acc False qB0_init runB]
      by auto
    show ?thesis
      using qA0_init qBf_acc run_concat
      by (auto simp: ta_lang_def accepts_def)
  qed
qed

theorem concat_ta_raw_correct:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  shows "ta_lang (concat_ta_raw A B) =
    concat_lang (ta_lang A) (ta_lang B)"
proof
  show "ta_lang (concat_ta_raw A B) \<subseteq>
    concat_lang (ta_lang A) (ta_lang B)"
    using concat_ta_raw_sound[OF wfA wfB cwfB disj] by blast
next
  show "concat_lang (ta_lang A) (ta_lang B) \<subseteq>
    ta_lang (concat_ta_raw A B)"
    using concat_ta_raw_complete[OF cwfB] by auto
qed

lemma automaton_wf_concat_ta_raw:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  shows "automaton_wf (concat_ta_raw A B)"
proof -
  have transition_endpoints:
    "trans_source t \<in> ta_locations A \<union> ta_locations B \<and>
     trans_target t \<in> ta_locations A \<union> ta_locations B"
    if t_in: "t \<in> ta_transitions (concat_ta_raw A B)"
    for t
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using wfA by (auto simp: automaton_wf_def)
  next
    case not_A: False
    show ?thesis
    proof (cases "t \<in> ta_transitions B")
      case True
      then show ?thesis
        using wfB by (auto simp: automaton_wf_def)
    next
      case not_B: False
      have "t \<in> concat_switches A B"
        using t_in not_A not_B by (auto simp: concat_ta_raw_transitions)
      then obtain tA q where
        tA_in: "tA \<in> ta_transitions A" and
        q_init: "q \<in> ta_initial B" and
        t_def: "t = concat_transition B tA q"
        by (auto elim: concat_switchesE)
      have "trans_source tA \<in> ta_locations A"
        using wfA tA_in by (auto simp: automaton_wf_def)
      moreover have "q \<in> ta_locations B"
        using wfB q_init by (auto simp: automaton_wf_def)
      ultimately show ?thesis
        using t_def by simp
    qed
  qed
  show ?thesis
    using assms transition_endpoints
    by (auto simp: automaton_wf_def)
qed

lemma clock_wf_concat_ta_raw:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  shows "clock_wf (concat_ta_raw A B)"
proof -
  have transition_clocks:
    "trans_resets t \<subseteq> ta_clocks A \<union> ta_clocks B \<and>
     guards_clocks (trans_guards t) \<subseteq> ta_clocks A \<union> ta_clocks B"
    if t_in: "t \<in> ta_transitions (concat_ta_raw A B)"
    for t
  proof (cases "t \<in> ta_transitions A")
    case True
    then show ?thesis
      using cwfA by (auto simp: clock_wf_def)
  next
    case not_A: False
    show ?thesis
    proof (cases "t \<in> ta_transitions B")
      case True
      then show ?thesis
        using cwfB by (auto simp: clock_wf_def)
    next
      case not_B: False
      have "t \<in> concat_switches A B"
        using t_in not_A not_B by (auto simp: concat_ta_raw_transitions)
      then obtain tA q where
        tA_in: "tA \<in> ta_transitions A" and
        t_def: "t = concat_transition B tA q"
        by (auto elim: concat_switchesE)
      have "trans_resets tA \<subseteq> ta_clocks A"
        "guards_clocks (trans_guards tA) \<subseteq> ta_clocks A"
        using cwfA tA_in by (simp_all add: clock_wf_def)
      then show ?thesis
        using t_def by auto
    qed
  qed
  show ?thesis
    using assms transition_clocks by (auto simp: clock_wf_def)
qed

theorem concat_ta_correct:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes cwfB: "clock_wf B"
  shows "ta_lang (concat_ta A B) =
    concat_lang (ta_lang A) (ta_lang B)"
proof -
  let ?B = "shift_locations (shift_offset A) B"
  have wfB': "automaton_wf ?B"
    using automaton_wf_shift_locations[OF wfB] .
  have cwfB': "clock_wf ?B"
    using clock_wf_shift_locations[OF cwfB] .
  have disj: "ta_locations A \<inter> ta_locations ?B = {}"
    using disjoint_shift_locations[OF wfA] .
  have "ta_lang (concat_ta A B) =
    ta_lang (concat_ta_raw A ?B)"
    by (simp add: concat_ta_def)
  also have "... = concat_lang (ta_lang A) (ta_lang ?B)"
    using concat_ta_raw_correct[OF wfA wfB' cwfB' disj] .
  also have "... = concat_lang (ta_lang A) (ta_lang B)"
    by (simp add: ta_lang_shift_locations)
  finally show ?thesis .
qed

lemma automaton_wf_concat_ta:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  shows "automaton_wf (concat_ta A B)"
  using automaton_wf_concat_ta_raw[
      OF wfA automaton_wf_shift_locations[OF wfB]]
  by (simp add: concat_ta_def)

lemma clock_wf_concat_ta:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  shows "clock_wf (concat_ta A B)"
  using clock_wf_concat_ta_raw[
      OF cwfA clock_wf_shift_locations[OF cwfB]]
  by (simp add: concat_ta_def)

lemma compile_concat_fragment_wf:
  assumes "compile_concat_fragment r = Some A"
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
    r_def: "compile_concat_fragment r = Some A1" and
    s_def: "compile_concat_fragment s = Some A2" and
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
    r_def: "compile_concat_fragment r = Some A1" and
    s_def: "compile_concat_fragment s = Some A2" and
    A_def: "A = concat_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1 \<and> clock_wf A1"
    using Concat.IH(1)[OF r_def] .
  have wf2: "automaton_wf A2 \<and> clock_wf A2"
    using Concat.IH(2)[OF s_def] .
  then show ?case
    using wf1 by (simp add: A_def automaton_wf_concat_ta clock_wf_concat_ta)
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_concat_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using Within.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_time_restrict_ta clock_wf_time_restrict_ta)
qed auto

theorem compile_concat_fragment_correct:
  assumes "compile_concat_fragment r = Some A"
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
    r_def: "compile_concat_fragment r = Some A1" and
    s_def: "compile_concat_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_concat_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_concat_fragment_wf[OF s_def] by simp
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
    r_def: "compile_concat_fragment r = Some A1" and
    s_def: "compile_concat_fragment s = Some A2" and
    A_def: "A = concat_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_concat_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_concat_fragment_wf[OF s_def] by simp
  have cwf2: "clock_wf A2"
    using compile_concat_fragment_wf[OF s_def] by simp
  have "ta_lang A = concat_lang (ta_lang A1) (ta_lang A2)"
    using concat_ta_correct[OF wf1 wf2 cwf2] by (simp add: A_def)
  also have "... = concat_lang (tre_lang r) (tre_lang s)"
    using Concat.IH(1)[OF r_def] Concat.IH(2)[OF s_def] by simp
  also have "... = tre_lang (Concat r s)"
    by simp
  finally show ?case .
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_concat_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0"
    using compile_concat_fragment_wf[OF r_def] by simp
  have cwf0: "clock_wf A0"
    using compile_concat_fragment_wf[OF r_def] by simp
  have "ta_lang A = {w \<in> ta_lang A0. interval_mem (duration w) I}"
    using time_restrict_ta_correct[OF wf0 cwf0] by (simp add: A_def)
  also have "... = {w \<in> tre_lang r. interval_mem (duration w) I}"
    using Within.IH[OF r_def] by simp
  also have "... = tre_lang (Within r I)"
    by simp
  finally show ?case .
qed auto

theorem compile_concat_fragment_trim_correct:
  assumes "compile_concat_fragment r = Some A"
  shows "ta_lang (trim_to_accepting A) = tre_lang r"
  using compile_concat_fragment_correct[OF assms] ta_lang_trim_to_accepting[of A]
  by simp

end
