theory Trim
  imports TA_Combinators
begin

definition edge :: "('q, 'a) automaton => 'q => 'q => bool" where
  "edge A p q \<longleftrightarrow>
    (\<exists>t \<in> ta_transitions A. trans_source t = p \<and> trans_target t = q)"

inductive reaches :: "('q, 'a) automaton => 'q => 'q => bool" for A where
  reaches_refl:
    "reaches A p p"
| reaches_step:
    "edge A p q \<Longrightarrow> reaches A q r \<Longrightarrow> reaches A p r"

definition coreachable :: "('q, 'a) automaton => 'q => bool" where
  "coreachable A p \<longleftrightarrow> (\<exists>q \<in> ta_accepting A. reaches A p q)"

definition trim_to_accepting :: "('q, 'a) automaton => ('q, 'a) automaton" where
  "trim_to_accepting A =
    \<lparr> ta_locations = {p \<in> ta_locations A. coreachable A p},
      ta_initial = {p \<in> ta_initial A. coreachable A p},
      ta_accepting = {p \<in> ta_accepting A. coreachable A p},
      ta_clocks = ta_clocks A,
      ta_transitions =
        {t \<in> ta_transitions A.
          coreachable A (trans_source t) \<and>
          coreachable A (trans_target t)} \<rparr>"

lemma edgeI:
  assumes "t \<in> ta_transitions A"
  assumes "trans_source t = p"
  assumes "trans_target t = q"
  shows "edge A p q"
  using assms by (auto simp: edge_def)

lemma accepting_coreachable [simp]:
  assumes "p \<in> ta_accepting A"
  shows "coreachable A p"
  using assms
  by (auto simp: coreachable_def intro: reaches.reaches_refl)

lemma trim_locations [simp]:
  "ta_locations (trim_to_accepting A) = {p \<in> ta_locations A. coreachable A p}"
  by (simp add: trim_to_accepting_def)

lemma trim_initial [simp]:
  "ta_initial (trim_to_accepting A) = {p \<in> ta_initial A. coreachable A p}"
  by (simp add: trim_to_accepting_def)

lemma trim_accepting [simp]:
  "ta_accepting (trim_to_accepting A) = ta_accepting A"
  by (auto simp: trim_to_accepting_def)

lemma trim_clocks [simp]:
  "ta_clocks (trim_to_accepting A) = ta_clocks A"
  by (simp add: trim_to_accepting_def)

lemma trim_transitions [simp]:
  "ta_transitions (trim_to_accepting A) =
    {t \<in> ta_transitions A.
      coreachable A (trans_source t) \<and>
      coreachable A (trans_target t)}"
  by (simp add: trim_to_accepting_def)

lemma trim_locations_subset:
  "ta_locations (trim_to_accepting A) \<subseteq> ta_locations A"
  by auto

lemma trim_initial_inter:
  "ta_initial (trim_to_accepting A) =
    ta_initial A \<inter> {p. coreachable A p}"
  by auto

lemma trim_transitions_subset:
  "ta_transitions (trim_to_accepting A) \<subseteq> ta_transitions A"
  by auto

lemma run_from_reaches:
  assumes "run_from A p v w q vf"
  shows "reaches A p q"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case
    by (rule reaches.reaches_refl)
next
  case (Run_Cons t A q a d v w qf vf)
  have "edge A q (trans_target t)"
    using Run_Cons.hyps(1,2) by (auto intro: edgeI)
  then show ?case
    using Run_Cons.IH by (rule reaches.reaches_step)
qed

lemma coreachable_from_run:
  assumes "run_from A p v w q vf"
  assumes "q \<in> ta_accepting A"
  shows "coreachable A p"
  using run_from_reaches[OF assms(1)] assms(2)
  by (auto simp: coreachable_def)

lemma run_from_transition_subset:
  assumes "run_from B q v w qf vf"
  assumes "ta_transitions B \<subseteq> ta_transitions A"
  shows "run_from A q v w qf vf"
  using assms
proof (induction arbitrary: A rule: run_from.induct)
  case (Run_Nil B q v)
  show ?case
    by (rule run_from.Run_Nil)
next
  case (Run_Cons t B q a d v w qf vf)
  have t_in: "t \<in> ta_transitions A"
    using Run_Cons.prems Run_Cons.hyps(1) by blast
  have tail: "run_from A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      w qf vf"
    using Run_Cons.IH[OF Run_Cons.prems] .
  then show ?case
    using Run_Cons t_in tail
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma run_from_trim_to_original:
  assumes "run_from (trim_to_accepting A) q v w qf vf"
  shows "run_from A q v w qf vf"
  using run_from_transition_subset[OF assms trim_transitions_subset] .

lemma ta_lang_trim_subset:
  "ta_lang (trim_to_accepting A) \<subseteq> ta_lang A"
proof
  fix w
  assume "w \<in> ta_lang (trim_to_accepting A)"
  then obtain q0 qf vf where
    q0_in: "q0 \<in> ta_initial (trim_to_accepting A)" and
    qf_in: "qf \<in> ta_accepting (trim_to_accepting A)" and
    run: "run_from (trim_to_accepting A) q0 zero_val w qf vf"
    by (auto simp: ta_lang_def accepts_def)
  have "run_from A q0 zero_val w qf vf"
    using run_from_trim_to_original[OF run] .
  then show "w \<in> ta_lang A"
    using q0_in qf_in by (auto simp: ta_lang_def accepts_def)
qed

lemma run_from_original_to_trim:
  assumes "run_from A q v w qf vf"
  assumes "qf \<in> ta_accepting A"
  shows "run_from (trim_to_accepting A) q v w qf vf"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  show ?case
    by (rule run_from.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  have target_coreach: "coreachable A (trans_target t)"
    using coreachable_from_run[OF Run_Cons.hyps(6) Run_Cons.prems] .
  have source_coreach: "coreachable A (trans_source t)"
  proof -
    obtain f where
      f_acc: "f \<in> ta_accepting A" and
      target_reaches: "reaches A (trans_target t) f"
      using target_coreach by (auto simp: coreachable_def)
    have "edge A (trans_source t) (trans_target t)"
      using Run_Cons.hyps(1) by (auto intro: edgeI)
    then have "reaches A (trans_source t) f"
      using target_reaches by (rule reaches.reaches_step)
    then show ?thesis
      using f_acc by (auto simp: coreachable_def)
  qed
  have t_trim: "t \<in> ta_transitions (trim_to_accepting A)"
    using Run_Cons.hyps(1) source_coreach target_coreach by auto
  show ?case
    using Run_Cons t_trim
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma ta_lang_original_subset_trim:
  "ta_lang A \<subseteq> ta_lang (trim_to_accepting A)"
proof
  fix w
  assume "w \<in> ta_lang A"
  then obtain q0 qf vf where
    q0_in: "q0 \<in> ta_initial A" and
    qf_in: "qf \<in> ta_accepting A" and
    run: "run_from A q0 zero_val w qf vf"
    by (auto simp: ta_lang_def accepts_def)
  have q0_coreach: "coreachable A q0"
    using coreachable_from_run[OF run qf_in] .
  have run_trim: "run_from (trim_to_accepting A) q0 zero_val w qf vf"
    using run_from_original_to_trim[OF run qf_in] .
  show "w \<in> ta_lang (trim_to_accepting A)"
    using q0_in q0_coreach qf_in run_trim
    by (auto simp: ta_lang_def accepts_def)
qed

theorem ta_lang_trim_to_accepting:
  "ta_lang (trim_to_accepting A) = ta_lang A"
  using ta_lang_trim_subset ta_lang_original_subset_trim by blast

theorem compile_basic_trim_correct:
  assumes "compile_basic r = Some A"
  shows "ta_lang (trim_to_accepting A) = tre_lang r"
  using compile_basic_correct[OF assms] ta_lang_trim_to_accepting[of A]
  by simp

end
