theory TA_Semantics
  imports TA_Syntax Timed_Word
begin

inductive run_from ::
  "('q, 'a) automaton => 'q => valuation => 'a timed_word => 'q => valuation => bool"
where
  Run_Nil:
    "run_from A q v [] q v"
| Run_Cons:
    "t \<in> ta_transitions A \<Longrightarrow>
     trans_source t = q \<Longrightarrow>
     trans_label t = a \<Longrightarrow>
     0 <= d \<Longrightarrow>
     guards_sat (delay_val d v) (trans_guards t) \<Longrightarrow>
     run_from A
       (trans_target t)
       (reset_val (trans_resets t) (delay_val d v))
       w qf vf \<Longrightarrow>
     run_from A q v ((d, a) # w) qf vf"

definition accepts :: "('q, 'a) automaton => 'a timed_word => bool" where
  "accepts A w \<longleftrightarrow>
    (\<exists>q0 qf vf.
      q0 \<in> ta_initial A \<and>
      qf \<in> ta_accepting A \<and>
      run_from A q0 zero_val w qf vf)"

definition ta_lang :: "('q, 'a) automaton => 'a timed_word set" where
  "ta_lang A = {w. accepts A w}"

lemma accepts_iff [simp]:
  "w \<in> ta_lang A \<longleftrightarrow> accepts A w"
  by (simp add: ta_lang_def)

lemma duration_singleton [simp]:
  "duration [(d, a)] = d"
  by simp

lemma wellformed_timed_word_singleton [simp]:
  "wellformed_timed_word [(d, a)] \<longleftrightarrow> 0 <= d"
  by simp

lemma run_from_no_transition_from_source_iff:
  assumes no_out: "\<And>t. t \<in> ta_transitions A \<Longrightarrow> trans_source t = q \<Longrightarrow> False"
  shows "run_from A q v w q' v' \<longleftrightarrow> w = [] \<and> q' = q \<and> v' = v"
proof
  assume run: "run_from A q v w q' v'"
  then show "w = [] \<and> q' = q \<and> v' = v"
  proof (cases rule: run_from.cases)
    case Run_Nil
    then show ?thesis by simp
  next
    case (Run_Cons t a d w)
    from no_out[OF Run_Cons(2) Run_Cons(3)] show ?thesis
      by simp
  qed
next
  assume "w = [] \<and> q' = q \<and> v' = v"
  then show "run_from A q v w q' v'"
    by (simp add: run_from.Run_Nil)
qed

lemma run_from_no_transitions_iff:
  assumes "ta_transitions A = {}"
  shows "run_from A q v w q' v' \<longleftrightarrow> w = [] \<and> q' = q \<and> v' = v"
  using assms run_from_no_transition_from_source_iff[of A q v w q' v']
  by auto

lemma atom_ta_no_transition_from_one:
  assumes "t \<in> ta_transitions (atom_ta a)"
  shows "trans_source t \<noteq> 1"
  using assms by auto

lemma run_from_atom_source_iff:
  "run_from (atom_ta a) 0 v w qf vf \<longleftrightarrow>
    (w = [] \<and> qf = 0 \<and> vf = v) \<or>
    (\<exists>d. 0 <= d \<and> w = [(d, a)] \<and> qf = 1 \<and> vf = delay_val d v)"
proof
  assume run: "run_from (atom_ta a) 0 v w qf vf"
  then show
    "(w = [] \<and> qf = 0 \<and> vf = v) \<or>
     (\<exists>d. 0 <= d \<and> w = [(d, a)] \<and> qf = 1 \<and> vf = delay_val d v)"
  proof (cases rule: run_from.cases)
    case Run_Nil
    then show ?thesis by simp
  next
    case (Run_Cons t b d w')
    have t_eq: "t = atom_transition a"
      using Run_Cons(2, 3)
      by auto
    have no_out_one:
      "\<And>t. t \<in> ta_transitions (atom_ta a) \<Longrightarrow> trans_source t = 1 \<Longrightarrow> False"
      by auto
    have tail_run:
      "run_from (atom_ta a) 1 (delay_val d v) w' qf vf"
      using Run_Cons(7) t_eq by simp
    have tail_iff:
      "run_from (atom_ta a) 1 (delay_val d v) w' qf vf \<longleftrightarrow>
        w' = [] \<and> qf = 1 \<and> vf = delay_val d v"
      by (rule run_from_no_transition_from_source_iff) auto
    have tail:
      "w' = [] \<and> qf = 1 \<and> vf = delay_val d v"
      using tail_run tail_iff by simp
    show ?thesis
      using Run_Cons t_eq tail
      by auto
  qed
next
  assume cases:
    "(w = [] \<and> qf = 0 \<and> vf = v) \<or>
     (\<exists>d. 0 <= d \<and> w = [(d, a)] \<and> qf = 1 \<and> vf = delay_val d v)"
  then show "run_from (atom_ta a) 0 v w qf vf"
  proof
    assume "w = [] \<and> qf = 0 \<and> vf = v"
    then show ?thesis by (simp add: run_from.Run_Nil)
  next
    assume "\<exists>d. 0 <= d \<and> w = [(d, a)] \<and> qf = 1 \<and> vf = delay_val d v"
    then obtain d where
      d_nonneg: "0 <= d" and
      w_def: "w = [(d, a)]" and
      qf_def: "qf = 1" and
      vf_def: "vf = delay_val d v"
      by auto
    have step:
      "run_from (atom_ta a) 0 v [(d, a)] 1 (delay_val d v)"
      by (rule run_from.Run_Cons[of "atom_transition a"])
         (auto intro: run_from.Run_Nil simp: d_nonneg)
    then show ?thesis
      by (simp add: w_def qf_def vf_def)
  qed
qed

lemma accepts_empty_ta_iff [simp]:
  "\<not> accepts empty_ta w"
  by (auto simp: accepts_def)

lemma accepts_epsilon_ta_iff [simp]:
  "accepts epsilon_ta w \<longleftrightarrow> w = []"
  by (auto simp: accepts_def run_from_no_transitions_iff)

lemma accepts_atom_ta_iff [simp]:
  "accepts (atom_ta a) w \<longleftrightarrow> (\<exists>d. 0 <= d \<and> w = [(d, a)])"
proof
  assume "accepts (atom_ta a) w"
  then show "\<exists>d. 0 <= d \<and> w = [(d, a)]"
    by (auto simp: accepts_def run_from_atom_source_iff)
next
  assume "\<exists>d. 0 <= d \<and> w = [(d, a)]"
  then obtain d where d_nonneg: "0 <= d" and w_def: "w = [(d, a)]"
    by auto
  have "run_from (atom_ta a) 0 zero_val [(d, a)] 1 (delay_val d zero_val)"
    using d_nonneg by (simp add: run_from_atom_source_iff)
  then show "accepts (atom_ta a) w"
    by (auto simp: accepts_def w_def)
qed

lemma ta_lang_empty_ta [simp]:
  "ta_lang empty_ta = {}"
  by (auto simp: ta_lang_def)

lemma ta_lang_epsilon_ta [simp]:
  "ta_lang epsilon_ta = {[]}"
  by (auto simp: ta_lang_def)

lemma ta_lang_atom_ta [simp]:
  "ta_lang (atom_ta a) = {w. \<exists>d. 0 <= d \<and> w = [(d, a)]}"
  by (auto simp: ta_lang_def)

lemma run_from_wellformed:
  assumes "run_from A q v w q' v'"
  shows "wellformed_timed_word w"
  using assms
  by (induction rule: run_from.induct) simp_all

lemma accepts_wellformed:
  assumes "accepts A w"
  shows "wellformed_timed_word w"
  using assms run_from_wellformed
  by (auto simp: accepts_def)

lemma ta_lang_wellformed:
  assumes "w \<in> ta_lang A"
  shows "wellformed_timed_word w"
  using assms accepts_wellformed by simp

end
