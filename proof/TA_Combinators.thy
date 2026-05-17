theory TA_Combinators
  imports TA_Semantics TRE_Semantics
begin

definition map_transition ::
  "('q => 'r) => ('q, 'a) transition => ('r, 'a) transition"
where
  "map_transition f t =
    \<lparr> trans_source = f (trans_source t),
      trans_label = trans_label t,
      trans_guards = trans_guards t,
      trans_resets = trans_resets t,
      trans_target = f (trans_target t) \<rparr>"

definition map_locations ::
  "('q => 'r) => ('q, 'a) automaton => ('r, 'a) automaton"
where
  "map_locations f A =
    \<lparr> ta_locations = f ` ta_locations A,
      ta_initial = f ` ta_initial A,
      ta_accepting = f ` ta_accepting A,
      ta_clocks = ta_clocks A,
      ta_transitions = map_transition f ` ta_transitions A \<rparr>"

definition shift_locations :: "nat => (nat, 'a) automaton => (nat, 'a) automaton" where
  "shift_locations k A = map_locations (\<lambda>q. q + k) A"

definition automaton_wf :: "('q, 'a) automaton => bool" where
  "automaton_wf A \<longleftrightarrow>
    finite (ta_locations A) \<and>
    ta_initial A \<subseteq> ta_locations A \<and>
    ta_accepting A \<subseteq> ta_locations A \<and>
    (\<forall>t \<in> ta_transitions A.
      trans_source t \<in> ta_locations A \<and>
      trans_target t \<in> ta_locations A)"

definition union_ta_raw ::
  "('q, 'a) automaton => ('q, 'a) automaton => ('q, 'a) automaton"
where
  "union_ta_raw A B =
    \<lparr> ta_locations = ta_locations A \<union> ta_locations B,
      ta_initial = ta_initial A \<union> ta_initial B,
      ta_accepting = ta_accepting A \<union> ta_accepting B,
      ta_clocks = ta_clocks A \<union> ta_clocks B,
      ta_transitions = ta_transitions A \<union> ta_transitions B \<rparr>"

definition shift_offset :: "(nat, 'a) automaton => nat" where
  "shift_offset A = Suc (Max (ta_locations A))"

definition union_ta :: "(nat, 'a) automaton => (nat, 'a) automaton => (nat, 'a) automaton" where
  "union_ta A B = union_ta_raw A (shift_locations (shift_offset A) B)"

fun compile_basic :: "'a tre => (nat, 'a) automaton option" where
  "compile_basic Empty = Some empty_ta"
| "compile_basic Epsilon = Some epsilon_ta"
| "compile_basic (Atom a) = Some (atom_ta a)"
| "compile_basic (Union r s) =
    (case compile_basic r of
       None => None
     | Some A =>
         (case compile_basic s of
            None => None
          | Some B => Some (union_ta A B)))"
| "compile_basic (Intersection r s) = None"
| "compile_basic (Concat r s) = None"
| "compile_basic (KleeneStar r) = None"
| "compile_basic (KleenePlus r) = None"
| "compile_basic (Within r I) = None"

lemma map_transition_simps [simp]:
  "trans_source (map_transition f t) = f (trans_source t)"
  "trans_label (map_transition f t) = trans_label t"
  "trans_guards (map_transition f t) = trans_guards t"
  "trans_resets (map_transition f t) = trans_resets t"
  "trans_target (map_transition f t) = f (trans_target t)"
  by (simp_all add: map_transition_def)

lemma map_locations_simps [simp]:
  "ta_locations (map_locations f A) = f ` ta_locations A"
  "ta_initial (map_locations f A) = f ` ta_initial A"
  "ta_accepting (map_locations f A) = f ` ta_accepting A"
  "ta_clocks (map_locations f A) = ta_clocks A"
  "ta_transitions (map_locations f A) = map_transition f ` ta_transitions A"
  by (simp_all add: map_locations_def)

lemma union_ta_raw_simps [simp]:
  "ta_locations (union_ta_raw A B) = ta_locations A \<union> ta_locations B"
  "ta_initial (union_ta_raw A B) = ta_initial A \<union> ta_initial B"
  "ta_accepting (union_ta_raw A B) = ta_accepting A \<union> ta_accepting B"
  "ta_clocks (union_ta_raw A B) = ta_clocks A \<union> ta_clocks B"
  "ta_transitions (union_ta_raw A B) = ta_transitions A \<union> ta_transitions B"
  by (simp_all add: union_ta_raw_def)

lemma run_from_ConsE:
  assumes "run_from A q v ((d, a) # w) qf vf"
  obtains t where
    "t \<in> ta_transitions A"
    "trans_source t = q"
    "trans_label t = a"
    "0 <= d"
    "guards_sat (delay_val d v) (trans_guards t)"
    "run_from A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      w qf vf"
  using assms
  by (cases rule: run_from.cases) auto

lemma run_from_map_locationsI:
  assumes "run_from A q v w qf vf"
  shows "run_from (map_locations f A) (f q) v w (f qf) vf"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by (rule run_from.Run_Nil)
next
  case (Run_Cons t A q a d v gs qf vf)
  have "map_transition f t \<in> ta_transitions (map_locations f A)"
    using Run_Cons.hyps(1) by simp
  then show ?case
    using Run_Cons
    by (auto intro!: run_from.Run_Cons[of "map_transition f t"]
        simp: reset_val_def)
qed

lemma run_from_map_locationsD:
  assumes inj: "inj f"
  assumes run: "run_from (map_locations f A) (f q) v w (f qf) vf"
  shows "run_from A q v w qf vf"
  using run
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case
    using inj
    by (cases rule: run_from.cases)
       (auto intro: run_from.Run_Nil dest: injD)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t' where
    t'_in: "t' \<in> ta_transitions (map_locations f A)" and
    source': "trans_source t' = f q" and
    label': "trans_label t' = a" and
    nonneg: "0 <= d" and
    guards': "guards_sat (delay_val d v) (trans_guards t')" and
    tail_run': "run_from (map_locations f A)
      (trans_target t')
      (reset_val (trans_resets t') (delay_val d v))
      xs (f qf) vf"
    using Cons.prems x_def by (auto elim: run_from_ConsE)
  obtain t where t_in: "t \<in> ta_transitions A" and t'_def: "t' = map_transition f t"
    using t'_in by auto
  have source: "trans_source t = q"
    using source' t'_def inj by (auto dest: injD)
  have tail:
    "run_from A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf"
    using Cons.IH[of "trans_target t"
        "reset_val (trans_resets t) (delay_val d v)" qf vf]
      tail_run' t'_def
    by (simp add: reset_val_def)
  show ?case
    using t_in source label' nonneg guards' t'_def tail x_def
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma accepts_map_locations_iff:
  assumes "inj f"
  shows "accepts (map_locations f A) w \<longleftrightarrow> accepts A w"
proof
  assume "accepts (map_locations f A) w"
  then obtain q0 qf vf where
    q0: "q0 \<in> ta_initial (map_locations f A)" and
    qf: "qf \<in> ta_accepting (map_locations f A)" and
    run: "run_from (map_locations f A) q0 zero_val w qf vf"
    by (auto simp: accepts_def)
  then obtain q0' qf' where
    q0_def: "q0 = f q0'" and
    q0'_in: "q0' \<in> ta_initial A" and
    qf_def: "qf = f qf'" and
    qf'_in: "qf' \<in> ta_accepting A"
    by auto
  have "run_from A q0' zero_val w qf' vf"
    using assms run q0_def qf_def
    by (simp add: run_from_map_locationsD)
  then show "accepts A w"
    using q0'_in qf'_in by (auto simp: accepts_def)
next
  assume acc: "accepts A w"
  then obtain q0 qf vf where
    q0_in: "q0 \<in> ta_initial A" and
    qf_in: "qf \<in> ta_accepting A" and
    run: "run_from A q0 zero_val w qf vf"
    by (auto simp: accepts_def)
  have run': "run_from (map_locations f A) (f q0) zero_val w (f qf) vf"
    using run_from_map_locationsI[OF run] .
  show "accepts (map_locations f A) w"
    using q0_in qf_in run' by (auto simp: accepts_def)
qed

lemma ta_lang_map_locations:
  assumes "inj f"
  shows "ta_lang (map_locations f A) = ta_lang A"
  using accepts_map_locations_iff[OF assms, of A]
  by (auto simp: ta_lang_def)

lemma automaton_wf_empty_ta [simp]:
  "automaton_wf empty_ta"
  by (simp add: automaton_wf_def)

lemma automaton_wf_epsilon_ta [simp]:
  "automaton_wf epsilon_ta"
  by (simp add: automaton_wf_def)

lemma automaton_wf_atom_ta [simp]:
  "automaton_wf (atom_ta a)"
  by (simp add: automaton_wf_def)

lemma automaton_wf_map_locations:
  assumes "automaton_wf A"
  shows "automaton_wf (map_locations f A)"
  using assms
  by (auto simp: automaton_wf_def)

lemma automaton_wf_shift_locations:
  assumes "automaton_wf A"
  shows "automaton_wf (shift_locations k A)"
  using automaton_wf_map_locations[OF assms, of "\<lambda>q. q + k"]
  by (simp add: shift_locations_def)

lemma run_from_union_raw_leftI:
  assumes "run_from A q v w qf vf"
  shows "run_from (union_ta_raw A B) q v w qf vf"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by (rule run_from.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  then show ?case
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma run_from_union_raw_rightI:
  assumes "run_from B q v w qf vf"
  shows "run_from (union_ta_raw A B) q v w qf vf"
  using assms
proof (induction rule: run_from.induct)
  case (Run_Nil A q v)
  then show ?case by (rule run_from.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  then show ?case
    by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
qed

lemma run_from_union_raw_leftD:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  assumes q_in: "q \<in> ta_locations A"
  assumes run: "run_from (union_ta_raw A B) q v w qf vf"
  shows "qf \<in> ta_locations A \<and> run_from A q v w qf vf"
  using run q_in
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case
    by (cases rule: run_from.cases)
       (auto intro: run_from.Run_Nil)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t where
    t_union: "t \<in> ta_transitions (union_ta_raw A B)" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from (union_ta_raw A B)
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf"
    using Cons.prems(1) x_def by (auto elim: run_from_ConsE)
  show ?case
  proof (cases "t \<in> ta_transitions A")
    case True
    then have target_in: "trans_target t \<in> ta_locations A"
      using wfA by (auto simp: automaton_wf_def)
    have tail: "qf \<in> ta_locations A \<and>
      run_from A
        (trans_target t)
        (reset_val (trans_resets t) (delay_val d v))
        xs qf vf"
      using Cons.IH[OF tail_run target_in] .
    then show ?thesis
      using True source label nonneg guards x_def
      by (auto intro!: run_from.Run_Cons[of t] simp: reset_val_def)
  next
    case False
    then have "t \<in> ta_transitions B"
      using t_union by auto
    then have "trans_source t \<in> ta_locations B"
      using wfB by (auto simp: automaton_wf_def)
    then have "q \<in> ta_locations B"
      using source by simp
    then show ?thesis
      using Cons.prems(2) disj by auto
  qed
qed

lemma run_from_union_raw_rightD:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  assumes q_in: "q \<in> ta_locations B"
  assumes run: "run_from (union_ta_raw A B) q v w qf vf"
  shows "qf \<in> ta_locations B \<and> run_from B q v w qf vf"
  using run q_in
proof (induction w arbitrary: q v qf vf)
  case Nil
  then show ?case
    by (cases rule: run_from.cases)
       (auto intro: run_from.Run_Nil)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain t where
    t_union: "t \<in> ta_transitions (union_ta_raw A B)" and
    source: "trans_source t = q" and
    label: "trans_label t = a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards t)" and
    tail_run: "run_from (union_ta_raw A B)
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
    then have "t \<in> ta_transitions A"
      using t_union by auto
    then have "trans_source t \<in> ta_locations A"
      using wfA by (auto simp: automaton_wf_def)
    then have "q \<in> ta_locations A"
      using source by simp
    then show ?thesis
      using Cons.prems(2) disj by auto
  qed
qed

lemma accepts_union_ta_raw_iff:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  assumes disj: "ta_locations A \<inter> ta_locations B = {}"
  shows "accepts (union_ta_raw A B) w \<longleftrightarrow> accepts A w \<or> accepts B w"
proof
  assume "accepts (union_ta_raw A B) w"
  then obtain q0 qf vf where
    q0_in: "q0 \<in> ta_initial (union_ta_raw A B)" and
    qf_in: "qf \<in> ta_accepting (union_ta_raw A B)" and
    run: "run_from (union_ta_raw A B) q0 zero_val w qf vf"
    by (auto simp: accepts_def)
  show "accepts A w \<or> accepts B w"
  proof (cases "q0 \<in> ta_initial A")
    case True
    then have q0_loc: "q0 \<in> ta_locations A"
      using wfA by (auto simp: automaton_wf_def)
    have left: "qf \<in> ta_locations A \<and> run_from A q0 zero_val w qf vf"
      using run_from_union_raw_leftD[OF wfA wfB disj q0_loc run] .
    have "qf \<in> ta_accepting A"
      using qf_in left wfB disj by (auto simp: automaton_wf_def)
    then show ?thesis
      using True left by (auto simp: accepts_def)
  next
    case False
    then have q0_B: "q0 \<in> ta_initial B"
      using q0_in by auto
    then have q0_loc: "q0 \<in> ta_locations B"
      using wfB by (auto simp: automaton_wf_def)
    have right: "qf \<in> ta_locations B \<and> run_from B q0 zero_val w qf vf"
      using run_from_union_raw_rightD[OF wfA wfB disj q0_loc run] .
    have "qf \<in> ta_accepting B"
      using qf_in right wfA disj by (auto simp: automaton_wf_def)
    then show ?thesis
      using q0_B right by (auto simp: accepts_def)
  qed
next
  assume "accepts A w \<or> accepts B w"
  then show "accepts (union_ta_raw A B) w"
  proof
    assume accA: "accepts A w"
    then obtain q0 qf vf where
      q0_in: "q0 \<in> ta_initial A" and
      qf_in: "qf \<in> ta_accepting A" and
      run: "run_from A q0 zero_val w qf vf"
      by (auto simp: accepts_def)
    have run': "run_from (union_ta_raw A B) q0 zero_val w qf vf"
      using run_from_union_raw_leftI[OF run] .
    show ?thesis
      using q0_in qf_in run' by (auto simp: accepts_def)
  next
    assume accB: "accepts B w"
    then obtain q0 qf vf where
      q0_in: "q0 \<in> ta_initial B" and
      qf_in: "qf \<in> ta_accepting B" and
      run: "run_from B q0 zero_val w qf vf"
      by (auto simp: accepts_def)
    have run': "run_from (union_ta_raw A B) q0 zero_val w qf vf"
      using run_from_union_raw_rightI[OF run] .
    show ?thesis
      using q0_in qf_in run' by (auto simp: accepts_def)
  qed
qed

lemma ta_lang_union_ta_raw:
  assumes "automaton_wf A"
  assumes "automaton_wf B"
  assumes "ta_locations A \<inter> ta_locations B = {}"
  shows "ta_lang (union_ta_raw A B) = ta_lang A \<union> ta_lang B"
  using accepts_union_ta_raw_iff[OF assms]
  by (auto simp: ta_lang_def)

lemma automaton_wf_union_ta_raw:
  assumes "automaton_wf A"
  assumes "automaton_wf B"
  shows "automaton_wf (union_ta_raw A B)"
  using assms by (auto simp: automaton_wf_def)

lemma inj_shift_nat:
  "inj (\<lambda>q::nat. q + k)"
  by (auto simp: inj_def)

lemma ta_lang_shift_locations:
  "ta_lang (shift_locations k A) = ta_lang A"
proof -
  have "ta_lang (map_locations (\<lambda>q. q + k) A) = ta_lang A"
    by (rule ta_lang_map_locations) (simp add: inj_shift_nat)
  then show ?thesis
    by (simp add: shift_locations_def)
qed

lemma disjoint_shift_locations:
  assumes wfA: "automaton_wf A"
  shows "ta_locations A \<inter>
    ta_locations (shift_locations (shift_offset A) B) = {}"
proof (rule equals0I)
  fix q
  assume q_both:
    "q \<in> ta_locations A \<inter>
      ta_locations (shift_locations (shift_offset A) B)"
  then obtain p where
    q_in: "q \<in> ta_locations A" and
    q_eq: "q = p + Suc (Max (ta_locations A))"
    by (auto simp: shift_locations_def shift_offset_def)
  have finite_A: "finite (ta_locations A)"
    using wfA by (simp add: automaton_wf_def)
  have "q <= Max (ta_locations A)"
    using Max_ge[OF finite_A q_in] .
  moreover have "Max (ta_locations A) < p + Suc (Max (ta_locations A))"
    by simp
  ultimately show False
    using q_eq by simp
qed

lemma ta_lang_union_ta:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  shows "ta_lang (union_ta A B) = ta_lang A \<union> ta_lang B"
proof -
  let ?B = "shift_locations (shift_offset A) B"
  have wfB': "automaton_wf ?B"
    using automaton_wf_shift_locations[OF wfB] .
  have disj: "ta_locations A \<inter> ta_locations ?B = {}"
    using disjoint_shift_locations[OF wfA] .
  have "ta_lang (union_ta A B) = ta_lang (union_ta_raw A ?B)"
    by (simp add: union_ta_def)
  also have "... = ta_lang A \<union> ta_lang ?B"
    using ta_lang_union_ta_raw[OF wfA wfB' disj] .
  also have "... = ta_lang A \<union> ta_lang B"
    by (simp add: ta_lang_shift_locations)
  finally show ?thesis .
qed

lemma automaton_wf_union_ta:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  shows "automaton_wf (union_ta A B)"
  using automaton_wf_union_ta_raw[OF wfA automaton_wf_shift_locations[OF wfB]]
  by (simp add: union_ta_def)

lemma compile_basic_wf:
  assumes "compile_basic r = Some A"
  shows "automaton_wf A"
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
    r_def: "compile_basic r = Some A1" and
    s_def: "compile_basic s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have "automaton_wf A1"
    using Union.IH(1)[OF r_def] .
  moreover have "automaton_wf A2"
    using Union.IH(2)[OF s_def] .
  ultimately show ?case
    by (simp add: A_def automaton_wf_union_ta)
qed auto

theorem compile_basic_correct:
  assumes "compile_basic r = Some A"
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
    r_def: "compile_basic r = Some A1" and
    s_def: "compile_basic s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_basic_wf[OF r_def] .
  have wf2: "automaton_wf A2"
    using compile_basic_wf[OF s_def] .
  have "ta_lang A = ta_lang A1 \<union> ta_lang A2"
    using ta_lang_union_ta[OF wf1 wf2]
    by (simp add: A_def)
  also have "... = tre_lang r \<union> tre_lang s"
    using Union.IH(1)[OF r_def] Union.IH(2)[OF s_def]
    by simp
  also have "... = tre_lang (Union r s)"
    by simp
  finally show ?case .
qed auto

end
