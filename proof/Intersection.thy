theory Intersection
  imports Label_Algebra "HOL-Library.Nat_Bijection"
begin

fun map_guard_clock :: "(clock => clock) => guard => guard" where
  "map_guard_clock f (Clock_In c I) = Clock_In (f c) I"

definition map_transition_clocks ::
  "(clock => clock) => ('q, 'a) transition => ('q, 'a) transition"
where
  "map_transition_clocks f t =
    t\<lparr> trans_guards := map (map_guard_clock f) (trans_guards t),
       trans_resets := f ` trans_resets t \<rparr>"

definition map_clocks ::
  "(clock => clock) => ('q, 'a) automaton => ('q, 'a) automaton"
where
  "map_clocks f A =
    \<lparr> ta_locations = ta_locations A,
      ta_initial = ta_initial A,
      ta_accepting = ta_accepting A,
      ta_clocks = f ` ta_clocks A,
      ta_transitions = map_transition_clocks f ` ta_transitions A \<rparr>"

definition clock_shift_offset :: "('q, 'a) automaton => nat" where
  "clock_shift_offset A = Suc (Max (ta_clocks A))"

definition shift_clocks :: "nat => ('q, 'a) automaton => ('q, 'a) automaton" where
  "shift_clocks k A = map_clocks (\<lambda>c. c + k) A"

definition product_transition ::
  "(nat, 'a) transition => (nat, 'a) transition => 'a =>
    (nat * nat, 'a) transition"
where
  "product_transition t1 t2 l =
    \<lparr> trans_source = (trans_source t1, trans_source t2),
      trans_label = l,
      trans_guards = trans_guards t1 @ trans_guards t2,
      trans_resets = trans_resets t1 \<union> trans_resets t2,
      trans_target = (trans_target t1, trans_target t2) \<rparr>"

context label_algebra
begin

definition product_ta_raw ::
  "(nat, 'label) automaton => (nat, 'label) automaton =>
    (nat * nat, 'label) automaton"
where
  "product_ta_raw A B =
    \<lparr> ta_locations = ta_locations A \<times> ta_locations B,
      ta_initial = ta_initial A \<times> ta_initial B,
      ta_accepting = ta_accepting A \<times> ta_accepting B,
      ta_clocks = ta_clocks A \<union> ta_clocks B,
      ta_transitions =
        {product_transition t1 t2 l | t1 t2 l.
          t1 \<in> ta_transitions A \<and>
          t2 \<in> ta_transitions B \<and>
          label_intersect (trans_label t1) (trans_label t2) = Some l} \<rparr>"

end

definition product_ta ::
  "(nat, 'a) automaton => (nat, 'a) automaton =>
    (nat * nat, 'a) automaton"
where
  "product_ta A B =
    equality_label_algebra.product_ta_raw A
      (shift_clocks (clock_shift_offset A) B)"

fun compile_fragment :: "'a tre => (nat, 'a) automaton option" where
  "compile_fragment Empty = Some empty_ta"
| "compile_fragment Epsilon = Some epsilon_ta"
| "compile_fragment (Atom a) = Some (atom_ta a)"
| "compile_fragment (Union r s) =
    (case compile_fragment r of
       None => None
     | Some A =>
         (case compile_fragment s of
            None => None
          | Some B => Some (union_ta A B)))"
| "compile_fragment (Intersection r s) =
    (case compile_fragment r of
       None => None
	     | Some A =>
	         (case compile_fragment s of
	            None => None
	          | Some B =>
	              Some (map_locations prod_encode (product_ta A B))))"
| "compile_fragment (Concat r s) =
    (case compile_fragment r of
       None => None
     | Some A =>
         (case compile_fragment s of
            None => None
          | Some B => Some (concat_ta A B)))"
| "compile_fragment (KleeneStar r) =
    (case compile_fragment r of
       None => None
     | Some A => Some (star_ta A))"
| "compile_fragment (KleenePlus r) =
    (case compile_fragment r of
       None => None
     | Some A => Some (plus_ta A))"
| "compile_fragment (Within r I) =
    (case compile_fragment r of
       None => None
     | Some A => Some (time_restrict_ta A I))"

lemma map_guard_clock_simps [simp]:
  "guard_sat v (map_guard_clock f (Clock_In c I)) =
    interval_mem (v (f c)) I"
  by simp

lemma map_transition_clocks_simps [simp]:
  "trans_source (map_transition_clocks f t) = trans_source t"
  "trans_label (map_transition_clocks f t) = trans_label t"
  "trans_guards (map_transition_clocks f t) =
    map (map_guard_clock f) (trans_guards t)"
  "trans_resets (map_transition_clocks f t) = f ` trans_resets t"
  "trans_target (map_transition_clocks f t) = trans_target t"
  by (simp_all add: map_transition_clocks_def)

lemma product_transition_simps [simp]:
  "trans_source (product_transition t1 t2 l) =
    (trans_source t1, trans_source t2)"
  "trans_label (product_transition t1 t2 l) = l"
  "trans_guards (product_transition t1 t2 l) =
    trans_guards t1 @ trans_guards t2"
  "trans_resets (product_transition t1 t2 l) =
    trans_resets t1 \<union> trans_resets t2"
  "trans_target (product_transition t1 t2 l) =
    (trans_target t1, trans_target t2)"
  by (simp_all add: product_transition_def)

lemma guards_sat_append [simp]:
  "guards_sat v (gs1 @ gs2) \<longleftrightarrow>
    guards_sat v gs1 \<and> guards_sat v gs2"
  by (simp add: guards_sat_def list_all_append)

lemma guards_clocks_append [simp]:
  "guards_clocks (gs1 @ gs2) =
    guards_clocks gs1 \<union> guards_clocks gs2"
  by (auto simp: guards_clocks_def)

lemma map_clocks_simps [simp]:
  "ta_locations (map_clocks f A) = ta_locations A"
  "ta_initial (map_clocks f A) = ta_initial A"
  "ta_accepting (map_clocks f A) = ta_accepting A"
  "ta_clocks (map_clocks f A) = f ` ta_clocks A"
  "ta_transitions (map_clocks f A) =
    map_transition_clocks f ` ta_transitions A"
  by (simp_all add: map_clocks_def)

lemma guards_sat_map_guard_clock:
  assumes inj: "inj_on f C"
  assumes clocks: "guards_clocks gs \<subseteq> C"
  assumes agree: "\<And>c. c \<in> C \<Longrightarrow> v' (f c) = v c"
  shows "guards_sat v' (map (map_guard_clock f) gs) =
    guards_sat v gs"
  using clocks
proof (induction gs)
  case Nil
  then show ?case by simp
next
  case (Cons g gs)
  then show ?case
    using agree by (cases g) (auto simp: guards_clocks_def)
qed

lemma clock_wf_transition_bounds:
  assumes "clock_wf A"
  assumes "t \<in> ta_transitions A"
  shows "trans_resets t \<subseteq> ta_clocks A"
    and "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
  using assms by (auto simp: clock_wf_def)

lemma guards_clocks_map_guard_clock_subset:
  assumes "guards_clocks gs \<subseteq> C"
  shows "guards_clocks (map (map_guard_clock f) gs) \<subseteq> f ` C"
  using assms
proof (induction gs)
  case Nil
  then show ?case by (simp add: guards_clocks_def)
next
  case (Cons g gs)
  then show ?case
    by (cases g) (auto simp: guards_clocks_def)
qed

lemma automaton_wf_map_clocks [simp]:
  assumes "automaton_wf A"
  shows "automaton_wf (map_clocks f A)"
  using assms by (auto simp: automaton_wf_def)

lemma clock_wf_map_clocks:
  assumes "clock_wf A"
  shows "clock_wf (map_clocks f A)"
proof -
  have finite_clocks: "finite (f ` ta_clocks A)"
    using assms by (simp add: clock_wf_def)
  have transition_clocks:
    "trans_resets mt \<subseteq> f ` ta_clocks A \<and>
     guards_clocks (trans_guards mt) \<subseteq> f ` ta_clocks A"
    if mt_in: "mt \<in> ta_transitions (map_clocks f A)"
    for mt
  proof -
    obtain t where t_in: "t \<in> ta_transitions A" and
      mt_def: "mt = map_transition_clocks f t"
      using mt_in by auto
    have resets: "trans_resets t \<subseteq> ta_clocks A"
      using clock_wf_transition_bounds(1)[OF assms t_in] .
    have guards: "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
      using clock_wf_transition_bounds(2)[OF assms t_in] .
    have "guards_clocks (map (map_guard_clock f) (trans_guards t))
      \<subseteq> f ` ta_clocks A"
      using guards_clocks_map_guard_clock_subset[OF guards] .
    then show ?thesis
      using resets mt_def by auto
  qed
  show ?thesis
    using finite_clocks transition_clocks by (auto simp: clock_wf_def)
qed

lemma automaton_wf_shift_clocks [simp]:
  assumes "automaton_wf A"
  shows "automaton_wf (shift_clocks k A)"
  using assms by (simp add: shift_clocks_def)

lemma clock_wf_map_locations [simp]:
  assumes "clock_wf A"
  shows "clock_wf (map_locations f A)"
  using assms by (auto simp: clock_wf_def)

lemma clock_wf_shift_clocks:
  assumes "clock_wf A"
  shows "clock_wf (shift_clocks k A)"
  using clock_wf_map_clocks[OF assms] by (simp add: shift_clocks_def)

lemma inj_on_shift_clock [simp]:
  "inj_on (\<lambda>c::nat. c + k) C"
  by (auto simp: inj_on_def)

lemma disjoint_shift_clocks:
  assumes cwf: "clock_wf A"
  shows "ta_clocks A \<inter>
    ta_clocks (shift_clocks (clock_shift_offset A) B) = {}"
proof (rule equals0I)
  fix c
  assume c_in: "c \<in> ta_clocks A \<inter>
    ta_clocks (shift_clocks (clock_shift_offset A) B)"
  then obtain b where
    c_A: "c \<in> ta_clocks A" and
    c_def: "c = b + Suc (Max (ta_clocks A))"
    by (auto simp: shift_clocks_def clock_shift_offset_def)
  have finite_A: "finite (ta_clocks A)"
    using cwf by (simp add: clock_wf_def)
  have "c <= Max (ta_clocks A)"
    using Max_ge[OF finite_A c_A] .
  moreover have "Max (ta_clocks A) < b + Suc (Max (ta_clocks A))"
    by simp
  ultimately show False
    using c_def by simp
qed

context label_algebra
begin

lemma run_from_l_map_clocksI:
  assumes run: "run_from_l A q v w qf vf"
  assumes cwf: "clock_wf A"
  assumes inj: "inj_on f (ta_clocks A)"
  assumes agree: "\<And>c. c \<in> ta_clocks A \<Longrightarrow> v' (f c) = v c"
  shows "\<exists>vf'. run_from_l (map_clocks f A) q v' w qf vf' \<and>
    (\<forall>c \<in> ta_clocks A. vf' (f c) = vf c)"
  using run cwf inj agree
proof (induction arbitrary: v' rule: run_from_l.induct)
  case (Run_Nil A q v)
  then show ?case
    by (auto intro: run_from_l.Run_Nil)
next
  case (Run_Cons t A q a d v w qf vf)
  have bounds:
    "trans_resets t \<subseteq> ta_clocks A"
    "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
  proof -
    have all: "\<forall>u \<in> ta_transitions A.
      trans_resets u \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards u) \<subseteq> ta_clocks A"
      using Run_Cons.prems(1) by (simp add: clock_wf_def)
    show "trans_resets t \<subseteq> ta_clocks A"
      using all Run_Cons.hyps(1) by simp
    show "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
      using all Run_Cons.hyps(1) by simp
  qed
  have guard_agree:
    "\<And>c. c \<in> ta_clocks A \<Longrightarrow>
      delay_val d v' (f c) = delay_val d v c"
    using Run_Cons.prems(3) by simp
  have guards':
    "guards_sat (delay_val d v')
      (trans_guards (map_transition_clocks f t))"
  proof -
    have "guards_sat (delay_val d v')
        (map (map_guard_clock f) (trans_guards t)) =
      guards_sat (delay_val d v) (trans_guards t)"
    proof (rule guards_sat_map_guard_clock)
      show "inj_on f (ta_clocks A)"
        using Run_Cons.prems(2) .
    next
      show "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
        using bounds(2) .
    next
      fix c
      assume "c \<in> ta_clocks A"
      then show "delay_val d v' (f c) = delay_val d v c"
        by (rule guard_agree)
    qed
    then show ?thesis
      using Run_Cons.hyps(5) by simp
  qed
  have reset_agree:
    "\<And>c. c \<in> ta_clocks A \<Longrightarrow>
      reset_val (f ` trans_resets t) (delay_val d v') (f c) =
      reset_val (trans_resets t) (delay_val d v) c"
  proof -
    fix c
    assume c_in: "c \<in> ta_clocks A"
    have "f c \<in> f ` trans_resets t \<longleftrightarrow> c \<in> trans_resets t"
      using Run_Cons.prems(2) c_in bounds(1) by (auto simp: inj_on_def)
    then show "reset_val (f ` trans_resets t) (delay_val d v') (f c) =
      reset_val (trans_resets t) (delay_val d v) c"
      using Run_Cons.prems(3) c_in by auto
  qed
  obtain vf' where
    tail: "run_from_l (map_clocks f A)
      (trans_target t)
      (reset_val (f ` trans_resets t) (delay_val d v'))
      w qf vf'" and
    final_agree: "\<forall>c \<in> ta_clocks A. vf' (f c) = vf c"
    using Run_Cons.IH[OF Run_Cons.prems(1) Run_Cons.prems(2) reset_agree]
    by (auto simp: reset_val_def delay_val_def)
  have t_in:
    "map_transition_clocks f t \<in> ta_transitions (map_clocks f A)"
    using Run_Cons.hyps(1) by simp
  have run':
    "run_from_l (map_clocks f A) q v' ((d, a) # w) qf vf'"
    using t_in Run_Cons.hyps tail guards'
    by (auto intro!: run_from_l.Run_Cons[of "map_transition_clocks f t"])
  then show ?case
    using final_agree by auto
qed

lemma run_from_l_map_clocksD:
  assumes run: "run_from_l (map_clocks f A) q v' w qf vf'"
  assumes cwf: "clock_wf A"
  assumes inj: "inj_on f (ta_clocks A)"
  assumes agree: "\<And>c. c \<in> ta_clocks A \<Longrightarrow> v' (f c) = v c"
  shows "\<exists>vf. run_from_l A q v w qf vf \<and>
    (\<forall>c \<in> ta_clocks A. vf' (f c) = vf c)"
  using run cwf inj agree
proof (induction w arbitrary: q v v' qf vf')
  case Nil
  then show ?case
    by (cases rule: run_from_l.cases) (auto intro: run_from_l.Run_Nil)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain mt where
    mt_in: "mt \<in> ta_transitions (map_clocks f A)" and
    source: "trans_source mt = q" and
    match: "event_matches (trans_label mt) a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v') (trans_guards mt)" and
    tail_run: "run_from_l (map_clocks f A)
      (trans_target mt)
      (reset_val (trans_resets mt) (delay_val d v'))
      xs qf vf'"
    using Cons.prems(1) x_def by (auto elim: run_from_l_ConsE)
  obtain t where t_in: "t \<in> ta_transitions A" and mt_def: "mt = map_transition_clocks f t"
    using mt_in by auto
  have bounds:
    "trans_resets t \<subseteq> ta_clocks A"
    "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
  proof -
    have all: "\<forall>u \<in> ta_transitions A.
      trans_resets u \<subseteq> ta_clocks A \<and>
      guards_clocks (trans_guards u) \<subseteq> ta_clocks A"
      using Cons.prems(2) by (simp add: clock_wf_def)
    show "trans_resets t \<subseteq> ta_clocks A"
      using all t_in by simp
    show "guards_clocks (trans_guards t) \<subseteq> ta_clocks A"
      using all t_in by simp
  qed
  have guard_agree:
    "\<And>c. c \<in> ta_clocks A \<Longrightarrow>
      delay_val d v' (f c) = delay_val d v c"
    using Cons.prems(4) by simp
    have guards_old:
      "guards_sat (delay_val d v) (trans_guards t)"
  proof -
    have "guards_sat (delay_val d v')
        (map (map_guard_clock f) (trans_guards t)) =
      guards_sat (delay_val d v) (trans_guards t)"
      by (rule guards_sat_map_guard_clock[where C="ta_clocks A"])
         (use Cons.prems(3) bounds(2) guard_agree in auto)
    then show ?thesis
      using guards mt_def by simp
  qed
  have reset_agree:
    "\<And>c. c \<in> ta_clocks A \<Longrightarrow>
      reset_val (trans_resets mt) (delay_val d v') (f c) =
      reset_val (trans_resets t) (delay_val d v) c"
  proof -
    fix c
    assume c_in: "c \<in> ta_clocks A"
    have "f c \<in> f ` trans_resets t \<longleftrightarrow> c \<in> trans_resets t"
      using inj c_in bounds(1) by (auto simp: inj_on_def)
    then show "reset_val (trans_resets mt) (delay_val d v') (f c) =
      reset_val (trans_resets t) (delay_val d v) c"
      using Cons.prems(4) c_in mt_def by auto
  qed
  obtain vf where
    tail: "run_from_l A
      (trans_target t)
      (reset_val (trans_resets t) (delay_val d v))
      xs qf vf" and
    final_agree: "\<forall>c \<in> ta_clocks A. vf' (f c) = vf c"
    using Cons.IH[OF tail_run Cons.prems(2) Cons.prems(3) reset_agree] mt_def
    by (auto simp: reset_val_def)
  have run_old:
    "run_from_l A q v ((d, a) # xs) qf vf"
    using t_in source match nonneg guards_old tail mt_def
    by (auto intro!: run_from_l.Run_Cons[of t])
  then show ?case
    using x_def final_agree by auto
qed

lemma ta_lang_l_map_clocks:
  assumes cwf: "clock_wf A"
  assumes inj: "inj_on f (ta_clocks A)"
  shows "ta_lang_l (map_clocks f A) = ta_lang_l A"
proof
  show "ta_lang_l (map_clocks f A) \<subseteq> ta_lang_l A"
  proof
    fix w
    assume "w \<in> ta_lang_l (map_clocks f A)"
    then obtain q0 qf vf where
      q0: "q0 \<in> ta_initial A" and
      qf: "qf \<in> ta_accepting A" and
      run: "run_from_l (map_clocks f A) q0 zero_val w qf vf"
      by (auto simp: accepts_l_def ta_lang_l_def)
    have agree0: "\<And>c. c \<in> ta_clocks A \<Longrightarrow> zero_val (f c) = zero_val c"
      by simp
    obtain vf0 where "run_from_l A q0 zero_val w qf vf0"
      using run_from_l_map_clocksD[OF run cwf inj agree0]
      by (auto simp: zero_val_def)
    then show "w \<in> ta_lang_l A"
      using q0 qf by (auto simp: accepts_l_def ta_lang_l_def)
  qed
next
  show "ta_lang_l A \<subseteq> ta_lang_l (map_clocks f A)"
  proof
    fix w
    assume "w \<in> ta_lang_l A"
    then obtain q0 qf vf where
      q0: "q0 \<in> ta_initial A" and
      qf: "qf \<in> ta_accepting A" and
      run: "run_from_l A q0 zero_val w qf vf"
      by (auto simp: accepts_l_def ta_lang_l_def)
    have agree0: "\<And>c. c \<in> ta_clocks A \<Longrightarrow> zero_val (f c) = zero_val c"
      by simp
    obtain vf' where "run_from_l (map_clocks f A) q0 zero_val w qf vf'"
      using run_from_l_map_clocksI[OF run cwf inj agree0]
      by (auto simp: zero_val_def)
    then show "w \<in> ta_lang_l (map_clocks f A)"
      using q0 qf by (auto simp: accepts_l_def ta_lang_l_def)
  qed
qed

lemma ta_lang_l_shift_clocks:
  assumes "clock_wf A"
  shows "ta_lang_l (shift_clocks k A) = ta_lang_l A"
  using ta_lang_l_map_clocks[OF assms inj_on_shift_clock]
  by (simp add: shift_clocks_def)

lemma product_ta_raw_simps [simp]:
  "ta_locations (product_ta_raw A B) = ta_locations A \<times> ta_locations B"
  "ta_initial (product_ta_raw A B) = ta_initial A \<times> ta_initial B"
  "ta_accepting (product_ta_raw A B) = ta_accepting A \<times> ta_accepting B"
  "ta_clocks (product_ta_raw A B) = ta_clocks A \<union> ta_clocks B"
  by (simp_all add: product_ta_raw_def)

lemma product_ta_raw_transitions:
  "ta_transitions (product_ta_raw A B) =
    {product_transition t1 t2 l | t1 t2 l.
      t1 \<in> ta_transitions A \<and>
      t2 \<in> ta_transitions B \<and>
      label_intersect (trans_label t1) (trans_label t2) = Some l}"
  by (simp add: product_ta_raw_def)

lemma product_transitionE:
  assumes "t \<in> ta_transitions (product_ta_raw A B)"
  obtains t1 t2 l where
    "t1 \<in> ta_transitions A"
    "t2 \<in> ta_transitions B"
    "label_intersect (trans_label t1) (trans_label t2) = Some l"
    "t = product_transition t1 t2 l"
  using assms by (auto simp: product_ta_raw_transitions)

lemma label_intersect_match_left:
  assumes "label_intersect l1 l2 = Some l"
  assumes "event_matches l e"
  shows "event_matches l1 e"
  using label_intersect_Some[OF assms(1)] assms(2)
  by (auto simp: event_matches_def)

lemma label_intersect_match_right:
  assumes "label_intersect l1 l2 = Some l"
  assumes "event_matches l e"
  shows "event_matches l2 e"
  using label_intersect_Some[OF assms(1)] assms(2)
  by (auto simp: event_matches_def)

lemma reset_union_agree_left:
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes tA: "t1 \<in> ta_transitions A"
  assumes tB: "t2 \<in> ta_transitions B"
  shows "agree_on (ta_clocks A)
    (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
    (reset_val (trans_resets t1) (delay_val d v))"
proof -
  have rB: "trans_resets t2 \<subseteq> ta_clocks B"
    using clock_wf_transition_bounds(1)[OF cwfB tB] .
  show ?thesis
    using disj rB by (auto simp: agree_on_def)
qed

lemma reset_union_agree_right:
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes tA: "t1 \<in> ta_transitions A"
  assumes tB: "t2 \<in> ta_transitions B"
  shows "agree_on (ta_clocks B)
    (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
    (reset_val (trans_resets t2) (delay_val d v))"
proof -
  have rA: "trans_resets t1 \<subseteq> ta_clocks A"
    using clock_wf_transition_bounds(1)[OF cwfA tA] .
  show ?thesis
    using disj rA by (auto simp: agree_on_def)
qed

lemma run_from_product_left:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes run: "run_from_l (product_ta_raw A B) (p1, p2) v w (q1, q2) vf"
  shows "\<exists>vfA. run_from_l A p1 v w q1 vfA"
  using run
proof (induction w arbitrary: p1 p2 v q1 q2 vf)
  case Nil
  then show ?case
    by (cases rule: run_from_l.cases) (auto intro: run_from_l.Run_Nil)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain pt where
    pt_in: "pt \<in> ta_transitions (product_ta_raw A B)" and
    source: "trans_source pt = (p1, p2)" and
    match: "event_matches (trans_label pt) a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards pt)" and
    tail_run: "run_from_l (product_ta_raw A B)
      (trans_target pt)
      (reset_val (trans_resets pt) (delay_val d v))
      xs (q1, q2) vf"
    using Cons.prems x_def by (auto elim: run_from_l_ConsE)
  obtain t1 t2 l where
    t1_in: "t1 \<in> ta_transitions A" and
    t2_in: "t2 \<in> ta_transitions B" and
    lint: "label_intersect (trans_label t1) (trans_label t2) = Some l" and
    pt_def: "pt = product_transition t1 t2 l"
    using product_transitionE[OF pt_in] by auto
  have tail_run_pair: "run_from_l (product_ta_raw A B)
      (trans_target t1, trans_target t2)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      xs (q1, q2) vf"
    using tail_run pt_def by simp
  obtain vf_tail where tail_left:
    "run_from_l A (trans_target t1)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      xs q1 vf_tail"
    using Cons.IH[OF tail_run_pair] by (auto simp: reset_val_def)
  have start_agree:
    "agree_on (ta_clocks A)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      (reset_val (trans_resets t1) (delay_val d v))"
    using reset_union_agree_left[OF disj cwfA cwfB t1_in t2_in] .
  obtain vfA where tail_left':
    "run_from_l A (trans_target t1)
      (reset_val (trans_resets t1) (delay_val d v)) xs q1 vfA"
    using run_from_l_agree_on[OF cwfA tail_left start_agree] by auto
  have match_left: "event_matches (trans_label t1) a"
    using label_intersect_match_left[OF lint] match pt_def by simp
  have guards_left: "guards_sat (delay_val d v) (trans_guards t1)"
    using guards pt_def by simp
  have run_left:
    "run_from_l A p1 v ((d, a) # xs) q1 vfA"
    using t1_in source pt_def match_left nonneg guards_left tail_left'
    by (auto intro!: run_from_l.Run_Cons[of t1])
  then show ?case
    using x_def by auto
qed

lemma run_from_product_right:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes run: "run_from_l (product_ta_raw A B) (p1, p2) v w (q1, q2) vf"
  shows "\<exists>vfB. run_from_l B p2 v w q2 vfB"
  using run
proof (induction w arbitrary: p1 p2 v q1 q2 vf)
  case Nil
  then show ?case
    by (cases rule: run_from_l.cases) (auto intro: run_from_l.Run_Nil)
next
  case (Cons x xs)
  obtain d a where x_def: "x = (d, a)"
    by (cases x)
  obtain pt where
    pt_in: "pt \<in> ta_transitions (product_ta_raw A B)" and
    source: "trans_source pt = (p1, p2)" and
    match: "event_matches (trans_label pt) a" and
    nonneg: "0 <= d" and
    guards: "guards_sat (delay_val d v) (trans_guards pt)" and
    tail_run: "run_from_l (product_ta_raw A B)
      (trans_target pt)
      (reset_val (trans_resets pt) (delay_val d v))
      xs (q1, q2) vf"
    using Cons.prems x_def by (auto elim: run_from_l_ConsE)
  obtain t1 t2 l where
    t1_in: "t1 \<in> ta_transitions A" and
    t2_in: "t2 \<in> ta_transitions B" and
    lint: "label_intersect (trans_label t1) (trans_label t2) = Some l" and
    pt_def: "pt = product_transition t1 t2 l"
    using product_transitionE[OF pt_in] by auto
  have tail_run_pair: "run_from_l (product_ta_raw A B)
      (trans_target t1, trans_target t2)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      xs (q1, q2) vf"
    using tail_run pt_def by simp
  obtain vf_tail where tail_right:
    "run_from_l B (trans_target t2)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      xs q2 vf_tail"
    using Cons.IH[OF tail_run_pair] by (auto simp: reset_val_def)
  have start_agree:
    "agree_on (ta_clocks B)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      (reset_val (trans_resets t2) (delay_val d v))"
    using reset_union_agree_right[OF disj cwfA cwfB t1_in t2_in] .
  obtain vfB where tail_right':
    "run_from_l B (trans_target t2)
      (reset_val (trans_resets t2) (delay_val d v)) xs q2 vfB"
    using run_from_l_agree_on[OF cwfB tail_right start_agree] by auto
  have match_right: "event_matches (trans_label t2) a"
    using label_intersect_match_right[OF lint] match pt_def by simp
  have guards_right: "guards_sat (delay_val d v) (trans_guards t2)"
    using guards pt_def by simp
  have run_right:
    "run_from_l B p2 v ((d, a) # xs) q2 vfB"
    using t2_in source pt_def match_right nonneg guards_right tail_right'
    by (auto intro!: run_from_l.Run_Cons[of t2])
  then show ?case
    using x_def by auto
qed

lemma product_ta_raw_sound:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes "w \<in> ta_lang_l (product_ta_raw A B)"
  shows "w \<in> ta_lang_l A \<inter> ta_lang_l B"
proof -
  obtain p0 p1 q0 q1 vf where
    init: "(p0, p1) \<in> ta_initial (product_ta_raw A B)" and
    acc: "(q0, q1) \<in> ta_accepting (product_ta_raw A B)" and
    run: "run_from_l (product_ta_raw A B) (p0, p1) zero_val w (q0, q1) vf"
    using assms(4) by (auto simp: accepts_l_def ta_lang_l_def)
  obtain vfA where "run_from_l A p0 zero_val w q0 vfA"
    using run_from_product_left[OF cwfA cwfB disj run] by auto
  moreover obtain vfB where "run_from_l B p1 zero_val w q1 vfB"
    using run_from_product_right[OF cwfA cwfB disj run] by auto
  ultimately show ?thesis
    using init acc by (auto simp: accepts_l_def ta_lang_l_def)
qed

lemma agree_reset_union_left:
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes tA: "t1 \<in> ta_transitions A"
  assumes tB: "t2 \<in> ta_transitions B"
  assumes agree: "agree_on (ta_clocks A) v vA"
  shows "agree_on (ta_clocks A)
    (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
    (reset_val (trans_resets t1) (delay_val d vA))"
proof -
  have rB: "trans_resets t2 \<subseteq> ta_clocks B"
    using clock_wf_transition_bounds(1)[OF cwfB tB] .
  show ?thesis
    using disj rB agree by (auto simp: agree_on_def)
qed

lemma agree_reset_union_right:
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes tA: "t1 \<in> ta_transitions A"
  assumes tB: "t2 \<in> ta_transitions B"
  assumes agree: "agree_on (ta_clocks B) v vB"
  shows "agree_on (ta_clocks B)
    (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
    (reset_val (trans_resets t2) (delay_val d vB))"
proof -
  have rA: "trans_resets t1 \<subseteq> ta_clocks A"
    using clock_wf_transition_bounds(1)[OF cwfA tA] .
  show ?thesis
    using disj rA agree by (auto simp: agree_on_def)
qed

lemma run_from_product_sync:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes runA: "run_from_l A p1 vA w q1 vfA"
  assumes runB: "run_from_l B p2 vB w q2 vfB"
  assumes agreeA: "agree_on (ta_clocks A) v vA"
  assumes agreeB: "agree_on (ta_clocks B) v vB"
  shows "\<exists>vf. run_from_l (product_ta_raw A B) (p1, p2) v w (q1, q2) vf"
  using runA runB agreeA agreeB cwfA disj
proof (induction arbitrary: p2 vB q2 vfB v rule: run_from_l.induct)
  case (Run_Nil A p1 vA)
  then have "q2 = p2"
    by (cases rule: run_from_l.cases) auto
  moreover have "vfB = vB"
    using Run_Nil.prems(1) by (cases rule: run_from_l.cases) auto
  ultimately show ?case
    by (auto intro: run_from_l.Run_Nil)
next
  case (Run_Cons t1 A p1 a d vA w q1 vfA)
  obtain t2 where
    t2_in: "t2 \<in> ta_transitions B" and
    source2: "trans_source t2 = p2" and
    match2: "event_matches (trans_label t2) a" and
    nonneg2: "0 <= d" and
    guards2: "guards_sat (delay_val d vB) (trans_guards t2)" and
    tailB: "run_from_l B
      (trans_target t2)
      (reset_val (trans_resets t2) (delay_val d vB))
      w q2 vfB"
    using Run_Cons.prems(1) by (auto elim: run_from_l_ConsE)
  obtain l where
    lint: "label_intersect (trans_label t1) (trans_label t2) = Some l" and
    match_l: "event_matches l a"
    using label_intersect_complete[OF Run_Cons.hyps(3) match2] by auto
  have bounds1: "guards_clocks (trans_guards t1) \<subseteq> ta_clocks A"
    using Run_Cons.prems(4) Run_Cons.hyps(1) by (force simp: clock_wf_def)
  have bounds2: "guards_clocks (trans_guards t2) \<subseteq> ta_clocks B"
    using cwfB t2_in by (auto simp: clock_wf_def)
  have guards1_product: "guards_sat (delay_val d v) (trans_guards t1)"
    using guards_sat_agree[OF bounds1 agree_on_delay[OF Run_Cons.prems(2)]]
      Run_Cons.hyps(5)
    by simp
  have guards2_product: "guards_sat (delay_val d v) (trans_guards t2)"
    using guards_sat_agree[OF bounds2 agree_on_delay[OF Run_Cons.prems(3)]]
      guards2
    by simp
  have agreeA':
    "agree_on (ta_clocks A)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      (reset_val (trans_resets t1) (delay_val d vA))"
    using agree_reset_union_left[OF Run_Cons.prems(5) Run_Cons.prems(4) cwfB
        Run_Cons.hyps(1) t2_in
        Run_Cons.prems(2)] .
  have agreeB':
    "agree_on (ta_clocks B)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      (reset_val (trans_resets t2) (delay_val d vB))"
    using agree_reset_union_right[OF Run_Cons.prems(5) Run_Cons.prems(4) cwfB
        Run_Cons.hyps(1) t2_in
        Run_Cons.prems(3)] .
  obtain vf where tail:
    "run_from_l (product_ta_raw A B)
      (trans_target t1, trans_target t2)
      (reset_val (trans_resets t1 \<union> trans_resets t2) (delay_val d v))
      w (q1, q2) vf"
    using Run_Cons.IH[OF tailB agreeA' agreeB' Run_Cons.prems(4)
        Run_Cons.prems(5)] by (auto simp: reset_val_def)
  have pt_in:
    "product_transition t1 t2 l \<in> ta_transitions (product_ta_raw A B)"
    using Run_Cons.hyps(1) t2_in lint by (auto simp: product_ta_raw_transitions)
  have run_product:
    "run_from_l (product_ta_raw A B) (p1, p2) v ((d, a) # w) (q1, q2) vf"
    using pt_in Run_Cons.hyps source2 match_l Run_Cons.hyps(4)
      guards1_product guards2_product tail
    by (auto intro!: run_from_l.Run_Cons[of "product_transition t1 t2 l"])
  then show ?case by auto
qed

lemma product_ta_raw_complete:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  assumes disj: "ta_clocks A \<inter> ta_clocks B = {}"
  assumes "w \<in> ta_lang_l A"
  assumes "w \<in> ta_lang_l B"
  shows "w \<in> ta_lang_l (product_ta_raw A B)"
proof -
  obtain p1 q1 vfA where
    p1: "p1 \<in> ta_initial A" and q1: "q1 \<in> ta_accepting A" and
    runA: "run_from_l A p1 zero_val w q1 vfA"
    using assms(4) by (auto simp: accepts_l_def ta_lang_l_def)
  obtain p2 q2 vfB where
    p2: "p2 \<in> ta_initial B" and q2: "q2 \<in> ta_accepting B" and
    runB: "run_from_l B p2 zero_val w q2 vfB"
    using assms(5) by (auto simp: accepts_l_def ta_lang_l_def)
  have agreeA: "agree_on (ta_clocks A) zero_val zero_val"
    by (simp add: agree_on_def)
  have agreeB: "agree_on (ta_clocks B) zero_val zero_val"
    by (simp add: agree_on_def)
  obtain vf where runP:
    "run_from_l (product_ta_raw A B) (p1, p2) zero_val w (q1, q2) vf"
    using run_from_product_sync[OF cwfA cwfB disj runA runB agreeA agreeB]
    by auto
  have "accepts_l (product_ta_raw A B) w"
    unfolding accepts_l_def
    using p1 p2 q1 q2 runP
    by (intro exI[where x = "(p1, p2)"]
        exI[where x = "(q1, q2)"] exI[where x = vf]) auto
  then show ?thesis
    by (simp add: ta_lang_l_def)
qed

theorem product_ta_raw_correct:
  assumes "clock_wf A"
  assumes "clock_wf B"
  assumes "ta_clocks A \<inter> ta_clocks B = {}"
  shows "ta_lang_l (product_ta_raw A B) = ta_lang_l A \<inter> ta_lang_l B"
  using product_ta_raw_sound[OF assms]
    product_ta_raw_complete[OF assms]
  by blast

lemma automaton_wf_product_ta_raw:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  shows "automaton_wf (product_ta_raw A B)"
proof -
  have transition_locs:
    "trans_source t \<in> ta_locations A \<times> ta_locations B \<and>
     trans_target t \<in> ta_locations A \<times> ta_locations B"
    if t_in: "t \<in> ta_transitions (product_ta_raw A B)"
    for t
  proof -
    obtain t1 t2 l where
      t1_in: "t1 \<in> ta_transitions A" and
      t2_in: "t2 \<in> ta_transitions B" and
      lint: "label_intersect (trans_label t1) (trans_label t2) = Some l" and
      t_def: "t = product_transition t1 t2 l"
      using product_transitionE[OF t_in] by auto
    show ?thesis
      using wfA wfB t1_in t2_in t_def
      by (auto simp: automaton_wf_def)
  qed
  show ?thesis
    using wfA wfB transition_locs by (auto simp: automaton_wf_def)
qed

lemma clock_wf_product_ta_raw:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  shows "clock_wf (product_ta_raw A B)"
proof -
  have transition_clocks:
    "trans_resets t \<subseteq> ta_clocks A \<union> ta_clocks B \<and>
     guards_clocks (trans_guards t) \<subseteq> ta_clocks A \<union> ta_clocks B"
    if t_in: "t \<in> ta_transitions (product_ta_raw A B)"
    for t
  proof -
    obtain t1 t2 l where
      t1_in: "t1 \<in> ta_transitions A" and
      t2_in: "t2 \<in> ta_transitions B" and
      lint: "label_intersect (trans_label t1) (trans_label t2) = Some l" and
      t_def: "t = product_transition t1 t2 l"
      using product_transitionE[OF t_in] by auto
    have bounds1:
      "trans_resets t1 \<subseteq> ta_clocks A"
      "guards_clocks (trans_guards t1) \<subseteq> ta_clocks A"
      using clock_wf_transition_bounds[OF cwfA t1_in] by simp_all
    have bounds2:
      "trans_resets t2 \<subseteq> ta_clocks B"
      "guards_clocks (trans_guards t2) \<subseteq> ta_clocks B"
      using clock_wf_transition_bounds[OF cwfB t2_in] by simp_all
    show ?thesis
      using bounds1 bounds2 t_def by auto
  qed
  show ?thesis
    using cwfA cwfB transition_clocks by (auto simp: clock_wf_def)
qed

end

lemma inj_prod_encode_global [simp]:
  "inj prod_encode"
  using inj_prod_encode[of UNIV] by (simp add: inj_on_def inj_def)

theorem product_ta_correct:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  shows "ta_lang (product_ta A B) = ta_lang A \<inter> ta_lang B"
proof -
  let ?B = "shift_clocks (clock_shift_offset A) B"
  have cwfB': "clock_wf ?B"
    using clock_wf_shift_clocks[OF cwfB] .
  have disj: "ta_clocks A \<inter> ta_clocks ?B = {}"
    using disjoint_shift_clocks[OF cwfA] .
  have "ta_lang (product_ta A B) =
      equality_label_algebra.ta_lang_l (product_ta A B)"
    by (simp add: equality_ta_lang_l)
  also have "... =
      equality_label_algebra.ta_lang_l
        (equality_label_algebra.product_ta_raw A ?B)"
    by (simp add: product_ta_def)
  also have "... =
      equality_label_algebra.ta_lang_l A \<inter>
      equality_label_algebra.ta_lang_l ?B"
    using equality_label_algebra.product_ta_raw_correct[OF cwfA cwfB' disj]
    by simp
  also have "... =
      ta_lang A \<inter> equality_label_algebra.ta_lang_l ?B"
    by (simp add: equality_ta_lang_l)
  also have "... =
      ta_lang A \<inter> equality_label_algebra.ta_lang_l B"
    using equality_label_algebra.ta_lang_l_shift_clocks[OF cwfB,
        of "clock_shift_offset A"]
    by simp
  also have "... = ta_lang A \<inter> ta_lang B"
    by (simp add: equality_ta_lang_l)
  finally show ?thesis .
qed

lemma automaton_wf_product_ta:
  assumes wfA: "automaton_wf A"
  assumes wfB: "automaton_wf B"
  shows "automaton_wf (product_ta A B)"
  using equality_label_algebra.automaton_wf_product_ta_raw[
      OF wfA automaton_wf_shift_clocks[OF wfB]]
  by (simp add: product_ta_def)

lemma clock_wf_product_ta:
  assumes cwfA: "clock_wf A"
  assumes cwfB: "clock_wf B"
  shows "clock_wf (product_ta A B)"
  using equality_label_algebra.clock_wf_product_ta_raw[
      OF cwfA clock_wf_shift_clocks[OF cwfB]]
  by (simp add: product_ta_def)

lemma compile_fragment_wf:
  assumes "compile_fragment r = Some A"
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
    r_def: "compile_fragment r = Some A1" and
    s_def: "compile_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1 \<and> clock_wf A1"
    using Union.IH(1)[OF r_def] .
  have wf2: "automaton_wf A2 \<and> clock_wf A2"
    using Union.IH(2)[OF s_def] .
  then show ?case
    using wf1 by (simp add: A_def automaton_wf_union_ta clock_wf_union_ta)
next
  case (Intersection r s)
  then obtain A1 A2 where
    r_def: "compile_fragment r = Some A1" and
    s_def: "compile_fragment s = Some A2" and
    A_def: "A = map_locations prod_encode (product_ta A1 A2)"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1 \<and> clock_wf A1"
    using Intersection.IH(1)[OF r_def] .
  have wf2: "automaton_wf A2 \<and> clock_wf A2"
    using Intersection.IH(2)[OF s_def] .
  then show ?case
    using wf1
    by (simp add: A_def automaton_wf_product_ta clock_wf_product_ta
        automaton_wf_map_locations)
next
  case (Concat r s)
  then obtain A1 A2 where
    r_def: "compile_fragment r = Some A1" and
    s_def: "compile_fragment s = Some A2" and
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
    r_def: "compile_fragment r = Some A0" and
    A_def: "A = star_ta A0"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using KleeneStar.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_star_ta clock_wf_star_ta)
next
  case (KleenePlus r)
  then obtain A0 where
    r_def: "compile_fragment r = Some A0" and
    A_def: "A = plus_ta A0"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using KleenePlus.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_plus_ta clock_wf_plus_ta)
next
  case (Within r I)
  then obtain A0 where
    r_def: "compile_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0 \<and> clock_wf A0"
    using Within.IH[OF r_def] .
  then show ?case
    by (simp add: A_def automaton_wf_time_restrict_ta clock_wf_time_restrict_ta)
qed

theorem compile_fragment_correct:
  assumes "compile_fragment r = Some A"
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
    r_def: "compile_fragment r = Some A1" and
    s_def: "compile_fragment s = Some A2" and
    A_def: "A = union_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_fragment_wf[OF s_def] by simp
  have "ta_lang A = ta_lang A1 \<union> ta_lang A2"
    using ta_lang_union_ta[OF wf1 wf2] by (simp add: A_def)
  also have "... = tre_lang r \<union> tre_lang s"
    using Union.IH(1)[OF r_def] Union.IH(2)[OF s_def] by simp
  also have "... = tre_lang (Union r s)"
    by simp
  finally show ?case .
next
  case (Intersection r s)
  then obtain A1 A2 where
    r_def: "compile_fragment r = Some A1" and
    s_def: "compile_fragment s = Some A2" and
    A_def: "A = map_locations prod_encode (product_ta A1 A2)"
    by (auto split: option.splits)
  have cwf1: "clock_wf A1"
    using compile_fragment_wf[OF r_def] by simp
  have cwf2: "clock_wf A2"
    using compile_fragment_wf[OF s_def] by simp
  have "ta_lang A = ta_lang (product_ta A1 A2)"
    using ta_lang_map_locations[OF inj_prod_encode_global]
    by (simp add: A_def)
  also have "... = ta_lang A1 \<inter> ta_lang A2"
    using product_ta_correct[OF cwf1 cwf2] .
  also have "... = tre_lang r \<inter> tre_lang s"
    using Intersection.IH(1)[OF r_def] Intersection.IH(2)[OF s_def]
    by simp
  also have "... = tre_lang (Intersection r s)"
    by simp
  finally show ?case .
next
  case (Concat r s)
  then obtain A1 A2 where
    r_def: "compile_fragment r = Some A1" and
    s_def: "compile_fragment s = Some A2" and
    A_def: "A = concat_ta A1 A2"
    by (auto split: option.splits)
  have wf1: "automaton_wf A1"
    using compile_fragment_wf[OF r_def] by simp
  have wf2: "automaton_wf A2"
    using compile_fragment_wf[OF s_def] by simp
  have cwf2: "clock_wf A2"
    using compile_fragment_wf[OF s_def] by simp
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
    r_def: "compile_fragment r = Some A0" and
    A_def: "A = star_ta A0"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0"
    using compile_fragment_wf[OF r_def] by simp
  have cwf0: "clock_wf A0"
    using compile_fragment_wf[OF r_def] by simp
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
    r_def: "compile_fragment r = Some A0" and
    A_def: "A = plus_ta A0"
    by (auto split: option.splits)
  have cwf0: "clock_wf A0"
    using compile_fragment_wf[OF r_def] by simp
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
    r_def: "compile_fragment r = Some A0" and
    A_def: "A = time_restrict_ta A0 I"
    by (auto split: option.splits)
  have wf0: "automaton_wf A0"
    using compile_fragment_wf[OF r_def] by simp
  have cwf0: "clock_wf A0"
    using compile_fragment_wf[OF r_def] by simp
  have "ta_lang A = {w \<in> ta_lang A0. interval_mem (duration w) I}"
    using time_restrict_ta_correct[OF wf0 cwf0] by (simp add: A_def)
  also have "... = {w \<in> tre_lang r. interval_mem (duration w) I}"
    using Within.IH[OF r_def] by simp
  also have "... = tre_lang (Within r I)"
    by simp
  finally show ?case .
qed

theorem compile_fragment_trim_correct:
  assumes "compile_fragment r = Some A"
  shows "ta_lang (trim_to_accepting A) = tre_lang r"
  using compile_fragment_correct[OF assms] ta_lang_trim_to_accepting[of A]
  by simp

end
