theory TA_Syntax
  imports Interval
begin

type_synonym clock = nat

type_synonym valuation = "clock => real"

definition zero_val :: valuation where
  "zero_val = (\<lambda>_. 0)"

definition delay_val :: "real => valuation => valuation" where
  "delay_val d v = (\<lambda>c. v c + d)"

definition reset_val :: "clock set => valuation => valuation" where
  "reset_val R v = (\<lambda>c. if c \<in> R then 0 else v c)"

datatype guard =
  Clock_In clock interval

fun guard_sat :: "valuation => guard => bool" where
  "guard_sat v (Clock_In c I) = interval_mem (v c) I"

definition guards_sat :: "valuation => guard list => bool" where
  "guards_sat v gs \<longleftrightarrow> list_all (guard_sat v) gs"

record ('q, 'a) transition =
  trans_source :: 'q
  trans_label :: 'a
  trans_guards :: "guard list"
  trans_resets :: "clock set"
  trans_target :: 'q

record ('q, 'a) automaton =
  ta_locations :: "'q set"
  ta_initial :: "'q set"
  ta_accepting :: "'q set"
  ta_clocks :: "clock set"
  ta_transitions :: "(('q, 'a) transition) set"

definition atom_transition :: "'a => (nat, 'a) transition" where
  "atom_transition a =
    \<lparr> trans_source = 0,
      trans_label = a,
      trans_guards = [],
      trans_resets = {},
      trans_target = 1 \<rparr>"

definition empty_ta :: "(nat, 'a) automaton" where
  "empty_ta =
    \<lparr> ta_locations = {0},
      ta_initial = {0},
      ta_accepting = {},
      ta_clocks = {},
      ta_transitions = {} \<rparr>"

definition epsilon_ta :: "(nat, 'a) automaton" where
  "epsilon_ta =
    \<lparr> ta_locations = {0},
      ta_initial = {0},
      ta_accepting = {0},
      ta_clocks = {},
      ta_transitions = {} \<rparr>"

definition atom_ta :: "'a => (nat, 'a) automaton" where
  "atom_ta a =
    \<lparr> ta_locations = {0, 1},
      ta_initial = {0},
      ta_accepting = {1},
      ta_clocks = {},
      ta_transitions = {atom_transition a} \<rparr>"

lemma zero_val_apply [simp]:
  "zero_val c = 0"
  by (simp add: zero_val_def)

lemma delay_val_apply [simp]:
  "delay_val d v c = v c + d"
  by (simp add: delay_val_def)

lemma reset_val_apply [simp]:
  "reset_val R v c = (if c \<in> R then 0 else v c)"
  by (simp add: reset_val_def)

lemma reset_val_in [simp]:
  "c \<in> R \<Longrightarrow> reset_val R v c = 0"
  by simp

lemma reset_val_notin [simp]:
  "c \<notin> R \<Longrightarrow> reset_val R v c = v c"
  by simp

lemma delay_val_zero [simp]:
  "delay_val 0 v = v"
  by (simp add: delay_val_def)

lemma reset_val_empty [simp]:
  "reset_val {} v = v"
  by (simp add: reset_val_def)

lemma guard_sat_Clock_In [simp]:
  "guard_sat v (Clock_In c I) \<longleftrightarrow> interval_mem (v c) I"
  by simp

lemma guards_sat_Nil [simp]:
  "guards_sat v []"
  by (simp add: guards_sat_def)

lemma guards_sat_Cons [simp]:
  "guards_sat v (g # gs) \<longleftrightarrow> guard_sat v g \<and> guards_sat v gs"
  by (simp add: guards_sat_def)

lemma atom_transition_simps [simp]:
  "trans_source (atom_transition a) = 0"
  "trans_label (atom_transition a) = a"
  "trans_guards (atom_transition a) = []"
  "trans_resets (atom_transition a) = {}"
  "trans_target (atom_transition a) = 1"
  by (simp_all add: atom_transition_def)

lemma empty_ta_simps [simp]:
  "ta_locations empty_ta = {0}"
  "ta_initial empty_ta = {0}"
  "ta_accepting empty_ta = {}"
  "ta_clocks empty_ta = {}"
  "ta_transitions empty_ta = {}"
  by (simp_all add: empty_ta_def)

lemma epsilon_ta_simps [simp]:
  "ta_locations epsilon_ta = {0}"
  "ta_initial epsilon_ta = {0}"
  "ta_accepting epsilon_ta = {0}"
  "ta_clocks epsilon_ta = {}"
  "ta_transitions epsilon_ta = {}"
  by (simp_all add: epsilon_ta_def)

lemma atom_ta_simps [simp]:
  "ta_locations (atom_ta a) = {0, 1}"
  "ta_initial (atom_ta a) = {0}"
  "ta_accepting (atom_ta a) = {1}"
  "ta_clocks (atom_ta a) = {}"
  "ta_transitions (atom_ta a) = {atom_transition a}"
  by (simp_all add: atom_ta_def)

lemma delay_val_nonnegative:
  assumes "\<And>c. 0 <= v c"
  assumes "0 <= d"
  shows "0 <= delay_val d v c"
  using assms by simp

lemma reset_val_nonnegative:
  assumes "\<And>c. 0 <= v c"
  shows "0 <= reset_val R v c"
  using assms by simp

end
