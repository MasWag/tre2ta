theory Interval
  imports "HOL.Real"
begin

record interval =
  lower :: real
  upper :: "real option"
  lower_inclusive :: bool
  upper_inclusive :: bool

definition valid_interval :: "interval => bool" where
  "valid_interval I \<longleftrightarrow>
    (case upper I of None => True | Some u => lower I <= u)"

definition lower_bound_mem :: "real => interval => bool" where
  "lower_bound_mem x I \<longleftrightarrow>
    (if lower_inclusive I then lower I <= x else lower I < x)"

definition upper_bound_mem :: "real => interval => bool" where
  "upper_bound_mem x I \<longleftrightarrow>
    (case upper I of
       None => True
     | Some u => (if upper_inclusive I then x <= u else x < u))"

definition interval_mem :: "real => interval => bool" where
  "interval_mem x I \<longleftrightarrow>
    0 <= x \<and> lower_bound_mem x I \<and> upper_bound_mem x I"

lemma valid_interval_unbounded [simp]:
  "valid_interval (I\<lparr>upper := None\<rparr>)"
  by (simp add: valid_interval_def)

lemma valid_interval_bounded_iff [simp]:
  "valid_interval (I\<lparr>upper := Some u\<rparr>) \<longleftrightarrow> lower I <= u"
  by (simp add: valid_interval_def)

lemma lower_bound_mem_iff [simp]:
  "lower_bound_mem x I \<longleftrightarrow>
    (if lower_inclusive I then lower I <= x else lower I < x)"
  by (simp add: lower_bound_mem_def)

lemma upper_bound_mem_unbounded [simp]:
  "upper_bound_mem x (I\<lparr>upper := None\<rparr>)"
  by (simp add: upper_bound_mem_def)

lemma upper_bound_mem_bounded_iff [simp]:
  "upper_bound_mem x (I\<lparr>upper := Some u\<rparr>) \<longleftrightarrow>
    (if upper_inclusive I then x <= u else x < u)"
  by (simp add: upper_bound_mem_def)

lemma interval_mem_iff [simp]:
  "interval_mem x I \<longleftrightarrow>
    0 <= x \<and>
    (if lower_inclusive I then lower I <= x else lower I < x) \<and>
    (case upper I of
       None => True
     | Some u => (if upper_inclusive I then x <= u else x < u))"
  by (simp add: interval_mem_def upper_bound_mem_def)

end
