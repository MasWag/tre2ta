theory Timed_Word
  imports "HOL.Real"
begin

type_synonym 'a timed_word = "(real * 'a) list"

definition wellformed_timed_word :: "'a timed_word => bool" where
  "wellformed_timed_word w \<longleftrightarrow> list_all (\<lambda>x. 0 <= fst x) w"

definition duration :: "'a timed_word => real" where
  "duration w = sum_list (map fst w)"

lemma wellformed_timed_word_Nil [simp]:
  "wellformed_timed_word []"
  by (simp add: wellformed_timed_word_def)

lemma wellformed_timed_word_Cons [simp]:
  "wellformed_timed_word ((d, a) # w) \<longleftrightarrow>
    0 <= d \<and> wellformed_timed_word w"
  by (simp add: wellformed_timed_word_def)

lemma wellformed_timed_word_append [simp]:
  "wellformed_timed_word (u @ v) \<longleftrightarrow>
    wellformed_timed_word u \<and> wellformed_timed_word v"
  by (simp add: wellformed_timed_word_def)

lemma duration_Nil [simp]:
  "duration [] = 0"
  by (simp add: duration_def)

lemma duration_Cons [simp]:
  "duration ((d, a) # w) = d + duration w"
  by (simp add: duration_def)

lemma duration_append [simp]:
  "duration (u @ v) = duration u + duration v"
  by (simp add: duration_def)

lemma duration_nonnegative:
  assumes "wellformed_timed_word w"
  shows "0 <= duration w"
  using assms
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (cases x) simp
qed

lemma wellformed_timed_word_concat:
  assumes "\<forall>w \<in> set ws. wellformed_timed_word w"
  shows "wellformed_timed_word (concat ws)"
  using assms
  by (induction ws) simp_all

end
