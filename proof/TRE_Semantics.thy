theory TRE_Semantics
  imports TRE_Syntax Timed_Word
begin

definition concat_lang ::
  "'a timed_word set => 'a timed_word set => 'a timed_word set"
where
  "concat_lang A B = {w. \<exists>u v. u \<in> A \<and> v \<in> B \<and> w = u @ v}"

definition star_lang :: "'a timed_word set => 'a timed_word set" where
  "star_lang A = {w. \<exists>ws. w = concat ws \<and> set ws \<subseteq> A}"

definition plus_lang :: "'a timed_word set => 'a timed_word set" where
  "plus_lang A =
    {w. \<exists>ws. w = concat ws \<and> ws \<noteq> [] \<and> set ws \<subseteq> A}"

primrec tre_lang :: "'a tre => 'a timed_word set" where
  "tre_lang Empty = {}"
| "tre_lang Epsilon = {[]}"
| "tre_lang (Atom a) = {w. \<exists>d. 0 <= d \<and> w = [(d, a)]}"
| "tre_lang (Union r s) = tre_lang r \<union> tre_lang s"
| "tre_lang (Intersection r s) = tre_lang r \<inter> tre_lang s"
| "tre_lang (Concat r s) = concat_lang (tre_lang r) (tre_lang s)"
| "tre_lang (KleeneStar r) = star_lang (tre_lang r)"
| "tre_lang (KleenePlus r) = plus_lang (tre_lang r)"
| "tre_lang (Within r I) =
    {w \<in> tre_lang r. interval_mem (duration w) I}"

lemma concat_lang_iff [simp]:
  "w \<in> concat_lang A B \<longleftrightarrow>
    (\<exists>u v. w = u @ v \<and> u \<in> A \<and> v \<in> B)"
  by (auto simp: concat_lang_def)

lemma star_lang_iff [simp]:
  "w \<in> star_lang A \<longleftrightarrow>
    (\<exists>ws. w = concat ws \<and> set ws \<subseteq> A)"
  by (auto simp: star_lang_def)

lemma plus_lang_iff [simp]:
  "w \<in> plus_lang A \<longleftrightarrow>
    (\<exists>ws. w = concat ws \<and> ws \<noteq> [] \<and> set ws \<subseteq> A)"
  by (auto simp: plus_lang_def)

lemma tre_lang_empty_iff [simp]:
  "w \<in> tre_lang Empty \<longleftrightarrow> False"
  by simp

lemma tre_lang_epsilon_iff [simp]:
  "w \<in> tre_lang Epsilon \<longleftrightarrow> w = []"
  by simp

lemma tre_lang_atom_iff [simp]:
  "w \<in> tre_lang (Atom a) \<longleftrightarrow>
    (\<exists>d. 0 <= d \<and> w = [(d, a)])"
  by auto

lemma tre_lang_union_iff [simp]:
  "w \<in> tre_lang (Union r s) \<longleftrightarrow>
    w \<in> tre_lang r \<or> w \<in> tre_lang s"
  by simp

lemma tre_lang_intersection_iff [simp]:
  "w \<in> tre_lang (Intersection r s) \<longleftrightarrow>
    w \<in> tre_lang r \<and> w \<in> tre_lang s"
  by simp

lemma tre_lang_concat_iff [simp]:
  "w \<in> tre_lang (Concat r s) \<longleftrightarrow>
    (\<exists>u v. w = u @ v \<and> u \<in> tre_lang r \<and> v \<in> tre_lang s)"
  by simp

lemma tre_lang_kleene_star_iff [simp]:
  "w \<in> tre_lang (KleeneStar r) \<longleftrightarrow>
    (\<exists>ws. w = concat ws \<and> set ws \<subseteq> tre_lang r)"
  by simp

lemma tre_lang_kleene_plus_iff [simp]:
  "w \<in> tre_lang (KleenePlus r) \<longleftrightarrow>
    (\<exists>ws. w = concat ws \<and> ws \<noteq> [] \<and> set ws \<subseteq> tre_lang r)"
  by simp

lemma tre_lang_within_iff [simp]:
  "w \<in> tre_lang (Within r I) \<longleftrightarrow>
    w \<in> tre_lang r \<and> interval_mem (duration w) I"
  by simp

end
