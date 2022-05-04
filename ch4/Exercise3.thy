theory Exercise3
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply assumption
  apply (metis step)
  done

lemma rel_impl_star: "r x y \<Longrightarrow> star r x y"
  by (metis star.simps)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

theorem star'_impl_star: "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
   apply (rule star.refl)
  apply (metis star.simps star_trans)
  done

lemma rel_impl_star': "r x y \<Longrightarrow> star' r x y"
  by (metis star'.refl' star'.step')

(* I couldn't figure out how to get these in place with "rule[of foo]",
   but I saw others just did this lemma directly, so whatever. *)
lemma star'_transpos_star_step: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
   apply (rule rel_impl_star')
   apply simp
  apply (metis star'.step')
  done

theorem "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (rule star'.refl')
  apply (rule star'_transpos_star_step)
   apply simp_all
  done

end