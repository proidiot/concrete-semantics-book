theory Exercise4
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refli: "iter r 0 x x" |
stepi: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma iter_zero: "iter r 0 x y \<Longrightarrow> x=y"
  apply (rule iter.cases)
    apply simp
  apply auto
  done

lemma iter_one: "iter r 1 x y \<Longrightarrow> r x y"
  apply (rule iter.cases)
    apply simp
   apply simp
  using iter_zero apply fastforce
  done

lemma iter_more: "iter r (Suc n) x y \<Longrightarrow> \<exists>z. ((r x z) \<and> (iter r n z y))"
  apply (rule iter.cases)
    apply simp
   apply (simp add: Nat.Suc_neq_Zero)
  apply auto
  done

lemma iter_one_exists: "r x y \<Longrightarrow> iter r (Suc 0) x y"
  apply (metis iter.simps)
  done

lemma iter_pre: "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (Suc n) x z"
  apply (induction rule: iter.induct)
   apply (simp add: iter_one_exists)
  apply (simp add: iter.intros)
  done

lemma iter_sum: "
  iter r n1 x y
  \<Longrightarrow> iter r n2 y z
  \<Longrightarrow> iter r (n1 + n2) x z
"
  apply (induction rule: iter.induct)
   apply (simp_all add: iter.stepi)
  done

theorem "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply (induction rule: star.induct)
  using iter.refli apply fastforce
  apply (metis iter.stepi)
  done

end