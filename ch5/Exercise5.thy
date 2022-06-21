theory Exercise5
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refli: "iter r 0 x x" |
stepi: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

theorem "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (refli x)
  thus ?case by (rule star.refl)
next
  case (stepi x y n z)
  thus ?case by (auto intro: star.step)
qed

end
