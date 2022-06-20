theory Exercise4
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?E3")
proof
  assume "?E3"
  thus False
  proof cases
    case evSS thus False using `?E3` ev.cases by auto
  qed
qed

end
