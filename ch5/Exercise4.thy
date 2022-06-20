theory Exercise4
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?EVEN3")
proof
  assume "?EVEN3"
  hence "ev (Suc 0)" by cases
  thus False by cases
qed

end
