theory Exercise2
  imports Main
begin

inductive palindrome :: "'a list \<Rightarrow> bool" where
pdrmNil:  "palindrome []" |
pdrmSing: "palindrome [x]" |
pdrmRec:  "palindrome xs \<Longrightarrow> palindrome (x # xs @ [x])"

theorem "(palindrome xs) \<Longrightarrow> (rev xs = xs)"
  apply (induction rule: palindrome.induct)
  by simp_all

end