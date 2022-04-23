theory Exercise5
  imports Main
begin

fun sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0"
  | "sum n = n + (sum (n - 1))"

theorem sum_first_n [simp]: "sum n = (n * (n + 1)) div 2"
  apply (induction n)
  apply (auto)
done

end