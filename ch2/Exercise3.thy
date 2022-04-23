theory Exercise3
  imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x Nil = 0"
  | "count x (Cons y xs) =
      (if x=y
        then Suc (count x xs)
        else (count x xs))"

theorem count_less_than_size [simp]: "count x xs \<le> length xs"
  apply (induction xs)
  apply (auto)
done

end