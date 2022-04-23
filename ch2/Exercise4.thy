theory Exercise4
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = Cons x Nil"
  | "snoc (Cons x xs) y = Cons x (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil"
  | "reverse (Cons x xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = Cons x (reverse xs)"
  apply (induction xs)
  apply (auto)
done

theorem double_reverse [simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply (auto)
done

end