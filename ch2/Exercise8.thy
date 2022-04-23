theory Exercise8
  imports Main
begin

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse x Nil = Nil"
  | "intersperse x [y] = [y]"
  | "intersperse x (y # (z # xs)) = y # (x # (intersperse x (z # xs)))"

theorem itnersperse_map_distributivity [simp]: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply auto
done

end