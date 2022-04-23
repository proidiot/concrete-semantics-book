theory Exercise6
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = Nil"
  | "contents (Node l a r) = (contents l) @ [a] @ (contents r)"

fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0"
  | "treesum (Node l a r) = (treesum l) + a + (treesum r)"

fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum Nil = 0"
  | "listsum (Cons x xs) = x + (listsum xs)"

lemma shallow_treesum [simp]: "treesum (Node Tip a Tip) = a"
  apply (induction a)
  apply (auto)
done

lemma zero_treesum [simp]: "treesum (Node l 0 r) = (treesum l) + (treesum r)"
  apply (induction l)
  apply (auto)
done

lemma suc_treesum [simp]: "treesum (Node l (Suc a) r) = Suc (treesum (Node l a r))"
  apply (induction a)
  apply (auto)
done

lemma listsum_app_distributivity [simp]: "listsum (xs @ ys) = (listsum xs) + (listsum ys)"
  apply (induction xs)
  apply (auto)
done

theorem treesum_is_contents_sum [simp]: "treesum t = listsum (contents t)"
  apply (induction t rule: treesum.induct)
  apply (auto)
done

end