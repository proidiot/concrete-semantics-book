theory Exercise7
  imports Main
begin

datatype 'a tree2 =
  Tip
  | Leaf 'a
  | Branch "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror Tip = Tip"
  | "mirror (Leaf l) = Leaf l"
  | "mirror (Branch l v r) = Branch (mirror r) v (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order Tip = Nil"
  | "pre_order (Leaf l) = [l]"
  | "pre_order (Branch l v r) = [v] @ (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order Tip = Nil"
  | "post_order (Leaf l) = [l]"
  | "post_order (Branch l v r) = (post_order l) @ (post_order r) @ [v]"

theorem pre_mirror_is_rev_post [simp]: "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply auto
done

end