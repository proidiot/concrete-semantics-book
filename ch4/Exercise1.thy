theory Exercise1 imports Main
begin

datatype 'a tree =
	Tip |
	Node "'a tree" 'a "'a tree"

fun set :: "'a tree => 'a set" where
"set (Tip) = {}" |
"set (Node a v b) = (set a) Un {v} Un (set b)"

fun ord :: "int tree => bool" where
"ord (Tip) = True" |
"ord (Node (Tip) v (Tip)) = True" |
"ord (Node (Node a v1 b) v2 c) = ((v1 < v2) \<and> (ord (Node a v1 b)) \<and> (ord c))" |
"ord (Node (Tip) v1 (Node a v2 b)) = ((v1 < v2) \<and> (ord (Node a v2 b)))"

fun ins :: "int => int tree => int tree" where
"ins v (Tip) = Node (Tip) v (Tip)" |
"ins v (Node a ov b) = (
  if (v : ({ov} Un (set a) Un (set b)))
  then (Node a ov b)
  else (
    if v<ov
    then (Node (ins v a) ov b)
    else (Node a ov (ins v b))
  )
)"

theorem ins_non_duplication [simp]: "(x \<in> (set t)) ==> (ins x t = t)"
  apply (induction t)
	apply auto
	done

theorem set_inc_is_union [simp]: "set (ins x t) = {x} Un (set t)"
  apply (induction t)
	apply auto
	done

theorem ins_preserves_ord [simp]: "ord t ==> ord (ins x t)"
  apply (induction t rule: ord.induct)
	apply auto
	done

end