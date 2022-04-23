theory Exercise10
  imports Main
begin

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 => nat" where
  "nodes Tip = 1"
  | "nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"
  | "explode (Suc n) t = explode n (Node t t)"

fun nodes_explode_calc :: "nat \<Rightarrow> tree0 \<Rightarrow> nat" where
  "nodes_explode_calc n t = ((nodes t) * (2 ^ n)) + (2^n - 1)"

(*
lemma nodes_suc_explode [simp]: "nodes (explode (Suc n) t) = 1 + (2 * (nodes (explode n t)))"
  apply (induction n arbitrary: t)
  apply (simp add: algebra_simps)
  apply (simp add: algebra_simps)
done

lemma nodes_explode_algebra_manip_lhs [simp]: "1 + (2 * (n + ((Suc n) * ((2^m) - 1)))) = (n * (2 ^ (Suc m))) + (2 ^ (Suc m)) - 1"
  apply (induction m)
  apply (auto simp add: algebra_simps)
done

lemma nodes_explode_algebra_manip_rhs [simp]: "(n * (2 ^ (Suc m))) + (2 ^ (Suc m)) - 1 = n + ((Suc n) * (2 ^ (Suc m) - 1))"
  apply (induction m)
  apply (auto simp add: algebra_simps)
done

lemma nodes_explode_algebra_manip [simp]: "1 + (2 * (n + ((Suc n) * ((2^m) -1)))) = n + ((Suc n) * (2^(Suc m) - 1))"
  apply (induction m arbitrary: n)
  apply (simp add: algebra_simps)
  unfolding nodes_explode_algebra_manip_lhs
  unfolding nodes_explode_algebra_manip_rhs
by (rule HOL.refl)

theorem explosion_size: "nodes (explode n t) = (nodes t) + (((nodes t) + 1) * ((2 ^ n) - 1))"
  apply (induction n arbitrary: t)
  apply (simp add: algebra_simps)
done
*)

theorem explosion_size: "nodes (explode n t) = nodes_explode_calc n t"
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps)
done

end