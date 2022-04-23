theory Exercise11
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x"
  | "eval (Const n) x = n"
  | "eval (Add l r) x = (eval l x) + (eval r x)"
  | "eval (Mult l r) x = (eval l x) * (eval r x)"

(*
fun polynomiate :: "int list \<Rightarrow> exp" where
  "polynomiate Nil = Const 0"
  | "polynomiate (Cons x xs) = Add (Const x) (Mult (Var) (polynomiate xs))"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp xs n = eval (polynomiate xs) n"
*)

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp Nil n = 0"
  | "evalp (Cons x xs) n = x + n * (evalp xs n)"

(* 2*(7^2) + 4*7 + 3 = 129 *)
lemma evalp_sanity [simp]: "evalp [3, 4, 2] 7 = 129"
  apply auto
done

fun linear_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "linear_add Nil ys = ys"
  | "linear_add xs Nil = xs"
  | "linear_add (Cons x xs) (Cons y ys) = Cons (x + y) (linear_add xs ys)"

fun linear_scale :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "linear_scale x Nil = Nil"
  | "linear_scale x (Cons y ys) = Cons (x*y) (linear_scale x ys)"

fun linear_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "linear_mult Nil ys = Nil"
  | "linear_mult (Cons x xs) ys = linear_add (linear_scale x ys) (Cons 0 (linear_mult xs ys))"

lemma linear_mult_binomial_sanity [simp]: "linear_mult [a, b] [c, d] = [(a*c), ((a*d) + (b*c)), (b*d)]"
  apply auto
done

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs (Const n) = [n]"
  | "coeffs Var = [0, 1]"
  | "coeffs (Add l r) = linear_add (coeffs l) (coeffs r)"
  | "coeffs (Mult l r) = linear_mult (coeffs l) (coeffs r)"

(* (x^2 + 3) * (2x + 7) = 2x^3 + 7x^2 + 6x + 21 *)
lemma coeffs_sanity [simp]: "coeffs (Mult (Add (Mult (Var) (Var)) (Const 3)) (Add (Mult (Const 2) (Var)) (Const 7))) = [21, 6, 7, 2]"
  apply auto
done

lemma linear_add_zero [simp]: "linear_add xs Nil = xs"
  apply (induction xs)
  apply auto
done

lemma evalp_linear_add [simp]: "evalp (linear_add xs ys) n = (evalp xs n) + (evalp ys n)"
(*
  apply (induction xs rule: polynomiate.induct)
  apply (auto simp add: algebra_simps)
*)
  apply (induction xs rule: linear_add.induct)
  apply (auto simp add: algebra_simps)
done

lemma evalp_nil_zero [simp]: "evalp (linear_mult xs Nil) n = 0"
  apply (induction xs arbitrary: n)
  apply auto
done

lemma evalp_linear_scale [simp]: "evalp (linear_scale x xs) n = x * (evalp xs n)"
  apply (induction xs)
  apply (auto simp add: algebra_simps)
done

lemma evalp_linear_mult [simp]: "evalp (linear_mult xs ys) n = (evalp xs n) * (evalp ys n)"
  apply (induction xs)
  apply (auto simp add: algebra_simps)
done

theorem evalp_coeffs_preserves_eval: "evalp (coeffs e) x = eval e x"
  apply (induction e arbitrary: x)
  apply simp
  apply simp
  apply (auto simp add: algebra_simps)
done

end