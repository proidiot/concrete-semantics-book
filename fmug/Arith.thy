theory Arith
  imports State
begin

datatype arith_exp =
  Num int
  | Var var_name
  | Plus arith_exp arith_exp

fun arith_val :: "arith_exp \<Rightarrow> state \<Rightarrow> int_val" where
  "arith_val (Num n) s = n"
| "arith_val (Var v) s = s v"
| "arith_val (Plus a b) s =
    arith_val a s
    + arith_val b s"

fun arith_const_simp :: "arith_exp \<Rightarrow> arith_exp" where
  "arith_const_simp (Num n) = Num n"
| "arith_const_simp (Var x) = Var x"
| "arith_const_simp (Plus a b) =
    (case (arith_const_simp a, arith_const_simp b) of
      (Num a', Num b') \<Rightarrow> Num (a' + b')
      | (a', b') \<Rightarrow> Plus a' b')"

lemma "arith_val (arith_const_simp a) s = arith_val a s"
  apply (induction a, auto split: arith_exp.split)
  done

fun plus :: "arith_exp \<Rightarrow> arith_exp \<Rightarrow> arith_exp" where
  "plus (Num a) (Num b) = Num (a + b)"
| "plus (Num a) b =
    (if a = 0
      then b
      else Plus (Num a) b)"
| "plus a (Num b) =
    (if b = 0
      then a
      else Plus a (Num b))"
| "plus a b = Plus a b"

lemma arith_val_plus: "arith_val (plus a b) s = arith_val a s + arith_val b s"
  apply (induction rule: plus.induct, simp+)
  done

fun arith_simp :: "arith_exp \<Rightarrow> arith_exp" where
  "arith_simp (Num n) = Num n"
| "arith_simp (Var v) = Var v"
| "arith_simp (Plus a b) =
    plus (arith_simp a) (arith_simp b)"

lemma "arith_val (arith_simp a) s = arith_val a s"
  apply (induction a, auto simp add: arith_val_plus)
  done

end