theory Exercise2
imports Main
begin

datatype MyNat = Zero | MySuc MyNat

fun myadd :: "MyNat => MyNat => MyNat" where
	"myadd Zero n = n"
	| "myadd (MySuc m) n = MySuc (myadd m n)"

fun double :: "MyNat \<Rightarrow> MyNat" where
  "double Zero = Zero"
  | "double (MySuc m) = MySuc (MySuc (double m))"

theorem myadd_associative [simp]: "myadd (myadd a b) c = myadd a (myadd b c)"
	apply (induction a)
	apply (auto)
done

lemma suc_add_distributivity [simp]: "MySuc (myadd a b) = myadd a (MySuc b)"
  apply (induction a)
  apply (auto)
done

lemma right_identity_zero_add [simp]: "myadd a Zero = a"
  apply (induction a)
  apply (auto)
done

theorem myadd_commutative [simp]: "myadd a b = myadd b a"
	apply (induction a)
	apply (auto)
done

theorem double_add_n_n [simp]: "double n = myadd n n"
  apply (induction n)
  apply (auto)
done

end