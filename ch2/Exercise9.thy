theory Exercise9
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"
  | "add (Suc x) y = Suc (add x y)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 x = x"
  | "itadd (Suc x) y = itadd x (Suc y)"

lemma add_n_zero [simp]: "add n 0 = n"
  apply (induction n)
  apply auto
done

lemma add_m_suc_n [simp]: "add m (Suc n) = Suc (add m n)"
  apply (induction m)
  apply auto
done

lemma add_commutativity [simp]: "add m n = add n m"
  apply (induction n)
  apply auto
done

theorem itadd_is_add [simp]: "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply auto
done

end