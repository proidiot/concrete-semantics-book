theory Exercise1
  imports Main
begin

lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  hence "T y x" using T by auto
  hence "A y x" using TA by simp
  hence "x = y" using A and `A x y` by simp
  hence "T x y" using `T y x` by blast
  thus "False" using `\<not> T x y` by simp
qed

end
