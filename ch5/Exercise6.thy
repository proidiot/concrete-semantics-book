theory Exercise6
  imports Main
begin

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (a # as) = {x. x=a \<or> x \<in> (elems as)}"

theorem "
  x \<in> elems xs
  \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs
    \<and> x \<notin> elems ys
"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  hence "x = a \<or> (x \<noteq> a \<and> x \<in> elems xs)" by auto
  thus ?case
  proof
    assume "x = a"
    hence "a # xs = [] @ x # xs \<and> x \<notin> elems []" by simp
    thus ?thesis by fastforce
  next
    assume "x \<noteq> a \<and> x \<in> elems xs"
    hence "
      \<exists> ys zs. a # xs = (a # ys) @ x # zs
      \<and> x \<notin> elems (a # ys)
    " using local.Cons.IH by simp
    thus ?thesis by fastforce
  qed
qed

end
