theory Exercise5
  imports Main
begin

datatype alpha =
  a |
  b

inductive S :: "alpha list \<Rightarrow> bool" where
\<epsilon>: "S []" |
wrap: "S w \<Longrightarrow> S (a # w @ [b])" |
concat: "S w \<Longrightarrow> S x \<Longrightarrow> S (w @ x)"

inductive T :: "alpha list \<Rightarrow> bool" where
\<epsilon>: "T []" |
postfix: "T w \<Longrightarrow> T x \<Longrightarrow> T (w @ [a] @ x @ [b])"

lemma TappNil: "T w \<Longrightarrow> T (w @ [])"
  apply simp
  done

lemma SappNil: "S (w @ []) \<Longrightarrow> S w"
  apply simp
  done

lemma TappimplT: "T x \<Longrightarrow> T w \<Longrightarrow> T (w @ x)"
  apply (induction rule: T.induct)
   apply simp
  apply (metis T.simps append.assoc)
  done

theorem TimpS: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
   apply (rule S.\<epsilon>)
  apply (simp add: S.concat S.wrap)
  done

theorem SimpT: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
    apply (rule T.\<epsilon>)
   apply (metis T.\<epsilon> T.simps append_Cons append_Nil)
  apply (simp add: TappimplT)
  done

theorem "S w = T w"
  apply (auto simp add: SimpT TimpS)
  done

end