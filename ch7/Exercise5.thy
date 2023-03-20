theory Exercise5
  imports IMP
begin

theorem if_conj:
    "(IF (And b1 b2) THEN c1 ELSE c2)
    \<sim> (IF b1 THEN (IF b2 THEN c1 ELSE c2) ELSE c2)"
  (is "?LHS \<sim> ?RHS")
proof -
  have "(?RHS,s) \<Rightarrow> t" if assm: "(?LHS,s) \<Rightarrow> t" for s t
  proof -
    have "bval (And b1 b2) s \<or> \<not> bval (And b1 b2) s"
      by simp
    thus ?thesis
    proof (elim disjE)
      assume "bval (And b1 b2) s"
      hence lsimp: "(?LHS,s) \<Rightarrow> t = (c1,s) \<Rightarrow>t" by auto
      have "bval b1 s" and "bval b2 s"
        using `bval (And b1 b2) s` by auto
      hence "(?RHS,s) \<Rightarrow> t = (c1,s) \<Rightarrow> t" by auto
      thus ?thesis using assm lsimp by auto
    next
      assume "\<not>bval (And b1 b2) s"
      hence lsimp: "(?LHS,s) \<Rightarrow> t = (c2,s) \<Rightarrow> t" by auto
      have "(\<not>bval b1 s) \<or> (\<not>bval b2 s)"
        using `\<not>bval (And b1 b2) s` by simp
      hence "(?RHS,s) \<Rightarrow> t = (c2,s) \<Rightarrow> t" by auto
      thus ?thesis using assm lsimp by auto
    qed
  qed
  moreover
  have "(?LHS,s) \<Rightarrow> t" if assm: "(?RHS,s) \<Rightarrow> t" for s t
  proof -
    have "bval (And b1 b2) s \<or> \<not> bval (And b1 b2) s"
      by simp
    thus ?thesis
    proof (elim disjE)
      assume "bval (And b1 b2) s"
      hence rsimp: "(?RHS,s) \<Rightarrow> t \<Longrightarrow> (c1,s) \<Rightarrow> t"
        by auto
      have "(?LHS,s) \<Rightarrow> t \<Longrightarrow> (c1,s) \<Rightarrow> t"
        using `bval (And b1 b2) s` by auto
      thus ?thesis using assm rsimp by auto
    next
      assume "\<not>bval (And b1 b2) s"
      hence rsimp: "(?RHS,s) \<Rightarrow> t \<Longrightarrow> (c2,s) \<Rightarrow> t"
        by auto
      have "(?LHS,s) \<Rightarrow> t \<Longrightarrow> (c2,s) \<Rightarrow> t"
        using `\<not>bval (And b1 b2) s` by auto
      thus ?thesis using assm rsimp by auto
    qed
  qed
  ultimately
  show ?thesis by auto
qed

theorem while_conj:
    "\<not>(\<forall>b1. \<forall>b2. \<forall>c.
        (WHILE (And b1 b2) DO c)
        \<sim> (WHILE b1 DO (WHILE b2 DO c)))"
proof
  assume spoz:
      "\<forall>b1. \<forall>b2. \<forall>c.
        (WHILE (And b1 b2) DO c)
        \<sim> (WHILE b1 DO (WHILE b2 DO c))"
  fix x
  obtain l1 l2 ax x0 x1 x2 where witness:
      "l1 = (Less (V x) (N 1))"
      "l2 = (Less (V x) (N 2))"
      "ax = (x ::= (Plus (V x) (N 1)))"
      "x0 = (\<lambda>v.0::int)"
      "x1 = x0(x:=1::int)"
      "x2 = x0(x:=2::int)"
    by simp
  hence neq: "x1 \<noteq> x2"
    by (smt (verit, del_insts) fun_upd_eqD)
  have "(WHILE (And l1 l2) DO ax,x0) \<Rightarrow> x1" and
      "(WHILE l1 DO (WHILE l2 DO ax),x0) \<Rightarrow> x2"
    using witness by fastforce+
  hence
      "\<not>((WHILE (And l1 l2) DO ax)
         \<sim> (WHILE l1 DO (WHILE l2 DO ax)))"
    using diff_end_impl_diff_com neq by blast
  thus False
    using witness spoz by simp
qed

theorem while_disj:
    "(WHILE (Or b1 b2) DO c)
    \<sim> (WHILE (Or b1 b2) DO (c ;; WHILE b1 DO c))"
  (is "?LHS \<sim> ?RHS")
proof -
  have
      "\<forall>s. \<not>final (?LHS,s) \<or> \<not>final (?RHS,s)
      \<Longrightarrow> \<exists>t. \<exists>n.
      state_changes (?LHS,s) (?LHS,t) n
      \<and> state_changes (?RHS,s) (?RHS,t) n
      \<and> n > 0"
    sorry
  thus "?LHS \<sim> ?RHS"
    by (rule while_state_equiv_impl_big_step_equiv)
qed

end
