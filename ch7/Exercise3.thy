theory Exercise3
  imports Exercise2
begin

fun deskip :: "com \<Rightarrow> com" where
"deskip (SKIP) = (SKIP)" |
"deskip (x ::= a) = (x ::= a)" |
"deskip (c1 ;; c2)
  = (if ((skip_ua c1) \<and> (skip_ua c2))
      then (SKIP)
      else if (skip_ua c1)
      then (deskip c2)
      else if (skip_ua c2)
      then (deskip c1)
      else ((deskip c1) ;; (deskip c2)))" |
"deskip (IF b THEN c1 ELSE c2)
  = (if ((skip_ua c1) \<and> (skip_ua c2))
      then (SKIP)
      else (IF b THEN (deskip c1) ELSE (deskip c2)))" |
"deskip (WHILE b DO c)
  = (WHILE b DO (deskip c))"

lemma "(deskip c = SKIP) \<longleftrightarrow> (skip_ua c)"
proof
  assume "deskip c = SKIP"
  thus "skip_ua c"
  proof induction
    case (Seq c1 c2)
    hence "((skip_ua c1) \<and> (skip_ua c2))"
      by (metis com.distinct(3) deskip.simps(3))
    thus ?case by simp
  next
    case (If b c1 c2)
    hence "((skip_ua c1) \<and> (skip_ua c2))"
      by (metis com.distinct(5) deskip.simps(4))
    thus ?case by simp
  qed auto
next
  assume "skip_ua c"
  thus "deskip c = SKIP"
  proof (induction c)
    case (Seq c1 c2)
    hence "((skip_ua c1) \<and> (skip_ua c2))" by simp
    thus ?case by simp
  next
    case (If b c1 c2)
    hence "((skip_ua c1) \<and> (skip_ua c2))" by simp
    thus ?case by simp
  qed auto
qed

value "deskip (SKIP;; WHILE b DO ((x ::= a);; SKIP))"

theorem deskip_equiv: "deskip c \<sim> c"
proof induction
  case (Seq c1 c2)
  have
    "(skip_ua c1 \<and> skip_ua c2)
      \<or> (skip_ua c1 \<and> \<not> skip_ua c2)
      \<or> (\<not> skip_ua c1 \<and> skip_ua c2)
      \<or> (\<not> skip_ua c1 \<and> \<not> skip_ua c2)"
    by auto
  thus ?case
  proof (elim disjE)
    assume assm: "skip_ua c1 \<and> skip_ua c2"
    hence skipped: "deskip (c1 ;; c2) = SKIP" by simp
    have "c1 \<sim> SKIP \<and> c2 \<sim> SKIP"
      using assm skip_ua_impl_equiv
      by presburger
    hence "SKIP \<sim> (c1 ;; c2)"
      using Exercise2.seq assm skip_ua_impl_equiv
      by presburger
    thus ?case
      using skipped
      by presburger
  next
    assume assm: "skip_ua c1 \<and> \<not> skip_ua c2"
    hence "deskip (c1 ;; c2) = deskip c2" by simp
    hence rdct: "deskip (c1 ;; c2) \<sim> c2"
      using `deskip c2 \<sim> c2` by simp
    have "c1 \<sim> SKIP"
      using assm skip_ua_impl_equiv by presburger
    hence "c2 \<sim> (c1 ;; c2)" by auto
    thus ?case using rdct by simp
  next
    assume assm: "\<not> skip_ua c1 \<and> skip_ua c2"
    hence "deskip (c1 ;; c2) = deskip c1" by simp
    hence rdct: "deskip (c1 ;; c2) \<sim> c1"
      using `deskip c1 \<sim> c1` by simp
    have "c2 \<sim> SKIP"
      using assm skip_ua_impl_equiv by presburger
    hence "c1 \<sim> (c1 ;; c2)" by auto
    thus ?case using rdct by simp
  next
    assume assm: "\<not> skip_ua c1 \<and> \<not> skip_ua c2"
    have expn:
      "deskip (c1 ;; c2)
        = ((deskip c1) ;; (deskip c2))"
      using assm deskip.simps(3)
      by presburger
    have "((deskip c1) ;; (deskip c2)) \<sim> (c1 ;; c2)"
      using `deskip c1 \<sim> c1` `deskip c2 \<sim> c2`
      by auto
    thus ?case
      using expn
      by presburger
  qed
next
  case (If b c1 c2)
  have
    "((skip_ua c1) \<and> (skip_ua c2))
      \<or> \<not> ((skip_ua c1) \<and> (skip_ua c2))"
    by simp
  thus ?case
  proof
    assume assm: "(skip_ua c1) \<and> (skip_ua c2)"
    hence isskip: "deskip (IF b THEN c1 ELSE c2) = SKIP" by simp
    have "c1 \<sim> SKIP \<and> c2 \<sim> SKIP"
      using assm skip_ua_impl_equiv
      by presburger
    hence "SKIP \<sim> (IF b THEN c1 ELSE c2)" by blast
    thus ?thesis using isskip by simp
  next
    assume assm: "\<not> ((skip_ua c1) \<and> (skip_ua c2))"
    hence
      "deskip (IF b THEN c1 ELSE c2)
        = (IF b THEN (deskip c1) ELSE (deskip c2))"
      by simp
    thus ?thesis
      using `deskip c1 \<sim> c1` `deskip c2 \<sim> c2`
      by auto
  qed
next
  case (While b c)
  have "deskip (WHILE b DO c) = (WHILE b DO (deskip c))"
    by simp
  thus ?case using `deskip c \<sim> c`
    using while_equiv by presburger
qed simp+

end
