theory Sat
  imports IMP
begin

fun Sat :: "bexp \<Rightarrow> bool" where
"Sat (Bc b) = b" |
"Sat (Not b) = (\<exists>s. \<not> bval b s)" |
"Sat (And a b) = (\<exists>s. bval a s \<and> bval b s)" |
"Sat (Less a b) = (\<exists>s. aval a s < aval b s)"

theorem sat_equiv: "Sat a \<longleftrightarrow> (\<exists>s. bval a s)"
  apply (induction a)
     apply auto
  done

theorem unsat_contradiction: "\<not> Sat (And a (Not a))"
  by simp

theorem sat_taut_incl: "(\<forall>s. bval a s) \<Longrightarrow> Sat b \<Longrightarrow> Sat (And a b)"
  apply (induction b arbitrary: a)
     apply simp_all
  done

theorem sat_split: "Sat (And a b) \<Longrightarrow> Sat a \<and> Sat b"
proof -
  assume "Sat (And a b)"
  hence "\<exists>s. bval a s \<and> bval b s" by simp
  hence "(\<exists>s. bval a s) \<and> (\<exists>s. bval b s)" by auto
  thus ?thesis using sat_equiv by simp
qed

end