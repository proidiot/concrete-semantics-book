theory BigStepEquiv
  imports BigStep
begin

(*
  Two programs are big step equivalent (which we show with \<sim>) if the same
  start state always leads the two programs to reach the same end state.
*)
abbreviation big_step_equiv :: "command \<Rightarrow> command \<Rightarrow> bool" (infix "\<sim>" 50) where
  "a \<sim> b \<equiv> \<forall>s. \<forall>t. ((a,s) \<leadsto> t) \<longleftrightarrow> ((b,s) \<leadsto> t)"

lemma "a \<sim> a" by auto

lemma "a \<sim> b \<Longrightarrow> b \<sim> a" by auto

lemma "a \<sim> b \<and> b \<sim> c \<Longrightarrow> a \<sim> c" by auto

end