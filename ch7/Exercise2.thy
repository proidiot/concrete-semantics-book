theory Exercise2
  imports IMP
begin

(* NOTE: Just as with assigned_oe from Exercise 1,
   skip_ua is an inaccurate approximation (in this case,
   an underapproximation of SKIP-equivalent commands, or
   an overapproximation of non-SKIP-equivalent
   commands. Also of note, given the command WHILE g
   DO c, if c is equivalent to SKIP then the while loop
   would never terminate (which we could reasonably say
   is not equivalent behavior to SKIP). Since we have
   already chosen not to explore satisfiability of guards
   with skip_ua, we will just say the WHILE g DO c form
   is not equivalent to SKIP. *)
fun skip_ua :: "com \<Rightarrow> bool" where
skip: "skip_ua (SKIP) = True" |
assign: "skip_ua (x ::= a) = False" |
seq: "skip_ua (a ;; b) = ((skip_ua a) \<and> (skip_ua b))" |
ifthen: "skip_ua (IF g THEN a ELSE b)
  = ((skip_ua a) \<and> (skip_ua b))" |
whiledo: "skip_ua (WHILE g DO a) = False"

theorem skip_ua_impl_equiv: "skip_ua c \<Longrightarrow> c \<sim> SKIP"
proof (induction c)
  case (Seq c1 c2)
  hence "c1 \<sim> SKIP" and "c2 \<sim> SKIP" by simp_all
  hence "(c1 ;; c2) \<sim> (SKIP ;; SKIP)" by blast
  thus "(c1 ;; c2) \<sim> SKIP" by auto
next
  case (If b c1 c2)
  hence "c1 \<sim> SKIP" and "c2 \<sim> SKIP" by simp_all
  thus "(IF b THEN c1 ELSE c2) \<sim> SKIP"
    by blast
qed auto

end
