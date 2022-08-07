theory Exercise4
  imports IMP
begin

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
var: "(V x,s) \<leadsto> N (s x)" |
ints: "(Plus (N i) (N j),s) \<leadsto> N (i + j)" |
fplus: "(Plus i j,s) \<leadsto> a \<Longrightarrow> (Plus (Plus i j) b,s) \<leadsto> (Plus a b)" |
splus: "(Plus i j,s) \<leadsto> b \<Longrightarrow> (Plus a (Plus i j),s) \<leadsto> (Plus a b)"

lemmas astep_induct = astep.induct[split_format(complete)]

theorem astep_preserve: "(a,s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep_induct)
  fix x s
  show "aval (V x) s = aval (N (s x)) s" by simp
next
  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by simp
next
  fix i j s a b
  assume "(Plus i j,s) \<leadsto> a"
    and "aval (Plus i j) s = aval a s"
  thus "aval (Plus (Plus i j) b) s = aval (Plus a b) s"
    by simp
next
  fix i j s b a
  assume "(Plus i j,s) \<leadsto> b"
    and "aval (Plus i j) s = aval b s"
  thus "aval (Plus a (Plus i j)) s = aval (Plus a b) s"
    by simp
qed

(* To be honest, this other solution looks like it is a
   much more sensible choice here:
    https://github.com/kolya-vasiliev/concrete-semantics/blob/ae2a4b32ec63766e6a11e043d85d082c70eeaebc/Chap_seven.thy#L68-L69

   I debated switching to that approach after I saw it,
   but I decided in interest of transparency to stick with
   my initial approach for now. However, should this
   small-step semantic be needed for later exercises, I
   won't be shocked if I need to come back and rename my
   current implementation so that I can use that more
   productive implementation. *)

end
