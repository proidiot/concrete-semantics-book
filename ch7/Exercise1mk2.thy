theory Exercise1mk2
  imports Sat
begin

fun srest :: "com \<Rightarrow> bexp \<Rightarrow> bexp" where
"srest SKIP b = b" |
"srest (v ::= a) b = (And b (VarEq v a))" |
"srest (c1 ;; c2) b = b" |
"srest (IF b1 THEN c1 ELSE c2) b2 = (

fun rassigned :: "com \<Rightarrow> bexp \<Rightarrow> vname set" where
"rassigned SKIP b = {}" |
"rassigned (v ::= a) b = {v}" |
"rassigned (c1 ;; c2) b
  = (rassigned c1 b) \<union> (rassigned c2 (srest c1 b))" |
"rassigned (IF b1 THEN c1 ELSE c2) b2
  = (if (Sat (And b1 b2))
      then (rassigned c1 (And b1 b2))
      else {})
    \<union> (if (Sat (And (Not b1) b2))
        then (rassigned c2 (And (Not b1) b2))
        else {})" |
"rassigned (WHILE b1 DO c) b2
  = (if (Sat (And b1 b2))
      then (rassigned c (srest c (And b1 b2)))
      else {})"

(* NOTE: I did not notice the split_format behavior
   until I saw it used by someone else to solve this
   problem (i.e. https://github.com/kolya-vasiliev/concrete-semantics/blob/ae2a4b32ec63766e6a11e043d85d082c70eeaebc/Big_Step.thy#L68-L84),
   but it is briefly documented in the Isar reference
   manual. *)
theorem not_assigned_oe_implies_unmodified:
  "\<lbrakk> (c,s) \<Rightarrow> t; x \<notin> assigned_oe c \<rbrakk> \<Longrightarrow> s x = t x"
  apply (induction rule: big_step.induct[split_format(complete)])
        apply auto
  done

(* I tried creating a more accurate version of assigned
   with the help of satisfiability of the guards seen
   given all previous guards and assignments, but this
   quickly became very complex. Furthermore, I have
   heard on multiple occasions that variable assignment
   and value reachability calculations are in general at
   least uncomputable, and so overapproximations or
   underapproximations are typically used instead (with
   ongoing interest in particular overapproximation or
   underapproximation formulations which could be more
   valuable in the appropriate context). I admit to
   having not seen the specific result myself, much less
   explored the proof, but it does seem like the wrong
   tree to be barking up in this introductory material.*)

end