theory Exercise1
  imports IMP
begin

(* NOTE: This is an over-estimate of potentially
   assigned variables. Specifically, it is possible that
   the collection of reachable states is restricted by
   execution within the sequence or while commands. This
   restriction could then reduce the collection of
   assignable variables of an if or while command. For
   example, consider:
      assigned (
        IF (Less (V a) (N 3))
        THEN (a ::= 3)
        ELSE (b ::=3)
      )
   In isolation, the answer would rightly be {a,b}.
   However, this could materially change if the state
   space going into the evaluation is restricted by an
   earlier command from a sequence or while command. For
   example:
      assigned (
        (a := 1) ;; (
        IF (Less (V a) (N 3))
        THEN (a ::= 3)
        ELSE (b ::= 3)
      ))
   In this latter case, the answer would be {a} and not
   {a,b}. While the initial state is completely
   unrestricted, this need not be the case for
   intermediate states.
*)
fun assigned_oe :: "com \<Rightarrow> vname set" where
"assigned_oe SKIP = {}" |
"assigned_oe (v ::= a) = {v}" |
"assigned_oe (a;;b)
  = (assigned_oe a) \<union> (assigned_oe b)" |
"assigned_oe (IF b THEN c1 ELSE c2)
  = (assigned_oe c1) \<union> (assigned_oe c2)" |
"assigned_oe (WHILE b DO c) = (assigned_oe c)"

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