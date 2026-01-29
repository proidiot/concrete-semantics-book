theory BigStep
  imports Sugar
begin

(*
  The Big Step Semantic describes how the state is changed by a program.
  We are adding some syntax here to help, specifically "(c,s) \<leadsto> t" will
  mean that running the program c from the starting state s will result
  in ending state t. Recall that the state is just a key-value store
  with variable names mapped to integers.

  Remember that this is declarative and not procedural. These rules
  aren't necessarily describing how to build a state change, but rather
  letting you know whether some described state change is valid or not.
  This becomes clear in the definition of the sequence rule, for example,
  where we talk about some otherwise undefined intermediate state which
  we don't actually care about beyond whether we know that state exists
  and satisfies the requirements.
*)
inductive big_step :: "command \<times> state \<Rightarrow> state \<Rightarrow> bool"
  (infix "\<leadsto>" 55)
  where

(* The SKIP command does not change the state. *)
  Skip:
"(SKIP,s) \<leadsto> s"

(* Assignment only replaces the value of the one key in the state. *)
| Assignment:
"(x ::= a,s) \<leadsto> s replacing x with (arith_val a s)"

(*
  We know that sequential commands will take us from state `s` to state
  `t` only if there is some other state `x` which exists between the two
  commands in the sequence.
*)
| Sequence:
"(a,s) \<leadsto> x \<and> (b,x) \<leadsto> t
\<Longrightarrow> (a ;; b,s) \<leadsto> t"

(*
  When `g` is true, the total state change of this if-block will be the
  same as if only the command `a` ran from state `s`.
*)
| BranchTrue:
"(bool_val g s) \<and> (a,s) \<leadsto> t
\<Longrightarrow> (IF g THEN a ELSE b FI,s) \<leadsto> t"

(*
  When `g` is false, the total state change of this if-block will be the
  same as if only the command `b` ran from state `s`. *)
| BranchFalse:
"(\<not> bool_val g s) \<and> (b,s) \<leadsto> t
\<Longrightarrow> (IF g THEN a ELSE b FI,s) \<leadsto> t"

(* When `g` is false, the while-loop doesn't change the state. *)
| LoopFalse:
"(\<not> bool_val g s)
\<Longrightarrow> (WHILE g DO c OD,s) \<leadsto> s"

(*
  When `g` is true, the total state change of this while-loop will be
  the same as if the command `c` ran from state `s` followed by the
  state change of this while-loop having run from the intermediate
  state after `c` ran once from state `s`.
*)
| LoopTrue:
"(bool_val g s) \<and> (c,s) \<leadsto> x \<and> (WHILE g DO c OD,x) \<leadsto> t
\<Longrightarrow> (WHILE g DO c OD,s) \<leadsto> t"

end