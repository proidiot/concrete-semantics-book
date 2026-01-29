theory Sugar
  imports IMP
begin

(* Syntactic sugar for our examples *)

(* Extract unambiguous constants *)
declare [[coercion "Num"]]
declare [[coercion_enabled]]
abbreviation "TRUE \<equiv> Bconst True"
abbreviation "FALSE \<equiv> Bconst False"

(* Shell-like variable name behavior *)
syntax "_Var" :: "id \<Rightarrow> arith_exp" ("${_}")
ML \<open>
  fun mk_string_term x = HOLogic.mk_string x;

  fun var_tr [Free (x, _)] = Const (@{const_syntax Var}, dummyT) $ mk_string_term x
    | var_tr [Const (x, _)] = Const (@{const_syntax Var}, dummyT) $ mk_string_term (Long_Name.base_name x)
    | var_tr _ = raise TERM ("var_tr", []);
\<close>
parse_translation \<open> [(@{syntax_const "_Var"}, K var_tr)] \<close>

syntax "_Assign" :: "id \<Rightarrow> arith_exp \<Rightarrow> command" ("_ ::= _" [1000, 21] 20)
ML \<open>
  fun assign_tr [Free (x, _), t2] = Const (@{const_syntax Assign}, dummyT) $ mk_string_term x $ t2
    | assign_tr [Const (x, _), t2] = Const (@{const_syntax Assign}, dummyT) $ mk_string_term (Long_Name.base_name x) $ t2
    | assign_tr ts = raise TERM ("assign_tr: Expected identifier on LHS", ts);
\<close>
parse_translation \<open> [(@{syntax_const "_Assign"}, K assign_tr)] \<close>

(* Structural syntax with precedence *)
notation

  (* Math precedence (higher) *)
  Plus (infixl "+" 60)
  and Less (infix "<" 50)

  (* Logic precedence (medium) *)
  and Not ("!_" [40] 40)
  and And (infixr "&&" 35)

  (* Language precedence (lower) *)
  and Sequence ("_;;/ _" [11, 10] 10)
  and CondBranch ("IF _/ THEN _/ ELSE _/ FI" [0, 0, 0] 20)
  and CondLoop ("WHILE _/ DO _/ OD" [0, 0] 20)

(* Less confusing than Isabelle syntax *)
syntax
  "_StateUpdate" :: "state \<Rightarrow> var_name \<Rightarrow> int_val \<Rightarrow> state" ("_ replacing _ with _" [1000, 0, 0] 1000)

translations
  "s replacing x with v " \<rightleftharpoons> "s(x := v)"


(* Examples *)
definition "sum_to_ten ==
  sum ::= 0;;
  i   ::= 0;;
  WHILE (${i} < 11) DO
    sum ::= ${sum} + ${i};;
    i   ::= ${i} + 1
  OD"

end