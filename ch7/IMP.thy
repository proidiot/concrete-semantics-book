theory IMP
  imports Main
begin

(* Data type definitions *)

(* Arithmetic expression (i.e. aexp) primitives from 3.1.1 *)
type_synonym vname = string
datatype aexp =
  N int
  | V vname
  | Plus aexp aexp

(* Variable state primitives from 3.1.2 *)
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(* Boolean expression (i.e. bexp) primitive from 3.2 *)
datatype bexp =
  Bc bool
  | Not bexp
  | And bexp bexp
  | Less aexp aexp

(* IMP language command (i.e. com) specification from 7.1 *)
datatype com =
  SKIP
  | Assign vname aexp ("_ ::= _")
  | Seq com com ("_ ;; _")
  | If bexp com com ("IF _ THEN _ ELSE _")
  | While bexp com ("WHILE _ DO _")


(* Convenient helpers *)
fun Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or a b = (Not (And (Not a) (Not b)))"

fun Cond :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Cond a b = (Or (Not a) b)"

fun VarEq :: "vname \<Rightarrow> aexp \<Rightarrow> bexp" where
"VarEq x a = (And (Not (Less (V x) a)) (Not (Less a (V x))))"

(* Semantic definitions *)

(* Arithmetic expression evaluation from 3.1.2 *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s= s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* Boolean expression evaluation from 3.2 *)
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

(* Big-step semantics for IMP from 7.2.1 *)
inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool"
  (infix "\<Rightarrow>" 55) where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "
  \<lbrakk> (c1,s1) \<Rightarrow> s2; (c2,s2) \<Rightarrow> s3 \<rbrakk>
  \<Longrightarrow> (c1;;c2,s1) \<Rightarrow> s3
" |
IfTrue: "
  \<lbrakk> bval b s; (c1,s) \<Rightarrow>t \<rbrakk>
  \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<Rightarrow> t
" |
IfFalse: "
  \<lbrakk> \<not>bval b s; (c2,s) \<Rightarrow> t \<rbrakk>
  \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<Rightarrow> t
" |
WhileFalse: "
  \<not>bval b s
  \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s
" |
WhileTrue: "
  \<lbrakk> bval b s1; (c,s1) \<Rightarrow> s2; (WHILE b DO c,s2) \<Rightarrow> s3 \<rbrakk>
  \<Longrightarrow> (WHILE b DO c,s1) \<Rightarrow> s3
"

inductive big_step_induct :: "com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
"(c,s) \<Rightarrow> t \<Longrightarrow> big_step_induct c s t"

(* Small-step semantic rules from 7.3 *)
inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool"
  (infix "\<rightarrow>" 55) where
Assign: "(x ::= a,s) \<rightarrow> (SKIP,s(x := aval a s))" |
Seq1: "(SKIP;;c2,s) \<rightarrow> (c2,s)" |
Seq2: "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |
IfTrue: "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |
While: "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;;WHILE b DO c ELSE SKIP,s)"

(* Reflexive transitive closure from 4.5.2 *)
(* Needed for closure of small-step semantic *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

(* Closure of small-step sequences from 7.3 *)
abbreviation small_step_closure :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool"
  (infix "\<rightarrow>*" 55) where
"x \<rightarrow>* y \<equiv> star small_step x y"

end