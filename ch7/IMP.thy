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

(* Big step tweaks to simplify usage as found in
   the implementation included in the Isabelle source *)
declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]
inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= c,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1 ;; c2,s) \<Rightarrow> t"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

(* Small-step semantic rules from 7.3 *)
inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool"
  (infix "\<rightarrow>" 55) where
Assign: "(x ::= a,s) \<rightarrow> (SKIP,s(x := aval a s))" |
Seq1: "(SKIP;;c2,s) \<rightarrow> (c2,s)" |
Seq2: "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |
IfTrue: "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |
While: "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;;WHILE b DO c ELSE SKIP,s)"


(* Semantic helpers *)

(* Rule inversion equivalence lemmas from 7.2.3 *)
lemma skip_state_equiv:
  "(SKIP,s) \<Rightarrow> t \<longleftrightarrow> t = s" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS"
  thus "?RHS" by cases
next
  assume "?RHS"
  thus "?LHS" by (simp add: Skip)
qed

lemma assign_state:
  "(x ::= a,s) \<Rightarrow> t \<longleftrightarrow> t = s(x := aval a s)"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS"
  thus "?RHS" by cases
next
  assume "?RHS"
  thus "?LHS" using big_step.Assign by blast
qed

lemma inter_seq:
  "(c1 ;; c2,s1) \<Rightarrow> s3
    \<longleftrightarrow> (\<exists>s2. ((c1,s1) \<Rightarrow> s2 \<and> (c2,s2) \<Rightarrow> s3))"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS"
  thus "?RHS"
  proof cases
    case Seq thus ?thesis by auto
  qed
next
  assume "?RHS"
  thus "?LHS" using Seq by blast
qed

lemma while_split:
  "(WHILE b DO c,s) \<Rightarrow> t
    \<longleftrightarrow> (
      \<not> bval b s \<and> t = s
      \<or> bval b s
        \<and> (\<exists>s'. (c,s) \<Rightarrow> s'
            \<and> (WHILE b DO c,s') \<Rightarrow> t))"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS"
  thus "?RHS"
  proof cases
    case WhileFalse
    thus ?thesis by auto
  next
    case WhileTrue
    thus ?thesis by auto
  qed
next
  assume "?RHS"
  thus "?LHS"
    using WhileFalse WhileTrue by blast
qed

(* Associativity of Seq from 7.2.3 *)
lemma seq_assoc:
  "((c1 ;; c2) ;; c3,s) \<Rightarrow> s'
   \<longleftrightarrow> (c1 ;; (c2 ;; c3),s) \<Rightarrow> s'"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS"
  then obtain s1 s2 where
    "(c1,s) \<Rightarrow> s1" and
    "(c2,s1) \<Rightarrow> s2" and
    "(c3,s2) \<Rightarrow> s'"
    using inter_seq by blast
  thus "?RHS" by (simp add: Seq)
next
  assume "?RHS"
  then obtain s1 s2 where
    "(c1,s) \<Rightarrow> s1" and
    "(c2,s1) \<Rightarrow> s2" and
    "(c3,s2) \<Rightarrow> s'"
    using inter_seq by blast
  thus "?LHS"
    using Seq by blast
qed

(* Big-step equivalence from 7.2.4 *)
abbreviation equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool"
  (infix "\<sim>" 50) where
"c \<sim> c' \<equiv> (\<forall>s. \<forall>t. ((c,s) \<Rightarrow> t = (c',s) \<Rightarrow> t))"

(* While is equivalent to a single unfold of itself *)
lemma while_is_unfolded_while:
  "(WHILE b DO c)
    \<sim> (IF b THEN c ;; WHILE b DO c ELSE SKIP)"
  (is "?LHS \<sim> ?RHS")
proof -
  have "(?RHS,s) \<Rightarrow> t" if assm: "(?LHS,s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case WhileTrue
      from this `bval b s` `(?LHS,s) \<Rightarrow> t`
      obtain s'
        where "(c,s) \<Rightarrow> s'" and "(?LHS,s') \<Rightarrow> t"
        by blast
      hence "(c ;; ?LHS,s) \<Rightarrow> t" by (rule Seq)
      thus ?thesis using `bval b s` by auto
    next
      case WhileFalse
      thus ?thesis by auto
    qed
  qed
  moreover
  have "(?LHS,s) \<Rightarrow> t" if assm: "(?RHS,s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case IfTrue
      from this inter_seq obtain s'
        where "(c,s) \<Rightarrow> s'" and "(?LHS,s') \<Rightarrow> t"
        by blast
      thus ?thesis using IfTrue by blast
    next
      case IfFalse
      hence "s = t" using skip_state_equiv by simp
      thus ?thesis using IfFalse by blast
    qed
  qed
  ultimately
  show ?thesis by blast
qed

(* The previous proof is likely clearer,
   but all that inductive_case stuff allows
   full auto here *)
lemma "(WHILE b DO c) \<sim> (IF b THEN c ;; WHILE b DO c ELSE SKIP)"
  by blast

(* A command in both if clauses is equivalent
   to the command *)
lemma if_both_com_is_com:
  "(IF b THEN c ELSE c) \<sim> c"
  by blast

(* Big-step equivalence is an equivalence relation *)
theorem refl_equiv_c: "c \<sim> c" by auto
theorem sym_equiv_c: "c1 \<sim> c2 \<Longrightarrow> c2 \<sim> c1" by auto
theorem trans_equiv_c: "c1 \<sim> c2 \<and> c2 \<sim> c3 \<Longrightarrow> c1 \<sim> c3"
  by auto

(* IMP is deterministic from 7.2.5 *)
theorem imp_deterministic:
  "(c,s) \<Rightarrow> t \<Longrightarrow> (c,s) \<Rightarrow> t' \<Longrightarrow> t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  fix b c s s1 t t'
  assume "bval b s"
    and "(c,s) \<Rightarrow> s1"
    and "(WHILE b DO c,s1) \<Rightarrow> t"
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s1"
  assume IHw: "\<And>t'. (WHILE b DO c,s1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with `bval b s` obtain s1' where
    c: "(c,s) \<Rightarrow> s1'" and
    w: "(WHILE b DO c,s1') \<Rightarrow> t'"
    by auto
  from c IHc have "s1' = s1" by blast
  with w IHw show "t' = t" by blast
qed blast+

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