theory IMP
  imports Main
begin

(* Data type definitions *)

(* Arithmetic expression (i.e. aexp) primitives from
   3.1.1 *)
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

(* IMP language command (i.e. com) specification from
   7.1 *)
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
    "VarEq x a =
      (And
        (Not (Less (V x) a))
        (Not (Less a (V x))))"

(* Semantic definitions *)

(* Arithmetic expression evaluation from 3.1.2 *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
    "aval (N n) s = n" |
    "aval (V x) s = s x" |
    "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

lemma unequal_plus:
    "n \<noteq> 0
    \<Longrightarrow> aval (V x) s \<noteq> aval (Plus (V x) (N n)) s"
  by simp


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
Seq:
    "\<lbrakk> (c1,s1) \<Rightarrow> s2; (c2,s2) \<Rightarrow> s3 \<rbrakk>
    \<Longrightarrow> (c1;;c2,s1) \<Rightarrow> s3" |
IfTrue:
    "\<lbrakk> bval b s; (c1,s) \<Rightarrow>t \<rbrakk>
    \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<Rightarrow> t" |
IfFalse:
    "\<lbrakk> \<not>bval b s; (c2,s) \<Rightarrow> t \<rbrakk>
    \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<Rightarrow> t" |
WhileFalse:
    "\<not>bval b s
    \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
    "\<lbrakk> bval b s1; (c,s1) \<Rightarrow> s2; (WHILE b DO c,s2) \<Rightarrow> s3 \<rbrakk>
    \<Longrightarrow> (WHILE b DO c,s1) \<Rightarrow> s3"

(* Big-step tweaks to simplify usage as found in
   the implementation included in the Isabelle source *)
declare big_step.intros [intro]
lemmas big_step_induct =
    big_step.induct[split_format(complete)]
inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= c,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1 ;; c2,s) \<Rightarrow> t"
inductive_cases IfE[elim!]:
    "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

(* Small-step semantic rules from 7.3 *)
inductive small_step ::
    "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool"
  (infix "\<rightarrow>" 55) where
Assign: "(x ::= a,s) \<rightarrow> (SKIP,s(x := aval a s))" |
Seq1: "(SKIP;;c2,s) \<rightarrow> (c2,s)" |
Seq2:
    "(c1,s) \<rightarrow> (c1',s')
    \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |
IfTrue:
    "bval b s
    \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse:
    "\<not>bval b s
    \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |
While:
    "(WHILE b DO c,s)
    \<rightarrow> (IF b THEN c;;WHILE b DO c ELSE SKIP,s)"

(* Small-step tweaks *)
lemmas small_step_induct =
    small_step.induct[split_format(complete)]
declare small_step.intros[intro,simp]
inductive_cases SmallSkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
inductive_cases SmallAssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
inductive_cases SmallSeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
inductive_cases SmallIfE[elim!]:
    "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases SmallWhileE[elim]:
    "(WHILE b DO c,s) \<rightarrow> ct"



(* Semantic helpers *)

(* Rule inversion equivalence lemmas from 7.2.3 *)
lemma skip_state_equiv:
    "(SKIP,s) \<Rightarrow> t \<longleftrightarrow> t = s"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS" thus "?RHS" by cases
next
  assume "?RHS" thus "?LHS" by (simp add: Skip)
qed

lemma assign_state:
    "(x ::= a,s) \<Rightarrow> t \<longleftrightarrow> t = s(x := aval a s)"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS" thus "?RHS" by cases
next
  assume "?RHS" thus "?LHS"
    using big_step.Assign by blast
qed

lemma inter_seq:
    "(c1 ;; c2,s1) \<Rightarrow> s3
    \<longleftrightarrow> (\<exists>s2. ((c1,s1) \<Rightarrow> s2 \<and> (c2,s2) \<Rightarrow> s3))"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS" thus "?RHS"
  proof cases
    case Seq thus ?thesis by auto
  qed
next
  assume "?RHS" thus "?LHS" using Seq by blast
qed

lemma while_split:
    "(WHILE b DO c,s) \<Rightarrow> t
    \<longleftrightarrow> ((\<not> bval b s \<and> t = s)
         \<or> (bval b s
            \<and> (\<exists>s'.
                (c,s) \<Rightarrow> s'
                \<and> (WHILE b DO c,s') \<Rightarrow> t)))"
  (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume "?LHS"
  thus "?RHS"
  proof cases
    case WhileFalse thus ?thesis by auto
  next
    case WhileTrue thus ?thesis by auto
  qed
next
  assume "?RHS" thus "?LHS"
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
  thus "?LHS" using Seq by blast
qed

(* Big-step equivalence from 7.2.4 *)
abbreviation equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool"
  (infix "\<sim>" 50) where
    "c \<sim> c' \<equiv> (\<forall>s. \<forall>t. ((c,s) \<Rightarrow> t = (c',s) \<Rightarrow> t))"

lemma non_equiv_c:
    "(\<exists>s. \<exists>t. ((c1,s) \<Rightarrow> t \<and> \<not>((c2,s) \<Rightarrow> t)))
    \<Longrightarrow> \<not>(c1 \<sim> c2)"
proof -
  assume "\<exists>s. \<exists>t. ((c1,s) \<Rightarrow> t \<and> \<not>((c2,s) \<Rightarrow> t))"
  hence "\<exists>s. \<exists>t. \<not>((c1,s) \<Rightarrow> t \<longrightarrow> (c2,s) \<Rightarrow> t)" by simp
  hence "\<exists>s. \<exists>t. ((c1,s) \<Rightarrow> t \<noteq> (c2,s) \<Rightarrow> t)" by auto
  hence "\<not>(\<forall>s. \<forall>t. ((c1,s) \<Rightarrow> t = (c2,s) \<Rightarrow> t))" by simp
  thus ?thesis by simp
qed


(* While is equivalent to a single unfold of itself *)
lemma while_is_unfolded_while:
    "(WHILE b DO c)
    \<sim> (IF b THEN c ;; WHILE b DO c ELSE SKIP)"
  (is "?LHS \<sim> ?RHS")
proof -
  have "(?RHS,s) \<Rightarrow> t" if assm: "(?LHS,s) \<Rightarrow> t" for s t
  proof -
    show ?thesis using assm
    proof cases
      case WhileTrue
      then obtain s' where
          "(c,s) \<Rightarrow> s'" and
          "(?LHS,s') \<Rightarrow> t"
        using `bval b s` `(?LHS,s) \<Rightarrow> t` by blast
      hence "(c ;; ?LHS,s) \<Rightarrow> t" by (rule Seq)
      thus ?thesis using `bval b s` by auto
    next
      case WhileFalse thus ?thesis by auto
    qed
  qed
  moreover
  have "(?LHS,s) \<Rightarrow> t" if assm: "(?RHS,s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case IfTrue
      then obtain s' where
          "(c,s) \<Rightarrow> s'" and
          "(?LHS,s') \<Rightarrow> t"
        using inter_seq by blast
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
lemma
    "(WHILE b DO c)
    \<sim> (IF b THEN (c ;; WHILE b DO c) ELSE SKIP)"
  by blast

(* A command in both if clauses is equivalent
   to the command (from 7.2.4) *)
lemma if_both_com_is_com:
    "(IF b THEN c ELSE c) \<sim> c"
  by blast

(* Equivalent commands yeild equivalent while loops
   (from 7.2.4) *)
lemma while_equiv_complex:
    "\<lbrakk> (WHILE b DO c,s) \<Rightarrow> t ; c \<sim> c' \<rbrakk>
    \<Longrightarrow> (WHILE b DO c',s) \<Rightarrow> t"
  apply (
      induction "WHILE b DO c" s t
      arbitrary: b c
      rule: big_step_induct)
  apply blast+
  done

corollary while_equiv:
    "c \<sim> c' \<Longrightarrow> ((WHILE b DO c) \<sim> (WHILE b DO c'))"
  by (meson while_equiv_complex)

lemma if_guard_equiv:
    "bval b1 s = bval b2 s
    \<Longrightarrow> (IF b1 THEN c1 ELSE c2,s) \<Rightarrow> t
        = (IF b2 THEN c1 ELSE c2,s) \<Rightarrow> t"
  by auto


(* Big-step equivalence is an equivalence relation *)
theorem refl_equiv_c: "c \<sim> c" by auto
theorem sym_equiv_c: "c1 \<sim> c2 \<Longrightarrow> c2 \<sim> c1" by auto
theorem trans_equiv_c:
    "c1 \<sim> c2 \<and> c2 \<sim> c3 \<Longrightarrow> c1 \<sim> c3"
  by auto


(* IMP is deterministic from 7.2.5 *)
theorem imp_deterministic:
    "(c,s) \<Rightarrow> t \<Longrightarrow> (c,s) \<Rightarrow> t' \<Longrightarrow> t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  fix b c s s1 t t'
  assume
      "bval b s" and
      IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s1" and
      IHw: "\<And>t'. (WHILE b DO c,s1) \<Rightarrow> t' \<Longrightarrow> t' = t" and
      "(WHILE b DO c,s) \<Rightarrow> t'"
  then obtain s1' where
      c: "(c,s) \<Rightarrow> s1'" and
      w: "(WHILE b DO c,s1') \<Rightarrow> t'"
    using WhileE by metis
  hence "s1' = s1" using IHc by blast
  thus "t' = t" using w IHw by blast
qed blast+

corollary diff_end_impl_diff_com:
    "\<lbrakk> t \<noteq> t'; (c,s) \<Rightarrow> t; (c',s) \<Rightarrow> t' \<rbrakk>
    \<Longrightarrow> \<not>(c \<sim> c')"
  using imp_deterministic by force

(* Small-step determinism *)
theorem small_step_imp_deterministic:
    "cs \<rightarrow> cs1 \<Longrightarrow> cs \<rightarrow> cs2 \<Longrightarrow> cs2 = cs1"
  by (induction arbitrary: cs2 rule: small_step.induct,
      blast+)


(* Reflexive transitive closure from 4.5.2 *)
(* Needed for closure of small-step semantic *)
inductive star ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r where
    refl: "star r x x" |
    step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
    "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof (induction rule: star.induct)
  case refl thus ?case by simp
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct =
    star.induct[
        of "r :: 'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool",
        split_format(complete)]
declare star.refl[simp,intro]
lemma star_base[simp,intro]: "r x y \<Longrightarrow> star r x y"
  by (meson star.simps)

inductive star2 ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for r where
    refl2: "star2 r x x" |
    step2: "star2 r x y \<Longrightarrow> r y z \<Longrightarrow> star2 r x z"

lemma star2_impl_star: "star2 r x y \<Longrightarrow> star r x y"
proof (induction rule: star2.induct)
  case refl2 thus ?case by simp
next
  case step2 thus ?case by (meson star_base star_trans)
qed

lemma rel_impl_star2: "r x y \<Longrightarrow> star2 r x y"
  by (meson star2.refl2 star2.step2)

lemma star2_transpose:
    "star2 r y z \<Longrightarrow> r x y \<Longrightarrow> star2 r x z"
proof (induction rule: star2.induct)
  case refl2 thus ?case by (rule rel_impl_star2)
next
  case step2 thus ?case by (meson star2.step2)
qed

lemma star_impl_star2: "star r x y \<Longrightarrow> star2 r x y"
proof (induction rule: star.induct)
  case refl thus ?case by (rule star2.refl2)
next
  case step thus ?case by (simp add: star2_transpose)
qed

lemmas star2_induct =
    star2.induct[
        of "r :: 'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool",
        split_format(complete)]

(* Closure of small-step sequences from 7.3 *)
abbreviation small_step_closure ::
    "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool"
  (infix "\<rightarrow>*" 55) where
    "x \<rightarrow>* y \<equiv> star small_step x y"

(* Small-step based determinism proof from 7.3 *)
lemma imp_deterministic_small_step:
    "\<lbrakk> cs \<rightarrow> cs'; cs \<rightarrow> cs'' \<rbrakk> \<Longrightarrow> cs'' = cs'"
  by (induction
        arbitrary: cs''
        rule: small_step.induct,
      blast+)

(* Small-step equivalence is preserved through the
   addition of a sequential suffix, proof from 7.3 *)
lemma seq_suffix:
    "(c1, s1) \<rightarrow>* (c, s2)
    \<Longrightarrow> (c1 ;; c2, s1) \<rightarrow>* (c ;; c2, s2)"
proof (induction rule: star_induct)
  case refl thus ?case by simp
next
  case step thus ?case by (meson Seq2 star.simps)
qed

(* Sequential transitivity of small steps *)
lemma star_seq:
    "\<lbrakk> (c1, s1) \<rightarrow>* (SKIP, s2); (c2, s2) \<rightarrow>* (SKIP, s3) \<rbrakk>
    \<Longrightarrow> (c1 ;; c2, s1) \<rightarrow>* (SKIP, s3)"
  by (blast intro: star.step seq_suffix star_trans)

(* Big-step implies small-step eventual termination,
   from 7.3.1 *)
theorem big_step_impl_small_term:
    "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s
  show "(SKIP, s) \<rightarrow>* (SKIP, s)"
    by (rule star.intros(1))
next
  fix x a s
  show "(x ::= a, s) \<rightarrow>* (SKIP, s(x := aval a s))"
    using star.simps small_step.Assign by metis
next
  fix c1 s1 s2 c2 s3
  assume
      "(c1, s1) \<rightarrow>* (SKIP, s2)"
      and "(c2, s2) \<rightarrow>* (SKIP, s3)"
  thus "(c1 ;; c2, s1) \<rightarrow>* (SKIP, s3)"
    by (rule star_seq)
next
  fix b s c1 t c2
  assume "bval b s" and "(c1,s) \<Rightarrow> t"
  hence "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
    by (rule big_step.IfTrue)
  assume "(c1,s) \<rightarrow>* (SKIP,t)"
  thus "(IF b THEN c1 ELSE c2,s) \<rightarrow>* (SKIP,t)"
    using `bval b s` small_step.IfTrue
    by (meson star.simps)
next
  fix b s c1 t c2
  assume "\<not>bval b s" and "(c2,s) \<Rightarrow> t"
  hence "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
    by (rule big_step.IfFalse)
  assume "(c2,s) \<rightarrow>* (SKIP,t)"
  thus "(IF b THEN c1 ELSE c2,s) \<rightarrow>* (SKIP,t)"
    using `\<not>bval b s` small_step.IfFalse
    by (meson star.simps)
next
  fix b s c
  have
      while_unfold: "(WHILE b DO c,s)
      \<rightarrow> (IF b THEN (c ;; WHILE b DO c) ELSE SKIP,s)"
    by blast
  assume "\<not>bval b s"
  hence
      "(IF b THEN (c ;; WHILE b DO c) ELSE SKIP,s)
      \<rightarrow> (SKIP,s)"
    by (rule small_step.IfFalse)
  thus "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)"
    using while_unfold by (metis star.simps)
next
  fix b s c s' t
  have
      while_unfold: "(WHILE b DO c,s)
      \<rightarrow> (IF b THEN (c ;; WHILE b DO c) ELSE SKIP,s)"
    by blast
  assume "bval b s"
  hence
      while_unroll: "(
          IF b
          THEN (c ;; WHILE b DO c)
          ELSE SKIP,s)
      \<rightarrow> (c ;; WHILE b DO c,s)"
    by simp
  assume
      "(WHILE b DO c,s') \<rightarrow>* (SKIP,t)"
      and "(c,s) \<rightarrow>* (SKIP,s')"
  hence "(c ;; WHILE b DO c,s) \<rightarrow>* (SKIP,t)"
    by (simp add: star_seq)
  thus "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)"
    using while_unfold while_unroll by (meson star.step)
qed

(* Small-step prepends to big-step, from 7.3 *)
lemma small_step_prepend_big_step:
    "\<lbrakk> cs \<rightarrow> cs'; cs' \<Rightarrow> t \<rbrakk> \<Longrightarrow> cs \<Rightarrow> t"
  by (induction arbitrary: t rule: small_step.induct,
      auto)

(* Small-step eventual termination implies big-step,
   from 7.3 *)
theorem small_term_impl_big_step:
    "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
proof (induction cs "(SKIP,t)" rule: star.induct)
  case refl thus ?case by (rule big_step.Skip)
next
  case step thus ?case
    by (simp add: small_step_prepend_big_step)
qed

corollary big_step_small_term_equiv:
    "cs \<Rightarrow> t \<longleftrightarrow> cs \<rightarrow>* (SKIP,t)"
  using
      big_step_impl_small_term
      small_term_impl_big_step
  by blast

definition final :: "(com \<times> state) \<Rightarrow> bool" where
    "final cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

corollary final_split:
    "final (c,s) \<longleftrightarrow> \<not>(\<exists>d. \<exists>t. (c,s) \<rightarrow> (d,t))"
  by (simp add: final_def)

(* Only SKIP is in final state, from 7.3 *)
lemma skip_finality: "final (c,s) \<longleftrightarrow> (c = SKIP)"
  by (simp add: final_def, induction c, blast+)

theorem big_step_term:
    "(\<exists>t. cs \<Rightarrow> t) \<longleftrightarrow> (\<exists>cs'. (cs \<rightarrow>* cs' \<and> final cs'))"
  by (simp add: big_step_small_term_equiv skip_finality)

theorem small_step_tail_equiv:
    "(c1 \<sim> c2)
    \<longleftrightarrow> (\<forall>s.\<forall>t. (c1,s) \<rightarrow>* (SKIP,t)
        = (c2,s) \<rightarrow>* (SKIP,t))"
    using
      big_step_impl_small_term
      small_term_impl_big_step
    by blast

lemma small_step_antireflexivity:
    "((c,s) \<rightarrow> (d,t)) \<Longrightarrow> (d \<noteq> c)"
  by (induction rule: small_step_induct, simp_all)

lemma non_final_successor:
    "(\<not> final (c,s))
    \<longleftrightarrow> (\<exists>d. \<exists>t. (c,s) \<rightarrow>* (d,t) \<and> (d \<noteq> c))"
proof
  assume "\<not> final (c,s)"
  hence "\<exists>d. \<exists>t. (c,s) \<rightarrow> (d,t)"
    by (simp add: final_def)
  hence "\<exists>d. \<exists>t. (c,s) \<rightarrow> (d,t) \<and> (d \<noteq> c)"
    using small_step_antireflexivity
    by blast
  have "((c,s) \<rightarrow> (d,t)) \<Longrightarrow> ((c,s) \<rightarrow>* (d,t))" for d t
    by simp
  hence "\<exists>d. \<exists>t. (c,s) \<rightarrow>* (d,t)"
    using `\<exists>d. \<exists>t. (c,s) \<rightarrow> (d,t)`
    by auto
  thus "\<exists>d. \<exists>t. (c,s) \<rightarrow>* (d,t) \<and> (d \<noteq> c)"
    using `\<exists>d t. (c, s) \<rightarrow> (d, t) \<and> d \<noteq> c`
    by blast
next
  assume "\<exists>d. \<exists>t. (c,s) \<rightarrow>* (d,t) \<and> (d \<noteq> c)"
  hence "\<exists>d. \<exists>t. (c,s) \<rightarrow> (d,t)"
    using prod.inject small_step.cases star.simps
    by (smt (verit))
  hence "\<not> (\<not> (\<exists>d. \<exists>t. (c,s) \<rightarrow> (d,t)))" by simp
  thus "\<not> final (c,s)"
    using final_split by blast
qed

thm impI[of "foo" "bar"]
thm impI[of "(c,s) \<noteq> (d,t)" "(\<exists>c'. \<exists>s'. (c,s) \<rightarrow> (c',s') \<and> (c',s') \<rightarrow>* (d,t))"]
thm iffI[of b c]

theorem big_step_equiv_is_small_term_equiv:
    "(\<forall>s. \<forall>t. ((a,s) \<rightarrow>* (SKIP,t) = (b,s) \<rightarrow>* (SKIP,t)))
    \<longleftrightarrow> (a \<sim> b)"
  by (simp add: big_step_small_term_equiv)

lemma penult_star_state:
    "((c \<noteq> d \<or> s \<noteq> t) \<and> (c,s) \<rightarrow>* (d,t))
    \<Longrightarrow> \<exists>d'. \<exists>t'. ((c,s) \<rightarrow>* (d',t')
                  \<and> (d',t') \<rightarrow> (d,t))"
proof -
  assume "(c \<noteq> d \<or> s \<noteq> t) \<and> (c,s) \<rightarrow>* (d,t)"
  hence "\<exists>c'. \<exists>s'. (c,s) \<rightarrow> (c',s') \<and> (c',s') \<rightarrow>* (d,t)"
    using
      SmallSkipE
      final_split
      imp_deterministic_small_step
      prod.inject
      skip_finality
      star.simps
    by (smt (verit, del_insts))
  then obtain c' s' where
      "(c,s) \<rightarrow> (c',s') \<and> (c',s') \<rightarrow>* (d,t)"
    by auto
  hence "(c',s') \<rightarrow>* (d,t)" by simp
  hence "star2 small_step (c',s') (d,t)"
    by (rule star_impl_star2)
  thus "\<exists>d'. \<exists>t'. (c,s) \<rightarrow>* (d',t') \<and> (d',t') \<rightarrow> (d,t)"
  proof (induction "(c',s')" "(d,t)" rule: star2.induct)
    case refl2
    hence "(c',s') = (d,t)" by simp
    hence "(c,s) \<rightarrow>* (c,s) \<and> (c,s) \<rightarrow> (d,t)"
      using `(c, s) \<rightarrow> (c', s') \<and> (c', s') \<rightarrow>* (d, t)`
      by blast
    thus
        "\<exists>d'. \<exists>t'. (c,s) \<rightarrow>* (d',t')
                   \<and> (d',t') \<rightarrow> (d,t)"
      by auto
  next
    case (step2 a)
    hence "(c',s') \<rightarrow>* a"
      by (simp add: star2_impl_star)
    hence "(c,s) \<rightarrow>* a"
      using
        `(c,s) \<rightarrow> (c',s')
        \<and> (c',s') \<rightarrow>* (d,t)`
      by (meson star.step)
    have "a \<rightarrow> (d,t)"
      by (rule local.step2(3))
    have "\<exists>d'. \<exists>t'. a = (d',t')"
      by (rule Product_Type.surj_pair)
    thus
        "\<exists>d'. \<exists>t'. (c,s) \<rightarrow>* (d',t')
                   \<and> (d',t') \<rightarrow> (d,t)"
      using `(c,s) \<rightarrow>* a` step2.hyps(3)
      by blast
  qed
qed

inductive small_step_count ::
    "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> nat \<Rightarrow> bool"
  where
Self: "small_step_count (c,s) (c,s) 0" |
Step:
    "(c,s) \<rightarrow> (d,t)
    \<Longrightarrow> small_step_count (c,s) (d,t) 1" |
Following:
    "n1 + n2 > 1
    \<Longrightarrow> small_step_count (c1,s1) (c2,s2) n1
    \<Longrightarrow> small_step_count (c2,s2) (c3,s3) n2
    \<Longrightarrow> small_step_count (c1,s1) (c3,s3) (n1 + n2)"

theorem zero_count_same:
    "small_step_count (c,s) (d,t) 0 \<longleftrightarrow> (c,s) = (d,t)"
proof
  assume "small_step_count (c,s) (d,t) 0"
  thus "(c,s) = (d,t)"
  proof cases
    case Self
    thus "(c,s) = (d,t)"
      by simp
  next
    case Step
    hence "0 = 1 \<Longrightarrow> (c,s) = (d,t)"
      by simp
    thus ?thesis
      using local.Step(1)
      by blast
  next
    case (Following n1 n2 c2 s2)
    hence "0 = n1 + n2 \<and> 0 < n1 + n2"
      by simp
    thus ?thesis
      by auto
  qed
next
  assume "(c,s) = (d,t)"
  thus "small_step_count (c,s) (d,t) 0"
    using small_step_count.Self
    by auto
qed

lemma leads_to_count:
    "(c,s) \<rightarrow>* (d,t)
    \<Longrightarrow> \<exists>n. small_step_count (c,s) (d,t) n"
proof (induction c s d t rule: star_induct)
  case refl
  thus ?case
    using small_step_count.Self
    by blast
next
  case (step c s c' s' d t)
  hence
      "(c,s) \<rightarrow> (c',s')"
      "(c',s') \<rightarrow>* (d,t)"
      "\<exists>n. small_step_count (c',s') (d,t) n"
    by auto
  hence "small_step_count (c,s) (c',s') 1"
    using small_step_count.Step
    by simp
  have "(c',s') = (d,t) \<or> (c',s') \<noteq> (d,t)"
    by simp
  thus "\<exists>n. small_step_count (c,s) (d,t) n"
  proof (elim disjE)
    assume "(c',s') = (d,t)"
    hence "small_step_count (c,s) (d,t) 1"
      using `small_step_count (c,s) (c',s') 1`
      by blast
    thus "\<exists>n. small_step_count (c,s) (d,t) n"
      by (rule HOL.exI)
  next
    assume "(c',s') \<noteq> (d,t)"
    then obtain n' where
        "small_step_count (c',s') (d,t) n'"
      using `\<exists>n. small_step_count (c',s') (d,t) n`
      by blast
    hence "n' \<noteq> 0"
      using
        `(c',s') \<noteq> (d,t)`
        zero_count_same
      by force
    hence "1 + n' > 1"
      by simp
    hence "small_step_count (c,s) (d,t) (1+n')"
      using
        small_step_count.Following
        `small_step_count (c,s) (c',s') 1`
        `small_step_count (c',s') (d,t) n'`
      by blast
    thus "\<exists>n. small_step_count (c,s) (d,t) n"
      by (rule HOL.exI)
  qed
qed

theorem count_leads_to:
    "(\<exists>n. small_step_count (c,s) (d,t) n)
    \<longleftrightarrow> ((c,s) \<rightarrow>* (d,t))"
proof
  assume "\<exists>n. small_step_count (c,s) (d,t) n"
  then obtain n' where
      "small_step_count (c,s) (d,t) n'"
    by auto
  thus "(c,s) \<rightarrow>* (d,t)"
  proof induction
    case (Self c s)
    thus "(c,s) \<rightarrow>* (c,s)"
      by simp
  next
    case (Step c s d t)
    hence "(c,s) \<rightarrow> (d,t)"
      by simp
    thus "(c,s) \<rightarrow>* (d,t)"
      by simp
  next
    case (Following n1 n2 c1 s1 c2 s2 c3 s3)
    hence
        "small_step_count (c1,s1) (c2,s2) n1
        \<and> small_step_count (c2,s2) (c3,s3) n2"
        "(c1,s1) \<rightarrow>* (c2,s2) \<and> (c2,s2) \<rightarrow>* (c3,s3)"
      by auto
    hence "small_step_count (c1,s1) (c3,s3) (n1+n2)"
      using
        local.Following.hyps(1)
        small_step_count.Following
      by auto
    have "(c1,s1) \<rightarrow>* (c3,s3)"
      using
        `(c1,s1) \<rightarrow>* (c2,s2) \<and> (c2,s2) \<rightarrow>* (c3,s3)`
        star_trans
      by meson
    thus ?case
      by simp
  qed
next
  assume "(c,s) \<rightarrow>* (d,t)"
  thus "\<exists>n. small_step_count (c,s) (d,t) n"
    by (simp add: leads_to_count)
qed

theorem one_count_is_step:
    "small_step_count (c,s) (d,t) 1 \<longleftrightarrow> (c,s) \<rightarrow> (d,t)"
proof
  assume "small_step_count (c,s) (d,t) 1"
  thus "(c,s) \<rightarrow> (d,t)"
  proof cases
    case Self
    hence "1 = 0"
      by simp
    thus "(c,s) \<rightarrow> (d,t)"
      using local.Self(3)
      by simp
  next
    case Step
    thus "(c,s) \<rightarrow> (d,t)"
      by simp
  next
    case (Following n1 n2 c2 s2)
    hence "1 = n1 + n2 \<and> 1 < n1 + n2"
      by simp
    thus "(c,s) \<rightarrow> (d,t)"
      using local.Following
      by linarith
  qed
next
  assume "(c,s) \<rightarrow> (d,t)"
  thus "small_step_count (c,s) (d,t) 1"
    by (rule small_step_count.Step)
qed

lemma count_penult_step_lt:
    "(small_step_count (c,s) (d,t) n \<and> n > 1)
    \<Longrightarrow> (\<exists>d'. \<exists>t'. small_step_count (c,s) (d',t') (n-1)
        \<and> small_step_count (d',t') (d,t) 1)"
proof -
  assume "small_step_count (c,s) (d,t) n \<and> n > 1"
  hence
      "small_step_count (c,s) (d,t) n"
      "n > 1"
    by auto
  thus
      "\<exists>d'. \<exists>t'. small_step_count (c,s) (d',t') (n-1)
      \<and> small_step_count (d',t') (d,t) 1"
  proof (induction rule: small_step_count.induct)
    case (Self c s)
    hence "1 < 0" by simp
    thus ?case by auto
  next
    case (Step c s d t)
    hence "1 < 1" by simp
    thus ?case by auto
  next
    case (Following n1 n2 c s d2 t2 d t)
    hence "n2 > 1 \<or> n2 = 1 \<or> (n2 = 0 \<and> n1 > 1)"
      by auto
    thus ?case
    proof (elim disjE)
      assume "n2 > 1"
      hence
          "\<exists>d'. \<exists>t'.
          small_step_count (d2,t2) (d',t') (n2-1)
          \<and> small_step_count (d',t') (d,t) 1"
        by (rule local.Following(5))
      then obtain d' t' where
          "small_step_count (d2,t2) (d',t') (n2-1)
          \<and> small_step_count (d',t') (d,t) 1"
        by auto
      hence
          "small_step_count (d2,t2) (d',t') (n2-1)"
          "small_step_count (d',t') (d,t) 1"
        by auto
      have "n1 = 0 \<or> n1 + n2 > 2"
        using `1 < n2`
        by linarith
      hence "small_step_count (c,s) (d',t') (n1+n2-1)"
        using
          Following.hyps(2)
          `1 < n2`
          `small_step_count (d2,t2) (d',t') (n2-1)`
          small_step_count.Following
          zero_count_same
        by (smt (verit, best)
            Nat.add_diff_assoc
            add_cancel_left_left
            less_diff_conv
            less_imp_le
            one_add_one)
      thus
          "\<exists>d'. \<exists>t'.
          small_step_count (c,s) (d',t') (n1+n2-1)
          \<and> small_step_count (d',t') (d,t) 1"
        using `small_step_count (d',t') (d,t) 1`
        by blast
    next
      assume "n2 = 1"
      hence "small_step_count (d2,t2) (d,t) 1"
        using local.Following.hyps(3)
        by blast
      have "n1 + n2 - 1 = n1"
        using `n2 = 1`
        by simp
      hence
          "small_step_count (c,s) (d2,t2) (n1+n2-1)
          \<and> small_step_count (d2,t2) (d,t) 1"
        using
          local.Following.hyps(2)
          `small_step_count (d2,t2) (d,t) 1`
        by presburger
      thus
          "\<exists>d'. \<exists>t'.
          small_step_count (c,s) (d',t') (n1+n2-1)
          \<and> small_step_count (d',t') (d,t) 1"
        by auto
    next
      assume "n2 = 0 \<and> n1 > 1"
      hence
          "n2 = 0"
          "n1 > 1"
        by auto
      hence "small_step_count (d2,t2) (d,t) 0"
        using local.Following.hyps(3)
        by blast
      hence "(d,t) = (d2,t2)"
        using zero_count_same
        by simp
      have "n1 + n2 - 1 = n1 - 1"
        using
          `n2 = 0`
          `n1 > 1`
        by simp
      have
          "\<exists>d'. \<exists>t'.
          small_step_count (c,s) (d',t') (n1-1)
          \<and> small_step_count (d',t') (d,t) 1"
        using
          Following.IH(1)
          `1 < n1`
          `(d,t) = (d2,t2)`
        by simp
      thus
          "\<exists>d'. \<exists>t'.
          small_step_count (c,s) (d',t') (n1+n2-1)
          \<and> small_step_count (d',t') (d,t) 1"
        using
          `(d,t) = (d2,t2)`
          `n1 + n2 - 1 = n1 - 1`
        by simp
    qed
  qed
qed

corollary count_penult_step:
    "(small_step_count (c,s) (d,t) n \<and> n \<ge> 1)
    \<Longrightarrow> (\<exists>d'. \<exists>t'. small_step_count (c,s) (d',t') (n-1)
        \<and> small_step_count (d',t') (d,t) 1)"
proof -
  assume "small_step_count (c,s) (d,t) n \<and> 1 \<le> n"
  hence "n = 1 \<or> n > 1"
    by auto
  thus
      "\<exists>d'. \<exists>t'.
      small_step_count (c,s) (d',t') (n-1)
      \<and> small_step_count (d',t') (d,t) 1"
  proof (elim disjE)
    assume "n = 1"
    have "small_step_count (c,s) (c,s) 0"
      by (rule small_step_count.Self)
    hence "small_step_count (c,s) (c,s) (n-1)"
      using `n = 1`
      by simp
    have "small_step_count (c,s) (d,t) n"
      using `small_step_count (c,s) (d,t) n \<and> 1 \<le> n`
      by simp
    hence "small_step_count (c,s) (d,t) 1"
      using `n = 1`
      by simp
    thus
        "\<exists>d'. \<exists>t'. small_step_count (c,s) (d',t') (n-1)
        \<and> small_step_count (d',t') (d,t) 1"
      using `small_step_count (c,s) (c,s) (n-1)`
      by auto
  next
    assume "n > 1"
    have "small_step_count (c,s) (d,t) n"
      using `small_step_count (c,s) (d,t) n \<and> 1 \<le> n`
      by simp
    thus
        "\<exists>d'. \<exists>t'. small_step_count (c,s) (d',t') (n-1)
        \<and> small_step_count (d',t') (d,t) 1"
        using
          count_penult_step_lt
          `n > 1`
      by blast
  qed
qed

theorem equiv_count_impl_equiv_state:
    "(small_step_count (c,s) (d1,t1) n
      \<and> small_step_count (c,s) (d2,t2) n)
    \<Longrightarrow> (d1,t1) = (d2,t2)"
proof (induction n arbitrary: d1 t1 d2 t2)
  case 0
  hence
      "small_step_count (c,s) (d1,t1) 0"
      "small_step_count (c,s) (d2,t2) 0"
    by auto
  hence
      "(c,s) = (d1,t1)"
      "(c,s) = (d2,t2)"
    using zero_count_same
    by simp_all
  thus "(d1,t1) = (d2,t2)"
    by simp
next
  case (Suc n)
  hence
      "small_step_count (c,s) (d1,t1) (Suc n)"
      "small_step_count (c,s) (d2,t2) (Suc n)"
    by auto
  then obtain d1' t1' where
      "small_step_count (c,s) (d1',t1') n
      \<and> small_step_count (d1',t1') (d1,t1) 1"
    using
      count_penult_step
      small_step_count.Self
    by fastforce
  obtain d2' t2' where
      "small_step_count (c,s) (d2',t2') n
      \<and> small_step_count (d2',t2') (d2,t2) 1"
    using
      count_penult_step
      small_step_count.Self
      `small_step_count (c,s) (d2,t2) (Suc n)`
    by fastforce
  hence
      "small_step_count (c,s) (d1',t1') n
      \<and> small_step_count (c,s) (d2',t2') n"
    using
      `small_step_count (c,s) (d1',t1') n
      \<and> small_step_count (d1',t1') (d1,t1) 1`
    by blast
  hence "(d1',t1') = (d2',t2')"
    by (rule local.Suc.IH)
  hence "small_step_count (d1',t1') (d2,t2) 1"
    using
      `small_step_count (c,s) (d2',t2') n
      \<and> small_step_count (d2',t2') (d2,t2) 1`
    by blast
  hence "(d1',t1') \<rightarrow> (d1,t1) \<and> (d1',t1') \<rightarrow> (d2,t2)"
    using
      `small_step_count (c,s) (d1',t1') n
      \<and> small_step_count (d1',t1') (d1,t1) 1`
      one_count_is_step
    by blast
  thus "(d1,t1) = (d2,t2)"
    using small_step_imp_deterministic
    by blast
qed

corollary small_step_count_split:
    "n1 \<ge> n2 \<and> n2 \<ge> 0
      \<and> small_step_count (c,s) (d,t) n1
    \<Longrightarrow> \<exists>c'. \<exists>s'. (
      small_step_count (c,s) (c',s') (n1-n2)
      \<and> small_step_count (c',s') (d,t) n2)"
proof (induction n2)
  case 0
  hence "small_step_count (c,s) (d,t) n1"
    by simp
  hence "small_step_count (c,s) (d,t) (n1-0)"
    by simp
  have "small_step_count (d,t) (d,t) 0"
    by (rule small_step_count.Self)
  thus
      "\<exists>c'. \<exists>s'. small_step_count (c,s) (c',s') (n1-0)
      \<and> small_step_count (c',s') (d,t) 0"
    using `small_step_count (c,s) (d,t) (n1-0)`
    by auto
next
  case (Suc n2)
  hence
      "(Suc n2) \<le> n1"
      "0 \<le> (Suc n2)"
      "small_step_count (c,s) (d,t) n1"
    by auto
  hence "n2 < n1"
    using `(Suc n2) \<le> n1`
    by simp
  hence "n2 \<le> n1"
    by simp
  have "0 \<le> n2"
    by simp
  hence
      "\<exists>c'. \<exists>s'. small_step_count (c,s) (c',s') (n1-n2)
      \<and> small_step_count (c',s') (d,t) n2"
    using
      `n2 \<le> n1`
      `small_step_count (c,s) (d,t) n1`
      local.Suc.IH
    by simp
  then obtain c' s' where
      "small_step_count (c,s) (c',s') (n1-n2)
      \<and> small_step_count (c',s') (d,t) n2"
    by auto
  hence
      "small_step_count (c,s) (c',s') (n1-n2)"
      "small_step_count (c',s') (d,t) n2"
    by auto
  have "n1 - n2 \<ge> 1"
    using
      `n2 < n1`
    by simp
  hence
      "\<exists>c''. \<exists>s''.
      small_step_count (c,s) (c'',s'') (n1-n2-1)
      \<and> small_step_count (c'',s'') (c',s') 1"
    using
      count_penult_step
      `small_step_count (c,s) (c',s') (n1-n2)`
    by blast
  then obtain c'' s'' where
      "small_step_count (c,s) (c'',s'') (n1-n2-1)
      \<and> small_step_count (c'',s'') (c',s') 1"
    by auto
  hence
      "small_step_count (c,s) (c'',s'') (n1-n2-1)"
      "small_step_count (c'',s'') (c',s') 1"
    by auto
  hence "small_step_count (c'',s'') (d,t) (n2+1)"
    using
      `small_step_count (c',s') (d,t) n2`
      `n2 \<ge> 0`
      zero_count_same
      small_step_count.Following
    by (metis
        add.commute
        add.right_neutral
        less_add_same_cancel1
        order_le_less)
  hence "small_step_count (c'',s'') (d,t) (Suc n2)"
    by simp
  have "(n1-n2-1) = (n1-(Suc n2))"
    by simp
  hence
      "small_step_count (c,s) (c'',s'') (n1-(Suc n2))
      \<and> small_step_count (c'',s'') (d,t) (Suc n2)"
    using
      `small_step_count (c'',s'') (d,t) (Suc n2)`
      `small_step_count (c,s) (c'',s'') (n1-n2-1)`
    by presburger
  hence
      "\<exists>c'. \<exists>s'.
      small_step_count (c,s) (c',s') (n1-(Suc n2))
      \<and> small_step_count (c',s') (d,t) (Suc n2)"
    by auto
  thus ?case
    by simp
qed

lemma determ_trace_triangle:
    "((c,s) \<rightarrow>* (d1,t1) \<and> (c,s) \<rightarrow>* (d2,t2))
    \<longrightarrow> ((d1,t1) \<rightarrow>* (d2,t2) \<or> (d2,t2) \<rightarrow>* (d1,t1))"
proof
  assume "(c,s) \<rightarrow>* (d1,t1) \<and> (c,s) \<rightarrow>* (d2,t2)"
  then obtain n1 n2 where
      "small_step_count (c,s) (d1,t1) n1"
      "small_step_count (c,s) (d2,t2) n2"
    using leads_to_count
    by presburger
  have "n1 = n2 \<or> n1 > n2 \<or> n1 < n2"
    by auto
  thus "(d1,t1) \<rightarrow>* (d2,t2) \<or> (d2,t2) \<rightarrow>* (d1,t1)"
  proof (elim disjE)
    assume "n1 = n2"
    hence "(d1,t1) = (d2,t2)"
      using
        `small_step_count (c,s) (d1,t1) n1`
        `small_step_count (c,s) (d2,t2) n2`
        equiv_count_impl_equiv_state
      by presburger
    hence "(d1,t1) \<rightarrow>* (d2,t2)"
      by simp
    thus "(d1,t1) \<rightarrow>* (d2,t2) \<or> (d2,t2) \<rightarrow>* (d1,t1)"
      by (rule HOL.disjI1)
  next
    assume "n1 > n2"
    hence "n1-(n1-n2) = n2"
      by simp
    have "n1-n2 >= 0"
      by simp
    have "n1 \<ge> (n1-n2)"
      by simp
    hence
        "\<exists>c'. \<exists>s'.
        small_step_count (c,s) (c',s') n2
        \<and> small_step_count (c',s') (d1,t1) (n1-n2)"
      using
        `n1-(n1-n2) = n2`
        `(n1-n2) \<ge> 0`
        `small_step_count (c,s) (d1,t1) n1`
        small_step_count_split
      by metis
    then obtain c' s' where
        "small_step_count (c,s) (c',s') n2
        \<and> small_step_count (c',s') (d1,t1) (n1-n2)"
      by auto
    hence
        "small_step_count (c,s) (c',s') n2"
        "small_step_count (c',s') (d1,t1) (n1-n2)"
      by auto
    hence "(c',s') = (d2,t2)"
      using
        equiv_count_impl_equiv_state
        `small_step_count (c,s) (d2,t2) n2`
      by simp
    hence "small_step_count (d2,t2) (d1,t1) (n1-n2)"
      using `small_step_count (c',s') (d1,t1) (n1-n2)`
      by simp
    hence "(d2,t2) \<rightarrow>* (d1,t1)"
      using count_leads_to
      by blast
    thus ?thesis
      by simp
  next
    assume "n1 < n2"
    hence "n2-(n2-n1) = n1"
      by simp
    have "n2-n1 >= 0"
      by simp
    have "n2 \<ge> (n2-n1)"
      by simp
    hence
        "\<exists>c'. \<exists>s'.
        small_step_count (c,s) (c',s') n1
        \<and> small_step_count (c',s') (d2,t2) (n2-n1)"
      using
        `n2-(n2-n1) = n1`
        `(n2-n1) \<ge> 0`
        `small_step_count (c,s) (d2,t2) n2`
        small_step_count_split
      by metis
    then obtain c' s' where
        "small_step_count (c,s) (c',s') n1
        \<and> small_step_count (c',s') (d2,t2) (n2-n1)"
      by auto
    hence
        "small_step_count (c,s) (c',s') n1"
        "small_step_count (c',s') (d2,t2) (n2-n1)"
      by auto
    hence "(c',s') = (d1,t1)"
      using
        equiv_count_impl_equiv_state
        `small_step_count (c,s) (d1,t1) n1`
      by simp
    hence "small_step_count (d1,t1) (d2,t2) (n2-n1)"
      using `small_step_count (c',s') (d2,t2) (n2-n1)`
      by simp
    hence "(d1,t1) \<rightarrow>* (d2,t2)"
      using count_leads_to
      by blast
    thus ?thesis
      by simp
  qed
qed

inductive state_changes ::
    "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> nat \<Rightarrow> bool"
  where
None:
  "state_changes (c,s) (c,s) 0" |
Stateless:
  "state_changes (c',s) (d,t) n
   \<and> (c,s) \<rightarrow> (c',s)
  \<Longrightarrow> state_changes (c,s) (d,t) n" |
Stateful:
  "state_changes (c',s') (d,t) n
   \<and> (c,s) \<rightarrow> (c',s')
   \<and> s \<noteq> s'
  \<Longrightarrow> state_changes (c,s) (d,t) (Suc n)"

lemma state_change_count_exists:
    "(c,s) \<rightarrow>* (d,t) \<Longrightarrow> \<exists>n. state_changes (c,s) (d,t) n"
proof (induction rule: star_induct)
  case (refl c s)
  hence "state_changes (c,s) (c,s) 0"
    by (rule state_changes.None)
  thus "\<exists>n. state_changes (c,s) (c,s) n"
    by (rule HOL.exI)
next
  case (step c s c' s' d t)
  hence
      "(c,s) \<rightarrow> (c',s')"
      "\<exists>n. state_changes (c',s') (d,t) n"
    by auto
  then obtain n where
      "state_changes (c',s') (d,t) n"
    by auto
  have "s = s' \<or> s \<noteq> s'"
    by simp
  thus "\<exists>n. state_changes (c,s) (d,t) n"
  proof (elim disjE)
    assume "s = s'"
    hence "state_changes (c,s) (d,t) n"
      using
        state_changes.Stateless
        `state_changes (c',s') (d,t) n`
        `(c,s) \<rightarrow> (c',s')`
      by blast
    thus "\<exists>n. state_changes (c,s) (d,t) n"
      by (rule HOL.exI)
  next
    assume "s \<noteq> s'"
    hence "state_changes (c,s) (d,t) (Suc n)"
      using
        state_changes.Stateful
        `state_changes (c',s') (d,t) n`
        `(c,s) \<rightarrow> (c',s')`
      by blast
    thus "\<exists>n. state_changes (c,s) (d,t) n"
      by (rule HOL.exI)
  qed
qed

lemma state_change_count_impl_leads_to:
    "state_changes (c,s) (d,t) n \<Longrightarrow> (c,s) \<rightarrow>* (d,t)"
proof (induction rule: state_changes.induct)
  case (None c s)
  thus "(c,s) \<rightarrow>* (c,s)"
    by (rule star.refl)
next
  case (Stateless c' s d t n c)
  hence
      "(c',s) \<rightarrow>* (d,t)"
      "(c,s) \<rightarrow> (c',s)"
    by simp+
  thus "(c,s) \<rightarrow>* (d,t)"
    using star.step[of small_step]
    by simp
next
  case (Stateful c' s' d t n c s)
  hence
      "(c',s') \<rightarrow>* (d,t)"
      "(c,s) \<rightarrow> (c',s')"
    by simp+
  thus "(c,s) \<rightarrow>* (d,t)"
    using star.step[of small_step]
    by simp
qed


lemma leads_to_state_changes:
    "(c,s) \<rightarrow>* (d,t) = (\<exists>n. state_changes (c,s) (d,t) n)"
  using
    state_change_count_impl_leads_to
    state_change_count_exists
  by blast

lemma state_change_count_prepend_ge:
    "state_changes (c',s') (d,t) n \<and> (c,s) \<rightarrow> (c',s')
    \<Longrightarrow> \<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<ge> n"
  using
    state_changes.Stateful
    state_changes.Stateless
  by (metis Suc_n_not_le_n nle_le)

lemma zero_state_changes_impl_same:
    "state_changes (c,s) (d,t) 0 \<Longrightarrow> s = t"
proof -
  assume "state_changes (c,s) (d,t) 0"
  then obtain n where
      "state_changes (c,s) (d,t) n"
      "n = 0"
    by auto
  thus "s = t"
  proof (induction "(c,s)" "(d,t)" n
         arbitrary: c d
         rule: state_changes.induct)
    case None
    thus "s = t"
      by simp
  next
    case (Stateless c' d n c)
    thus "s = t"
      by simp
  next
    case (Stateful c' s' d n c)
    thus "s = t" by simp
  qed
qed

corollary zero_state_changes_is_same:
    "(\<exists>d. state_changes (c,s) (d,t) 0) \<longleftrightarrow> (s = t)"
proof
  assume "\<exists>d. state_changes (c,s) (d,t) 0"
  thus "s = t"
    using zero_state_changes_impl_same
    by blast
next
  assume "s = t"
  hence "state_changes (c,s) (c,t) 0"
    using state_changes.None
    by simp
  thus "\<exists>d. state_changes (c,s) (d,t) 0"
    by (rule HOL.exI)
qed

lemma nonzero_state_changes_impl_interior_change:
    "state_changes (c,s) (d,t) n \<and> n > 0
    \<Longrightarrow> \<exists>c'. \<exists>s'.
        (c,s) \<rightarrow>* (c',s')
        \<and> (c',s') \<rightarrow>* (d,t)
        \<and> s \<noteq> s'"
proof -
  assume "state_changes (c,s) (d,t) n \<and> n > 0"
  hence
      "state_changes (c,s) (d,t) n"
      "n > 0"
    by auto
  thus
      "\<exists>c'. \<exists>s'.
      (c,s) \<rightarrow>* (c',s')
      \<and> (c',s') \<rightarrow>* (d,t)
      \<and> s \<noteq> s'"
  proof (induction "(c,s)" "(d,t)" n
         arbitrary: c d t
         rule: state_changes.induct)
    case None
    thus ?case
      by simp
  next
    case (Stateless c' d t n c)
    thus ?case
      by (metis star.step)
  next
    case (Stateful c' s' d t n c)
    hence
        "state_changes (c',s') (d,t) n"
        "(c,s) \<rightarrow> (c',s')"
        "s \<noteq> s'"
      by simp+
    hence "(c',s') \<rightarrow>* (d,t)"
      using state_change_count_impl_leads_to
      by simp
    have "(c,s) \<rightarrow>* (c',s')"
      using `(c,s) \<rightarrow> (c',s')`
      by simp
    hence
        "(c,s) \<rightarrow>* (c',s')
        \<and> (c',s') \<rightarrow>* (d,t)
        \<and> s \<noteq> s'"
      using
        `(c',s') \<rightarrow>* (d,t)`
        `s \<noteq> s'`
      by simp
    thus
        "\<exists>c'. \<exists>s'.
        (c,s) \<rightarrow>* (c',s')
        \<and> (c',s') \<rightarrow>* (d,t)
        \<and> s \<noteq> s'"
      by auto
  qed
qed

lemma non_ident_zero_state_change_impl_stateless:
    "state_changes (c,s) (d,t) 0 \<and> c \<noteq> d
    \<Longrightarrow> \<exists>c'. (c,s) \<rightarrow> (c',s)
        \<and> state_changes (c',s) (d,t) 0"
proof -
  assume "state_changes (c,s) (d,t) 0 \<and> c \<noteq> d"
  hence
      "state_changes (c,s) (d,t) 0"
      "c \<noteq> d"
    by simp+
  hence "(c,s) \<rightarrow>* (d,t)"
    using state_change_count_impl_leads_to
    by simp
  have "s = t"
    using `state_changes (c,s) (d,t) 0`
    by (rule zero_state_changes_impl_same)
  hence "(c,s) \<rightarrow>* (d,s)"
    using `(c,s) \<rightarrow>* (d,t)`
    by simp
  hence "\<exists>c'. (c,s) \<rightarrow> (c',s) \<and> (c',s) \<rightarrow>* (d,s)"
    using
      `c \<noteq> d`
      `state_changes (c,s) (d,t) 0`
      imp_deterministic_small_step
      star.cases
      state_changes.simps
    by (smt (verit)
        One_nat_def
        add_diff_cancel_right'
        diff_add_zero
        one_neq_zero
        plus_1_eq_Suc
        prod.inject)
  then obtain c' where
      "(c,s) \<rightarrow> (c',s) \<and> (c',s) \<rightarrow>* (d,s)"
    by (rule HOL.exE)
  have "state_changes (c,s) (d,s) 0"
    using
      `state_changes (c,s) (d,t) 0`
      `s = t`
    by simp
  hence "state_changes (c',s) (d,s) 0"
  proof (cases rule: state_changes.cases)
    case None
    hence "c = d"
      by simp
    thus "state_changes (c',s) (d,s) 0"
      using `c \<noteq> d`
      by contradiction
  next
    case Stateless
    thus "state_changes (c',s) (d,s) 0"
      using
        `(c,s) \<rightarrow> (c',s) \<and> (c',s) \<rightarrow>* (d,s)`
        imp_deterministic_small_step
      by blast
  qed
  hence "state_changes (c',s) (d,t) 0"
    using `s = t`
    by simp
  thus
      "\<exists>c'. (c,s) \<rightarrow> (c',s)
      \<and> state_changes (c',s) (d,t) 0"
    using
      `(c,s) \<rightarrow> (c',s) \<and> (c',s) \<rightarrow>* (d,s)`
    by auto
qed

lemma state_changes_stateless_tail:
    "state_changes (c,s) (d',t) n \<and> (d',t) \<rightarrow> (d,t)
    \<Longrightarrow> state_changes (c,s) (d,t) n"
proof -
  assume "state_changes (c,s) (d',t) n \<and> (d',t) \<rightarrow> (d,t)"
  hence
      "state_changes (c,s) (d',t) n"
      "(d',t) \<rightarrow> (d,t)"
    by simp+
  thus "state_changes (c,s) (d,t) n"
  proof (induction "(c,s)" "(d',t)" n
         arbitrary: c s
         rule: state_changes.induct)
    case None
    thus "state_changes (d',t) (d,t) 0"
      using
        state_changes.Stateless
        state_changes.None
      by blast
  next
    case (Stateless c' s n c)
    hence
        "state_changes (c',s) (d',t) n
        \<and> (d',t) \<rightarrow> (d,t)"
        "(c,s) \<rightarrow> (c',s)"
      by simp+
    hence "state_changes (c',s) (d,t) n"
      using Stateless.hyps
      by simp
    thus "state_changes (c,s) (d,t) n"
      using
        `(c,s) \<rightarrow> (c',s)`
        state_changes.Stateless
      by blast
  next
    case (Stateful c' s' n c s)
    hence
        "state_changes (c',s') (d',t) n
        \<and> (d',t) \<rightarrow> (d,t)"
        "(c,s) \<rightarrow> (c',s') \<and> s \<noteq> s'"
      by simp+
    hence "state_changes (c',s') (d,t) n"
      using Stateful.hyps
      by blast
    thus "state_changes (c,s) (d,t) (Suc n)"
      using `(c,s) \<rightarrow> (c',s') \<and> s \<noteq> s'`
      using state_changes.Stateful
      by simp
  qed
qed

lemma state_changes_stateful_tail:
    "state_changes (c,s) (d',t') n
     \<and> (d',t') \<rightarrow> (d,t)
     \<and> t' \<noteq> t
    \<Longrightarrow> state_changes (c,s) (d,t) (Suc n)"
proof -
  assume
    "state_changes (c,s) (d',t') n
    \<and> (d',t') \<rightarrow> (d,t)
    \<and> t' \<noteq> t"
  hence
      "state_changes (c,s) (d',t') n"
      "(d',t') \<rightarrow> (d,t)"
      "t' \<noteq> t"
    by simp+
  thus "state_changes (c,s) (d,t) (Suc n)"
  proof (induction "(c,s)" "(d',t')" n
         arbitrary: c s
         rule: state_changes.induct)
    case None
    thus "state_changes (d',t') (d,t) (Suc 0)"
      using
        state_changes.Stateful
        state_changes.None
      by blast
  next
    case (Stateless c' s n c)
    hence
        "state_changes (c',s) (d',t') n
        \<and> (d',t') \<rightarrow> (d,t)
        \<and> t' \<noteq> t"
        "(c,s) \<rightarrow> (c',s)"
      by simp+
    hence "state_changes (c',s) (d,t) (Suc n)"
      using Stateless.hyps
      by blast
    thus "state_changes (c,s) (d,t) (Suc n)"
      using
        `(c,s) \<rightarrow> (c',s)`
        state_changes.Stateless
      by blast
  next
    case (Stateful c' s' n c s)
    hence
        "state_changes (c',s') (d',t') n
        \<and> (d',t') \<rightarrow> (d,t)
        \<and> t' \<noteq> t"
        "(c,s) \<rightarrow> (c',s') \<and> s \<noteq> s'"
      by simp+
    hence "state_changes (c',s') (d,t) (Suc n)"
      using Stateful.hyps
      by simp
    thus "state_changes (c,s) (d,t) (Suc (Suc n))"
      using
        `(c,s) \<rightarrow> (c',s') \<and> s \<noteq> s'`
        state_changes.Stateful
      by simp
  qed
qed

inductive state_changes_tail ::
    "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> nat \<Rightarrow> bool"
  where
None:
  "state_changes_tail (c,s) (c,s) 0" |
Stateless:
  "state_changes_tail (c,s) (d',t) n
   \<and> (d',t) \<rightarrow> (d,t)
  \<Longrightarrow> state_changes_tail (c,s) (d,t) n" |
Stateful:
  "state_changes_tail (c,s) (d',t') n
   \<and> (d',t') \<rightarrow> (d,t)
   \<and> t' \<noteq> t
  \<Longrightarrow> state_changes_tail (c,s) (d,t) (Suc n)"

lemma state_changes_tail_stateless_head:
    "state_changes_tail (c',s) (d,t) n \<and> (c,s) \<rightarrow> (c',s)
    \<Longrightarrow> state_changes_tail (c,s) (d,t) n"
proof -
  assume
    "state_changes_tail (c',s) (d,t) n
    \<and> (c,s) \<rightarrow> (c',s)"
  hence
      "state_changes_tail (c',s) (d,t) n"
      "(c,s) \<rightarrow> (c',s)"
    by simp+
  thus "state_changes_tail (c,s) (d,t) n"
  proof (induction "(c',s)" "(d,t)" n
         arbitrary: d t
         rule: state_changes_tail.induct)
    case None
    thus "state_changes_tail (c,s) (c',s) 0"
      using
        state_changes_tail.Stateless
        state_changes_tail.None
      by blast
  next
    case (Stateless d' t n d)
    hence
        "state_changes_tail (c',s) (d',t) n
        \<and> (c,s) \<rightarrow> (c',s)"
        "(d',t) \<rightarrow> (d,t)"
      by simp+
    hence "state_changes_tail (c,s) (d',t) n"
      using Stateless.hyps
      by blast
    thus "state_changes_tail (c,s) (d,t) n"
      using
        `(d',t) \<rightarrow> (d,t)`
        state_changes_tail.Stateless
      by blast
  next
    case (Stateful d' t' n d t)
    hence
        "state_changes_tail (c',s) (d',t') n
        \<and> (c,s) \<rightarrow> (c',s)"
        "(d',t') \<rightarrow> (d,t) \<and> t' \<noteq> t"
      by simp+
    hence "state_changes_tail (c,s) (d',t') n"
      using Stateful.hyps
      by blast
    thus "state_changes_tail (c,s) (d,t) (Suc n)"
      using
        `(d',t') \<rightarrow> (d,t) \<and> t' \<noteq> t`
        state_changes_tail.Stateful
      by simp
  qed
qed

lemma state_changes_tail_stateful_head:
    "state_changes_tail (c',s') (d,t) n
     \<and> (c,s) \<rightarrow> (c',s')
     \<and> s \<noteq> s'
    \<Longrightarrow> state_changes_tail (c,s) (d,t) (Suc n)"
proof -
  assume
    "state_changes_tail (c',s') (d,t) n
    \<and> (c,s) \<rightarrow> (c',s')
    \<and> s \<noteq> s'"
  hence
      "state_changes_tail (c',s') (d,t) n"
      "(c,s) \<rightarrow> (c',s')"
      "s \<noteq> s'"
    by simp+
  thus "state_changes_tail (c,s) (d,t) (Suc n)"
  proof (induction "(c',s')" "(d,t)" n
         arbitrary: d t
         rule: state_changes_tail.induct)
    case None
    thus "state_changes_tail (c,s) (c',s') (Suc 0)"
      using
        state_changes_tail.None
        state_changes_tail.Stateful
      by blast
  next
    case (Stateless d' t n d)
    hence
        "state_changes_tail (c',s') (d',t) n
        \<and> (c,s) \<rightarrow> (c',s')
        \<and> s \<noteq> s'"
        "(d',t) \<rightarrow> (d,t)"
      by simp+
    hence "state_changes_tail (c,s) (d',t) (Suc n)"
      using Stateless.hyps
      by blast
    thus "state_changes_tail (c,s) (d,t) (Suc n)"
      using
        `(d',t) \<rightarrow> (d,t)`
        state_changes_tail.Stateless
      by blast
  next
    case (Stateful d' t' n d t)
    hence
        "state_changes_tail (c',s') (d',t') n
        \<and> (c,s) \<rightarrow> (c',s')
        \<and> s \<noteq> s'"
        "(d',t') \<rightarrow> (d,t) \<and> t' \<noteq> t"
      by simp+
    hence "state_changes_tail (c,s) (d',t') (Suc n)"
      using Stateful.hyps
      by blast
    thus "state_changes_tail (c,s) (d,t) (Suc (Suc n))"
      using
        `(d',t') \<rightarrow> (d,t) \<and> t' \<noteq> t`
        state_changes_tail.Stateful
      by blast
  qed
qed

theorem state_changes_tail_equiv:
    "state_changes (c,s) (d,t) n
    \<longleftrightarrow> state_changes_tail (c,s) (d,t) n"
proof
  assume "state_changes (c,s) (d,t) n"
  thus "state_changes_tail (c,s) (d,t) n"
  proof (induction rule: state_changes.induct)
    case None
    thus ?case
      by (rule state_changes_tail.None)
  next
    case Stateless
    thus ?case
      using state_changes_tail_stateless_head
      by auto
  next
    case Stateful
    thus ?case
      using state_changes_tail_stateful_head
      by auto
  qed
next
  assume "state_changes_tail (c,s) (d,t) n"
  thus "state_changes (c,s) (d,t) n"
  proof (induction rule: state_changes_tail.induct)
    case None
    thus ?case
      by (rule state_changes.None)
  next
    case Stateless
    thus ?case
      using state_changes_stateless_tail
      by auto
  next
    case Stateful
    thus ?case
      using state_changes_stateful_tail
      by auto
  qed
qed

lemma state_change_count_append_ge:
    "state_changes (c,s) (d',t') n \<and> (d',t') \<rightarrow> (d,t)
    \<Longrightarrow> \<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<ge> n"
  using
    state_changes_stateless_tail
    state_changes_stateful_tail
  by (metis Suc_n_not_le_n linorder_linear)

theorem state_changes_transitivity:
    "state_changes (c,s) (c',s') n1
     \<and> state_changes (c',s') (d,t) n2
    \<Longrightarrow> state_changes (c,s) (d,t) (n1+n2)"
proof -
  assume
    "state_changes (c,s) (c',s') n1
     \<and> state_changes (c',s') (d,t) n2"
  thus "state_changes (c,s) (d,t) (n1+n2)"
  proof (induction n2)
    case 0
    hence "state_changes (c,s) (c',s') n1"
      by (rule HOL.conjE)
    hence "state_changes_tail (c,s) (c',s') n1"
      using state_changes_tail_equiv
      by simp
    have "state_changes (c',s') (d,t) 0"
      using 0
      by simp
    then obtain n2 where
        "state_changes (c',s') (d,t) n2"
        "n2 = 0"
      by simp
    hence "state_changes_tail (c,s) (d,t) n1"
    proof (induction "(c',s')" "(d,t)" n2
           arbitrary: d t
           rule: state_changes.induct)
      case None
      thus "state_changes_tail (c,s) (c',s') n1"
        using `state_changes_tail (c,s) (c',s') n1`
        by simp
    next
      case (Stateless c3 d3 t3 n3)
      hence
          "state_changes (c3,s') (d3,t3) 0"
          "(c',s') \<rightarrow> (c3,s')"
        by simp+
      hence "s' = t3"
        using zero_state_changes_impl_same
        by simp
      thus "state_changes_tail (c,s) (d,t) n1" sorry
    next
      case (Stateful c' s' d t n)
      thus "state_changes_tail (c,s) (d,t) n1" sorry
    qed
    hence "state_changes (c,s) (d,t) n1"
      using state_changes_tail_equiv
      by force
    thus "state_changes (c,s) (d,t) (n1+0)"
      by simp
  next
    case (Suc n2)
    thus "state_changes (c,s) (d,t) (n1+(Suc n2))" sorry
  qed
qed

theorem determ_state_changes:
    "state_changes (c,s) (d1,t1) n
    \<and> state_changes (c,s) (d2,t2) n
    \<Longrightarrow> t1 = t2"
proof -
  assume
    "state_changes (c,s) (d1,t1) n
    \<and> state_changes (c,s) (d2,t2) n"
  thus "t1 = t2"
  proof (induction n arbitrary: d1 t1 d2 t2)
    case 0
    hence "s = t1 \<and> s = t2"
      using zero_state_changes_impl_same
      by force
    thus "t1 = t2"
      by auto
  next
    case (Suc n)
    fix d1' t1' d2' t2'
    have
        "state_changes (c,s) (d1',t1') n
        \<and> state_changes (c,s) (d2',t2') n
        \<Longrightarrow> t1' = t2'"
      using local.Suc
      by simp
    thus "t1 = t2" sorry
  qed
qed

(*
lemma interior_changes_impl_nonzero_state_changes:
    "(c,s) \<rightarrow>* (c',s') \<and> (c',s') \<rightarrow>* (d,t)
    \<Longrightarrow> \<exists>n. \<exists>n'.
        state_changes (c,s) (d,t) n
        \<and> state_changes (c,s) (c',s') n'
        \<and> n' \<le> n"
proof -
  assume "(c,s) \<rightarrow>* (c',s') \<and> (c',s') \<rightarrow>* (d,t)"
  hence
      "(c,s) \<rightarrow>* (c',s')"
      "(c',s') \<rightarrow>* (d,t)"
    by auto
  hence "\<exists>n'. state_changes (c,s) (c',s') n'"
    using state_change_count_exists
    by simp
  then obtain n' where
      "state_changes (c,s) (c',s') n'"
    by (rule HOL.exE)
  have "\<exists>n''. state_changes (c',s') (d,t) n''"
    using
      `(c',s') \<rightarrow>* (d,t)`
      state_change_count_exists
    by simp
  then obtain n'' where
      "state_changes (c',s') (d,t) n''"
    by (rule HOL.exE)
  obtain n where
      "n = n' + n''"
    by simp
  have "n'' \<ge> 0"
    by simp
  hence "n' \<le> n"
    using `n = n' + n''`
    by simp
  have "state_changes (c,s) (d,t) n"
    using
      `n = n' + n''`
      `state_changes (c,s) (c',s') n'`
      `state_changes (c',s') (d,t) n''`
    sorry
*)

lemma one_state_change_impl_diff_states:
    "state_changes (c,s) (d,t) 1 \<Longrightarrow> s \<noteq> t"
proof -
  assume "state_changes (c,s) (d,t) 1"
  then obtain n where
      "state_changes (c,s) (d,t) n"
      "n = 1"
    by simp
  thus "s \<noteq> t"
  proof (induction "(c,s)" "(d,t)" n
         arbitrary: c d
         rule: state_changes.induct)
    case None
    hence "n = 0"
      by simp
    thus "s \<noteq> t"
      using `n = 1`
      by simp
  next
    case (Stateless c' d n c)
    thus "s \<noteq> t"
      by simp
  next
    case (Stateful c' s' d n c)
    thus "s \<noteq> t"
      using zero_state_changes_impl_same
      by auto
  qed
qed

(*
theorem state_dist_le_step_count:
    "small_step_count (c,s) (d,t) n
    \<Longrightarrow> \<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<le> n"
  sorry
*)
(*
proof (induction "(c,s)" "(d,t)" n
       rule: small_step_count.induct)
  case Self
  hence "state_changes (c,s) (d,t) 0"
    using state_changes.None
    by simp
  have "0 \<le> n"
    by simp
  hence "\<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<le> n"
    using `state_changes (c,s) (d,t) 0`
    by auto
  thus ?case
    using `state_changes (c,s) (d,t) 0`
    by blast
next
  case Step
  hence "small_step_count (c,s) (d,t) 1"
    by (rule small_step_count.Step)
  have "s = t \<or> s \<noteq> t"
    by simp
  thus "\<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<le> 1"
  proof (elim disjE)
    assume "s = t"
    hence "state_changes (c,s) (d,t) 0"
      using
        state_changes.None
        state_changes.Stateless
        local.Step
      by blast
    thus "\<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<le> 1"
      using `state_changes (c,s) (d,t) 0`
      by auto
  next
    assume "s \<noteq> t"
    hence "state_changes (c,s) (d,t) 1"
      using
        state_changes.None
        state_changes.Stateful
        local.Step
      by (metis One_nat_def add.commute plus_1_eq_Suc)
    thus "\<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<le> 1"
      by auto
  qed
next
  case (Following n1 n2 c2 s2)
  hence "\<exists>n'. state_changes (c,s) (c2,s2) n' \<and> n' \<le> n1" by try
  thus "\<exists>n'. state_changes (c,s) (d,t) n' \<and> n' \<le> (n1+n2)"
    by try
qed
  *)

inductive finalish :: "(com \<times> state) \<Rightarrow> bool" where
Final: "finalish (SKIP,s)" |
ModuloParsing:
    "finalish (c',s) \<and> (c,s) \<rightarrow> (c',s)
    \<Longrightarrow> finalish (c,s)"

theorem max_term_state_changes:
    "(c,s) \<rightarrow>* (SKIP,f)
    \<longleftrightarrow> (\<exists>x. \<forall>n. \<forall>d. \<forall>t.
         state_changes (c,s) (d,t) n
         \<longrightarrow> n \<le> x)"
proof
  assume "(c,s) \<rightarrow>* (SKIP,f)"
  hence "\<exists>x. state_changes (c,s) (SKIP,f) x"
    by (rule state_change_count_exists)
  then obtain x where
      "state_changes (c,s) (SKIP,f) x"
    by (rule HOL.exE)
  have
      "\<not>(\<exists>n. \<exists>d. \<exists>t.
      state_changes (c,s) (d,t) n
      \<and> n > x)"
  proof
    assume
        "\<exists>n. \<exists>d. \<exists>t. state_changes (c,s) (d,t) n \<and> n > x"
    then obtain n d t where
        "state_changes (c,s) (d,t) n \<and> n > x"
      by auto
    hence "(c,s) \<rightarrow>* (d,t)"
      using state_change_count_impl_leads_to
      by blast
    hence "(d,t) \<rightarrow>* (SKIP,f) \<or> (SKIP,f) \<rightarrow>* (d,t)"
      using
        `(c,s) \<rightarrow>* (SKIP,f)`
        determ_trace_triangle
      by blast
    thus False sorry
  qed
  thus
      "\<exists>x. \<forall>n. \<forall>d. \<forall>t.
      state_changes (c,s) (d,t) n
      \<longrightarrow> n \<le> x"
    sorry
next
  assume
      "\<exists>x. \<forall>n. \<forall>d. \<forall>t.
      state_changes (c,s) (d,t) n
      \<longrightarrow> n \<le> x"
  thus "(c,s) \<rightarrow>* (SKIP,f)"
    sorry
qed

corollary skip_is_max_state_changes:
    "(\<exists>f. state_changes (c,s) (SKIP,f) x)
    \<longleftrightarrow> (\<forall>n. \<forall>d. \<forall>t.
         state_changes (c,s) (d,t) n
         \<longrightarrow> n \<le> x)"
proof
  assume "\<exists>f. state_changes (c,s) (SKIP,f) x"
  then obtain f where
      "state_changes (c,s) (SKIP,f) x"
    by (rule HOL.exE)
  have
      "\<not>(\<exists>n. \<exists>d. \<exists>t.
      state_changes (c,s) (d,t) n
      \<and> n > x)"
  proof
    assume
        "\<exists>n. \<exists>d. \<exists>t. state_changes (c,s) (d,t) n \<and> n > x"
    then obtain n d t where
        "state_changes (c,s) (d,t) n \<and> n > x"
      by auto
    hence "(c,s) \<rightarrow>* (d,t)"
      using state_change_count_impl_leads_to
      by blast
    hence "(d,t) \<rightarrow>* (SKIP,f) \<or> (SKIP,f) \<rightarrow>* (d,t)"
      using
        `state_changes (c,s) (SKIP,f) x`
        determ_trace_triangle
        leads_to_state_changes
      by blast
    thus False
      sorry
  qed
  thus
      "\<forall>n. \<forall>d. \<forall>t.
      state_changes (c,s) (d,t) n
      \<longrightarrow> n \<le> x"
    by fastforce
next
  assume
      "\<forall>n. \<forall>d. \<forall>t.
      state_changes (c,s) (d,t) n
      \<longrightarrow> n \<le> x"
  thus "\<exists>f. state_changes (c,s) (SKIP,f) x"
    sorry
qed

theorem non_term_state_changes:
    "\<not> final (c,s)
    \<longleftrightarrow> (\<exists>d. \<exists>t. \<exists>n. state_changes (c,s) (d,t) n \<and> n > 0)"
proof
  assume "\<not> final (c,s)"
  thus "\<exists>d. \<exists>t. \<exists>n. state_changes (c,s) (d,t) n \<and> n > 0"
    sorry
next
  assume "\<exists>d. \<exists>t. \<exists>n. state_changes (c,s) (d,t) n \<and> n > 0"
  thus "\<not> final (c,s)"
    sorry
qed

(* Note that c1 \<sim> c2 would also be true for divergent
   non-termination, so unfortunately we don't the
   converse. *)
theorem state_equiv_impl_big_step_equiv:
    "\<forall>n. \<forall>t. (\<exists>d1. state_changes (c1,s) (d1,t) n)
    = (\<exists>d2. state_changes (c2,s) (d2,t) n)
    \<Longrightarrow> c1 \<sim> c2"
proof -
  assume assm:
      "\<forall>n. \<forall>t. (\<exists>d1. state_changes (c1,s) (d1,t) n)
      = (\<exists>d2. state_changes (c2,s) (d2,t) n)"
  have
      "(\<exists>f. (c1,s) \<rightarrow>* (SKIP,f))
      \<or> \<not>(\<exists>f. (c1,s) \<rightarrow>* (SKIP,f))"
    by auto
  thus "c1 \<sim> c2"
  proof (elim disjE)
    assume "\<exists>f. (c1,s) \<rightarrow>* (SKIP,f)"
    then obtain f where
        "(c1,s) \<rightarrow>* (SKIP,f)"
      by auto
    hence "\<exists>x. state_changes (c1,s) (SKIP,f) x"
      by (rule state_change_count_exists)
    then obtain x where
        "state_changes (c1,s) (SKIP,f) x"
      by (rule HOL.exE)
    hence
        "\<not>(\<exists>x'. \<exists>d1'. \<exists>t1'.
           state_changes (c1,s) (d1',t1') x'
           \<and> x' > x)"
      using skip_is_max_state_changes
      by (metis not_less)
    have
        "\<not>(\<exists>x'. \<exists>d2'. \<exists>t2'.
           state_changes (c2,s) (d2',t2') x'
           \<and> x' > x)"
    proof
      assume
          "\<exists>x'. \<exists>d2'. \<exists>t2'.
          state_changes (c2,s) (d2',t2') x'
          \<and> x' > x"
      then obtain x' d2' t2' where
          "state_changes (c2,s) (d2',t2') x'
          \<and> x' > x"
        by auto
      hence
          "\<exists>d1'. state_changes (c1,s) (d1',t2') x'
          \<and> x' > x"
        using assm
        by blast
      hence
          "\<exists>x'. \<exists>d1'. \<exists>t1'.
          state_changes (c1,s) (d1',t1') x'
          \<and> x' > x"
        by auto
      thus False
        using
          `\<not>(\<exists>x'. \<exists>d1'. \<exists>t1'.
             state_changes (c1,s) (d1',t1') x'
             \<and> x' > x)`
        by contradiction
    qed
    hence
        "\<forall>n. \<forall>d2. \<forall>t2.
        state_changes (c2,s) (d2,t2) n
        \<longrightarrow> n \<le> x"
      by fastforce
    hence "(c2,s) \<rightarrow>* (SKIP,f)"
      sorry
    hence "(c2,s) \<Rightarrow> f"
      by (rule small_term_impl_big_step)
    thus "c1 \<sim> c2"
      sorry
  next
    assume "\<not>(\<exists>f. (c1,s) \<rightarrow>* (SKIP,f))"
    thus "c1 \<sim> c2"
      sorry
  qed
qed

theorem while_state_equiv_impl_big_step_equiv:
    "(\<forall>s. \<not>final (c1,s) \<and> \<not>final (c2,s)
      \<Longrightarrow> \<exists>t. \<exists>n. state_changes (c1,s) (c1,t) n
          \<and> state_changes (c2,s) (c2,t) n
          \<and> n > 0)
    \<Longrightarrow> c1 \<sim> c2"
proof -
  assume
    "\<forall>s. \<not>final (c1,s) \<and> \<not>final (c2,s)
    \<Longrightarrow> \<exists>t. \<exists>n. state_changes (c1,s) (c1,t) n
        \<and> state_changes (c2,s) (c2,t) n
        \<and> n > 0"
  thus "c1 \<sim> c2"
    sorry
qed

end