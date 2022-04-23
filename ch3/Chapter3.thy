theory Chapter3
  imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
    (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
    apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N n1) (N n2) = N (n1 + n2)" |
"plus (N n) v = (if n=0 then v else Plus (N n) v)" |
"plus v (N n) = (if n=0 then v else Plus v (N n))" |
"plus v1 v2 = Plus v1 v2"

lemma aval_plus [simp]: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 rule: plus.induct)
              apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus a1 a2"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
    apply auto
  done

fun has_ints :: "aexp \<Rightarrow> bool" where
"has_ints (N n) = True" |
"has_ints (V x) = False" |
"has_ints (Plus a b) = disj (has_ints a) (has_ints b)"

fun minimally_int_free :: "aexp \<Rightarrow> bool" where
"minimally_int_free (N n) = (if n=0 then True else False)" |
"minimally_int_free (V x) = True" |
"minimally_int_free (Plus a b) = conj (~ (has_ints a)) (~ (has_ints b))"

fun has_vars :: "aexp \<Rightarrow> bool" where
"has_vars (N n) = False" |
"has_vars (V x) = True" |
"has_vars (Plus a b) = disj (has_vars a) (has_vars b)"

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (Plus (N n1) (N n2)) = False" |
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus a1 a2) = conj (optimal a1) (optimal a2)"

theorem asimp_const_optimal: "optimal (asimp_const a)"
  apply (induction a)
    apply (auto split: aexp.split)
  done

fun var_count :: "aexp \<Rightarrow> nat" where
"var_count (N n) = 0" |
"var_count (V v) = 1" |
"var_count (Plus a b) = (var_count a) + (var_count b)"

fun int_count :: "aexp \<Rightarrow> nat" where
"int_count (N n) = 1" |
"int_count (V v) = 0" |
"int_count (Plus a b) = (int_count a) + (int_count b)"

fun val_count :: "aexp \<Rightarrow> nat" where
"val_count (N n) = 1" |
"val_count (V v) = 1" |
"val_count (Plus a b) = (val_count a) + (val_count b)"

lemma val_count_is_int_plus_var_count: "val_count a = (int_count a) + (var_count a)"
  apply (induction a)
    apply auto
  done

lemma val_count_gt_zero [simp]: "val_count a > 0"
  apply (induction a)
    apply auto
  done

lemma val_count_addend_lt_sum [simp]: "val_count (Plus a b) > val_count a"
  apply (induction a)
    apply auto
  done

function (sequential) full_asimp_step :: "aexp \<Rightarrow> aexp \<Rightarrow> int \<Rightarrow> aexp" where
"full_asimp_step (N n1) (N n2) n3 = N (n1 + n2 + n3)" |
"full_asimp_step (N n1) (V v) n2 = Plus (V v) (N (n1 + n2))" |
"full_asimp_step (N n1) (Plus a b) n2 = full_asimp_step a b (n1 + n2)" |
"full_asimp_step (V v) (N n1) n2 = Plus (V v) (N (n1 + n2))" |
"full_asimp_step (V v1) (V v2) n = Plus (V v1) (Plus (V v2) (N n))" |
"full_asimp_step (V v) (Plus a b) n = Plus (V v) (full_asimp_step a b n)" |
"full_asimp_step (Plus a b) (N n1) n2 = full_asimp_step a b (n1 + n2)" |
"full_asimp_step (Plus a b) (V v) n = Plus (V v) (full_asimp_step a b n)" |
"full_asimp_step (Plus a b) (Plus c d) n = full_asimp_step a (Plus b (Plus c d)) n"
by pat_completeness auto
termination full_asimp_step
  apply (relation "measures [\<lambda>(a,b,n). (val_count (Plus a b)), \<lambda>(a,b,n). (var_count (Plus a b)), \<lambda>(a,b,n). (val_count a)]")
  apply auto
  done

lemma aval_full_asimp_step [simp]: "aval (full_asimp_step a b n) s = (aval a s) + (aval b s) + n"
  apply (induction a b n arbitrary: s rule: full_asimp_step.induct)
          apply auto
  done

lemma int_count_full_asimp_step [simp]: "int_count (full_asimp_step a b n) < 2"
  apply (induction a b n rule: full_asimp_step.induct)
          apply auto
  done

lemma optimal_full_asimp_step [simp]: "optimal (full_asimp_step a b n)"
  apply (induction a b n rule: full_asimp_step.induct)
  apply auto
  done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = full_asimp_step a (N 0) 0"

theorem full_asimp_example: "full_asimp (Plus (N 1) (Plus (V x) (N 2))) = Plus (V x) (N 3)"
  apply auto
  done

theorem aval_full_asimp: "aval (full_asimp a) s = aval a s"
  apply (induction a arbitrary: s)
    apply auto
  done

lemma int_count_full_asimp: "int_count (full_asimp a) < 2"
  apply (induction a)
    apply auto
  done

lemma optimal_full_asimp: "optimal (full_asimp a)"
  apply (induction a rule: full_asimp.induct)
  apply auto
  done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst v a (N n) = N n" |
"subst v1 a (V v2) = (if v1=v2 then a else (V v2))" |
"subst v a (Plus b c) = Plus (subst v a b) (subst v a c)"

theorem substitution_lemma [simp]: "aval (subst x a e) s = aval e (s (x := aval a s))"
  apply (induction e rule: subst.induct)
  apply auto
  done

theorem substitution_distributivity: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply auto
  done

datatype mexp = N int | V vname | Plus mexp mexp | Times mexp mexp

fun mval :: "mexp \<Rightarrow> state \<Rightarrow> val" where
"mval (N n) s = n" |
"mval (V v) s = s v" |
"mval (Plus a b) s = (mval a s) + (mval b s)" |
"mval (Times a b) s = (mval a s) * (mval b s)"

fun mplus :: "mexp \<Rightarrow> mexp \<Rightarrow> mexp" where
"mplus (N n1) (N n2) = N (n1 + n2)" |
"mplus (N n) a = (if n=0 then a else (Plus (N n) a))" |
"mplus a (N n) = (if n=0 then a else (Plus a (N n)))" |
"mplus a b = Plus a b"

fun mtimes :: "mexp \<Rightarrow> mexp \<Rightarrow> mexp" where
"mtimes (N n1) (N n2) = N (n1 * n2)" |
"mtimes (N n) a = (if n=1 then a else if n=0 then (N 0) else (Times (N n) a))" |
"mtimes a (N n) = (if n=1 then a else if n=0 then (N 0) else (Times a (N n)))" |
"mtimes a b = Times a b"

fun msimp :: "mexp \<Rightarrow> mexp" where
"msimp (N n) = N n" |
"msimp (V v) = V v" |
"msimp (Plus a b) = mplus (msimp a) (msimp b)" |
"msimp (Times a b) = mtimes (msimp a) (msimp b)"

lemma mval_mplus [simp]: "mval (mplus a b) s = (mval a s) + (mval b s)"
  apply (induction a rule: mplus.induct)
     apply auto
  done

lemma mval_mtimes [simp]: "mval (mtimes a b) s = (mval a s) * (mval b s)"
  apply (induction a rule: mtimes.induct)
  apply auto
  done

theorem mval_msimp: "mval (msimp a) s = mval a s"
  apply (induction a)
     apply auto
  done

fun moptimal :: "mexp \<Rightarrow> bool" where
"moptimal (Plus (N n1) (N n2)) = False" |
"moptimal (Times (N n1) (N n2)) = False" |
"moptimal (Plus a b) = conj (moptimal a) (moptimal b)" |
"moptimal (Times a b) = conj (moptimal a) (moptimal b)" |
"moptimal a = True"

lemma moptimal_mplus [simp]: "(conj (moptimal a) (moptimal b)) \<Longrightarrow> moptimal (mplus a b)"
  apply (induction a b rule: mplus.induct)
  apply auto
  done

lemma moptimal_mtimes [simp]: "(conj (moptimal a) (moptimal b)) \<Longrightarrow> moptimal (mtimes a b)"
  apply (induction a b rule: mtimes.induct)
  apply auto
  done

theorem moptimal_msimp: "moptimal (msimp a)"
  apply (induction a)
  apply auto
  done

datatype cexp = N int |
  V vname |
  Plus cexp cexp |
  Times cexp cexp |
  Minus cexp cexp |
  Divide cexp cexp |
  Incr vname |
  Decr vname

fun cval :: "cexp \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"cval (N n) s = Some (n, s)" |
"cval (V v) s = Some (s v, s)" |
"cval (Incr v) s = Some (s v, s (v:=(s v)+1))" |
"cval (Decr v) s = Some (s v, s (v:=(s v)-1))" |
"cval (Plus a b) s = Some (
  (fst (the (cval a s))) + (fst (the (cval b (snd (the (cval a s)))))),
  snd (the (cval b (snd (the (cval a s)))))
)" |
"cval (Minus a b) s = Some (
  (fst (the (cval a s))) - (fst (the (cval b (snd (the (cval a s)))))),
  snd (the (cval b (snd (the (cval a s)))))
)" |
"cval (Times a b) s = Some (
  (fst (the (cval a s))) * (fst (the (cval b (snd (the (cval a s)))))),
  snd (the (cval b (snd (the (cval a s)))))
)" |
"cval (Divide a b) s = (
  if b=(N 0)
  then None
  else Some (
    (fst (the (cval a s))) div (fst (the (cval b (snd (the (cval a s)))))),
    snd (the (cval b (snd (the (cval a s)))))
  )
)"

fun cval_last :: "cexp list \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
"cval_last Nil s = (0,s)" |
"cval_last (Cons a Nil) s = the (cval a s)" |
"cval_last (Cons a l) s = cval_last l (snd (the (cval a s)))"

lemma incr_is_add_one [simp]: "
fst (cval_last [(Incr v), (V v)] s)
= fst (the (cval (Plus (V v) (N 1)) s))
"
  apply auto
  done

lemma decr_is_minus_one [simp]: "
fst (cval_last [(Decr v), (V v)] s)
= fst (the (cval (Minus (V v) (N 1)) s))
"
  apply auto
  done

lemma incr_decr_is_noop [simp]: "snd (cval_last [(Incr v), (Decr v)] s) = s"
  apply auto
  done

lemma decr_incr_is_noop [simp]: "snd (cval_last [(Decr v), (Incr v)] s) = s"
  apply auto
  done

lemma subeval_order_behavior_l [simp]: "the (cval (Plus (Incr v) (V v)) s) = (fst (the (cval (Plus (Plus (V v) (V v)) (N 1)) s)), snd (the (cval (Incr v) s)))"
  apply auto
  done

lemma subeval_order_behavior_r [simp]: "the (cval (Plus (V v) (Incr v)) s) = (fst (the (cval (Plus (V v) (V v)) s)), snd (the (cval (Incr v) s)))"
  apply auto
  done

lemma plus_minus_is_zero [simp]: "cval (Minus (Plus (V a) (V b)) (V b)) s = cval (V a) s"
  apply auto
  done

lemma times_divide_is_one [simp]: "(fst (the (cval (V b) s)) \<noteq> 0) \<Longrightarrow> (cval (Divide (Times (V a) (V b)) (V b)) s = cval (V a) s)"
  apply auto
  done

lemma times_and_plus_related [simp]: "cval (Times (V a) (N 2)) s = cval (Plus (V a) (V a)) s"
  apply auto
  done

datatype lexp = N int |
  V vname |
  Plus lexp lexp |
  Let vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
"lval (N n) s = n" |
"lval (V v) s = s v" |
"lval (Plus a b) s = (lval a s) + (lval b s)" |
"lval (Let v t e) s = lval e (s (v:=(lval t s)))"

lemma let_identity: "lval (Let x a (V x)) s = lval a s"
  apply auto
  done

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (lexp.N n) = aexp.N n" |
"inline (lexp.V v) = aexp.V v" |
"inline (lexp.Plus a b) = aexp.Plus (inline a) (inline b)" |
"inline (lexp.Let v t e) = subst v (inline t) (inline e)"

theorem lval_inline [simp]: "aval (inline a) s = lval a s"
  apply (induction a arbitrary: s rule: inline.induct)
  apply auto
  done

datatype bexp =
  Bc bool |
  Not bexp |
  And bexp bexp |
  Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc b) s = b" |
"bval (Not b) s = (~ (bval b s))" |
"bval (And a b) s = conj (bval a s) (bval b s)" |
"bval (Less a b) s = ((aval a s) < (aval b s))"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

(* book says and, but that's a keyword *)
fun andd :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"andd (Bc True) b = b" |
"andd b (Bc True) = b" |
"andd (Bc False) b = Bc False" |
"andd b (Bc False) = Bc False" |
"andd a b = And a b"

(* it is necessary to specify aexp.N since I created lexp.N as well *)
fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (aexp.N a) (aexp.N b) = Bc (a < b)" |
"less a b = Less a b"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc b) = Bc b" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And a b) = andd (bsimp a) (bsimp b)" |
"bsimp (Less a b) = less (asimp a) (asimp b)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Not (Less a b)) (Not (Less b a))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (Less b a)"

theorem bval_eq [simp]: "bval (Eq a b) s = ((aval a s) = (aval b s))"
  apply auto
  done

theorem bval_le [simp]: "bval (Le a b) s = ((aval a s) \<le> (aval b s))"
  apply auto
  done

datatype ifexp =
  Bc2 bool |
  If ifexp ifexp ifexp |
  Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) s = b" |
"ifval (If g a b) s = (
  if (ifval g s)
  then (ifval a s)
  else (ifval b s)
)" |
"ifval (Less2 a b) s = ((aval a s) < (aval b s))"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = Bc2 b" |
"b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
"b2ifexp (And a b) = If (b2ifexp a) (b2ifexp b) (Bc2 False)" |
"b2ifexp (Less a b) = Less2 a b"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = (Bc b)" |
"if2bexp (If g a b) =
And
  (Not (And
    (if2bexp g)
    (Not (if2bexp a))
  ))
  (Not (And
    (Not (if2bexp g))
    (Not (if2bexp b))
   ))
" |
"if2bexp (Less2 a b) = Less a b"

theorem b2ifexp_if2exp_noop [simp]: "ifval (b2ifexp (if2bexp a)) s = ifval a s"
  apply (induction a arbitrary: s)
  apply auto
  done

theorem if2bexp_b2ifexp_noop [simp]: "bval (if2bexp (b2ifexp a)) s = bval a s"
  apply (induction a arbitrary: s)
  apply auto
  done

datatype pbexp =
  VAR vname |
  NOT pbexp |
  AND pbexp pbexp |
  OR pbexp pbexp

type_synonym pbstate = "vname \<Rightarrow> bool"

fun pbval :: "pbexp \<Rightarrow> pbstate \<Rightarrow> bool" where
"pbval (VAR v) bs = bs v" |
"pbval (NOT b) bs = (~ (pbval b bs))" |
"pbval (AND a b) bs = conj (pbval a bs) (pbval b bs)" |
"pbval (OR a b) bs = disj (pbval a bs) (pbval b bs)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR v) = True" |
"is_nnf (NOT (VAR v)) = True" |
"is_nnf (NOT b) = False" |
"is_nnf (AND a b) = conj (is_nnf a) (is_nnf b)" |
"is_nnf (OR a b) = conj (is_nnf a) (is_nnf b)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR v) = VAR v" |
"nnf (NOT (VAR v)) = NOT (VAR v)" |
"nnf (NOT (NOT b)) = nnf b" |
"nnf (NOT (AND a b)) = OR (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (OR a b)) = AND (nnf (NOT a)) (nnf (NOT b))" |
"nnf (AND a b) = AND (nnf a) (nnf b)" |
"nnf (OR a b) = OR (nnf a) (nnf b)"

theorem nnf_preserves_pbval [simp]: "pbval (nnf b) bs = pbval b bs"
  apply (induction b rule: nnf.induct)
  apply auto
  done

theorem nnf_is_nnf [simp]: "is_nnf (nnf a)"
  apply (induction a rule: nnf.induct)
  apply auto
  done

fun is_dnf_conj :: "pbexp \<Rightarrow> bool" where
"is_dnf_conj (VAR v) = True" |
"is_dnf_conj (NOT (VAR v)) = True" |
"is_dnf_conj (NOT b) = False" |
"is_dnf_conj (AND a b) = conj (is_dnf_conj a) (is_dnf_conj b)" |
"is_dnf_conj (OR a b) = False"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR v) = True" |
"is_dnf (NOT (VAR v)) = True" |
"is_dnf (NOT b) = False" |
"is_dnf (AND a b) = conj (is_dnf_conj a) (is_dnf_conj b)" |
"is_dnf (OR a b) = conj (is_dnf a) (is_dnf b)"

lemma is_dnf_not_implies_is_dnf_conj_not [simp]: "is_dnf (NOT b) \<Longrightarrow> is_dnf_conj (NOT b)"
  apply (induction b)
  apply auto
  done

lemma is_nnf_not_implies_is_dnf_not [simp]: "is_nnf (NOT b) \<Longrightarrow> is_dnf (NOT b)"
  apply (induction b)
  apply auto
  done

fun dist_conj_over_dnfs :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dist_conj_over_dnfs (OR a b) c = OR (dist_conj_over_dnfs a c) (dist_conj_over_dnfs b c)" |
"dist_conj_over_dnfs a (OR b c) = OR (dist_conj_over_dnfs a b) (dist_conj_over_dnfs a c)" |
"dist_conj_over_dnfs a b = AND a b"

lemma dist_conj_over_dnfs_preserves_val [simp]: "pbval (dist_conj_over_dnfs a b) bs = pbval (AND a b) bs"
  apply (induction a b rule: dist_conj_over_dnfs.induct)
  apply auto
  done

lemma dist_conj_over_dnfs_preserves_dnf [simp]: "(conj (is_dnf a) (is_dnf b)) \<Longrightarrow> is_dnf (dist_conj_over_dnfs a b)"
  apply (induction a b rule: dist_conj_over_dnfs.induct)
  apply auto
  done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR v) = VAR v" |
"dnf_of_nnf (NOT b) = NOT b" |
"dnf_of_nnf (AND a b) = dist_conj_over_dnfs (dnf_of_nnf a) (dnf_of_nnf b)" |
"dnf_of_nnf (OR a b) = OR (dnf_of_nnf a) (dnf_of_nnf b)"

theorem dnf_of_nnf_preserves_val [simp]: "pbval (dnf_of_nnf b) bs = pbval b bs"
  apply (induction b)
  apply auto
  done

theorem dnf_of_nnf_turns_nnf_into_dnf [simp]: "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply (induction b rule: dnf_of_nnf.induct)
  apply auto
  done

lemma full_dnf_preserves_val [simp]: "pbval (dnf_of_nnf (nnf b)) bs = pbval b bs"
  apply auto
  done

datatype instr =
  LOADI val |
  LOAD vname |
  ADD

type_synonym stack = "val list"

abbreviation hd2 :: "'a list \<Rightarrow> 'a" where
"hd2 xs \<equiv> hd (tl xs)"

abbreviation tl2 :: "'a list \<Rightarrow> 'a list" where
"tl2 xs \<equiv> tl (tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 (LOAD v) s stk = Some (s (v) # stk)" |
"exec1 ADD _ (Cons a (Cons b stk)) = Some ((a + b) # stk)" |
"exec1 ADD _ stk = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack option \<Rightarrow> stack option" where
"exec [] _ (Some stk) = Some stk" |
"exec is s None = None" |
"exec (i#is) s (Some stk) = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (aexp.N n) = [(LOADI n)]" |
"comp (aexp.V v) = [(LOAD v)]" |
"comp (aexp.Plus a b) = (comp a) @ (comp b) @ [(ADD)]"

theorem seq_instr_exec_equiv_recurs_stack_eval [simp]: "exec (a @ b) s some_stk = exec b s (exec a s some_stk)"
  apply (induction a s some_stk arbitrary: b rule: exec.induct)
   apply auto
  done

theorem compiled_execution_matches_evaluation [simp]: "exec (comp a) s (Some stk) = Some (aval a s#stk)"
  apply (induction a arbitrary: stk)
  apply auto
  done

type_synonym reg = nat

datatype rinstr =
  RLOADI int reg |
  RLOAD vname reg |
  RADD reg reg

type_synonym rstate = "reg \<Rightarrow> int"

(* The book says exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int",
   but exec isn't going to know which register has been set without a deeper spec,
   which would defeat the purpose of having a separate exec1 in the first place. *)
fun rexec1 :: "rinstr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"rexec1 (RLOADI i r) _ rs = (rs (r:=i))" |
"rexec1 (RLOAD v r) s rs = (rs (r:=s v))" |
"rexec1 (RADD r r2) _ rs = (rs (r:=(rs r) + (rs r2)))"

lemma rexec1_radd_behavior [simp]: "(conj (a = rs r1) (b = rs r2)) \<Longrightarrow> ((rexec1 (RADD r1 r2) s rs) r1 = a + b)"
  apply auto
  done

fun rexec :: "rinstr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"rexec [] _ rs = rs" |
"rexec (i#is) s rs = rexec is s (rexec1 i s rs)"

fun rcomp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr list" where
"rcomp (aexp.N n) r = [(RLOADI n r)]" |
"rcomp (aexp.V v) r = [(RLOAD v r)]" |
"rcomp (aexp.Plus a b) r = (rcomp a r) @ (rcomp b (r+1)) @ [(RADD r (r+1))]"

lemma rexec_seq_instr_equals_seq_rexec [simp]: "(rexec (a @ b) s rs) rr = (rexec b s (rexec a s rs)) rr"
  apply (induction a s rs arbitrary: b rr rule: rexec.induct)
  apply auto
  done

lemma smaller_registers_untouched [simp]: "(rl < r) \<Longrightarrow> ((rexec (rcomp a r) s rs) rl = rs rl)"
  apply (induction a r arbitrary: s rs rl rule: rcomp.induct)
  apply auto
  done

lemma rcomp_preserves_incr_regs [simp]: "(rexec (a @ (rcomp b r)) s rs) r = (rexec (rcomp b r) s rs) r"
  apply (induction b r arbitrary: a s rs rule: rcomp.induct)
  apply auto
  done

theorem rexec_rcomp_equals_aval [simp]: "rexec (rcomp a r) s rs r = aval a s"
  apply (induction a r arbitrary: s rs rule: rcomp.induct)
  apply auto
  done

datatype instr0 =
  LDI0 val |
  LD0 vname |
  MV0 reg |
  ADD0 reg

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec01 (LDI0 i) _ rs = rs (0:=i)" |
"exec01 (LD0 v) s rs = rs (0:=s v)" |
"exec01 (MV0 r) _ rs = rs (r:=rs 0)" |
"exec01 (ADD0 r) _ rs = rs (0:=(rs 0) + (rs r))"

lemma exec01_mov0_behavior [simp]: "(exec01 (MV0 r) s rs) r = rs 0"
  apply auto
  done

(* "is" is a keyword in some circumstances.
   While using it as a variable name as described in the book
   is sometimes not a problem, at other times it can be a problem.
   As such, it seems prudent to always avoid using "is" as a variable name. *)
fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
"exec0 [] _ rs = rs" |
"exec0 (i#ins) s rs = exec0 ins s (exec01 i s rs)"

fun comp0_below :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0_below (aexp.N n) r = [(LDI0 n)]" |
"comp0_below (aexp.V v) r = [(LD0 v)]" |
"comp0_below (aexp.Plus a b) r = (comp0_below a (r+2)) @ [(MV0 (r+1))] @ (comp0_below b (r+2)) @ [(ADD0 (r+1))]"

lemma exec0_seq_instr_equals_seq_exec0 [simp]: "exec0 (a @ b) s rs = exec0 b s (exec0 a s rs)"
  apply (induction a s rs arbitrary: b rule: exec0.induct)
  apply auto
  done

lemma comp0_below_skips_regs [simp]: "(conj (rl \<noteq> 0) (rl < r)) \<Longrightarrow> ((exec0 (comp0_below a r) s rs) rl = rs rl)"
  apply (induction a r arbitrary: rl rs s rule: comp0_below.induct)
  apply auto
  done

lemma append_mv0_behavior [simp]: "(exec0 (ins @ [(MV0 r)]) s rs) r = (exec0 ins s rs) 0"
  apply auto
  done

lemma exec0_comp0_below_equals_aval [simp]: "(exec0 (comp0_below a r) s rs) 0 = aval a s"
  apply (induction a r arbitrary: s rs rule: comp0_below.induct)
  apply auto
  done

fun comp0 :: "aexp \<Rightarrow> instr0 list" where
"comp0 a = comp0_below a 0"

theorem exec0_comp0_equals_aval [simp]: "(exec0 (comp0 a) s rs) 0 = aval a s"
  apply auto
  done

end
