theory Exercise7
  imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype instr =
  LOADI val |
  LOAD vname |
  ADD

type_synonym stack = "val list"

abbreviation hd2 :: "'a list \<Rightarrow> 'a" where
"hd2 xs \<equiv> hd (tl xs)"

abbreviation tl2 :: "'a list \<Rightarrow> 'a list" where
"tl2 xs \<equiv> tl (tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD v) s stk = s (v) # stk" |
"exec1 ADD _ stk = (hd2 stk + hd stk) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#ins) s stk = exec ins s (exec1 i s stk)"

lemma exec_rev_app [simp]: "exec (a @ b) s stk = exec b s (exec a s stk)"
  apply (induction a s stk arbitrary: b rule: exec.induct)
   apply auto
  done

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (aexp.N n) = [(LOADI n)]" |
"comp (aexp.V v) = [(LOAD v)]" |
"comp (aexp.Plus a b) = (comp a) @ (comp b) @ [(ADD)]"

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
empty: "ok n [] n" |
loadi: "ok n ins n' ==> ok n (ins @ [(LOADI _)]) (n' + 1)" |
load: "ok n ins n' ==> ok n (ins @ [(LOAD _)]) (n' + 1)" |
add: "ok n ins (n' + 2) \<Longrightarrow> ok n (ins @ [(ADD)]) (n' + 1)"

lemma chg_impl_instructs: "ok n ins n' \<Longrightarrow> n \<noteq> n' \<Longrightarrow> ins \<noteq> []"
  apply (induction rule: ok.induct)
     apply simp_all
  done

lemma ok_app: "ok n2 b n3 \<Longrightarrow> ok n1 a n2 \<Longrightarrow> ok n1 (a @ b) n3"
  apply (induction rule: ok.induct)
     apply simp
    apply (metis append.assoc ok.loadi)
   apply (metis append.assoc ok.load)
  apply (metis append.assoc ok.add)
  done

theorem ok_predicts_depth: "
  ok n ins n'
  \<Longrightarrow> length stk = n
  \<Longrightarrow> length (exec ins s stk) = n'
"
  apply (induction rule: ok.induct)
     apply simp_all
  done

theorem comp_is_ok: "ok n (comp a) (n + 1)"
  apply (induction a arbitrary: n)
    apply (metis Groups.add_ac(2) append.left_neutral comp.simps(1) ok.simps plus_1_eq_Suc)
   apply (metis Groups.add_ac(2) append.left_neutral comp.simps(2) ok.simps plus_1_eq_Suc)
  apply (smt (verit, best) One_nat_def ab_semigroup_add_class.add_ac(1) comp.simps(3) numerals(2) ok.intros(4) ok_app plus_1_eq_Suc)
  done

end