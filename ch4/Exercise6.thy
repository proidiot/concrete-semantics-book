theory Exercise6
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

(* NOTE: aval_rel name is taken by an auto-generated property
   during the definition of aval, so switching to double
   underscore here. *)
inductive aval__rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
num: "aval__rel (N n) s n" |
var: "(s v = n) \<Longrightarrow> aval__rel (V v) s n" |
plus: "
  aval__rel a s na
  \<Longrightarrow> aval__rel b s nb
  \<Longrightarrow> aval__rel (Plus a b) s (na + nb)"

theorem rel_thus_aval: "aval__rel a s v \<Longrightarrow> aval a s = v"
  apply (induction rule: aval__rel.induct)
  apply auto
  done

theorem aval_thus_rel: "(aval a s = n) \<Longrightarrow> aval__rel a s n"
  apply (induction a arbitrary: s n)
    apply (simp add: aval__rel.num)
  using aval__rel.var apply (simp add: aval__rel.intros)
  apply (metis aval.simps(3) aval__rel.simps)
  done

theorem rel_is_aval: "aval__rel a s v \<longleftrightarrow> aval a s = v"
  using rel_thus_aval aval_thus_rel apply blast
  done

end