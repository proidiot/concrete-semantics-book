theory Bool
  imports Arith
begin

datatype bool_exp =
  Bconst bool
| Not bool_exp
| And bool_exp bool_exp
| Less arith_exp arith_exp

fun bool_val :: "bool_exp \<Rightarrow> state \<Rightarrow> bool" where
  "bool_val (Bconst b) s = b"
| "bool_val (Not b) s = (\<not> bool_val b s)"
| "bool_val (And a b) s =
    (bool_val a s \<and> bool_val b s)"
| "bool_val (Less a b) s =
    (arith_val a s < arith_val b s)"

fun not :: "bool_exp \<Rightarrow> bool_exp" where
  "not (Bconst True) = Bconst False"
| "not (Bconst False) = Bconst True"
| "not b = Not b"

fun "and" :: "bool_exp \<Rightarrow> bool_exp \<Rightarrow> bool_exp" where
  "and (Bconst True) b = b"
| "and b (Bconst True) = b"
| "and (Bconst False) b = Bconst False"
| "and b (Bconst False) = Bconst False"
| "and a b = And a b"

fun less :: "arith_exp \<Rightarrow> arith_exp \<Rightarrow> bool_exp" where
  "less (Num a) (Num b) = Bconst (a < b)"
| "less a b = Less a b"

fun bool_simp :: "bool_exp \<Rightarrow> bool_exp" where
  "bool_simp (Bconst b) = Bconst b"
| "bool_simp (Not b) = not (bool_simp b)"
| "bool_simp (And a b) =
    and (bool_simp a) (bool_simp b)"
| "bool_simp (Less a b) =
    less (arith_simp a) (arith_simp b)"

end