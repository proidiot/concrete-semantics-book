theory State
  imports Main
begin

type_synonym var_name = "string"
type_synonym int_val = "int"
type_synonym state = "var_name \<Rightarrow> int_val"

end