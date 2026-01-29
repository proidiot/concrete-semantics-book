theory IMP
  imports Bool
begin

datatype command =
  SKIP
| Assign var_name arith_exp
| Sequence command command
| CondBranch bool_exp command command
| CondLoop bool_exp command

end