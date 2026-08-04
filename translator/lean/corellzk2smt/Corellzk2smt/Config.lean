import Corellzk2smt.Basic


namespace Corellzk2smt.Config

structure ProgPrinterParams where
  spaces_per_indent_level : Nat := 2
  show_liveness : Bool := false
  deriving Inhabited



/- How to encode that an FF variable is boolean.
    - 'range' scheme encodes that a variable is boolean by checking that it is in the range [0,1].
    - 'mul' scheme encodes that a variable is boolean by checking that x*(1-x) = 0.
-/
inductive BoolFFVarScm where
  | range -- range(x,0,1)
  | mul -- x*(1-x) = 0
  deriving Repr, BEq, Inhabited


structure SymExecParams (c : ZKConfig) where
  boolFFVarScm : BoolFFVarScm := BoolFFVarScm.range
  new_var_assignment : Bool := false -- whether to generate new smt variable
  new_var_array_read : Bool := false -- whether to generate new smt variable for array read
  new_var_array_write : Bool := false -- whether to generate new smt variable for array write
  new_var_array_new : Bool := false -- whether to generate new smt variable for array write
  deriving Inhabited


-- Structure for storing flags and global configurations
structure GlobalConfig (c : ZKConfig) where
  prog_printer : ProgPrinterParams := default
  sym_exec : SymExecParams c := default
  deriving Inhabited



end Corellzk2smt.Config
