import Corellzk2smt.Basic


namespace Corellzk2smt.Config

structure ProgPrinterParams where
  spaces_per_indent_level : Nat := 2
  show_liveness : Bool := false
  deriving Inhabited




/- This defines several schemes that are used to encode signed comparisons of FF values. In
   particular for 'lt' as other operations are defined in terms of it.

   - 'always_sub_range' scheme always encodes x<y by checking the range x-y.
   - 'normal' scheme encodes x<y using ranges when x or y are constants, and
     falls back to a bitwise comparison otherwise.

     For more information see the actual encodings in BoolExpr.lean.
-/
inductive CmpScm where
  | range_of_diff -- based one checking the range of x-y to encode x<y
  | normal
  deriving Repr, BEq, Inhabited


/- How to encode that an FF variable is boolean.
    - 'range' scheme encodes that a variable is boolean by checking that it is in the range [0,1].
    - 'mul' scheme encodes that a variable is boolean by checking that x*(1-x) = 0.
-/
inductive BoolFFScm where
  | range -- range(x,0,1)
  | mul -- x*(1-x) = 0
  deriving Repr, BEq, Inhabited


structure SymExecParams (c : ZKConfig) where
  cmpScm : CmpScm := CmpScm.normal
  boolFFScm : BoolFFScm := BoolFFScm.range
  deriving Inhabited


-- Structure for storing flags and global configurations
structure GlobalConfig (c : ZKConfig) where
  prog_printer : ProgPrinterParams := default
  sym_exec : SymExecParams c := default
  deriving Inhabited



end Corellzk2smt.Config
