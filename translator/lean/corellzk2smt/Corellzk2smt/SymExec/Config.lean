namespace Corellzk2smt.SymExec.Config


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


end Corellzk2smt.SymExec.Config
