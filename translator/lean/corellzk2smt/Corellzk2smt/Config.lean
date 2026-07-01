import Corellzk2smt.Basic


structure ProgPrinterConfig where
  spaces_per_indent_level : Nat := 2
  show_liveness : Bool := false
  deriving Inhabited

-- Structure for storing flags and global configurations
structure GlobalConfig (c : ZKConfig) where
  prog_printer : ProgPrinterConfig := default
  deriving Inhabited
