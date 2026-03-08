import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic


/- Symbolic execution of 'skip' -/
def seSkip {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) : Except String (CmdsSpec c) := do
  return { inSymEnv := symEnv, outSymEnv := symEnv, f := FFFormula.true, nextId := cfg.nextId }


end Llzk.SymExec.SymInstr
