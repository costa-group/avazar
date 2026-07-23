import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST


namespace Corellzk2smt.SymExec.BigStep


open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic

def seEvalAssignment {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_id : VarID)
    (_e : Expr c)
    : Except String (CmdsSpec c) :=
  Except.error "seEvalAssign: TBD"

end Corellzk2smt.SymExec.BigStep
