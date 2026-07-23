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


def seNewArray {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_id : VarID)
    (_size : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  Except.error "seNewArray: TBD"

def seReadArray {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_out : VarID)
    (_a : VarID)
    (_index : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  Except.error "seReadArray: TBD"

def seWriteArray {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_a : VarID)
    (_index : SimpleExpr c)
    (_value : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  Except.error "seWriteArray: TBD"

def seCopyArray {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_out : VarID)
    (_a : VarID)
    : Except String (CmdsSpec c) :=
  Except.error "seCopyArray: TBD"

end Corellzk2smt.SymExec.BigStep
