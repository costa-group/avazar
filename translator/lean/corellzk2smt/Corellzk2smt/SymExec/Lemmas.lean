import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.Language.Core.Semantics.BigStep
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.BigStep
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability


open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability


def senv_eq_env_wrt_assignment {c : ZKConfig}
    (symEnv : SymEnv c)
    (assignment : Assignment c)
    (env : Env c)
    : Prop :=
  env.keys = symEnv.keys ∧ -- same keys
  env.arrays = symEnv.arrays -- same arrays
