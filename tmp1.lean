

    --IO.println s! "{module.toString}"

 Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Batteries.Data.String.Basic
import Cli

open Lean Elab IO Meta
open Cli System

def getEnvFromModule (module : Name) : IO Environment := do
  initSearchPath (← findSysroot)
  let env ← CoreM.withImportModules #[module] getEnv
  return env
