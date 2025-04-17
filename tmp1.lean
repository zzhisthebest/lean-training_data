import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Batteries.Data.String.Basic
import Cli

open Lean Elab IO Meta Tactic Term
open Cli System

def fun1 : TacticM String := do
  return "hello"

def fun2 : IO String := do
  return fun1
