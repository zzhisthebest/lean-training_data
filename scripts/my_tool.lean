import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Batteries.Data.String.Basic
import Cli

open Lean Elab IO Meta
open Cli System

#check Elab.TacticInfo

namespace Lean.Elab.TacticInfo--创建了一个namespace

def verboseTrainingData (module : Name) (i : TacticInfo) (ctx : ContextInfo) : IO String := do
  let mut result := "===\n"
  result := result ++ s!"{module}\n---\n"
  let sourceUpToTactic := Substring.mk (← moduleSource module) 0 (i.stx.getPos?.getD 0)
  let chunks := sourceUpToTactic.splitOn "\n\n"
  let declUpToTactic := chunks.getLast!.toString
  let offset := chunks.dropLast.foldl (init := 0) (fun t c => t + (c.toString.count '\n') + 2)
  result := result ++ s!"{offset}\n---\n{declUpToTactic}\n---\n"
  result := result ++ (Format.joinSep (← i.goalState ctx) "\n").pretty ++ "\n---\n"
  let ⟨⟨startLine, startCol⟩, ⟨endLine, endCol⟩⟩ := i.range ctx
  result := result ++ s!"{startLine}:{startCol}-{endLine}:{endCol}\n---\n"
  result := result ++ (← i.pp ctx).pretty ++ "\n---\n"
  result := result ++ (Format.joinSep (← i.goalStateAfter ctx) "\n").pretty ++ "\n---\n"
  return result

def proofStepData (i : TacticInfo) (ctx : ContextInfo) : IO String := do
  return "[GOAL]\n" ++ (Format.joinSep (← i.goalState ctx) "\n").pretty ++ "\n[PROOFSTEP]\n" ++ (← i.pp ctx).pretty

end Lean.Elab.TacticInfo

-- def extractTheorem (i : TacticInfo) (ctx : ContextInfo) : MetaM Unit:= do
--   -- 1. 提取原始战术语法
--   let originalSyntax := i.stx

--   -- 2. 在原始上下文中重新运行战术
--   let _ ← Lean.Elab.Tactic.run ctx i.mctxBefore do
--     Lean.Elab.Tactic.evalTactic originalSyntax

--   -- 3. 可选：打印调试信息
--   dbg_trace f!"成功重新运行战术: {originalSyntax}"
--   return


def trainingData (args : Cli.Parsed) : IO UInt32 := do
    initSearchPath (← findSysroot)
    let module := args.positionalArg! "module" |>.as! ModuleName
    let mut trees ← moduleInfoTrees module
    trees := trees.flatMap InfoTree.retainTacticInfo
    trees := trees.flatMap InfoTree.retainOriginal
    trees := trees.flatMap InfoTree.retainSubstantive
    for t in trees do
      IO.println ("\u001b[32;1m=== TREE BEGIN ===\u001b[0m")
      for (i, ctx) in t.tactics do
        IO.println (← i.pp ctx)
        IO.println ("--------------")
        -- if args.hasFlag "proofstep" then
        --   IO.println (← i.proofStepData ctx)
        -- else
        --   IO.println (← i.verboseTrainingData module ctx)
        -- ctx.runMetaM {} (
        --   Meta.withMCtx i.mctxBefore (
        --     extractTheorem i ctx
        --   )
        -- )
    return 0

/-- Setting up command line options and help text for `lake exe training_data`. -/
def my_tool : Cmd := `[Cli|
  --指定了命令的名称 training_data，并且通过 VIA 将命令与 trainingData 这个函数进行关联。
  --["0.0.1"]：这是命令的版本号。
  my_tool VIA trainingData; ["0.0.1"]
"Export training data consisting of goal states and tactic invocations from the given file.

The output consists of blocks of the form:
```
===
Mathlib.Logic.Hydra
---
61
---
theorem cutExpand_le_invImage_lex [DecidableEq α] [IsIrrefl α r] :
    CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ (· ≠ ·)) (· < ·)) toFinsupp := by

---
α : Type u_1
r : α → α → Prop
inst✝¹ : DecidableEq α
inst✝ : IsIrrefl α r
⊢ CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ fun x x_1 => x ≠ x_1) fun x x_1 => x < x_1) ↑toFinsupp
---
64:2-64:27
---
rintro s t ⟨u, a, hr, he⟩
---
case intro.intro.intro
α : Type u_1
r : α → α → Prop
inst✝¹ : DecidableEq α
inst✝ : IsIrrefl α r
s t u : Multiset α
a : α
hr : ∀ (a' : α), a' ∈ u → r a' a
he : s + {a} = t + u
⊢ InvImage (Finsupp.Lex (rᶜ ⊓ fun x x_1 => x ≠ x_1) fun x x_1 => x < x_1) (↑toFinsupp) s t
---
```
Here:
* `Mathlib.Logic.Hydra` is the name of the module where this goal occurs.
* `61` is the number of lines before the declaration (i.e. the `theorem` statement is on line `62`.)
* `theorem ...` is the *partial* declaration, including a fragment of the tactic proof.
* Next is the goal state at that point.
  (Typically just one goal, as we don't report the goal states before structuring commands.)
  Note that there is no guarantee that truncating the file at this point will actually cause Lean
  to display this goal: the presence of earlier structuring commands could result in Lean showing
  an error message instead.
* `64:2-64:27` is the range of positions occupied by the tactic invocation in the original file.
  This allows us to look up this goal in a live Lean session, so we can try out alternative tactics.
* `rintro s t ⟨u, a, hr, he⟩` is the tactic used in the library.
* After that is the goal state after running the tactic.
  (Often multiple goals.)"

  FLAGS:
    "proofstep";       "Use the proofstep format: [GOAL]tactic-state[PROOFSTEP]next-tactic"

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."
]

/-- `lake exe training_data` -/
def main (args : List String) : IO UInt32 :=
  my_tool.validate args

-- See `scripts/training_data.sh` for a script to run this on all of Mathlib.
