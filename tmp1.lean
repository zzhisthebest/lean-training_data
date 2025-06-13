import Mathlib
import Lean.Elab.Tactic

open Lean Elab Tactic Meta

elab "to_theorem" t:tactic : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let levels ← Term.getLevelNames
  let type ← goal.getType
  let goal' := (← goal.withContext <| mkFreshExprSyntheticOpaqueMVar type).mvarId!
  let goals ← getGoals
  setGoals [goal']
  evalTactic t
  setGoals goals
  let some proof ← getExprMVarAssignment? goal' |
    throwError "tactic made no progress"
  let (_, state) ← (collectMVars proof).run {}
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  let mvars := state.result
  let type' := type.abstract (mvars.map mkMVar)
  let proof' := proof.abstract (mvars.map mkMVar)
  let (type'', proof'') ← mvars.foldrM (fun mvar (type, proof) =>
    return (
      Expr.forallE (← mvar.getTag) (← mvar.getType) type .default,
      Expr.lam (← mvar.getTag) (← mvar.getType) proof .default
    )
  ) (type', proof')
  let (type''', proof''') ← goal'.withContext do
    let fvars := (← getLCtx).decls.toArray.filterMap
      (fun d => d.bind fun x => if x.isImplementationDetail then none else some <| Expr.fvar x.fvarId)
    (← getLCtx).decls.foldrM (fun decl (type, proof) => do
      match decl with
      | none => return (type, proof)
      | some decl =>
        if decl.isLet then
          return (
            Expr.letE decl.userName decl.type decl.value type false,
            Expr.letE decl.userName decl.type decl.value proof false
          )
        else if !decl.isImplementationDetail then
          return (
            Expr.forallE decl.userName decl.type type decl.binderInfo,
            Expr.lam decl.userName decl.type proof decl.binderInfo
          )
        else
          return (type, proof)
    ) (type''.abstract fvars, proof''.abstract fvars)
  let some declName ← Term.getDeclName? | throwError "not in declaration"
  let thmVal : TheoremVal := {
    name := ← mkAuxName (.str declName "extracted") 1
    levelParams := levels
    type := type'''
    value := proof'''
  }
  let decl : Declaration := .thmDecl thmVal
  try
    Lean.addDecl decl
    let newProof := Expr.const thmVal.name (levels.map Level.param)
    Lean.logInfo m!"theorem generated under {newProof}"
    let newProof' ← goal.withContext do
      let fvars := (← getLCtx).decls.toArray.filterMap
        (fun d => d.bind fun x => if x.isImplementationDetail || x.isLet then none else some <| Expr.fvar x.fvarId)
      return mkAppN newProof fvars
    let newProof' := mvars.foldl (fun proof mvar => mkApp proof (.mvar mvar)) newProof'
    goal.assign newProof'
    replaceMainGoal mvars.toList
  catch e =>
    throwTacticEx `to_theorem goal m!"failed to generate theorem: {e.toMessageData}"

theorem tmp_1 {a b:ℝ} : (a+b)^2=a^2+2*a*b+b^2:=by
  to_theorem repeat rw [pow_two]
  to_theorem rw [add_mul]
  to_theorem repeat rw [mul_add]
  to_theorem rw [←add_assoc]
  to_theorem nth_rw 3 [mul_comm]
  to_theorem ring

/--
info: theorem tmp_1 : ∀ {a b : ℝ}, (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
fun {a b} =>
  tmp_1.extracted_1 (tmp_1.extracted_2 (tmp_1.extracted_3 (tmp_1.extracted_4 (tmp_1.extracted_5 tmp_1.extracted_6))))
-/
#guard_msgs in
#print tmp_1
