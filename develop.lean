import Mathlib
import Lean
open Lean Elab IO Meta Tactic


elab "faq_main_goal" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    dbg_trace f!"goal: {goal.name}"


elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]


elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

elab "add_goal_to_hyps " : tactic => do--有用
  let mvarId ← getMainGoal
  let t ← mvarId.getType
  let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque `h_1
  mvarId.withContext do
    let (_, mvarIdNew) ← MVarId.intro1P $ ← mvarId.assert `h_1 t p
    --replaceMainGoal [mvarIdNew]

elab "delete_h1": tactic => do
  evalTactic (← `(tactic| clear $(mkIdent `h1)))

elab "tactic1" : tactic => do
  let rawVal : Expr := mkRawNatLit 1
  let type : Expr := mkConst ``Int
  let instType : Expr := mkApp2 (.const ``OfNat [0]) type rawVal
  let inst : Expr ← synthInstance instType
  let one : Expr := mkApp3 (.const ``OfNat.ofNat [0]) type rawVal inst
  let oneEqOne : Expr := mkApp3 (.const ``Eq [1]) type one one
  withMainContext do
    let newGoal ← mkFreshExprSyntheticOpaqueMVar oneEqOne
    setGoals ((← getGoals).concat newGoal.mvarId!)

elab "add_goal" type:term : tactic => do
  let typeExpr ← elabTerm type none
  withMainContext do
    let newGoal ← mkFreshExprSyntheticOpaqueMVar typeExpr
    setGoals ((← getGoals).concat newGoal.mvarId!)

#check MVarId.assertHypotheses

elab "to_theorem" tac:tactic :tactic => do
  let goal ← getMainGoal
  --let levels ← Term.getLevelNames
  let type ← goal.getType
  let goal' := (← goal.withContext <| mkFreshExprSyntheticOpaqueMVar type).mvarId!
  --let goals ← getGoals
  -- let _ ← popMainGoal
  -- pushGoal goal'
  evalTactic tac
  let goals ← getUnsolvedGoals
  --logInfo m!"goals: {goals}"
  let newGoals ← goals.mapM fun goal2 => do
    --不直接用goal，这样每个goal'的mvarId不同，而非都使用具有相同mvarId的goal。
    --这就像避免多个指针指向同一个变量
    let goal' := (← goal'.withContext <| mkFreshExprSyntheticOpaqueMVar type).mvarId!
    let t ← goal'.getType
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque `h_original_goal
    let (_, goal') ← MVarId.intro1P $ ← goal'.assert `h_original_goal t p

    goal2.withContext do
      let goal2_lctx ← getLCtx
      goal'.withContext do
        let goal'_lctx ← getLCtx
        let mut newGoalsList : List MVarId := []
        for ldecl in goal2_lctx do
          if !ldecl.isImplementationDetail then
            --logInfo m!"ldecl: {ldecl.userName}"
            let found := goal'_lctx.decls.any fun decl =>
              match decl with
              | none => false
              | some d =>
                d.userName == ldecl.userName &&
                (d.type != ldecl.type ||
                 (if d.isLet then d.value? != ldecl.value? else false))
            if found then
              -- 如果存在无这个userName的假设或有这个userName但内容不同的假设，创建新目标
              --logInfo m! "zzh"
              let newGoal ← mkFreshExprSyntheticOpaqueMVar ldecl.type
              newGoalsList := newGoalsList.concat newGoal.mvarId!
        goal'.setType (←goal2.getType)
        logInfo m! "{goal'}"
        newGoalsList := newGoalsList.concat goal'
        return newGoalsList
  setGoals (List.flatten newGoals)

  let newGoals ← getUnsolvedGoals
  for _ in List.range (newGoals.length) do
    evalTactic (← `(tactic| extract_goal))
    let _ ← popMainGoal
  setGoals goals
  -- let goals ← getUnsolvedGoals
  -- logInfo m!"goals: {goals}"
  -- evalTactic (← `(tactic| clear *-))
  -- -- 接下来是先把maingoal改得和goal1的hypotheses一模一样
  -- ctx.forM (fun (decl : Lean.LocalDecl) => do
  --   let declExpr := decl.toExpr -- Find the expression of the declaration.
  --   let declType := decl.type -- Find the type of the declaration.
  --   let declName := decl.userName -- Find the name of the declaration.
  --   logInfo m!" local decl: name: {declName} | expr: {declExpr} | type: {declType}"
  -- )


-- elab "to_theorem"  a:tactic :tactic => do
  -- let goal1 ← getMainGoal
  -- let t ← goal1.getType
  -- let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque `h100
  -- evalTactic a
  -- --let extractedInfos ← withoutModifyingState do
  -- let goals ← getUnsolvedGoals
  -- let newGoals ← goals.mapM fun goal2 => do
  --   goal2.withContext do
  --     let (_, goal3) ← MVarId.intro1P $ ← goal2.assert `h100 t p
  --     return goal3
  -- pushGoals newGoals
  -- let goals ← getUnsolvedGoals
  -- for _ in List.range (goals.length) do
  --   evalTactic (← `(tactic| extract_goal))
  --   let _ ← popMainGoal

  -- pushGoals newGoals
  -- let goals ← getUnsolvedGoals
  -- let newGoals2 ← goals.mapM fun goal => do
  --   goal.withContext do
  --     let some ldecl := (← getLCtx).findFromUserName? `h100 |
  --       throwTacticEx `delete_h1 (← getMainGoal) m!"h100 doesn't exist"
  --     let goal' ← (← getMainGoal).clear ldecl.fvarId
  --     return goal'
  -- pushGoals newGoals2




theorem tmp_1 {a b:ℝ} :(a+b)^2=a^2+2*a*b+b^2:=by
  to_theorem repeat rw [pow_two]
  to_theorem rw [add_mul]
  to_theorem repeat rw [mul_add]
  to_theorem rw [←add_assoc]
  to_theorem nth_rw 3 [mul_comm]
  to_theorem ring



theorem tmp_2 {p q:Bool}(h1:p=true)(h2:q=true):p∧q:=by
  to_theorem constructor
  --to_theorem swap
  to_theorem rw [h1]
  to_theorem rw [h2]

theorem tmp_3 {a b c d:ℝ}(h1:a+c+d+1=b+d+c+1): a=b:=by
  to_theorem simp at h1
  to_theorem rw [add_assoc] at h1--正确提取出的定理应该是：theorem extracted_1
  --{a b c d : ℝ} (h1 : a+c+d=b+d+c) : a + (c + d) = b + d + c := sorry
  --extract_goal
  rw [add_assoc] at h1
  rw [add_comm c] at h1
  simp at h1
  trivial

example : True := by

  exfalso




  --extract_goal
  --exact h2
