import Mathlib
open Lean Meta Elab Tactic Term

--n就是假设名，t就是假设的内容。tactic就是返回类型。
def fun1 (i : TacticInfo) : TacticM Unit:= do
  let goalsBefore:=i.goalsBefore
  let goalsAfter:=i.goalsAfter
  for goal1 in goalsBefore do
    for goal2 in goalsAfter do
      let goal2_type ← goal2.getType
      let p ← mkFreshExprMVar goal2_type MetavarKind.syntheticOpaque `h_100
      goal1.withContext do
        let (_, goal1New) ← MVarId.intro1P $ ← goal1.assert `h_100 goal2_type p
        replaceMainGoal [goal1New]
