import Lean
open Lean Elab System

def createFileLogger (filePath : String) : IO (Log.Handler) := do
  let handle ← IO.FS.Handle.mk filePath IO.FS.Mode.write
  return {
    handle := handle
    process := fun msg => do
      let msgStr := toString msg.data
      let posStr := match msg.pos? with
        | some pos => s!"[{pos.line}:{pos.column}] "
        | none => ""
      let fullMsg := s!"{posStr}{msgStr}\n"
      handle.putStr fullMsg
    close := handle.flush *> handle.close
  }

def withFileLogger (filePath : String) (action : IO α) : IO α := do
  let fileLogger ← createFileLogger filePath
  let prevHandlers ← Log.getHandlers
  Log.setHandlers (prevHandlers.push fileLogger)
  try
    action
  finally
    Log.setHandlers prevHandlers
    fileLogger.close

def exampleUsage : IO Unit :=
  withFileLogger "output.log" do
    logInfo m!"This message will be written to output.log"
    logInfo m!"Another message"

-- 运行示例
#eval exampleUsage
