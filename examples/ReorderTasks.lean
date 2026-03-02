import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def reorderTasks_body : Expr :=
  (.seq
    (.forOf "taskId"
      (.var "tasks")
      (.call "db.task.update"
        [("where", (.obj [
  ("id", (.var "taskId")),
  ("projectId", (.var "projectId"))
])), ("data", (.obj [
  ("position", (.numLit 0))
]))]
        "__void_0"
        Expr.none))
    Expr.none)

theorem reorderTasks_ws_isolation
    (fuel : Nat)
    (auth : Val)
    (projectId : Val)
    (tasks : Val)
    (env : Env)
    (store : Store)
    (h_env_auth : env "auth" = some auth)
    (h_env_projectId : env "projectId" = some projectId)
    (h_env_tasks : env "tasks" = some tasks)
    : ∀ c ∈ callsTo (eval fuel env store reorderTasks_body).trace "db.*",
      argAtPath c "where.projectId" = some projectId := by
  sorry
