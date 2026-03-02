import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Tactics

namespace JSCore

def reorderTasks_body : Expr :=
  (.seq
    (.forOf "taskId"
      (.var "tasks")
      (.call "dbTaskUpdate"
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
    (h_req_0 : ∃ n, auth = some (Val.num n) ∧ n > 0)
    : ∀ c ∈ callsTo (eval fuel env store reorderTasks_body).trace "db.*",
      argAtPath c "where.projectId" = some projectId := by
  sorry

end JSCore