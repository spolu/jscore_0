import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Tactics

set_option linter.sorryIn false

namespace JSCore

def exportWorkspaceData_body : Expr :=
  (.call "dbProjectsFindMany"
    [("where", (.obj [
  ("workspaceId", (.field
  (.var "auth")
  "workspaceId"))
]))]
    "projects"
    (.call "dbTasksFindMany"
      [("where", (.obj [
  ("workspaceId", (.field
  (.var "auth")
  "workspaceId"))
]))]
      "tasks"
      (.ret
        (.obj [
          ("projects", (.var "projects")),
          ("tasks", (.var "tasks"))
        ]))))

theorem exportWorkspaceData_ws_isolation
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (env : Env)
    (store : Store)
    (h_req_0 : ∃ n, auth = some (Val.num n) ∧ n > 0)
    : ∀ c ∈ callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*",
      argAtPath c "where.workspaceId" = some auth := by
  sorry

theorem exportWorkspaceData_read_only
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (env : Env)
    (store : Store)
    (h_req_0 : ∃ n, auth = some (Val.num n) ∧ n > 0)
    : callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*.update" = [] := by
  sorry

theorem exportWorkspaceData_read_only_1
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (env : Env)
    (store : Store)
    (h_req_0 : ∃ n, auth = some (Val.num n) ∧ n > 0)
    : callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*.create" = [] := by
  sorry

theorem exportWorkspaceData_read_only_2
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (env : Env)
    (store : Store)
    (h_req_0 : ∃ n, auth = some (Val.num n) ∧ n > 0)
    : callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*.delete" = [] := by
  sorry

end JSCore