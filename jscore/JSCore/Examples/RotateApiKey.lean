import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

namespace JSCore

def rotateApiKey_body : Expr :=
  (.call "dbApiKeyFindUnique"
    [("where", (.obj [
  ("id", (.var "keyId")),
  ("workspaceId", (.field
  (.var "auth")
  "workspaceId"))
]))]
    "existing"
    (.letConst "apiKey"
      (.field
        (.var "existing")
        "key")
      (.call "generateKey"
        []
        "newKey"
        (.call "dbApiKeyUpdate"
          [("where", (.obj [
  ("id", (.var "keyId"))
])), ("data", (.obj [
  ("key", (.var "newKey"))
]))]
          "__void_0"
          (.call "loggerInfo"
            [("arg0", (.strLit "API key rotated successfully"))]
            "__void_1"
            Expr.none)))))

theorem rotateApiKey_no_secret_leak
    (fuel : Nat)
    (auth : Val)
    (keyId : Val)
    (env : Env)
    (store : Store)
    (h_req_0 : ∃ n, auth = some (Val.num n) ∧ n > 0)
    : notTaintedIn rotateApiKey_body "apiKey" "logger.*" = true := by
  sorry

end JSCore