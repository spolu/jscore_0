import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def rotateApiKey_body : Expr :=
  (.call "db.apiKey.findUnique"
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
        (.call "db.apiKey.update"
          [("where", (.obj [
  ("id", (.var "keyId"))
])), ("data", (.obj [
  ("key", (.var "newKey"))
]))]
          "__void_0"
          (.call "logger.info"
            [("arg0", (.strLit "API key rotated successfully"))]
            "__void_1"
            Expr.none)))))

theorem rotateApiKey_no_secret_leak
    : notTaintedIn rotateApiKey_body "apiKey" "logger.*" = true := by
  native_decide
