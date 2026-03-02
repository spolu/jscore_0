/-
  JSCore₀ String Predicates — startsWith, mem, contains as decidable functions.
-/
import JSCore.Values

namespace JSCore

-- Does a string value start with a prefix string value?
def Val.startsWith' (v1 v2 : Val) : Bool :=
  match v1, v2 with
  | .str a, .str b => b.isPrefixOf a
  | _, _ => false

-- Is a Val a member of a list of Vals?
def Val.mem' (v : Val) (vs : List Val) : Bool :=
  vs.any (· == v)

-- Does a Val.obj contain a specific field key?
def Val.contains' (v : Val) (key : String) : Bool :=
  match v with
  | .obj fields => (fields.find? (fun p => p.1 == key)).isSome
  | _ => false

end JSCore
