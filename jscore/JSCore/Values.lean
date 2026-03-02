/-
  JSCore₀ Values — Val, Env, Store, and lookup functions.
-/
import JSCore.Syntax

namespace JSCore

inductive Val where
  | str  : String → Val
  | num  : Int → Val
  | bool : Bool → Val
  | none : Val
  | obj  : List (String × Val) → Val
  | arr  : List Val → Val
  deriving Repr, BEq

-- Manual DecidableEq since deriving may fail on nested List
mutual
  def Val.decEq : (a b : Val) → Decidable (a = b)
    | .str s1, .str s2 =>
      if h : s1 = s2 then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
    | .num n1, .num n2 =>
      if h : n1 = n2 then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
    | .bool b1, .bool b2 =>
      if h : b1 = b2 then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
    | .none, .none => isTrue rfl
    | .obj fs1, .obj fs2 =>
      match Val.decEqFields fs1 fs2 with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .arr es1, .arr es2 =>
      match Val.decEqList es1 es2 with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .str _, .num _ => isFalse (by intro h; cases h)
    | .str _, .bool _ => isFalse (by intro h; cases h)
    | .str _, .none => isFalse (by intro h; cases h)
    | .str _, .obj _ => isFalse (by intro h; cases h)
    | .str _, .arr _ => isFalse (by intro h; cases h)
    | .num _, .str _ => isFalse (by intro h; cases h)
    | .num _, .bool _ => isFalse (by intro h; cases h)
    | .num _, .none => isFalse (by intro h; cases h)
    | .num _, .obj _ => isFalse (by intro h; cases h)
    | .num _, .arr _ => isFalse (by intro h; cases h)
    | .bool _, .str _ => isFalse (by intro h; cases h)
    | .bool _, .num _ => isFalse (by intro h; cases h)
    | .bool _, .none => isFalse (by intro h; cases h)
    | .bool _, .obj _ => isFalse (by intro h; cases h)
    | .bool _, .arr _ => isFalse (by intro h; cases h)
    | .none, .str _ => isFalse (by intro h; cases h)
    | .none, .num _ => isFalse (by intro h; cases h)
    | .none, .bool _ => isFalse (by intro h; cases h)
    | .none, .obj _ => isFalse (by intro h; cases h)
    | .none, .arr _ => isFalse (by intro h; cases h)
    | .obj _, .str _ => isFalse (by intro h; cases h)
    | .obj _, .num _ => isFalse (by intro h; cases h)
    | .obj _, .bool _ => isFalse (by intro h; cases h)
    | .obj _, .none => isFalse (by intro h; cases h)
    | .obj _, .arr _ => isFalse (by intro h; cases h)
    | .arr _, .str _ => isFalse (by intro h; cases h)
    | .arr _, .num _ => isFalse (by intro h; cases h)
    | .arr _, .bool _ => isFalse (by intro h; cases h)
    | .arr _, .none => isFalse (by intro h; cases h)
    | .arr _, .obj _ => isFalse (by intro h; cases h)

  def Val.decEqList : (a b : List Val) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _::_ => isFalse (by intro h; cases h)
    | _::_, [] => isFalse (by intro h; cases h)
    | a::as_, b::bs =>
      match Val.decEq a b, Val.decEqList as_ bs with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

  def Val.decEqFields : (a b : List (String × Val)) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _::_ => isFalse (by intro h; cases h)
    | _::_, [] => isFalse (by intro h; cases h)
    | (k1, v1)::as_, (k2, v2)::bs =>
      if hk : k1 = k2 then
        match Val.decEq v1 v2, Val.decEqFields as_ bs with
        | isTrue hv, isTrue ht => isTrue (by rw [hk, hv, ht])
        | isFalse hv, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, isFalse ht => isFalse (by intro h; cases h; exact ht rfl)
      else
        isFalse (by intro h; cases h; exact hk rfl)
end

instance : DecidableEq Val := Val.decEq

-- Env and Store as function types for proof tractability
abbrev Env := String → Option Val
abbrev Store := String → Option Val

def emptyEnv : Env := fun _ => .none
def emptyStore : Store := fun _ => .none

def Env.set (env : Env) (x : String) (v : Val) : Env :=
  fun y => if y = x then some v else env y

def Store.set (store : Store) (x : String) (v : Val) : Store :=
  fun y => if y = x then some v else store y

def lookup (env : Env) (store : Store) (x : String) : Option Val :=
  store x <|> env x

def fieldLookup (fields : List (String × Val)) (key : String) : Option Val :=
  match fields.find? (fun p => p.1 == key) with
  | some (_, v) => some v
  | none => .none

-- Set a field in a field list (or add it)
def fieldSet (fields : List (String × Val)) (key : String) (v : Val) : List (String × Val) :=
  if fields.any (fun p => p.1 == key) then
    fields.map (fun p => if p.1 == key then (key, v) else p)
  else
    fields ++ [(key, v)]

end JSCore
