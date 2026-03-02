/-
  JSCore₀ Evaluator — eval with global fuel parameter.
  Structural recursion on `fuel`.
  List processing uses List.foldl (opaque to recursion checker).
  ForOf also uses List.foldl inline.
  WhileLoop uses a separate Nat recursion via evalWhile.
-/
import JSCore.Trace

namespace JSCore

def mkResult (o : Outcome) (s : Store) (t : List TraceEntry) : Result :=
  { outcome := o, store := s, trace := t }

def evalBinOp (op : BinOp) (v1 v2 : Val) : Outcome :=
  match op, v1, v2 with
  | .eq, a, b => .ok (.bool (a == b))
  | .neq, a, b => .ok (.bool (a != b))
  | .lt, .num a, .num b => .ok (.bool (a < b))
  | .le, .num a, .num b => .ok (.bool (a ≤ b))
  | .gt, .num a, .num b => .ok (.bool (a > b))
  | .ge, .num a, .num b => .ok (.bool (a ≥ b))
  | .add, .num a, .num b => .ok (.num (a + b))
  | .sub, .num a, .num b => .ok (.num (a - b))
  | .mul, .num a, .num b => .ok (.num (a * b))
  | .div, .num _, .num 0 => .error (.str "division by zero")
  | .div, .num a, .num b => .ok (.num (a / b))
  | .mod, .num _, .num 0 => .error (.str "modulo by zero")
  | .mod, .num a, .num b => .ok (.num (a % b))
  | .strConcat, .str a, .str b => .ok (.str (a ++ b))
  | _, _, _ => .error (.str "type error in binop")

def evalUnOp (op : UnOp) (v : Val) : Outcome :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | .neg, .num n => .ok (.num (-n))
  | _, _ => .error (.str "type error in unop")

-- WhileLoop as a separate function with Nat recursion on loopFuel.
-- Takes evalBody and evalCond as function arguments (will be partially applied).
def evalWhileAux (loopFuel : Nat) (evalCond evalBody : Store → Result)
    (store : Store) (accTrace : List TraceEntry) : Result :=
  match loopFuel with
  | 0 => mkResult (.error (.str "fuel exhausted")) store accTrace
  | loopFuel' + 1 =>
    let rc := evalCond store
    match rc.outcome with
    | .ok (.bool true) =>
      let rb := evalBody rc.store
      match rb.outcome with
      | .ok _ => evalWhileAux loopFuel' evalCond evalBody rb.store
          (accTrace ++ rc.trace ++ rb.trace)
      | .brk => mkResult (.ok .none) rb.store (accTrace ++ rc.trace ++ rb.trace)
      | .returned v => mkResult (.returned v) rb.store (accTrace ++ rc.trace ++ rb.trace)
      | _ => mkResult rb.outcome rb.store (accTrace ++ rc.trace ++ rb.trace)
    | .ok (.bool false) => mkResult (.ok .none) rc.store (accTrace ++ rc.trace)
    | .ok _ => mkResult (.error (.str "while condition not boolean")) rc.store (accTrace ++ rc.trace)
    | _ => mkResult rc.outcome rc.store (accTrace ++ rc.trace)

-- Main evaluator with global fuel
def eval (fuel : Nat) (env : Env) (store : Store) (e : Expr) : Result :=
  match fuel with
  | 0 => mkResult (.error (.str "fuel exhausted")) store []
  | fuel' + 1 =>
    match e with
    | .var x =>
      match lookup env store x with
      | some v => mkResult (.ok v) store []
      | Option.none => mkResult (.error (.str s!"undefined variable: {x}")) store []

    | .strLit s => mkResult (.ok (.str s)) store []
    | .numLit n => mkResult (.ok (.num n)) store []
    | .boolLit b => mkResult (.ok (.bool b)) store []
    | .none => mkResult (.ok .none) store []

    | .letConst x e body =>
      let r1 := eval fuel' env store e
      match r1.outcome with
      | .ok v =>
        let r2 := eval fuel' (env.set x v) r1.store body
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .letMut x e body =>
      let r1 := eval fuel' env store e
      match r1.outcome with
      | .ok v =>
        let r2 := eval fuel' env (r1.store.set x v) body
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .assign x e body =>
      let r1 := eval fuel' env store e
      match r1.outcome with
      | .ok v =>
        let r2 := eval fuel' env (r1.store.set x v) body
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .field e fname =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok (.obj fields) =>
        match fieldLookup fields fname with
        | some v => mkResult (.ok v) r.store r.trace
        | Option.none => mkResult (.ok .none) r.store r.trace
      | .ok _ => mkResult (.ok .none) r.store r.trace
      | _ => r

    | .obj pairs =>
      let result := pairs.foldl (fun (acc : List (String × Val) × Store × List TraceEntry)
          (pair : String × Expr) =>
        let (vals, curStore, curTrace) := acc
        let r := eval fuel' env curStore pair.2
        match r.outcome with
        | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
        | _ => (vals, r.store, curTrace ++ r.trace)
      ) ([], store, [])
      mkResult (.ok (.obj result.1)) result.2.1 result.2.2

    | .spread base overrides =>
      let rb := eval fuel' env store base
      match rb.outcome with
      | .ok (.obj baseFields) =>
        let result := overrides.foldl (fun (acc : List (String × Val) × Store × List TraceEntry)
            (pair : String × Expr) =>
          let (vals, curStore, curTrace) := acc
          let r := eval fuel' env curStore pair.2
          match r.outcome with
          | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
          | _ => (vals, r.store, curTrace ++ r.trace)
        ) ([], rb.store, [])
        let merged := result.1.foldl (fun acc (k, v) => fieldSet acc k v) baseFields
        mkResult (.ok (.obj merged)) result.2.1 (rb.trace ++ result.2.2)
      | .ok _ => mkResult (.error (.str "spread on non-object")) rb.store rb.trace
      | _ => rb

    | .arr exprs =>
      let result := exprs.foldl (fun (acc : List Val × Store × List TraceEntry) (expr : Expr) =>
        let (vals, curStore, curTrace) := acc
        let r := eval fuel' env curStore expr
        match r.outcome with
        | .ok v => (vals ++ [v], r.store, curTrace ++ r.trace)
        | _ => (vals, r.store, curTrace ++ r.trace)
      ) ([], store, [])
      mkResult (.ok (.arr result.1)) result.2.1 result.2.2

    | .index e idx =>
      let re := eval fuel' env store e
      match re.outcome with
      | .ok (.arr elems) =>
        let ri := eval fuel' env re.store idx
        match ri.outcome with
        | .ok (.num i) =>
          let idx' := if i ≥ 0 then i.toNat else 0
          match elems.get? idx' with
          | some v => mkResult (.ok v) ri.store (re.trace ++ ri.trace)
          | Option.none => mkResult (.ok .none) ri.store (re.trace ++ ri.trace)
        | .ok _ => mkResult (.error (.str "index not a number")) ri.store (re.trace ++ ri.trace)
        | _ => mkResult ri.outcome ri.store (re.trace ++ ri.trace)
      | .ok _ => mkResult (.error (.str "index on non-array")) re.store re.trace
      | _ => re

    | .push arrName valExpr =>
      let rv := eval fuel' env store valExpr
      match rv.outcome with
      | .ok v =>
        match lookup env rv.store arrName with
        | some (.arr elems) =>
          let newArr := Val.arr (elems ++ [v])
          mkResult (.ok newArr) (rv.store.set arrName newArr) rv.trace
        | _ => mkResult (.error (.str s!"push on non-array: {arrName}")) rv.store rv.trace
      | _ => rv

    | .seq e1 e2 =>
      let r1 := eval fuel' env store e1
      match r1.outcome with
      | .ok _ =>
        let r2 := eval fuel' env r1.store e2
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .ite cond thn els =>
      let rc := eval fuel' env store cond
      match rc.outcome with
      | .ok (.bool true) =>
        let r := eval fuel' env rc.store thn
        mkResult r.outcome r.store (rc.trace ++ r.trace)
      | .ok (.bool false) =>
        let r := eval fuel' env rc.store els
        mkResult r.outcome r.store (rc.trace ++ r.trace)
      | .ok _ => mkResult (.error (.str "if condition not boolean")) rc.store rc.trace
      | _ => rc

    | .forOf x arrExpr body =>
      let ra := eval fuel' env store arrExpr
      match ra.outcome with
      | .ok (.arr elems) =>
        elems.foldl (fun (acc : Result) elem =>
          match acc.outcome with
          | .ok _ =>
            let r := eval fuel' (env.set x elem) acc.store body
            match r.outcome with
            | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
            | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
            | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
          | _ => acc
        ) (mkResult (.ok .none) ra.store ra.trace)
      | .ok _ => mkResult (.error (.str "forOf on non-array")) ra.store ra.trace
      | _ => ra

    | .whileLoop loopFuel cond body =>
      evalWhileAux loopFuel
        (fun st => eval fuel' env st cond)
        (fun st => eval fuel' env st body)
        store []

    | .«break» => mkResult .brk store []

    | .ret e =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok v => mkResult (.returned v) r.store r.trace
      | _ => r

    | .call target argExprs resultBinder body =>
      let argResult := argExprs.foldl (fun (acc : List (String × Val) × Store × List TraceEntry)
          (pair : String × Expr) =>
        let (vals, curStore, curTrace) := acc
        let r := eval fuel' env curStore pair.2
        match r.outcome with
        | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
        | _ => (vals, r.store, curTrace ++ r.trace)
      ) ([], store, [])
      let (argVals, argStore, argTrace) := argResult
      let cr : CallRecord := { target := target, args := argVals, resultId := resultBinder }
      let callTrace := argTrace ++ [.call cr]
      -- Result value is universally quantified in proofs.
      -- For evaluation, we use Val.none as the default result.
      let resultVal := Val.none
      let r := eval fuel' (env.set resultBinder resultVal) argStore body
      mkResult r.outcome r.store (callTrace ++ r.trace)

    | .throw e =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok v => mkResult (.error v) r.store r.trace
      | _ => r

    | .tryCatch body errName handler =>
      let rb := eval fuel' env store body
      match rb.outcome with
      | .error v =>
        let rh := eval fuel' (env.set errName v) rb.store handler
        mkResult rh.outcome rh.store (rb.trace ++ rh.trace)
      | _ => rb

    | .binOp op e1 e2 =>
      let r1 := eval fuel' env store e1
      match r1.outcome with
      | .ok v1 =>
        let r2 := eval fuel' env r1.store e2
        match r2.outcome with
        | .ok v2 => mkResult (evalBinOp op v1 v2) r2.store (r1.trace ++ r2.trace)
        | _ => r2
      | _ => r1

    | .unOp op e =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok v => mkResult (evalUnOp op v) r.store r.trace
      | _ => r

-- Top-level wrapper for forOf used in theorems (explicit recursion on elems)
def evalForOf (fuel : Nat) (env : Env) (store : Store) (x : String)
    (elems : List Val) (body : Expr) (pfx : List TraceEntry) : Result :=
  match elems with
  | [] => mkResult (.ok .none) store pfx
  | hd :: tl =>
    let r := eval fuel (env.set x hd) store body
    match r.outcome with
    | .ok _ => evalForOf fuel env r.store x tl body (pfx ++ r.trace)
    | .brk => mkResult (.ok .none) r.store (pfx ++ r.trace)
    | .returned v => mkResult (.returned v) r.store (pfx ++ r.trace)
    | .error e => mkResult (.error e) r.store (pfx ++ r.trace)

end JSCore
