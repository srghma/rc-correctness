import Std.Data.TreeSet
import Mathlib.Data.Finset.Basic

open Std

@[expose] public section

namespace RcCorrectness

/-!
# Abstract Syntax Tree (AST) for Reference Counting Language

This module defines the core AST types for an intermediate language with explicit
reference counting primitives (`inc` and `dec`).

## Types Overview:
- `Var`, `Const`, `Cnstr`: Numerical identifiers for variables, functions, and constructors.
- `Expr`: Pure expressions (function applications, constructor allocations, projections).
- `FnBody`: Imperative control flow and memory management statements.
- `Rc`: Sum type uniting `Expr` and `FnBody`.
- `Fn`: Top-level function definition with parameters and a body.
- `Program`: Environment mapping function constants (`Const`) to function definitions (`Fn`).
-/

/--
Variable identifiers represented as natural numbers (`Nat`).
Representing variables as natural numbers simplifies register/variable allocation,
substitution, and allows total ordering (`LE`, `Ord`) for efficient set datastructures (`TreeSet`).
-/
def Var := Nat deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, LE, Ord
instance : OfNat Var n := ⟨n⟩

instance : DecidableRel (· ≤ · : Var → Var → Prop) := fun a b => Nat.decLe a b
instance : Trans (· ≤ · : Var → Var → Prop) (· ≤ ·) (· ≤ ·) where
  trans := Nat.le_trans
instance : Std.Antisymm (· ≤ · : Var → Var → Prop) where
  antisymm {_a _b} := Nat.le_antisymm
instance : Std.Total (· ≤ · : Var → Var → Prop) where
  total := Nat.le_total

/--
Top-level function / constant identifiers represented as natural numbers (`Nat`).
Used to index global function definitions in a `Program` environment.
-/
def Const := Nat deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq
instance : OfNat Const n := ⟨n⟩

/--
Data constructor tags represented as natural numbers (`Nat`).
Distinguishes variants of algebraic data types (e.g., tag 0 for `None`/`Nil`, tag 1 for `Some`/`Cons`).
-/
def Cnstr := Nat deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq
instance : OfNat Cnstr n := ⟨n⟩

/--
Pure expressions in the intermediate language:
- `const_app_full`: Full application of function constant `c` to arguments `ys`.
- `const_app_part`: Partial application (closure creation) of function `c` to arguments `ys`.
- `var_app`: Indirect application of variable `x` to argument `y`.
- `ctor`: Allocation of data structure with constructor tag `i` and fields `ys`.
- `proj`: Field projection extracting field `i` from variable `x`.
-/
inductive Expr : Type
| const_app_full (c : Const) (ys : List Var) : Expr
| const_app_part (c : Const) (ys : List Var) : Expr
| var_app (x : Var) (y : Var) : Expr
| ctor (i : Cnstr) (ys : List Var) : Expr
| proj (i : Cnstr) (x : Var) : Expr
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

/--
Function body statements:
- `ret`: Return variable `x`.
- `let_`: Bind result of expression `e` to variable `x` in continuation `F`.
- `case`: Multi-branch case split on variable `x` over alternative bodies `Fs`.
- `inc`: Increment reference count of variable `x` before executing `F`.
- `dec`: Decrement reference count of variable `x` before executing `F`.
-/
inductive FnBody : Type
| ret (x : Var) : FnBody
| let_ (x : Var) (e : Expr) (F : FnBody) : FnBody
| case (x : Var) (Fs : List FnBody) : FnBody
| inc (x : Var) (F : FnBody) : FnBody
| dec (x : Var) (F : FnBody) : FnBody
deriving Repr

mutual
  def FnBody.decEq (a b : FnBody) : Decidable (a = b) :=
    match a, b with
    | .ret x, .ret x' =>
      if h : x = x' then isTrue (h ▸ rfl) else isFalse (by intro h'; injection h'; contradiction)
    | .let_ x e F, .let_ x' e' F' =>
      if hx : x = x' then
        if he : e = e' then
          match FnBody.decEq F F' with
          | isTrue hf => isTrue (by simp [hx, he, hf])
          | isFalse hf => isFalse (by intro h'; injection h'; contradiction)
        else isFalse (by intro h'; injection h'; contradiction)
      else isFalse (by intro h'; injection h'; contradiction)
    | .case x Fs, .case x' Fs' =>
      if hx : x = x' then
        match decEqFs Fs Fs' with
        | isTrue hf => isTrue (by simp [hx, hf])
        | isFalse hf => isFalse (by intro h'; injection h'; contradiction)
      else isFalse (by intro h'; injection h'; contradiction)
    | .inc x F, .inc x' F' =>
      if hx : x = x' then
        match FnBody.decEq F F' with
        | isTrue hf => isTrue (by simp [hx, hf])
        | isFalse hf => isFalse (by intro h'; injection h'; contradiction)
      else isFalse (by intro h'; injection h'; contradiction)
    | .dec x F, .dec x' F' =>
      if hx : x = x' then
        match FnBody.decEq F F' with
        | isTrue hf => isTrue (by simp [hx, hf])
        | isFalse hf => isFalse (by intro h'; injection h'; contradiction)
      else isFalse (by intro h'; injection h'; contradiction)
    | .ret _, .let_ _ _ _ | .ret _, .case _ _ | .ret _, .inc _ _ | .ret _, .dec _ _
    | .let_ _ _ _, .ret _ | .let_ _ _ _, .case _ _ | .let_ _ _ _, .inc _ _ | .let_ _ _ _, .dec _ _
    | .case _ _, .ret _ | .case _ _, .let_ _ _ _ | .case _ _, .inc _ _ | .case _ _, .dec _ _
    | .inc _ _, .ret _ | .inc _ _, .let_ _ _ _ | .inc _ _, .case _ _ | .inc _ _, .dec _ _
    | .dec _ _, .ret _ | .dec _ _, .let_ _ _ _ | .dec _ _, .case _ _ | .dec _ _, .inc _ _ =>
      isFalse (by intro h; injection h)


  def decEqFs (as bs : List FnBody) : Decidable (as = bs) :=
    match as, bs with
    | [], [] => isTrue rfl
    | a::as, b::bs =>
      match FnBody.decEq a b with
      | isTrue h1 =>
        match decEqFs as bs with
        | isTrue h2 => isTrue (by simp [h1, h2])
        | isFalse h2 => isFalse (by simp [h2])
      | isFalse h1 => isFalse (by simp [h1])
    | [], _::_ | _::_, [] => isFalse (by intro h; injection h)
end

instance : DecidableEq FnBody := FnBody.decEq

instance : BEq FnBody where
  beq a b := decide (a = b)

instance : ReflBEq FnBody where
  rfl := decide_eq_true rfl

instance : LawfulBEq FnBody where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

-- expr notation
notation c "⟦" ys "…⟧" => Expr.const_app_full c ys
notation c "⟦" ys "…, " "_" "⟧" => Expr.const_app_part c ys
notation x "⟦" y "⟧" => Expr.var_app x y
notation "⟪" ys "⟫" i => Expr.ctor i ys
notation x "[ᵉ" i "]" => Expr.proj i x

-- fn_body notation
notation x " ≔ᶠᵇ " e ";ᶠᵇ " F => FnBody.let_ x e F
notation "caseᶠᵇ " x " ofᶠᵇ " Fs => FnBody.case x Fs
notation "incᶠᵇ " x ";ᶠᵇ " F => FnBody.inc x F
notation "decᶠᵇ " x ";ᶠᵇ " F => FnBody.dec x F

/--
`Rc` (Reference Counting entity) is a sum type of `Expr` and `FnBody`.
It provides a single unified type to represent any AST node (expression or statement)
for reference counting analysis, transformation, or correctness proofs.
-/
inductive Rc : Type
| expr (e : Expr) : Rc
| fn_body (F : FnBody) : Rc
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance : CoeOut Expr Rc where
  coe := Rc.expr

instance : CoeOut FnBody Rc where
  coe := Rc.fn_body

/--
Computes the set of free variables occurring inside a pure expression (`Expr`).
`fv_expr` collects variables referenced in argument lists, projection target variables, or application targets.
-/
def fv_of_expr : Expr → Finset Var
| (Expr.const_app_full _ xs) => xs.toFinset
| (Expr.const_app_part _ xs) => xs.toFinset
| (Expr.var_app x y) => {x, y}
| (Expr.ctor _ xs) => xs.toFinset
| (Expr.proj _ x) => {x}

/--
Computes the set of free variables occurring inside a statement (`FnBody`).
While `fv_expr` calculates free variables of pure expressions, `fv` handles statement control flow
and scoping rules: in `let_ x e F`, `x` is bound in `F`, so `x` is erased (`.erase x`) from `fv_of_fn_body F`.
-/
def fv_of_fn_body : FnBody → Finset Var
| (FnBody.ret x) => {x}
| (FnBody.let_ x e fn_body) => fv_of_expr e ∪ ((fv_of_fn_body fn_body).erase x)
| (FnBody.case x fn_bodies) => fn_bodies.foldl (fun acc f => acc ∪ fv_of_fn_body f) {x}
| (FnBody.inc x fn_body) => insert x (fv_of_fn_body fn_body)
| (FnBody.dec x fn_body) => insert x (fv_of_fn_body fn_body)

/--
A top-level function definition consisting of:
- `ys`: List of formal parameter variable IDs.
- `fn_body`: Function body statement execution root.
-/
structure Fn where
  ys : List Var
  fn_body : FnBody
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

/--
A `Program` represents a global program environment / symbol table mapping each function constant ID (`Const`)
to its function definition (`Fn`). Modeling `Program` as a function `Const → Fn` allows straightforward lookup
and formal semantics modeling without array bounds or hash table lookups.
-/
def Program := Const → Fn

--------------------------------------------------------------------------------
-- #guard Tests & Examples
--------------------------------------------------------------------------------

-- Test 1: fv_expr on pure expressions
#guard fv_of_expr (Expr.ctor 0 [1, 2]) == [1, 2].toFinset
#guard fv_of_expr (Expr.proj 0 3) == [3].toFinset
#guard fv_of_expr (Expr.var_app 4 5) == [4, 5].toFinset

-- Test 2: fv_of_fn_body on FnBody statements
-- return statement: ret x => {x}
#guard fv_of_fn_body (FnBody.ret 1) == [1].toFinset

-- let statement: x ≔ e; F (x is bound in F, so x is erased from fv_of_fn_body F)
-- let 1 ≔ ctor 0 [2, 3]; ret 1  ==> free vars: {2, 3} (1 is bound)
#guard fv_of_fn_body (FnBody.let_ 1 (Expr.ctor 0 [2, 3]) (FnBody.ret 1)) == [2, 3].toFinset

-- let with extra unbound var in continuation: let 1 ≔ ctor 0 [2]; ret 3 ==> {2, 3}
#guard fv_of_fn_body (FnBody.let_ 1 (Expr.ctor 0 [2]) (FnBody.ret 3)) == [2, 3].toFinset

-- inc & dec statement: inc 1; ret 2 ==> {1, 2}
#guard fv_of_fn_body (FnBody.inc 1 (FnBody.ret 2)) == [1, 2].toFinset
#guard fv_of_fn_body (FnBody.dec 1 (FnBody.ret 2)) == [1, 2].toFinset

-- case statement: case x of [F1, F2] ==> includes x and free vars of all branches
#guard fv_of_fn_body (FnBody.case 0 [FnBody.ret 1, FnBody.ret 2]) == [0, 1, 2].toFinset

-- Example of a Program mapping function IDs to Fn definitions:

-- Function 0: identity function (lambda x. ret x)
private def fnId : Fn := ⟨[1], FnBody.ret 1⟩

-- Function 1: inc and return (lambda x. inc x; ret x)
private def fnIncRet : Fn := ⟨[1], FnBody.inc 1 (FnBody.ret 1)⟩

-- Sample Program mapping Const 0 to fnId, Const 1 to fnIncRet, and defaulting to fnId
private def sampleProgram (c : Const) : Fn :=
  let cNat : Nat := (c : Nat)
  match cNat with
  | 0 => fnId
  | 1 => fnIncRet
  | _ => fnId

#guard (sampleProgram 0).ys == [1]
#guard fv_of_fn_body (sampleProgram 1).fn_body == [1].toFinset

end RcCorrectness
section end
