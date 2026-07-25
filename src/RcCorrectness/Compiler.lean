import Mathlib.Data.Finset.Sort
import RcCorrectness.TypeSystem

namespace RcCorrectness

open Expr FnBody LinType

def inc_𝕆_var (x : Var) (V : Finset Var) (F : FnBody) (βₗ : Var → LinType) : FnBody :=
  if βₗ x = 𝕆 ∧ x ∉ V then F else incᶠᵇ x;ᶠᵇ F

def dec_𝕆_var (x : Var) (F : FnBody) (βₗ : Var → LinType) : FnBody :=
  if βₗ x = 𝕆 ∧ x ∉ fv_of_fn_body F then decᶠᵇ x;ᶠᵇ F else F

def dec_𝕆 (xs : List Var) (F : FnBody) (βₗ : Var → LinType) : FnBody :=
  xs.foldr (fun x acc => dec_𝕆_var x acc βₗ) F

def dec_𝕆' (xs : List Var) (F : FnBody) (βₗ : Var → LinType) : FnBody :=
  xs.foldr (fun x acc => if βₗ x = 𝕆 ∧ x ∉ fv_of_fn_body F then decᶠᵇ x;ᶠᵇ acc else acc) F

def C_app : List (Var × LinType) → FnBody → (Var → LinType) → FnBody
| [], (z ≔ᶠᵇ e;ᶠᵇ F), _βₗ => z ≔ᶠᵇ e;ᶠᵇ F
| ((y, t)::xs), (z ≔ᶠᵇ e;ᶠᵇ F), βₗ =>
  if t = 𝕆 then
    inc_𝕆_var y ((xs.map Prod.fst).toFinset ∪ fv_of_fn_body F) (C_app xs (z ≔ᶠᵇ e;ᶠᵇ F) βₗ) βₗ
  else
    C_app xs (z ≔ᶠᵇ e;ᶠᵇ dec_𝕆_var y F βₗ) βₗ
| _xs, F, _βₗ => F

def C (β : Const → Var → LinType) : FnBody → (Var → LinType) → FnBody
| (FnBody.ret x), βₗ => inc_𝕆_var x ∅ (FnBody.ret x) βₗ
| fb@(caseᶠᵇ x ofᶠᵇ Fs), βₗ =>
  let fvars_of_case_of_fn_body : Finset Var := fv_of_fn_body fb
  let fvars_of_case_of_fn_body_sorted : List Var := fvars_of_case_of_fn_body.sort (· ≤ · : Var → Var → Prop)
  caseᶠᵇ x ofᶠᵇ (Fs.map (fun F => dec_𝕆 fvars_of_case_of_fn_body_sorted (C β F βₗ) βₗ))
| (y ≔ᶠᵇ x[ᵉi];ᶠᵇ F), βₗ =>
  if βₗ x = 𝕆 then
    y ≔ᶠᵇ x[ᵉi];ᶠᵇ incᶠᵇ y;ᶠᵇ dec_𝕆_var x (C β F (Function.update βₗ y 𝕆)) βₗ
  else
    y ≔ᶠᵇ x[ᵉi];ᶠᵇ C β F (Function.update βₗ y 𝔹)
| (z ≔ᶠᵇ c⟦ys…⟧;ᶠᵇ F), βₗ =>
  C_app (ys.map (fun y => (y, β c y))) (z ≔ᶠᵇ c⟦ys…⟧;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ
| (z ≔ᶠᵇ c⟦ys…, _⟧;ᶠᵇ F), βₗ =>
  C_app (ys.map (fun y => (y, β c y))) (z ≔ᶠᵇ c⟦ys…, _⟧;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ
| (z ≔ᶠᵇ x⟦y⟧;ᶠᵇ F), βₗ =>
  C_app [(x, 𝕆), (y, 𝕆)] (z ≔ᶠᵇ x⟦y⟧;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ
| (z ≔ᶠᵇ ⟪ys⟫i;ᶠᵇ F), βₗ =>
  C_app (ys.map (fun y => (y, 𝕆))) (z ≔ᶠᵇ ⟪ys⟫i;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ
| F, _βₗ => F

def C_prog (β : Const → Var → LinType) (δ : Program) (c : Const) : Fn :=
  let (βₗ, f) := (β c, δ c)
  ⟨f.ys, dec_𝕆 f.ys (C β f.fn_body βₗ) βₗ⟩

end RcCorrectness
