import RcCorrectness.Ast
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

namespace RcCorrectness

inductive LinType : Type
  | 𝕆 | 𝔹
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

structure TypedRC where
  c : Rc
  ty : LinType
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

structure TypedVar where
  x : Var
  ty : LinType
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

notation:60 x " ∶ " τ => TypedVar.mk x τ
notation:60 xs " [∶] " τ => ((List.map (fun x => (x ∶ τ)) xs : List TypedVar) : Multiset TypedVar)
notation:60 c " ∷ " τ => TypedRC.mk c τ

abbrev TypeContext := Multiset TypedVar

section

set_option quotPrecheck false in
set_option hygiene false in
local notation:50 Γ " ⊩ " t => Linear β Γ t

open FnBody Expr LinType in
inductive Linear (β : Const → Var → LinType) : TypeContext → TypedRC → Prop
| weaken {Γ : TypeContext} {t : TypedRC} (x : Var)
  (t_typed : Γ ⊩ t) :
  (x ∶ 𝔹) ::ₘ Γ ⊩ t
| contract {Γ : TypeContext} {x : Var} {t : TypedRC}
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (t_typed : (x ∶ 𝔹) ::ₘ Γ ⊩ t) :
  Γ ⊩ t
| inc_𝕆 {Γ : TypeContext} {x : Var} {F : FnBody}
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (F_𝕆 : (x ∶ 𝕆) ::ₘ Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (incᶠᵇ x;ᶠᵇ F) ∷ 𝕆
| inc_𝔹 {Γ : TypeContext} {x : Var} {F : FnBody}
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (F_𝕆 : (x ∶ 𝕆) ::ₘ Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (incᶠᵇ x;ᶠᵇ F) ∷ 𝕆
| «dec» {Γ : TypeContext} (x : Var) {F : FnBody}
  (F_𝕆 : Γ ⊩ F ∷ 𝕆) :
  (x ∶ 𝕆) ::ₘ Γ ⊩ (decᶠᵇ x;ᶠᵇ F) ∷ 𝕆
| ret {x : Var} :
  (x ∶ 𝕆) ::ₘ 0 ⊩ (ret x) ∷ 𝕆
| case_𝕆 {Γ : TypeContext} {x : Var} {Fs : List FnBody}
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (Fs_𝕆 : ∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆) :
  Γ ⊩ (caseᶠᵇ x ofᶠᵇ Fs) ∷ 𝕆
| case_𝔹 {Γ : TypeContext} {x : Var} {Fs : List FnBody}
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (Fs_𝕆 : ∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆) :
  Γ ⊩ (caseᶠᵇ x ofᶠᵇ Fs) ∷ 𝕆
| const_app_full (ys : List Var) (c : Const) :
  ((ys.map (fun y => y ∶ β c y) : List TypedVar) : Multiset TypedVar) ⊩ c⟦ys…⟧ ∷ 𝕆
| const_app_part (ys : List Var) (c : Const) :
  (ys [∶] 𝕆) ⊩ c⟦ys…, _⟧ ∷ 𝕆
| var_app (x y : Var) :
  (x ∶ 𝕆) ::ₘ (y ∶ 𝕆) ::ₘ 0 ⊩ x⟦y⟧ ∷ 𝕆
| ctor_app (ys : List Var) (i : Cnstr) :
  (ys [∶] 𝕆) ⊩ (⟪ys⟫i) ∷ 𝕆
| «let» {Γ : TypeContext} {xs : List Var} {e : Expr} {Δ : TypeContext} {z : Var} {F : FnBody}
  (xs_𝕆 : (xs [∶] 𝕆) ⊆ Δ) (e_𝕆 : Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) (F_𝕆 : (z ∶ 𝕆) ::ₘ Δ ⊩ F ∷ 𝕆) :
  Γ + Δ ⊩ (z ≔ᶠᵇ e;ᶠᵇ F) ∷ 𝕆
| proj_𝔹 {Γ : TypeContext} {x y : Var} {F : FnBody} (i : Cnstr)
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (F_𝕆 : (y ∶ 𝔹) ::ₘ Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (y ≔ᶠᵇ x[ᵉi];ᶠᵇ F) ∷ 𝕆
| proj_𝕆 {Γ : TypeContext} {x y : Var} {F : FnBody} (i : Cnstr)
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (F_𝕆 : (y ∶ 𝕆) ::ₘ Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (y ≔ᶠᵇ x[ᵉi];ᶠᵇ incᶠᵇ y;ᶠᵇ F) ∷ 𝕆
end section

-- Expression typing
notation β " ; " Γ " ⊩ " t => Linear β Γ t

section
set_option quotPrecheck false in
set_option hygiene false in
local notation " ⊩ " c => LinearConst β δ c

open FnBody Expr LinType in
inductive LinearConst (β : Const → Var → LinType) (δ : Program) : Const → Prop
| const {c : Const}
  (F_𝕆 : β; ((δ c).ys.map (fun y => y ∶ β c y) : Multiset TypedVar) ⊩ (δ c).fn_body ∷ 𝕆) :
  ⊩ c
end section

-- Constant typing
notation β " ;ᶜ " δ " ⊩ᶜ " c => LinearConst β δ c

section

set_option quotPrecheck false in
set_option hygiene false in
local notation " ⊩ᵖ " δ => LinearProgram β δ

open FnBody Expr LinType in
inductive LinearProgram (β : Const → Var → LinType) : Program → Prop
| program {δ : Program}
  (const_typed : ∀ c : Const, β ;ᶜ δ ⊩ᶜ c) :
  ⊩ᵖ δ
end section

-- Program typing
notation:50 β " ⊩ᵖ " δ => LinearProgram β δ

end
