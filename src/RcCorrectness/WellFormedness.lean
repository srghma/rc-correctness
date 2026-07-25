import RcCorrectness.TypeSystem

namespace RcCorrectness

section

set_option quotPrecheck false in
set_option hygiene false in
local notation:50 Γ " ⊢ʷᶠᵇ " fn_body => FnBodyWf β δ Γ fn_body

open FnBody Expr LinType in
inductive FnBodyWf (β : Const → Var → LinType) (δ : Program) : Finset Var → FnBody → Prop
| ret {Γ : Finset Var} {x : Var}
  (x_def : x ∈ Γ) :
  Γ ⊢ʷᶠᵇ ret x
| let_const_app_full {Γ : Finset Var} {z : Var} {c : Const} {ys : List Var} {fn_body : FnBody}
  (ys_def : ys.toFinset ⊆ Γ) (arity_eq : ys.length = (δ c).ys.length)
  (z_used : z ∈ fv_of_fn_body fn_body) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ʷᶠᵇ fn_body) :
  Γ ⊢ʷᶠᵇ (z ≔ᶠᵇ c⟦ys…⟧;ᶠᵇ fn_body)
| let_const_app_part {Γ : Finset Var} {z : Var} {c : Const} {ys : List Var} {fn_body : FnBody}
  (ys_def : ys.toFinset ⊆ Γ)
  (no_𝔹_var : ∀ x : Var, β c x ≠ 𝔹)
  (z_used : z ∈ fv_of_fn_body fn_body) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ʷᶠᵇ fn_body) :
  Γ ⊢ʷᶠᵇ (z ≔ᶠᵇ c⟦ys…, _⟧;ᶠᵇ fn_body)
| let_var_app {Γ : Finset Var} {z : Var} {x y : Var} {fn_body : FnBody}
  (x_def : x ∈ Γ) (y_in_Γ : y ∈ Γ)
  (z_used : z ∈ fv_of_fn_body fn_body) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ʷᶠᵇ fn_body) :
  Γ ⊢ʷᶠᵇ (z ≔ᶠᵇ x⟦y⟧;ᶠᵇ fn_body)
| let_ctor {Γ : Finset Var} {z : Var} (i : Cnstr) {ys : List Var} {fn_body : FnBody}
  (ys_def : ys.toFinset ⊆ Γ)
  (z_used : z ∈ fv_of_fn_body fn_body) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ʷᶠᵇ fn_body) :
  Γ ⊢ʷᶠᵇ (z ≔ᶠᵇ ⟪ys⟫i;ᶠᵇ fn_body)
| let_proj {Γ : Finset Var} {z : Var} {x : Var} (i : Cnstr) {fn_body : FnBody}
  (x_def : x ∈ Γ)
  (z_used : z ∈ fv_of_fn_body fn_body) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ʷᶠᵇ fn_body) :
  Γ ⊢ʷᶠᵇ (z ≔ᶠᵇ x[ᵉi];ᶠᵇ fn_body)
| case {Γ : Finset Var} {x : Var} {Fs : List FnBody}
  (x_def : x ∈ Γ) (Fs_wf : ∀ fn_body ∈ Fs, Γ ⊢ʷᶠᵇ fn_body) :
  Γ ⊢ʷᶠᵇ (caseᶠᵇ x ofᶠᵇ Fs)
end section

-- 1023 is max - 1, without it the first ;ʷᶠᵇ will fight with second ;ʷᶠᵇ
notation β " ;ʷᶠᵇ " δ:1023 " ;ʷᶠᵇ " Γ " ⊢ʷᶠᵇ " fn_body => FnBodyWf β δ Γ fn_body

section

set_option quotPrecheck false in
set_option hygiene false in
local notation " ⊢ʷᶜ " c => ConstWf β δ c

open FnBody Expr LinType in
inductive ConstWf (β : Const → Var → LinType) (δ : Program) : Const → Prop
| const {c : Const}
  (F_wf : β;ʷᶠᵇ δ;ʷᶠᵇ (δ c).ys.toFinset ⊢ʷᶠᵇ (δ c).fn_body) (nd_ys : (δ c).ys.Nodup) :
  ⊢ʷᶜ c
end section

notation β " ;ʷᶜ " δ " ⊢ʷᶜ " c => ConstWf β δ c

section

set_option quotPrecheck false in
set_option hygiene false in
local notation " ⊢ᵖʷ " δ => ProgramWf β δ

open FnBody Expr LinType in
inductive ProgramWf (β : Const → Var → LinType) : Program → Prop
| program {δ : Program}
  (const_wf : ∀ c : Const, β ;ʷᶜ δ ⊢ʷᶜ c) :
  ⊢ᵖʷ δ
end section

notation β " ⊢ᵖʷ " δ => ProgramWf β δ

end
