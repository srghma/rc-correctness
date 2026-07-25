import ast

namespace rc_correctness

@[derive decidable_eq]
inductive lin_type : Type
  | 𝕆 | 𝔹

structure typed_rc := (c : rc) (ty : lin_type)

@[derive decidable_eq]
structure typed_var := (x : var) (ty : lin_type)

notation x ` ∶ `:2 τ := typed_var.mk x τ
notation xs ` [∶] `:2 τ := (list.map (λ x, (x ∶ τ)) xs : multiset typed_var)
notation xs ` {∶} `:2 τ := multiset.map (λ x, (x ∶ τ)) xs
notation c ` ∷ `:2 τ := typed_rc.mk c τ

abbreviation type_context := multiset typed_var

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.lin_type

inductive linear (β : const → var → lin_type) : type_context → typed_rc → Prop
notation Γ ` ⊩ `:1 t := linear Γ t
| weaken {Γ : type_context} {t : typed_rc} (x : var)
  (t_typed : Γ ⊩ t) :
  (x ∶ 𝔹) :: Γ ⊩ t
| contract {Γ : type_context} {x : var} {t : typed_rc}
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (t_typed : (x ∶ 𝔹) :: Γ ⊩ t) :
  Γ ⊩ t
| inc_𝕆 {Γ : type_context} {x : var} {F : fn_body}
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (F_𝕆 : (x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (inc x; F) ∷ 𝕆
| inc_𝔹 {Γ : type_context} {x : var} {F : fn_body}
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (F_𝕆 : (x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (inc x; F) ∷ 𝕆
| «dec» {Γ : type_context} (x : var) {F : fn_body}
  (F_𝕆 : Γ ⊩ F ∷ 𝕆) :
  (x ∶ 𝕆) :: Γ ⊩ (dec x; F) ∷ 𝕆
| ret {x : var} :
  (x ∶ 𝕆) :: 0 ⊩ (ret x) ∷ 𝕆
| case_𝕆 {Γ : type_context} {x : var} {Fs : list fn_body}
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (Fs_𝕆 : ∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆) :
  Γ ⊩ (case x of Fs) ∷ 𝕆
| case_𝔹 {Γ : type_context} {x : var} {Fs : list fn_body}
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (Fs_𝕆 : ∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆) :
  Γ ⊩ (case x of Fs) ∷ 𝕆
| const_app_full (ys : list var) (c : const) :
  list.map (λ y, y ∶ β c y) ys ⊩ c⟦ys…⟧ ∷ 𝕆
| const_app_part (ys : list var) (c : const) :
  ys [∶] 𝕆 ⊩ c⟦ys…, _⟧ ∷ 𝕆
| var_app (x y : var) :
  (x ∶ 𝕆) :: (y ∶ 𝕆) :: 0 ⊩ x⟦y⟧ ∷ 𝕆
| ctor_app (ys : list var) (i : cnstr) :
  ys [∶] 𝕆 ⊩ (⟪ys⟫i) ∷ 𝕆
| «let» {Γ : type_context} {xs : list var} {e : expr} {Δ : type_context} {z : var} {F : fn_body}
  (xs_𝕆 : (xs [∶] 𝕆) ⊆ Δ) (e_𝕆 : Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) (F_𝕆 : (z ∶ 𝕆) :: Δ ⊩ F ∷ 𝕆) :
  Γ + Δ ⊩ (z ≔ e; F) ∷ 𝕆
| proj_𝔹 {Γ : type_context} {x y : var} {F : fn_body} (i : cnstr)
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (F_𝕆 : (y ∶ 𝔹) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (y ≔ x[i]; F) ∷ 𝕆
| proj_𝕆 {Γ : type_context} {x y : var} {F : fn_body} (i : cnstr)
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (F_𝕆 : (y ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (y ≔ x[i]; inc y; F) ∷ 𝕆

notation β `; ` Γ ` ⊩ `:1 t := linear β Γ t

inductive linear_const (β : const → var → lin_type) (δ : program) : const → Prop
notation ` ⊩ `:1 c := linear_const c
| const {c : const}
  (F_𝕆 : β; (δ c).ys.map (λ y, y ∶ β c y) ⊩ (δ c).F ∷ 𝕆) :
  ⊩ c

notation β `; ` δ ` ⊩ `:1 c := linear_const β δ c

inductive linear_program (β : const → var → lin_type) : program → Prop
notation ` ⊩ `:1 δ := linear_program δ
| program {δ : program}
  (const_typed : ∀ c : const, (β; δ ⊩ c)) :
  ⊩ δ

notation β ` ⊩ `:1 δ := linear_program β δ

end rc_correctness
