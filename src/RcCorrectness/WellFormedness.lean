import type_system
import data.multiset

namespace rc_correctness

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.lin_type

inductive fn_body_wf (β : const → var → lin_type) (δ : program) : finset var → fn_body → Prop
notation Γ ` ⊢ `:1 F := fn_body_wf Γ F
| ret {Γ : finset var} {x : var}
  (x_def : x ∈ Γ) :
  Γ ⊢ ret x
| let_const_app_full {Γ : finset var} {z : var} {c : const} {ys : list var} {F : fn_body}
  (ys_def : ys.to_finset ⊆ Γ) (arity_eq : ys.length = (δ c).ys.length)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ F) :
  Γ ⊢ (z ≔ c⟦ys…⟧; F)
| let_const_app_part {Γ : finset var} {z : var} {c : const} {ys : list var} {F : fn_body}
  (ys_def : ys.to_finset ⊆ Γ)
  (no_𝔹_var : ∀ x : var, β c x ≠ 𝔹)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ F) :
  Γ ⊢ (z ≔ c⟦ys…, _⟧; F)
| let_var_app {Γ : finset var} {z : var} {x y : var} {F : fn_body}
  (x_def : x ∈ Γ) (y_in_Γ : y ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ F) :
  Γ ⊢ (z ≔ x⟦y⟧; F)
| let_ctor {Γ : finset var} {z : var} (i : cnstr) {ys : list var} {F : fn_body}
  (ys_def : ys.to_finset ⊆ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ F) :
  Γ ⊢ (z ≔ ⟪ys⟫i; F)
| let_proj {Γ : finset var} {z : var} {x : var} (i : cnstr) {F : fn_body}
  (x_def : x ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ ⊢ F) :
  Γ ⊢ (z ≔ x[i]; F)
| «case» {Γ : finset var} {x : var} {Fs : list fn_body}
  (x_def : x ∈ Γ) (Fs_wf : ∀ F ∈ Fs, Γ ⊢ F) :
  Γ ⊢ (case x of Fs)

notation β `; ` δ `; ` Γ ` ⊢ `:1 F := fn_body_wf β δ Γ F

inductive const_wf (β : const → var → lin_type) (δ : program) : const → Prop
notation `⊢ `:1 c := const_wf c
| const {c : const}
  (F_wf : β; δ; (δ c).ys.to_finset ⊢ (δ c).F) (nd_ys : multiset.nodup (δ c).ys) :
  ⊢ c

notation β `; ` δ ` ⊢ `:1 c := const_wf β δ c

inductive program_wf (β : const → var → lin_type) : program → Prop
notation `⊢ `:1 δ := program_wf δ
| program {δ : program}
  (const_wf : ∀ c : const, β; δ ⊢ c) :
  ⊢ δ

notation β ` ⊢ `:1 δ := program_wf β δ

end rc_correctness
