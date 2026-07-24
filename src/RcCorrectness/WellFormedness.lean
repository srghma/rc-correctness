import RcCorrectness.TypeSystem

namespace RcCorrectness

inductive fn_body_wf (β : const → var → lin_type) (δ : program) : Finset var → fn_body → Prop
| ret {Γ : Finset var} {x : var}
  (x_def : x ∈ Γ) :
  fn_body_wf β δ Γ (fn_body.ret x)
| let_const_app_full {Γ : Finset var} {z : var} {c : const} {ys : List var} {F : fn_body}
  (ys_def : ys.toFinset ⊆ Γ) (arity_eq : ys.length = (δ c).ys.length)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : fn_body_wf β δ (insert z Γ) F) :
  fn_body_wf β δ Γ (fn_body.let_ z (expr.const_app_full c ys) F)
| let_const_app_part {Γ : Finset var} {z : var} {c : const} {ys : List var} {F : fn_body}
  (ys_def : ys.toFinset ⊆ Γ)
  (no_𝔹_var : ∀ x : var, β c x ≠ lin_type.𝔹)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : fn_body_wf β δ (insert z Γ) F) :
  fn_body_wf β δ Γ (fn_body.let_ z (expr.const_app_part c ys) F)
| let_var_app {Γ : Finset var} {z : var} {x y : var} {F : fn_body}
  (x_def : x ∈ Γ) (y_in_Γ : y ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : fn_body_wf β δ (insert z Γ) F) :
  fn_body_wf β δ Γ (fn_body.let_ z (expr.var_app x y) F)
| let_ctor {Γ : Finset var} {z : var} (i : cnstr) {ys : List var} {F : fn_body}
  (ys_def : ys.toFinset ⊆ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : fn_body_wf β δ (insert z Γ) F) :
  fn_body_wf β δ Γ (fn_body.let_ z (expr.ctor i ys) F)
| let_proj {Γ : Finset var} {z : var} {x : var} (i : cnstr) {F : fn_body}
  (x_def : x ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : fn_body_wf β δ (insert z Γ) F) :
  fn_body_wf β δ Γ (fn_body.let_ z (expr.proj i x) F)
| case {Γ : Finset var} {x : var} {Fs : List fn_body}
  (x_def : x ∈ Γ) (Fs_wf : ∀ F, F ∈ Fs → fn_body_wf β δ Γ F) :
  fn_body_wf β δ Γ (fn_body.case x Fs)

inductive const_wf (β : const → var → lin_type) (δ : program) : const → Prop
| const {c : const}
  (F_wf : fn_body_wf β δ (δ c).ys.toFinset (δ c).F) (nd_ys : List.Nodup (δ c).ys) :
  const_wf β δ c

inductive program_wf (β : const → var → lin_type) : program → Prop
| program {δ : program}
  (const_wf : ∀ c : const, const_wf β δ c) :
  program_wf β δ

end RcCorrectness
