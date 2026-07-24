import RcCorrectness.Compiler
import RcCorrectness.WellFormedness

namespace RcCorrectness

lemma not_𝔹_iff_𝕆 {τ : lin_type} : τ ≠ lin_type.𝔹 ↔ τ = lin_type.𝕆 := sorry

lemma not_𝕆_iff_𝔹 {τ : lin_type} : τ ≠ lin_type.𝕆 ↔ τ = lin_type.𝔹 := sorry

theorem FV_sub_wf_context {δ : program} {β : const → var → lin_type} {Γ : Finset var} {F : fn_body}
  (h : fn_body_wf β δ Γ F) :
  FV F ⊆ Γ := sorry

lemma FV_inc_𝕆_var_eq_FV {x : var} {F : fn_body} (V : Finset var) (βₗ : var → lin_type)
  (h : x ∈ FV F) :
  FV (inc_𝕆_var x V F βₗ) = FV F := sorry

lemma FV_sub_FV_dec_𝕆 (ys : List var) (F : fn_body) (βₗ : var → lin_type) :
  FV F ⊆ FV (dec_𝕆 ys F βₗ) := sorry

lemma FV_dec_𝕆_filter (ys : List var) (F : fn_body) (βₗ : var → lin_type) :
  FV (dec_𝕆 ys F βₗ) = ys.toFinset.filter (fun y => βₗ y = lin_type.𝕆 ∧ y ∉ FV F) ∪ FV F := sorry

lemma FV_dec_𝕆_sub_vars_FV (vars : List var) (F : fn_body) (βₗ : var → lin_type) :
  FV (dec_𝕆 vars F βₗ) ⊆ vars.toFinset ∪ FV F := sorry

lemma FV_dec_eq_FV {e : expr} {x z : var} {F : fn_body}
  (h : x ∈ FV_expr e ∪ (FV F).erase z) :
  FV_expr e ∪ (FV (fn_body.dec x F)).erase z = FV_expr e ∪ (FV F).erase z := sorry

lemma FV_Capp_eq_FV {xs : List (var × lin_type)} {z : var} {e : expr} {F1 F2 : fn_body} (βₗ : var → lin_type)
  (heq : FV F1 = FV F2) (h : ∀ xτ, xτ ∈ xs → xτ.1 ∈ FV (fn_body.let_ z e F1)) :
  FV (C_app xs (fn_body.let_ z e F1) βₗ) = FV (fn_body.let_ z e F2) := sorry

theorem FV_C_eq_FV (β : const → var → lin_type) (F : fn_body) (βₗ : var → lin_type) :
  FV (C β F βₗ) = FV F := sorry

lemma wf_sandwich {β : const → var → lin_type} {δ : program} {Γ Γ' Γ'' : Finset var} {F : fn_body}
  (Γ_sub_Γ' : Γ ⊆ Γ') (Γ'_sub_Γ'' : Γ' ⊆ Γ'') (hΓ : fn_body_wf β δ Γ F) (hΓ'' : fn_body_wf β δ Γ'' F) :
  fn_body_wf β δ Γ' F := sorry

lemma FV_wf {β : const → var → lin_type} {δ : program} {Γ : Finset var} {F : fn_body}
  (h : fn_body_wf β δ Γ F) :
  fn_body_wf β δ (FV F) F := sorry

lemma wf_FV_sandwich {β : const → var → lin_type} {δ : program} {Γ Γ' : Finset var} {F : fn_body}
  (Γ'_low : FV F ⊆ Γ') (Γ'_high : Γ' ⊆ Γ) (h : fn_body_wf β δ Γ F) :
  fn_body_wf β δ Γ' F := sorry

lemma vars_sub_FV_dec_𝕆 (ys : List var) (F : fn_body) (βₗ : var → lin_type) :
  ∀ y, y ∈ ys → βₗ y = lin_type.𝕆 → y ∈ FV (dec_𝕆 ys F βₗ) := sorry

lemma dec_𝕆_eq_dec_𝕆'_of_nodup (F : fn_body) (βₗ : var → lin_type) {ys : List var}
  (d : List.Nodup ys) :
  dec_𝕆 ys F βₗ = dec_𝕆' ys F βₗ := sorry

lemma inductive_dec' {β : const → var → lin_type} {ys : List var} {y𝕆 y𝔹 : Multiset var} {F : fn_body} {βₗ : var → lin_type}
  (ys_sub_vars : (ys : Multiset var) ⊆ y𝕆 + y𝔹) (d : List.Nodup ys)
  (y𝕆_𝕆 : ∀ y, y ∈ y𝕆 → βₗ y = lin_type.𝕆) (y𝔹_𝔹 : ∀ y, y ∈ y𝔹 → βₗ y = lin_type.𝔹) (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (h : linear β ((y𝕆.filter (fun y => y ∉ ys ∨ y ∈ FV F)).map (fun y => typed_var.mk y lin_type.𝕆) + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) (typed_rc.mk F lin_type.𝕆)) :
  linear β (y𝕆.map (fun y => typed_var.mk y lin_type.𝕆) + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) (typed_rc.mk (dec_𝕆 ys F βₗ) lin_type.𝕆) := sorry

lemma inductive_dec {β : const → var → lin_type} {ys : List var} {y𝕆 y𝔹 : Multiset var} {F : fn_body} {βₗ : var → lin_type}
  (y𝕆_sub_ys : y𝕆 ⊆ (ys : Multiset var)) (ys_sub_vars : (ys : Multiset var) ⊆ y𝕆 + y𝔹) (d : List.Nodup ys)
  (y𝕆_𝕆 : ∀ y, y ∈ y𝕆 → βₗ y = lin_type.𝕆) (y𝔹_𝔹 : ∀ y, y ∈ y𝔹 → βₗ y = lin_type.𝔹) (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (h : linear β ((y𝕆.filter (fun y => y ∈ FV F)).map (fun y => typed_var.mk y lin_type.𝕆) + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) (typed_rc.mk F lin_type.𝕆)) :
  linear β (y𝕆.map (fun y => typed_var.mk y lin_type.𝕆) + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) (typed_rc.mk (dec_𝕆 ys F βₗ) lin_type.𝕆) := sorry

lemma inductive_weakening {β : const → var → lin_type} {ys : Multiset typed_var} {y𝔹 : Multiset var}
  {r : typed_rc}
  (h : linear β ys r) :
  linear β (ys + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) r := sorry

theorem C_app_rc_insertion_correctness {β : const → var → lin_type} {βₗ : var → lin_type} {F : fn_body} {y : var} {e : expr} {y𝕆 y𝔹 : Multiset var} {Γ : List (var × lin_type)}
  (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (y𝕆_𝕆 : ∀ y, y ∈ y𝕆 → βₗ y = lin_type.𝕆) (y𝔹_𝔹 : ∀ y, y ∈ y𝔹 → βₗ y = lin_type.𝔹)
  (ty : linear β (Multiset.ofList (List.map (fun yτ => typed_var.mk yτ.1 yτ.2) Γ)) (typed_rc.mk e lin_type.𝕆)) :
  linear β (y𝕆.map (fun y => typed_var.mk y lin_type.𝕆) + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) (typed_rc.mk (C_app Γ (fn_body.let_ y e (C β F (Function.update βₗ y lin_type.𝕆))) βₗ) lin_type.𝕆) := sorry

theorem rc_insertion_correctness' {β : const → var → lin_type} {δ : program} {c : const} {y𝕆 y𝔹 : Multiset var}
  (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (y𝕆_𝕆 : ∀ y, y ∈ y𝕆 → β c y = lin_type.𝕆) (y𝔹_𝔹 : ∀ y, y ∈ y𝔹 → β c y = lin_type.𝔹)
  (y𝕆_sub_FV : y𝕆.toFinset ⊆ FV (δ c).F) (wf : fn_body_wf β δ (y𝕆.toFinset ∪ y𝔹.toFinset) (δ c).F) :
  linear β (y𝕆.map (fun y => typed_var.mk y lin_type.𝕆) + y𝔹.map (fun y => typed_var.mk y lin_type.𝔹)) (typed_rc.mk (C β (δ c).F (β c)) lin_type.𝕆) := sorry

theorem rc_insertion_correctness (β : const → var → lin_type) (δ : program) (wf : program_wf β δ) :
  linear_program β (C_prog β δ) := sorry

end RcCorrectness
