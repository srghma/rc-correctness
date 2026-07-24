import RcCorrectness.Ast

namespace RcCorrectness

inductive lin_type : Type
| 𝕆 | 𝔹
deriving DecidableEq, Repr

structure typed_rc where
  c : rc
  ty : lin_type
deriving DecidableEq, Repr

structure typed_var where
  x : var
  ty : lin_type
deriving DecidableEq, Repr

abbrev type_context := Multiset typed_var

-- Notation
notation x " ∶ " τ => typed_var.mk x τ
notation c " ∷ " τ => typed_rc.mk c τ

inductive linear (β : const → var → lin_type) : Multiset typed_var → typed_rc → Prop
| weaken {Γ : Multiset typed_var} {t : typed_rc} (x : var)
  (t_typed : linear β Γ t) :
  linear β (Multiset.cons (typed_var.mk x lin_type.𝔹) Γ) t
| contract {Γ : Multiset typed_var} {x : var} {t : typed_rc}
  (x_𝔹 : (typed_var.mk x lin_type.𝔹) ∈ Γ) (t_typed : linear β (Multiset.cons (typed_var.mk x lin_type.𝔹) Γ) t) :
  linear β Γ t
| inc_𝕆 {Γ : Multiset typed_var} {x : var} {F : fn_body}
  (x_𝕆 : (typed_var.mk x lin_type.𝕆) ∈ Γ) (F_𝕆 : linear β (Multiset.cons (typed_var.mk x lin_type.𝕆) Γ) (typed_rc.mk F lin_type.𝕆)) :
  linear β Γ (typed_rc.mk (fn_body.inc x F) lin_type.𝕆)
| inc_𝔹 {Γ : Multiset typed_var} {x : var} {F : fn_body}
  (x_𝔹 : (typed_var.mk x lin_type.𝔹) ∈ Γ) (F_𝕆 : linear β (Multiset.cons (typed_var.mk x lin_type.𝕆) Γ) (typed_rc.mk F lin_type.𝕆)) :
  linear β Γ (typed_rc.mk (fn_body.inc x F) lin_type.𝕆)
| dec {Γ : Multiset typed_var} (x : var) {F : fn_body}
  (F_𝕆 : linear β Γ (typed_rc.mk F lin_type.𝕆)) :
  linear β (Multiset.cons (typed_var.mk x lin_type.𝕆) Γ) (typed_rc.mk (fn_body.dec x F) lin_type.𝕆)
| ret {x : var} :
  linear β (Multiset.cons (typed_var.mk x lin_type.𝕆) 0) (typed_rc.mk (fn_body.ret x) lin_type.𝕆)
| case_𝕆 {Γ : Multiset typed_var} {x : var} {Fs : List fn_body}
  (x_𝕆 : (typed_var.mk x lin_type.𝕆) ∈ Γ) (Fs_𝕆 : ∀ F, F ∈ Fs → linear β Γ (typed_rc.mk F lin_type.𝕆)) :
  linear β Γ (typed_rc.mk (fn_body.case x Fs) lin_type.𝕆)
| case_𝔹 {Γ : Multiset typed_var} {x : var} {Fs : List fn_body}
  (x_𝔹 : (typed_var.mk x lin_type.𝔹) ∈ Γ) (Fs_𝕆 : ∀ F, F ∈ Fs → linear β Γ (typed_rc.mk F lin_type.𝕆)) :
  linear β Γ (typed_rc.mk (fn_body.case x Fs) lin_type.𝕆)
| const_app_full (ys : List var) (c : const) :
  linear β (Multiset.ofList (List.map (fun y => typed_var.mk y (β c y)) ys)) (typed_rc.mk (expr.const_app_full c ys) lin_type.𝕆)
| const_app_part (ys : List var) (c : const) :
  linear β (Multiset.ofList (List.map (fun y => typed_var.mk y lin_type.𝕆) ys)) (typed_rc.mk (expr.const_app_part c ys) lin_type.𝕆)
| var_app (x y : var) :
  linear β (Multiset.cons (typed_var.mk x lin_type.𝕆) (Multiset.cons (typed_var.mk y lin_type.𝕆) 0)) (typed_rc.mk (expr.var_app x y) lin_type.𝕆)
| ctor_app (ys : List var) (i : cnstr) :
  linear β (Multiset.ofList (List.map (fun y => typed_var.mk y lin_type.𝕆) ys)) (typed_rc.mk (expr.ctor i ys) lin_type.𝕆)
| let_ {Γ : Multiset typed_var} {xs : List var} {e : expr} {Δ : Multiset typed_var} {z : var} {F : fn_body}
  (xs_𝕆 : Multiset.ofList (List.map (fun y => typed_var.mk y lin_type.𝕆) xs) ⊆ Δ)
  (e_𝕆 : linear β (Γ + Multiset.ofList (List.map (fun y => typed_var.mk y lin_type.𝔹) xs)) (typed_rc.mk e lin_type.𝕆))
  (F_𝕆 : linear β (Multiset.cons (typed_var.mk z lin_type.𝕆) Δ) (typed_rc.mk F lin_type.𝕆)) :
  linear β (Γ + Δ) (typed_rc.mk (fn_body.let_ z e F) lin_type.𝕆)
| proj_𝔹 {Γ : Multiset typed_var} {x y : var} {F : fn_body} (i : cnstr)
  (x_𝔹 : (typed_var.mk x lin_type.𝔹) ∈ Γ) (F_𝕆 : linear β (Multiset.cons (typed_var.mk y lin_type.𝔹) Γ) (typed_rc.mk F lin_type.𝕆)) :
  linear β Γ (typed_rc.mk (fn_body.let_ y (expr.proj i x) F) lin_type.𝕆)
| proj_𝕆 {Γ : Multiset typed_var} {x y : var} {F : fn_body} (i : cnstr)
  (x_𝕆 : (typed_var.mk x lin_type.𝕆) ∈ Γ) (F_𝕆 : linear β (Multiset.cons (typed_var.mk y lin_type.𝕆) Γ) (typed_rc.mk F lin_type.𝕆)) :
  linear β Γ (typed_rc.mk (fn_body.let_ y (expr.proj i x) (fn_body.inc y F)) lin_type.𝕆)

inductive linear_const (β : const → var → lin_type) (δ : program) : const → Prop
| const {c : const}
  (F_𝕆 : linear β (Multiset.ofList (List.map (fun y => typed_var.mk y (β c y)) (δ c).ys)) (typed_rc.mk (δ c).F lin_type.𝕆)) :
  linear_const β δ c

inductive linear_program (β : const → var → lin_type) : program → Prop
| program {δ : program}
  (const_typed : ∀ c : const, linear_const β δ c) :
  linear_program β δ

end RcCorrectness
