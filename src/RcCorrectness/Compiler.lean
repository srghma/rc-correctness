import RcCorrectness.TypeSystem

namespace RcCorrectness

open lin_type

def inc_𝕆_var (x : var) (V : Finset var) (F : fn_body) (βₗ : var → lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ V then F else fn_body.inc x F

def dec_𝕆_var (x : var) (F : fn_body) (βₗ : var → lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ FV F then fn_body.dec x F else F

def dec_𝕆 (xs : List var) (F : fn_body) (βₗ : var → lin_type) : fn_body :=
xs.foldr (fun x acc => dec_𝕆_var x acc βₗ) F

def dec_𝕆' (xs : List var) (F : fn_body) (βₗ : var → lin_type) : fn_body :=
xs.foldr (fun x acc => if βₗ x = 𝕆 ∧ x ∉ FV F then fn_body.dec x acc else acc) F

def C_app : List (var × lin_type) → fn_body → (var → lin_type) → fn_body
| [], (fn_body.let_ z e F), _ => fn_body.let_ z e F
| ((y, t)::xs), (fn_body.let_ z e F), βₗ =>
  if t = 𝕆 then
    inc_𝕆_var y ((xs.map Prod.fst).toFinset ∪ FV F) (C_app xs (fn_body.let_ z e F) βₗ) βₗ
  else
    C_app xs (fn_body.let_ z e (dec_𝕆_var y F βₗ)) βₗ
| _, F, _ => F

partial def C (β : const → var → lin_type) : fn_body → (var → lin_type) → fn_body
| (fn_body.ret x), βₗ => inc_𝕆_var x Finset.empty (fn_body.ret x) βₗ
| (fn_body.case x Fs), βₗ =>
  fn_body.case x (Fs.map (fun F => dec_𝕆 (Finset.sort (· ≤ ·) (FV (fn_body.case x Fs))) (C β F βₗ) βₗ))
| (fn_body.let_ y (expr.proj i x) F), βₗ =>
  if βₗ x = 𝕆 then
    fn_body.let_ y (expr.proj i x) (fn_body.inc y (dec_𝕆_var x (C β F (Function.update βₗ y 𝕆)) βₗ))
  else
    fn_body.let_ y (expr.proj i x) (C β F (Function.update βₗ y 𝔹))
| (fn_body.let_ z (expr.const_app_full c ys) F), βₗ =>
  C_app (ys.map (fun y => (y, β c y))) (fn_body.let_ z (expr.const_app_full c ys) (C β F (Function.update βₗ z 𝕆))) βₗ
| (fn_body.let_ z (expr.const_app_part c ys) F), βₗ =>
  C_app (ys.map (fun y => (y, β c y))) (fn_body.let_ z (expr.const_app_part c ys) (C β F (Function.update βₗ z 𝕆))) βₗ
| (fn_body.let_ z (expr.var_app x y) F), βₗ =>
  C_app ([(x, 𝕆), (y, 𝕆)]) (fn_body.let_ z (expr.var_app x y) (C β F (Function.update βₗ z 𝕆))) βₗ
| (fn_body.let_ z (expr.ctor i ys) F), βₗ =>
  C_app (ys.map (fun y => (y, 𝕆))) (fn_body.let_ z (expr.ctor i ys) (C β F (Function.update βₗ z 𝕆))) βₗ
| F, _ => F

def C_prog (β : const → var → lin_type) (δ : program) (c : const) : fn :=
  let βₗ := β c
  let f := δ c
  ⟨f.ys, dec_𝕆 f.ys (C β f.F βₗ) βₗ⟩

end RcCorrectness
