import RcCorrectness.Util

namespace RcCorrectness

-- ast defs
abbrev var := Nat
abbrev const := Nat
abbrev cnstr := Nat

inductive expr : Type
| const_app_full (c : const) (ys : List var) : expr
| const_app_part (c : const) (ys : List var) : expr
| var_app (x : var) (y : var) : expr
| ctor (i : cnstr) (ys : List var) : expr
| proj (i : cnstr) (x : var) : expr
deriving Repr, DecidableEq

inductive fn_body : Type
| ret (x : var) : fn_body
| let_ (x : var) (e : expr) (F : fn_body) : fn_body
| case (x : var) (Fs : List fn_body) : fn_body
| inc (x : var) (F : fn_body) : fn_body
| dec (x : var) (F : fn_body) : fn_body
deriving Repr

instance : DecidableEq fn_body := sorry

structure fn where
  ys : List var
  F : fn_body
deriving Repr

instance : DecidableEq fn := sorry

def program := const → fn

inductive rc : Type
| expr (e : expr) : rc
| fn_body (F : fn_body) : rc
deriving Repr

instance : DecidableEq rc := sorry

-- expr
notation c "⟦" ys "…⟧" => expr.const_app_full c ys
notation c "⟦" ys "…, " "_" "⟧" => expr.const_app_part c ys
notation x "⟦" y "⟧" => expr.var_app x y
notation "⟪" ys "⟫" i => expr.ctor i ys
notation x "[" i "]" => expr.proj i x

-- fn_body
notation x " ≔ " e "; " F => fn_body.let_ x e F
notation "case " x " of " Fs => fn_body.case x Fs
notation "inc " x "; " F => fn_body.inc x F
notation "dec " x "; " F => fn_body.dec x F

-- rc
instance : Coe expr rc where
  coe := rc.expr

instance : Coe fn_body rc where
  coe := rc.fn_body

-- fn_body recursor
def fn_body.rec_wf {C : fn_body → Sort _}
  (ret_ : ∀ (x : var), C (fn_body.ret x))
  (let_ : ∀ (x : var) (e : expr) (F : fn_body) (F_ih : C F), C (fn_body.let_ x e F))
  (case_ : ∀ (x : var) (Fs : List fn_body) (Fs_ih : ∀ F, F ∈ Fs → C F), C (fn_body.case x Fs))
  (inc_ : ∀ (x : var) (F : fn_body) (F_ih : C F), C (fn_body.inc x F))
  (dec_ : ∀ (x : var) (F : fn_body) (F_ih : C F), C (fn_body.dec x F)) : ∀ (x : fn_body), C x := sorry

-- free variables
def FV_expr : expr → Finset var
| (expr.const_app_full _ xs) => xs.toFinset
| (expr.const_app_part _ xs) => xs.toFinset
| (expr.var_app x y) => {x, y}
| (expr.ctor _ xs) => xs.toFinset
| (expr.proj _ x) => {x}

partial def FV : fn_body → Finset var
| (fn_body.ret x) => {x}
| (fn_body.let_ x e F) => FV_expr e ∪ ((FV F).erase x)
| (fn_body.case x Fs) => insert x (Finset.join (Fs.map FV))
| (fn_body.inc x F) => insert x (FV F)
| (fn_body.dec x F) => insert x (FV F)

-- var order
abbrev var_le : var -> var -> Prop := Nat.le

end RcCorrectness
