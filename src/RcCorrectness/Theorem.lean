import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.AddSub
import RcCorrectness.Compiler
import RcCorrectness.WellFormedness
import Aesop

namespace RcCorrectness

open LinType

lemma not_𝔹_iff_𝕆 {τ : LinType} : τ ≠ 𝔹 ↔ τ = 𝕆 := by
  cases τ <;> simp

lemma not_𝕆_iff_𝔹 {τ : LinType} : τ ≠ 𝕆 ↔ τ = 𝔹 := by
  cases τ <;> simp

section FV_wf
  open Finset
  open List

  theorem FV_sub_wf_context {δ : Program} {β : Const → Var → LinType} {Γ : Finset Var} {F : FnBody}
    (h : β ;ʷᶠᵇ δ ;ʷᶠᵇ Γ ⊢ʷᶠᵇ F) :
    fv_of_fn_body F ⊆ Γ :=
  by
    induction h
    case ret x_def =>
      simp [fv_of_fn_body, x_def]
    case let_const_app_full ys_def arity_eq z_used z_undef F_wf ih =>
      intro y hy
      simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_erase] at hy
      rcases hy with hy1 | ⟨hy_neq, hy2⟩
      · exact ys_def hy1
      · have := ih hy2
        rcases Finset.mem_insert.mp this with rfl | hy3
        · contradiction
        · exact hy3
    case let_const_app_part ys_def no_𝔹 z_used z_undef F_wf ih =>
      intro y hy
      simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_erase] at hy
      rcases hy with hy1 | ⟨hy_neq, hy2⟩
      · exact ys_def hy1
      · have := ih hy2
        rcases Finset.mem_insert.mp this with rfl | hy3
        · contradiction
        · exact hy3
    case let_var_app x_def y_in_Γ z_used z_undef F_wf ih =>
      intro y hy
      simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with (rfl | rfl) | ⟨hy_neq, hy2⟩
      · exact x_def
      · exact y_in_Γ
      · have := ih hy2
        rcases Finset.mem_insert.mp this with rfl | hy3
        · contradiction
        · exact hy3
    case let_ctor ys_def z_used z_undef F_wf ih =>
      intro y hy
      simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_erase] at hy
      rcases hy with hy1 | ⟨hy_neq, hy2⟩
      · exact ys_def hy1
      · have := ih hy2
        rcases Finset.mem_insert.mp this with rfl | hy3
        · contradiction
        · exact hy3
    case let_proj x_def z_used z_undef F_wf ih =>
      intro y hy
      simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at hy
      rcases hy with rfl | ⟨hy_neq, hy2⟩
      · exact x_def
      · have := ih hy2
        rcases Finset.mem_insert.mp this with rfl | hy3
        · contradiction
        · exact hy3
    case case x Fs x_def Fs_wf ih =>
      intro y hy
      simp only [fv_of_fn_body] at hy
      have h_general : ∀ Fs init, y ∈ List.foldl (fun acc f => acc ∪ fv_of_fn_body f) init Fs → y ∈ init ∨ ∃ F' ∈ Fs, y ∈ fv_of_fn_body F' := by
        intro Fs
        induction Fs with
        | nil =>
          intro init h
          simp only [List.foldl_nil] at h
          exact Or.inl h
        | cons F' Fs' ih_Fs =>
          intro init h
          simp only [List.foldl_cons] at h
          have h' := ih_Fs (init ∪ fv_of_fn_body F') h
          rcases h' with h_init | ⟨F'', hF'', hy''⟩
          · simp only [Finset.mem_union] at h_init
            rcases h_init with h_init | h_F'
            · exact Or.inl h_init
            · exact Or.inr ⟨F', List.Mem.head _, h_F'⟩
          · exact Or.inr ⟨F'', List.mem_cons_of_mem F' hF'', hy''⟩
      rcases h_general Fs {x} hy with hy_x | ⟨F', hF', hy'⟩
      · simp only [Finset.mem_singleton] at hy_x
        subst hy_x
        exact x_def
      · exact Finset.subset_iff.mp (ih F' hF') hy'
end FV_wf

section FV_C
  open Finset

  lemma FV_inc_𝕆_var_eq_FV {x : Var} {F : FnBody} (V : Finset Var) (βₗ : Var → LinType)
    (h : x ∈ fv_of_fn_body F) :
    fv_of_fn_body (inc_𝕆_var x V F βₗ) = fv_of_fn_body F := by
    unfold inc_𝕆_var
    split_ifs
    simp_all only
    simp_all only [not_and, Decidable.not_not]
    grind only [fv_of_fn_body.eq_def, forall_mem_not_eq, forall_mem_not_eq', = insert_eq_of_mem]

  lemma FV_sub_FV_dec_𝕆 (ys : List Var) (F : FnBody) (βₗ : Var → LinType)
    : fv_of_fn_body F ⊆ fv_of_fn_body (dec_𝕆 ys F βₗ) := by
    apply subset_iff.mpr
    intros x h
    unfold dec_𝕆 dec_𝕆_var
    induction ys
    simp_all only [List.foldr_nil]
    simp_all only [List.foldr_cons]
    split
    next h_1 =>
      obtain ⟨left, right⟩ := h_1
      grind only [fv_of_fn_body.eq_def, forall_mem_not_eq, forall_mem_not_eq', = mem_insert]
    next h_1 => simp_all only [not_and, Decidable.not_not]

  lemma FV_dec_𝕆_filter (ys : List Var) (F : FnBody) (βₗ : Var → LinType)
    : fv_of_fn_body (dec_𝕆 ys F βₗ) = ys.toFinset.filter (fun y => βₗ y = 𝕆 ∧ y ∉ fv_of_fn_body F) ∪ fv_of_fn_body F := by
    induction ys with
    | nil =>
      simp [dec_𝕆]
    | cons y ys ih =>
      change fv_of_fn_body (dec_𝕆_var y (dec_𝕆 ys F βₗ) βₗ) = _
      unfold dec_𝕆_var
      simp only [List.toFinset_cons, filter_insert]
      by_cases hy : βₗ y = 𝕆 ∧ y ∉ fv_of_fn_body (dec_𝕆 ys F βₗ)
      · rw [if_pos hy]
        simp only [fv_of_fn_body]
        have hyF : y ∉ fv_of_fn_body F := fun hF => hy.2 (FV_sub_FV_dec_𝕆 ys F βₗ hF)
        rw [ih, if_pos ⟨hy.1, hyF⟩]
        ext z
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, List.mem_toFinset]
        tauto
      · rw [if_neg hy]
        by_cases hyF : βₗ y = 𝕆 ∧ y ∉ fv_of_fn_body F
        · push Not at hy
          have hy_in : y ∈ ys.toFinset.filter (fun y => βₗ y = 𝕆 ∧ y ∉ fv_of_fn_body F) := by
            have h_in_dec := hy hyF.1
            rw [ih] at h_in_dec
            rcases Finset.mem_union.mp h_in_dec with h | h
            · exact h
            · exact absurd h hyF.2
          rw [ih, if_pos hyF, Finset.insert_eq_of_mem hy_in]
        · rw [ih, if_neg hyF]

  lemma FV_dec_𝕆_sub_vars_FV (vars : List Var) (F : FnBody) (βₗ : Var → LinType)
  : fv_of_fn_body (dec_𝕆 vars F βₗ) ⊆ vars.toFinset ∪ fv_of_fn_body F :=
  by
    simp only [FV_dec_𝕆_filter, subset_iff, mem_union, mem_filter]
    intros x h
    cases h
    simp only [or_false, *]
    simp only [List.mem_toFinset, or_true, *]

  lemma FV_dec_eq_FV {e : Expr} {x z : Var} {F : FnBody}
    (h : x ∈ fv_of_expr e ∪ erase (fv_of_fn_body F) z) :
    fv_of_expr e ∪ erase (fv_of_fn_body (decᶠᵇ x;ᶠᵇ F)) z = fv_of_expr e ∪ erase (fv_of_fn_body F) z := by
    unfold fv_of_fn_body
    grind only [fv_of_fn_body.eq_def, erase_eq, = mem_union, = mem_erase, = mem_sdiff,
      eq_of_mem_of_notMem_erase, = mem_insert, = mem_singleton, erase_union_distrib,
      erase_sdiff_comm, erase_sdiff_distrib, mem_of_mem_erase]

  lemma FV_Capp_eq_FV {xs : List (Var × LinType)} {z : Var} {e : Expr} {F1 F2 : FnBody} (βₗ : Var → LinType)
    (heq : fv_of_fn_body F1 = fv_of_fn_body F2) (h : ∀ xτ ∈ xs, (xτ : Var × LinType).1 ∈ fv_of_fn_body (z ≔ᶠᵇ e;ᶠᵇ F1)) :
    fv_of_fn_body (C_app xs (z ≔ᶠᵇ e;ᶠᵇ F1) βₗ) = fv_of_fn_body (z ≔ᶠᵇ e;ᶠᵇ F2) :=
  by
    induction xs generalizing F1 F2 with
    | nil =>
      simp only [fv_of_fn_body, C_app]
      rw [heq]
    | cons head tail ih =>
      obtain ⟨x, τ⟩ := head
      rw [List.forall_mem_cons] at h
      obtain ⟨x_in_FV, h⟩ := h
      simp only [C_app, fv_of_fn_body] at *
      cases τ with
      | 𝕆 =>
        rw [if_pos rfl]
        unfold inc_𝕆_var
        split_ifs
        · exact ih heq h
        · simp only [fv_of_fn_body]
          rw [ih heq h]
          rw [heq] at x_in_FV
          exact insert_eq_of_mem x_in_FV
      | 𝔹 =>
        rw [if_neg (by decide)]
        simp only [dec_𝕆_var]
        split_ifs with h_cond
        · suffices h2 : ∀ (xτ : Var × LinType), xτ ∈ tail → xτ.fst ∈ fv_of_expr e ∪ (fv_of_fn_body (decᶠᵇ x;ᶠᵇ F1)).erase z by
            have h3 : fv_of_fn_body (decᶠᵇ x;ᶠᵇ F1) = fv_of_fn_body (decᶠᵇ x;ᶠᵇ F2) := by
              simp only [fv_of_fn_body]; rw [heq]
            rw [ih h3 h2]
            rw [heq] at x_in_FV
            exact FV_dec_eq_FV x_in_FV
          intros yτ yτ_in_tl
          have y_in_FV := h yτ yτ_in_tl
          rwa [FV_dec_eq_FV x_in_FV]
        · exact ih heq h

  lemma subset_foldl_union {α : Type} (f : α → Finset Var) (init : Finset Var) (l : List α) :
      init ⊆ List.foldl (fun acc x => acc ∪ f x) init l := by
    induction l generalizing init with
    | nil => exact Finset.Subset.refl _
    | cons x xs ih =>
      simp only [List.foldl_cons]
      have h1 : init ⊆ init ∪ f x := fun v hv => Finset.mem_union.mpr (Or.inl hv)
      exact Finset.Subset.trans h1 (ih (init ∪ f x))

  lemma mem_foldl_union_subset {α : Type} (f : α → Finset Var) (init : Finset Var) (l : List α) (x : α) (hx : x ∈ l) :
      f x ⊆ List.foldl (fun acc x => acc ∪ f x) init l := by
    induction l generalizing init with
    | nil => cases hx
    | cons y ys ih =>
      simp only [List.foldl_cons]
      cases List.mem_cons.mp hx with
      | inl hy =>
        subst hy
        have h1 : f x ⊆ init ∪ f x := fun v hv => Finset.mem_union.mpr (Or.inr hv)
        exact Finset.Subset.trans h1 (subset_foldl_union f (init ∪ f x) ys)
      | inr hy =>
        exact ih (init ∪ f y) hy

  lemma foldl_union_sub {α : Type} (f : α → Finset Var) (init S : Finset Var) (l : List α)
      (h_init : init ⊆ S) (h_f : ∀ x ∈ l, f x ⊆ S) :
      List.foldl (fun acc x => acc ∪ f x) init l ⊆ S := by
    induction l generalizing init with
    | nil => exact h_init
    | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Finset.union_subset h_init (h_f x (List.Mem.head xs))
      · intro y hy; exact h_f y (List.Mem.tail x hy)

  lemma foldl_union_mono {α : Type} (f g : α → Finset Var) (init1 init2 : Finset Var) (l : List α)
      (h_init : init1 ⊆ init2) (h_fg : ∀ x ∈ l, f x ⊆ g x) :
      List.foldl (fun acc x => acc ∪ f x) init1 l ⊆ List.foldl (fun acc x => acc ∪ g x) init2 l := by
    induction l generalizing init1 init2 with
    | nil => exact h_init
    | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Finset.union_subset_union h_init (h_fg x (List.Mem.head xs))
      · intro y hy; exact h_fg y (List.Mem.tail x hy)

  theorem FV_C_eq_FV (β : Const → Var → LinType) (F : FnBody) (βₗ : Var → LinType) : fv_of_fn_body (C β F βₗ) = fv_of_fn_body F := by
    induction F using FnBody.rec (motive_2 := fun Fs => ∀ F ∈ Fs, ∀ βₗ, fv_of_fn_body (C β F βₗ) = fv_of_fn_body F) generalizing βₗ with
    | nil F hF βₗ =>
      cases hF
    | cons head tail head_ih tail_ih F hF βₗ =>
      cases hF with
      | head => exact head_ih βₗ
      | tail _ hF' => exact tail_ih F hF' βₗ
    | ret x =>
      unfold C
      simp only [fv_of_fn_body, inc_𝕆_var]
      split_ifs <;> simp [fv_of_fn_body]
    | case x Fs ih =>
      unfold C fv_of_fn_body
      simp only [List.foldl_map]
      apply Finset.Subset.antisymm
      · apply foldl_union_sub
        · exact subset_foldl_union _ _ _
        · intro F hF
          refine Subset.trans (FV_dec_𝕆_sub_vars_FV _ _ _) ?_
          simp only [Finset.sort_toFinset, ih F hF βₗ]
          intro v hv
          simp only [fv_of_fn_body, Finset.mem_union] at hv
          rcases hv with hv | hv
          · exact hv
          · exact mem_foldl_union_subset _ _ _ F hF hv
      · apply foldl_union_mono
        · exact Finset.Subset.refl _
        · intro F hF
          rw [← ih F hF βₗ]
          exact FV_sub_FV_dec_𝕆 _ _ _
    | let_ x e F ih =>
      cases e with
      | const_app_full c ys =>
        unfold C
        apply FV_Capp_eq_FV βₗ (ih (Function.update βₗ x 𝕆))
        intro xτ hxτ
        simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, List.mem_map] at *
        obtain ⟨v, hv, rfl⟩ := hxτ
        left; exact List.mem_toFinset.mpr hv
      | const_app_part c ys =>
        unfold C
        apply FV_Capp_eq_FV βₗ (ih (Function.update βₗ x 𝕆))
        intro xτ hxτ
        simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, List.mem_map] at *
        obtain ⟨v, hv, rfl⟩ := hxτ
        left; exact List.mem_toFinset.mpr hv
      | var_app a b =>
        unfold C
        apply FV_Capp_eq_FV βₗ (ih (Function.update βₗ x 𝕆))
        intro xτ hxτ
        rcases List.mem_cons.mp hxτ with rfl | hxτ
        · simp only [fv_of_fn_body, fv_of_expr]
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inl rfl)))
        · rcases List.mem_singleton.mp hxτ with rfl
          simp only [fv_of_fn_body, fv_of_expr]
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b))))
      | ctor i ys =>
        unfold C
        apply FV_Capp_eq_FV βₗ (ih (Function.update βₗ x 𝕆))
        intro xτ hxτ
        simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, List.mem_map] at *
        obtain ⟨v, hv, rfl⟩ := hxτ
        left; exact List.mem_toFinset.mpr hv
      | proj i a =>
        unfold C
        split_ifs with h𝕆
        · simp only [dec_𝕆_var]
          split_ifs with hd
          · simp only [fv_of_fn_body, fv_of_expr]
            rw [ih (Function.update βₗ x 𝕆)]
            ext v
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
            constructor
            · rintro (rfl | ⟨hne, rfl | rfl | hv⟩)
              · exact Or.inl rfl
              · contradiction
              · exact Or.inl rfl
              · exact Or.inr ⟨hne, hv⟩
            · rintro (rfl | ⟨hne, hv⟩)
              · exact Or.inl rfl
              · exact Or.inr ⟨hne, Or.inr (Or.inr hv)⟩
          · simp only [fv_of_fn_body, fv_of_expr]
            rw [ih (Function.update βₗ x 𝕆)]
            ext v
            simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert]
            constructor
            · rintro (rfl | ⟨hne, rfl | hv⟩)
              · exact Or.inl rfl
              · contradiction
              · exact Or.inr ⟨hne, hv⟩
            · rintro (rfl | ⟨hne, hv⟩)
              · exact Or.inl rfl
              · exact Or.inr ⟨hne, Or.inr hv⟩
        · simp only [fv_of_fn_body]
          rw [ih (Function.update βₗ x 𝔹)]
    | inc x F ih =>
      simp [C, fv_of_fn_body]
    | dec x F ih =>
      simp [C, fv_of_fn_body]
end FV_C

section sandwich
  open Finset

  lemma wf_sandwich {β : Const → Var → LinType} {δ : Program} {Γ Γ' Γ'' : Finset Var} {F : FnBody}
    (Γ_sub_Γ' : Γ ⊆ Γ') (Γ'_sub_Γ'' : Γ' ⊆ Γ'') (hΓ : β ;ʷᶠᵇ δ ;ʷᶠᵇ Γ ⊢ʷᶠᵇ F) (hΓ'' : β;ʷᶠᵇ δ;ʷᶠᵇ Γ'' ⊢ʷᶠᵇ F)
    : β;ʷᶠᵇ δ;ʷᶠᵇ Γ' ⊢ʷᶠᵇ F := by
    induction hΓ generalizing Γ' Γ'' with
    | ret x_def =>
      exact FnBodyWf.ret (Γ_sub_Γ' x_def)
    | let_const_app_full ys_def arity_eq z_used z_undef F_wf ih =>
      cases hΓ'' with | let_const_app_full _ _ _ z_undef'' F_wf'' =>
      refine FnBodyWf.let_const_app_full (Subset.trans ys_def Γ_sub_Γ') arity_eq z_used ?_ ?_
      · intro h; exact z_undef'' (Γ'_sub_Γ'' h)
      · exact ih (insert_subset_insert _ Γ_sub_Γ') (insert_subset_insert _ Γ'_sub_Γ'') F_wf''
    | let_const_app_part ys_def no_𝔹 z_used z_undef F_wf ih =>
      cases hΓ'' with | let_const_app_part _ _ _ z_undef'' F_wf'' =>
      refine FnBodyWf.let_const_app_part (Subset.trans ys_def Γ_sub_Γ') no_𝔹 z_used ?_ ?_
      · intro h; exact z_undef'' (Γ'_sub_Γ'' h)
      · exact ih (insert_subset_insert _ Γ_sub_Γ') (insert_subset_insert _ Γ'_sub_Γ'') F_wf''
    | let_var_app x_def y_in_Γ z_used z_undef F_wf ih =>
      cases hΓ'' with | let_var_app _ _ _ z_undef'' F_wf'' =>
      refine FnBodyWf.let_var_app (Γ_sub_Γ' x_def) (Γ_sub_Γ' y_in_Γ) z_used ?_ ?_
      · intro h; exact z_undef'' (Γ'_sub_Γ'' h)
      · exact ih (insert_subset_insert _ Γ_sub_Γ') (insert_subset_insert _ Γ'_sub_Γ'') F_wf''
    | let_ctor i ys_def z_used z_undef F_wf ih =>
      cases hΓ'' with | let_ctor _ _ _ z_undef'' F_wf'' =>
      refine FnBodyWf.let_ctor i (Subset.trans ys_def Γ_sub_Γ') z_used ?_ ?_
      · intro h; exact z_undef'' (Γ'_sub_Γ'' h)
      · exact ih (insert_subset_insert _ Γ_sub_Γ') (insert_subset_insert _ Γ'_sub_Γ'') F_wf''
    | let_proj i x_def z_used z_undef F_wf ih =>
      cases hΓ'' with | let_proj _ _ _ z_undef'' F_wf'' =>
      refine FnBodyWf.let_proj i (Γ_sub_Γ' x_def) z_used ?_ ?_
      · intro h; exact z_undef'' (Γ'_sub_Γ'' h)
      · exact ih (insert_subset_insert _ Γ_sub_Γ') (insert_subset_insert _ Γ'_sub_Γ'') F_wf''
    | case x_def Fs_wf ih =>
      cases hΓ'' with | case _ Fs_wf'' =>
      refine FnBodyWf.case (Γ_sub_Γ' x_def) ?_
      intro fn_body hfn
      exact ih fn_body hfn Γ_sub_Γ' Γ'_sub_Γ'' (Fs_wf'' fn_body hfn)

  lemma let_fv_low_sub (z : Var) (e : Expr) (F : FnBody) :
      insert z (fv_of_fn_body F) ⊆ insert z (fv_of_expr e ∪ (fv_of_fn_body F).erase z) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at *
    rcases hv with rfl | hv
    · exact Or.inl rfl
    · by_cases hz : v = z
      · exact Or.inl hz
      · exact Or.inr (Or.inr ⟨hz, hv⟩)

  lemma let_fv_high_sub (z : Var) (e : Expr) (F : FnBody) (Γ : Finset Var)
      (h_e : fv_of_expr e ⊆ Γ) (h_F : fv_of_fn_body F ⊆ insert z Γ) :
      insert z (fv_of_expr e ∪ (fv_of_fn_body F).erase z) ⊆ insert z Γ := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at *
    rcases hv with rfl | (hv | ⟨hne, hv⟩)
    · exact Or.inl rfl
    · exact Or.inr (h_e hv)
    · rcases Finset.mem_insert.mp (h_F hv) with rfl | hΓ
      · contradiction
      · exact Or.inr hΓ

  lemma let_z_undef (z : Var) (s : Finset Var) (F : FnBody) (Γ : Finset Var)
      (h_s : s ⊆ Γ) (hz : z ∉ Γ) :
      z ∉ s ∪ (fv_of_fn_body F).erase z := by
    intro h
    simp only [Finset.mem_union, Finset.mem_erase] at h
    rcases h with h | ⟨hne, _⟩
    · exact hz (h_s h)
    · exact hne rfl

  lemma insert_FV_sub_context (z : Var) {Γ : Finset Var} {F : FnBody}
      (h_F : fv_of_fn_body F ⊆ insert z Γ) :
      insert z (fv_of_fn_body F) ⊆ insert z Γ := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv'
    · exact Finset.mem_insert_self _ _
    · exact h_F hv'

  lemma FV_wf {β : Const → Var → LinType} {δ : Program} {Γ : Finset Var} {F : FnBody} (h : β ;ʷᶠᵇ δ ;ʷᶠᵇ Γ ⊢ʷᶠᵇ F)
    : β ;ʷᶠᵇ δ ;ʷᶠᵇ fv_of_fn_body F ⊢ʷᶠᵇ F := by
    induction h with
    | ret x_def =>
      simp only [fv_of_fn_body]
      exact FnBodyWf.ret (Finset.mem_singleton_self _)
    | let_const_app_full ys_def arity_eq z_used z_undef F_wf ih =>
      rename_i z _ _ _
      unfold fv_of_fn_body
      have ih' := wf_sandwich (Finset.subset_insert z _) (insert_FV_sub_context z (FV_sub_wf_context F_wf)) ih F_wf
      refine FnBodyWf.let_const_app_full Finset.subset_union_left arity_eq z_used (let_z_undef _ _ _ _ ys_def z_undef) ?_
      exact wf_sandwich (let_fv_low_sub _ _ _) (let_fv_high_sub _ _ _ _ ys_def (FV_sub_wf_context F_wf)) ih' F_wf
    | let_const_app_part ys_def no_𝔹 z_used z_undef F_wf ih =>
      rename_i z _ _ _
      unfold fv_of_fn_body
      have ih' := wf_sandwich (Finset.subset_insert z _) (insert_FV_sub_context z (FV_sub_wf_context F_wf)) ih F_wf
      refine FnBodyWf.let_const_app_part Finset.subset_union_left no_𝔹 z_used (let_z_undef _ _ _ _ ys_def z_undef) ?_
      exact wf_sandwich (let_fv_low_sub _ _ _) (let_fv_high_sub _ _ _ _ ys_def (FV_sub_wf_context F_wf)) ih' F_wf
    | let_var_app x_def y_in_Γ z_used z_undef F_wf ih =>
      rename_i Γ_ctx z x y fn_body
      unfold fv_of_fn_body
      have h_e : fv_of_expr (x⟦y⟧) ⊆ Γ_ctx := by
        intro v hv; simp only [fv_of_expr, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
      have ih' := wf_sandwich (Finset.subset_insert z _) (insert_FV_sub_context z (FV_sub_wf_context F_wf)) ih F_wf
      refine FnBodyWf.let_var_app
        (Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inl rfl))))
        (Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))))
        z_used (let_z_undef _ _ _ _ h_e z_undef) ?_
      exact wf_sandwich (let_fv_low_sub _ _ _) (let_fv_high_sub _ _ _ _ h_e (FV_sub_wf_context F_wf)) ih' F_wf
    | let_ctor i ys_def z_used z_undef F_wf ih =>
      rename_i z _ _
      unfold fv_of_fn_body
      have ih' := wf_sandwich (Finset.subset_insert z _) (insert_FV_sub_context z (FV_sub_wf_context F_wf)) ih F_wf
      refine FnBodyWf.let_ctor i Finset.subset_union_left z_used (let_z_undef _ _ _ _ ys_def z_undef) ?_
      exact wf_sandwich (let_fv_low_sub _ _ _) (let_fv_high_sub _ _ _ _ ys_def (FV_sub_wf_context F_wf)) ih' F_wf
    | let_proj i x_def z_used z_undef F_wf ih =>
      rename_i Γ_ctx z x fn_body
      unfold fv_of_fn_body
      have h_e : fv_of_expr (x[ᵉi]) ⊆ Γ_ctx := by
        intro v hv; simp only [fv_of_expr, Finset.mem_singleton] at hv; subst hv; exact x_def
      have ih' := wf_sandwich (Finset.subset_insert z _) (insert_FV_sub_context z (FV_sub_wf_context F_wf)) ih F_wf
      refine FnBodyWf.let_proj i (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))) z_used (let_z_undef _ _ _ _ h_e z_undef) ?_
      exact wf_sandwich (let_fv_low_sub _ _ _) (let_fv_high_sub _ _ _ _ h_e (FV_sub_wf_context F_wf)) ih' F_wf
    | case x_def Fs_wf ih =>
      refine FnBodyWf.case ?_ ?_
      · simp only [fv_of_fn_body]
        exact subset_foldl_union _ _ _ (Finset.mem_singleton_self _)
      · intro F hF
        unfold fv_of_fn_body
        apply wf_sandwich (mem_foldl_union_subset _ _ _ F hF) ?_ (ih F hF) (Fs_wf F hF)
        apply foldl_union_sub
        · intro v hv; simp only [Finset.mem_singleton] at hv; rwa [hv]
        · intro F' hF'; exact FV_sub_wf_context (Fs_wf F' hF')

  lemma wf_FV_sandwich {β : Const → Var → LinType} {δ : Program} {Γ Γ' : Finset Var} {F : FnBody}
    (Γ'_low : fv_of_fn_body F ⊆ Γ') (Γ'_high : Γ' ⊆ Γ) (h : β ;ʷᶠᵇ δ ;ʷᶠᵇ Γ ⊢ʷᶠᵇ F)
    : β;ʷᶠᵇ δ;ʷᶠᵇ Γ' ⊢ʷᶠᵇ F := wf_sandwich Γ'_low Γ'_high (FV_wf h) h
end sandwich

lemma vars_sub_FV_dec_𝕆 (ys : List Var) (F : FnBody) (βₗ : Var → LinType)
  : ∀ y ∈ ys, βₗ y = 𝕆 → y ∈ fv_of_fn_body (dec_𝕆 ys F βₗ) :=
by
  intros y y_in_ys y𝕆
  rw [FV_dec_𝕆_filter]
  simp only [Finset.mem_union, Finset.mem_filter]
  by_cases y ∈ fv_of_fn_body F
  simp_all only [List.mem_toFinset, not_true_eq_false, and_false, or_true]
  simp_all only [List.mem_toFinset, not_false_eq_true, and_self, or_false]

lemma dec_𝕆_eq_dec_𝕆'_of_nodup {ys : List Var} (F : FnBody) (βₗ : Var → LinType)
  (d : List.Nodup ys) : dec_𝕆 ys F βₗ = dec_𝕆' ys F βₗ := by
  unfold dec_𝕆 dec_𝕆_var dec_𝕆'
  induction ys with
  | nil =>
    simp only [List.foldr_nil]
  | cons y ys ih =>
    obtain ⟨ys_hd_not_in_ys_tl, nodup_ys_tl⟩ := List.nodup_cons.mp d
    simp only [List.foldr_cons]
    split_ifs with hA hB
    · congr 1
      exact ih nodup_ys_tl
    · simp only [not_and, not_not] at hB
      have g1 := hA.1
      have g2 := hA.2
      have g3 := hB g1
      have g4 := Finset.subset_iff.mp (FV_sub_FV_dec_𝕆 ys F βₗ) g3
      exact False.elim (g2 g4)
    · rename_i h2
      simp only [not_and, not_not] at hA
      have g1 := h2.1
      have g2 := h2.2
      have g3 := hA g1
      have g4 := Finset.subset_iff.mp (FV_dec_𝕆_sub_vars_FV ys F βₗ) g3
      simp only [List.mem_toFinset, Finset.mem_union] at g4
      rcases g4 with g4 | g4
      · exact False.elim (ys_hd_not_in_ys_tl g4)
      · exact False.elim (g2 g4)
    · exact ih nodup_ys_tl

notation:60 xs " {∶} " τ => Multiset.map (fun x => (x ∶ τ)) xs

lemma inductive_dec' {β : Const → Var → LinType} {ys : List Var} {y𝕆 y𝔹 : Multiset Var} {F : FnBody} {βₗ : Var → LinType}
  (ys_sub_vars : (ys : Multiset Var) ⊆ y𝕆 + y𝔹) (d : List.Nodup ys)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹) (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (h : β; (Multiset.filter (fun y => y ∉ ys ∨ y ∈ fv_of_fn_body F) y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ F ∷ 𝕆)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ dec_𝕆 ys F βₗ ∷ 𝕆 := by
  have h_congr : ∀ {ys_hd : Var} {ys_tl : List Var} {ys' : Multiset Var}
    (f : ∀ y ∈ ys', y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ fv_of_fn_body F),
    ∀ y ∈ ys', y ∉ (ys_hd :: ys_tl : List Var) ∨ y ∈ fv_of_fn_body F ↔ y ∉ ys_tl ∨ y ∈ fv_of_fn_body F := by
    intros ys_hd ys_tl ys' f y y_in_ys'
    rw [List.mem_cons, not_or]
    exact ⟨fun h' => h'.elim (fun h'' => Or.inl h''.2) (fun h'' => Or.inr h''),
           fun h' => h'.elim (fun h'' => f y y_in_ys' h'') (fun h'' => Or.inr h'')⟩
  rw [dec_𝕆_eq_dec_𝕆'_of_nodup F βₗ d]
  induction ys generalizing y𝕆 y𝔹 with
  | nil =>
    rw [dec_𝕆', List.foldr_nil]
    simp only [List.not_mem_nil, not_false_eq_true, true_or, Multiset.filter_true] at h
    exact h
  | cons ys_hd ys_tl ys_ih =>
    obtain ⟨ys_hd_not_in_ys_tl, nodup_ys_tl⟩ := List.nodup_cons.mp d
    change (ys_hd ::ₘ (ys_tl : Multiset Var)) ⊆ y𝕆 + y𝔹 at ys_sub_vars
    simp only [Multiset.cons_subset, Multiset.mem_add] at ys_sub_vars
    obtain ⟨ys_hd_def, ys_tl_sub_vars⟩ := ys_sub_vars
    rw [dec_𝕆', List.foldr_cons]
    split_ifs with h_ifs
    · rcases ys_hd_def with ys_hd_in_y𝕆 | ys_hd_in_y𝔹
      · obtain ⟨y𝕆', y𝕆_def⟩ := Multiset.exists_cons_of_mem ys_hd_in_y𝕆
        rw [y𝕆_def, Multiset.map_cons, Multiset.cons_add]
        apply Linear.dec
        apply ys_ih
        · rw [y𝕆_def] at ys_tl_sub_vars
          intro x x_in_tl
          have := ys_tl_sub_vars x_in_tl
          simp only [Multiset.mem_add, Multiset.mem_cons] at this
          rcases this with (rfl | x_in_y𝕆') | x_in_y𝔹
          · contradiction
          · exact Multiset.mem_add.mpr (Or.inl x_in_y𝕆')
          · exact Multiset.mem_add.mpr (Or.inr x_in_y𝔹)
        · exact nodup_ys_tl
        · intros y hy
          exact y𝕆_𝕆 y (by rw [y𝕆_def]; exact Multiset.mem_cons_of_mem hy)
        · exact y𝔹_𝔹
        · rw [y𝕆_def, Multiset.nodup_cons] at nd_y𝕆
          exact nd_y𝕆.2
        · exact nd_y𝔹
        · rw [y𝕆_def] at h nd_y𝕆
          rw [Multiset.filter_cons_of_neg] at h
          · rw [Multiset.nodup_cons] at nd_y𝕆
            have : ∀ y ∈ y𝕆', y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ fv_of_fn_body F := by
              intros y y_in_y𝕆' h'
              apply Or.inl
              refine ⟨?_, h'⟩
              intro h_eq
              subst h_eq
              exact nd_y𝕆.1 y_in_y𝕆'
            rwa [Multiset.filter_congr (h_congr this)] at h
          · subst y𝕆_def
            simp_all only [not_false_eq_true, and_true, List.mem_cons, not_or, forall_const, List.nodup_cons, and_self,
              true_and, Multiset.nodup_cons, not_true_eq_false, or_self, Multiset.filter_cons_of_neg, Multiset.mem_cons,
              forall_eq_or_imp, Multiset.cons_add, or_false]
      · rw [y𝔹_𝔹 ys_hd ys_hd_in_y𝔹] at h_ifs
        simp_all only [not_false_eq_true, and_true, List.mem_cons, not_or, forall_const, List.nodup_cons, and_self,
          reduceCtorEq, false_and]
    · apply ys_ih
      · exact ys_tl_sub_vars
      · exact nodup_ys_tl
      · exact y𝕆_𝕆
      · exact y𝔹_𝔹
      · exact nd_y𝕆
      · exact nd_y𝔹
      · simp only [not_and, not_not] at h_ifs
        by_cases h_case : βₗ ys_hd = 𝕆
        · have h_in_fv := h_ifs h_case
          have : ∀ y ∈ y𝕆, y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ fv_of_fn_body F := by
            intros y y_in_y𝕆 h'
            by_cases hy : y = ys_hd
            · subst hy
              exact Or.inr h_in_fv
            · exact Or.inl ⟨hy, h'⟩
          rwa [Multiset.filter_congr (h_congr this)] at h
        · rcases ys_hd_def with ys_hd_in_y𝕆 | ys_hd_in_y𝔹
          · rw [y𝕆_𝕆 ys_hd ys_hd_in_y𝕆] at h_case
            contradiction
          · have : ∀ y ∈ y𝕆, y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ fv_of_fn_body F := by
              intros y y_in_y𝕆 h'
              refine Or.inl ⟨?_, h'⟩
              intro hy
              subst hy
              simp_all only [not_false_eq_true, and_true, List.mem_cons, not_or, forall_const, List.nodup_cons,
                and_self, not_true_eq_false]
            rwa [Multiset.filter_congr (h_congr this)] at h

lemma inductive_dec {β : Const → Var → LinType} {ys : List Var} {y𝕆 y𝔹 : Multiset Var} {F : FnBody} {βₗ : Var → LinType}
  (y𝕆_sub_ys : y𝕆 ⊆ ↑ys) (ys_sub_vars : ↑ys ⊆ y𝕆 + y𝔹) (d : List.Nodup ys)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹) (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (h : β; (Multiset.filter (λ y => y ∈ fv_of_fn_body F) y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ F ∷ 𝕆)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ dec_𝕆 ys F βₗ ∷ 𝕆 := by
  have : ∀ y ∈ y𝕆, y ∈ fv_of_fn_body F ↔ y ∉ ys ∨ y ∈ fv_of_fn_body F :=
    fun y y_in_y𝕆 => by
    by_cases h_case : y ∈ ys
    · simp_all only [not_true_eq_false, false_or]
    · simp_all only [not_false_eq_true, true_or, iff_true]
      solve_by_elim
  rw [Multiset.filter_congr this] at h
  exact inductive_dec' ys_sub_vars d y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹 h

lemma inductive_weakening {β : Const → Var → LinType} {ys : Multiset TypedVar} {y𝔹 : Multiset Var}
  {r : Rc} {τ : LinType}
  (h : β; ys ⊩ r ∷ τ)
  : β; ys + (y𝔹 {∶} 𝔹) ⊩ r ∷ τ :=
by
  refine Multiset.induction_on y𝔹 ?_ ?_
  · simp only [Multiset.map_zero, add_zero]
    assumption
  · intros a s ih
    simp only [Multiset.map_cons, Multiset.add_cons]
    apply Linear.weaken a
    assumption

notation f "[" a " ↦ " b "]" => Function.update f a b

section CAppGeneral

/-! ### Typing of the `C_app` translation of `let`-bound applications

`C_app args (z ≔ e; F) βₗ` decorates a `let`-bound application with reference count
adjustments dictated by the parameter types recorded in `args`:

* an `inc` in front for every owned (`𝕆`) parameter position whose argument is either
  borrowed by the caller or still needed afterwards;
* a `dec` inside the body for every borrowed (`𝔹`) parameter position whose argument is
  owned by the caller and dead afterwards.

The argument is split into

* `C_app_base` : the final `Linear.let` step, once all arguments have been processed;
* `C_app_gen`  : the induction over the argument list;
* `C_app_main` : the packaging used for each of the four kinds of applications.
-/

/-- Multi-contraction: extra `𝔹`-typed copies of variables that already occur in the
context may be dropped. -/
lemma inductive_contract {β : Const → Var → LinType} {Γ : Multiset TypedVar}
    {ys : Multiset Var} {r : Rc} {τ : LinType}
    (h_mem : ∀ y ∈ ys, (y ∶ 𝔹) ∈ Γ)
    (h : β; Γ + (ys {∶} 𝔹) ⊩ r ∷ τ) : β; Γ ⊩ r ∷ τ := by
  induction ys using Multiset.induction_on with
  | empty => simp at h; exact h
  | cons a ys ih =>
    have h_a_mem : (a ∶ 𝔹) ∈ Γ := h_mem a (Multiset.mem_cons_self a ys)
    have h_ys_subset : ∀ y ∈ ys, (y ∶ 𝔹) ∈ Γ := fun y hy => h_mem y (Multiset.mem_cons_of_mem hy)
    -- The key is that (a ::ₘ ys) {∶} 𝔹 = (a ∶ 𝔹) + ys {∶} 𝔹
    -- Let's rewrite h to use this
    have key : Γ + ((a ::ₘ ys) {∶} 𝔹) = Γ + ((a ∶ 𝔹) ::ₘ (ys {∶} 𝔹)) := by
      simp
    rw [key] at h
    -- Need to rearrange: Γ + (a ∶ 𝔹) ::ₘ (ys {∶} 𝔹) = (a ∶ 𝔹) ::ₘ (Γ + ys {∶} 𝔹)
    have key2 : Γ + ((a ∶ 𝔹) ::ₘ (ys {∶} 𝔹)) = (a ∶ 𝔹) ::ₘ (Γ + (ys {∶} 𝔹)) := by
      simp
    rw [key2] at h
    have h_a_mem' : (a ∶ 𝔹) ∈ Γ + (ys {∶} 𝔹) := Multiset.mem_add.mpr (Or.inl h_a_mem)
    have h' := Linear.contract h_a_mem' h
    exact ih h_ys_subset h'

/-- `dec_𝕆` only inspects `βₗ` at the variables of its list argument. -/
lemma dec_𝕆_congr {l : List Var} {F : FnBody} {βₗ βₗ' : Var → LinType}
    (h : ∀ y ∈ l, βₗ y = βₗ' y) : dec_𝕆 l F βₗ = dec_𝕆 l F βₗ' := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [dec_𝕆, List.foldr_cons]
    have hx : βₗ x = βₗ' x := h x (by simp)
    have ih' : ∀ y ∈ xs, βₗ y = βₗ' y := fun y hy => h y (by simp [hy])
    have fold_eq : List.foldr (fun x acc => dec_𝕆_var x acc βₗ) F xs = List.foldr (fun x acc => dec_𝕆_var x acc βₗ') F xs := ih ih'
    rw [dec_𝕆_var, dec_𝕆_var, fold_eq]
    simp [hx]

/-- Repeated variables in the list argument of `dec_𝕆` are irrelevant. -/
lemma dec_𝕆_dedup (l : List Var) (F : FnBody) (βₗ : Var → LinType) :
    dec_𝕆 l F βₗ = dec_𝕆 l.dedup F βₗ := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases hy : y ∈ ys
    · rw [List.dedup_cons_of_mem hy]
      -- Need to show dec_𝕆 (y :: ys) F βₗ = dec_𝕆 ys F βₗ
      -- Key: after processing ys, y ∈ fv_of_fn_body (dec_𝕆 ys)
      unfold dec_𝕆
      -- dec_𝕆_var y (dec_𝕆 ys) = if βₗ y = 𝕆 ∧ y ∉ fv_of_fn_body (dec_𝕆 ys)
      --                           then decᶠᵇ y;ᶠᵇ (dec_𝕆 ys) else (dec_𝕆 ys)
      -- Since y ∈ ys, by FV_dec_𝕆_filter, y ∈ fv_of_fn_body (dec_𝕆 ys)
      -- So the condition is false and we get dec_𝕆 ys
      by_cases hyβ : βₗ y = 𝕆
      · -- βₗ y = 𝕆, need to show y ∈ fv_of_fn_body (dec_𝕆 ys)
        have hy_fv : y ∈ fv_of_fn_body (dec_𝕆 ys F βₗ) := by
          rw [FV_dec_𝕆_filter]
          simp only [Finset.mem_union, Finset.mem_filter, List.mem_toFinset]
          by_cases hyF : y ∈ fv_of_fn_body F
          · right; exact hyF
          · left
            exact ⟨hy, hyβ, hyF⟩
        -- dec_𝕆_var y acc = acc when y ∈ fv_of_fn_body acc
        have hv : dec_𝕆_var y (dec_𝕆 ys F βₗ) βₗ = dec_𝕆 ys F βₗ := by
          unfold dec_𝕆_var
          simp only [hyβ, true_and]
          simp [hy_fv]
        simp [dec_𝕆] at hv ih ⊢
        rw [hv, ih]
      · -- βₗ y ≠ 𝕆, so dec_𝕆_var y always returns acc
        have hv : dec_𝕆_var y (List.foldr (fun x acc => dec_𝕆_var x acc βₗ) F ys) βₗ =
                  List.foldr (fun x acc => dec_𝕆_var x acc βₗ) F ys := by
          unfold dec_𝕆_var
          simp [hyβ]
        simp [dec_𝕆] at hv ih ⊢
        rw [hv, ih]
    · -- y ∉ ys, so (y :: ys).dedup = y :: ys.dedup
      have hd : (y :: ys).dedup = y :: ys.dedup := by simp [hy]
      rw [hd]
      simp [dec_𝕆]
      simp [dec_𝕆] at ih
      rw [ih]

/-- Splitting a typing context built from a list of variables and their types into its
owned and borrowed parts. -/
lemma typed_list_split (ys : List Var) (f : Var → LinType) :
    (↑(ys.map (fun y => (y ∶ f y))) : Multiset TypedVar)
      = (((ys.filter (fun y => f y = 𝕆) : List Var) : Multiset Var) {∶} 𝕆)
        + (((ys.filter (fun y => f y = 𝔹) : List Var) : Multiset Var) {∶} 𝔹) := by
  induction ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    have h : f x = 𝕆 ∨ f x = 𝔹 := by cases f x <;> simp
    have perm : ∀ (z : List Var) (g : Var → LinType),
        (z.map (fun a => a ∶ g a)).Perm
          ((z.filter (fun a => g a = 𝕆)).map (fun b => b ∶ 𝕆) ++ (z.filter (fun a => g a = 𝔹)).map (fun b => b ∶ 𝔹)) :=
      fun z g => List.perm_iff_count.mpr
        (List.recOn z (fun a => by simp)
          fun c z ih a => by
            simp only [List.count_cons, List.map_cons, List.filter_cons]
            have h : g c = 𝕆 ∨ g c = 𝔹 := by cases g c <;> simp
            rcases h with h | h
            · simp [h, ih, List.count_cons]
            · simp [h, ih, List.count_cons]; omega)
    rcases h with h | h
    · simp only [h, decide_true, ↓reduceIte]
      simp [(perm xs f)]
    · simp only [h, decide_true, ↓reduceIte]
      have p := perm xs f
      have q := p.cons (x ∶ 𝔹)
      -- q : (x ∶ 𝔹) :: (xs.map ...).Perm (x ∶ 𝔹) :: ((xs.filter 𝕆).map 𝕆 ++ (xs.filter 𝔹).map 𝔹)
      -- We need: _ .Perm (xs.filter 𝕆).map 𝕆 ++ (x ∶ 𝔹) :: (xs.filter 𝔹).map 𝔹
      -- Use: (a :: (l1 ++ l2)).Perm = (l1 ++ (a :: l2)) via permutation
      have r : ((x ∶ 𝔹) :: ((List.map (fun b => b ∶ 𝕆) (List.filter (fun a => decide (f a = 𝕆)) xs) ++
          List.map (fun b => b ∶ 𝔹) (List.filter (fun a => decide (f a = 𝔹)) xs))) : List TypedVar).Perm
          ((List.map (fun b => b ∶ 𝕆) (List.filter (fun a => decide (f a = 𝕆)) xs) ++
          ((x ∶ 𝔹) :: List.map (fun b => b ∶ 𝔹) (List.filter (fun a => decide (f a = 𝔹)) xs)))) := by
        -- Need to prove: (a :: (l1 ++ l2)).Perm (l1 ++ (a :: l2))
        have perm_lemma : ∀ (a : TypedVar) (l1 l2 : List TypedVar),
            (a :: (l1 ++ l2)).Perm (l1 ++ (a :: l2)) := by
          intro a l1 l2
          induction l1 with
          | nil => simp [List.nil_append]
          | cons c l1' ih =>
            simp only [List.cons_append]
            have swap : (a :: c :: (l1' ++ l2)).Perm (c :: a :: (l1' ++ l2)) :=
              (List.Perm.swap a c (l1' ++ l2)).symm
            exact swap.trans (List.Perm.cons c ih)
        exact perm_lemma (x ∶ 𝔹) _ _
      exact Multiset.coe_eq_coe.mpr (q.trans r)

/-- The variables occurring at parameter positions of type `t` in the argument list
`ys.map (fun y => (y, f y))`. -/
lemma filter_map_args (ys : List Var) (f : Var → LinType) (t : LinType) :
    (((ys.map (fun y => (y, f y))).filter (fun p => p.2 = t)).map Prod.fst)
      = ys.filter (fun y => f y = t) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.filter_cons]
    split
    · simp [ih]
    · simp [ih]

/-- The continuation of a `let`-bound application is typable in the context consisting of
exactly the variables it needs: the freshly bound `z` together with the caller-owned
variables that are free in it. -/
lemma C_app_cont_typing {β : Const → Var → LinType} {δ : Program}
    {z : Var} {F : FnBody} {βₗ : Var → LinType} {y𝕆 y𝔹 S : Multiset Var}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (z_used : z ∈ fv_of_fn_body F)
    (z_undef : z ∉ y𝕆.toFinset ∪ y𝔹.toFinset)
    (F_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) ⊢ʷᶠᵇ F)
    (hS_nodup : Multiset.Nodup S)
    (hS_mem : ∀ w ∈ S, w = z ∨ w ∈ y𝕆)
    (hS_fv : ∀ w ∈ S, w ∈ fv_of_fn_body F)
    (hS_covers : ∀ w ∈ fv_of_fn_body F, w ∈ y𝕆 → w ∈ S)
    (hz : z ∈ S) :
    β; (S {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F (βₗ[z ↦ 𝕆]) ∷ 𝕆 := by
  have hz𝕆 : ∀ w ∈ S, (βₗ[z ↦ 𝕆]) w = 𝕆 := by
    intro w hw
    rcases hS_mem w hw with rfl | hw𝕆
    · simp
    · have hwz : w ≠ z := by
        rintro rfl
        exact z_undef (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hw𝕆))
      rw [Function.update_of_ne hwz]
      exact y𝕆_𝕆 w hw𝕆
  have hz𝔹 : ∀ w ∈ y𝔹, (βₗ[z ↦ 𝕆]) w = 𝔹 := by
    intro w hw
    have hwz : w ≠ z := by
      rintro rfl
      exact z_undef (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hw))
    rw [Function.update_of_ne hwz]
    exact y𝔹_𝔹 w hw
  refine ih hS_nodup nd_y𝔹 _ hz𝕆 hz𝔹 (fun w hw => hS_fv w (Multiset.mem_toFinset.mp hw)) ?_
  refine wf_FV_sandwich ?_ ?_ F_wf
  · intro w hw
    rcases Finset.mem_insert.mp (FV_sub_wf_context F_wf hw) with rfl | hmem'
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hz)
    · rcases Finset.mem_union.mp hmem' with h | h
      · exact Finset.mem_union_left _
          (Multiset.mem_toFinset.mpr (hS_covers w hw (Multiset.mem_toFinset.mp h)))
      · exact Finset.mem_union_right _ h
  · intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases hS_mem w (Multiset.mem_toFinset.mp h) with rfl | h'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr h'))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)

/-- Typing of the body of a translated `let`-bound application: the translated
continuation, decorated with the `dec`s inserted for the borrowed parameter positions
(recorded in `D`). -/
lemma C_app_dec_typing {β : Const → Var → LinType} {δ : Program}
    {z : Var} {F : FnBody} {βₗ : Var → LinType} {y𝕆 y𝔹 surv : Multiset Var} {D : List Var}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (z_used : z ∈ fv_of_fn_body F)
    (z_undef : z ∉ y𝕆.toFinset ∪ y𝔹.toFinset)
    (F_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) ⊢ʷᶠᵇ F)
    (surv_le : surv ≤ y𝕆)
    (surv_fv : ∀ y ∈ surv, y ∈ fv_of_fn_body (dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ))
    (D_mem : ∀ w ∈ D, (βₗ w = 𝕆 → w ∈ surv) ∧ (βₗ w = 𝔹 → w ∈ y𝔹))
    (surv_covers : ∀ w ∈ fv_of_fn_body F, w ∈ y𝕆 → w ∈ surv) :
    β; ((z ::ₘ surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ ∷ 𝕆 := by
  have z_not_in_D : z ∉ D := by
    intro hzD
    rcases D_mem z hzD with ⟨hO, hB⟩
    by_cases hβz : βₗ z = 𝕆
    · have hz_y𝕆 : z ∈ y𝕆 := Multiset.mem_of_le surv_le (hO hβz)
      exact z_undef (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hz_y𝕆))
    · have hβz_𝔹 : βₗ z = 𝔹 := not_𝕆_iff_𝔹.mp hβz
      exact z_undef (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr (hB hβz_𝔹)))
  have dec_𝕆_var_eq : ∀ x F βₗ₁ βₗ₂, βₗ₁ x = βₗ₂ x → dec_𝕆_var x F βₗ₁ = dec_𝕆_var x F βₗ₂ := by
    intro x F βₗ₁ βₗ₂ h
    simp [dec_𝕆_var, h]
  have heq : dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ = dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) (βₗ[z ↦ 𝕆]) := by
    have hagree : ∀ w ∈ D, βₗ w = (βₗ[z ↦ 𝕆]) w := by
      intro w hw
      rw [Function.update_of_ne]
      exact fun h => z_not_in_D (h ▸ hw)
    have heq_aux : ∀ l : List Var, ∀ βₗ₁ βₗ₂ : Var → LinType, (∀ w ∈ l, βₗ₁ w = βₗ₂ w) →
        dec_𝕆 l (C β F (βₗ[z ↦ 𝕆])) βₗ₁ = dec_𝕆 l (C β F (βₗ[z ↦ 𝕆])) βₗ₂ := by
      intro l
      induction l with
      | nil => simp [dec_𝕆]
      | cons x xs ih =>
        intro βₗ₁ βₗ₂ hagree'
        simp only [dec_𝕆, List.foldr_cons]
        have hfolds : List.foldr (fun x acc => dec_𝕆_var x acc βₗ₁) (C β F (βₗ[z ↦ 𝕆])) xs =
            List.foldr (fun x acc => dec_𝕆_var x acc βₗ₂) (C β F (βₗ[z ↦ 𝕆])) xs := by
          calc List.foldr (fun x acc => dec_𝕆_var x acc βₗ₁) (C β F (βₗ[z ↦ 𝕆])) xs
              = dec_𝕆 xs (C β F (βₗ[z ↦ 𝕆])) βₗ₁ := rfl
            _ = dec_𝕆 xs (C β F (βₗ[z ↦ 𝕆])) βₗ₂ := ih _ _ (fun w hw => hagree' w (List.mem_cons_of_mem _ hw))
            _ = List.foldr (fun x acc => dec_𝕆_var x acc βₗ₂) (C β F (βₗ[z ↦ 𝕆])) xs := rfl
        rw [hfolds]
        apply dec_𝕆_var_eq
        exact hagree' x (by simp)
    exact heq_aux D _ _ hagree
  rw [heq, dec_𝕆_dedup]
  have surv_nodup : surv.Nodup := Multiset.nodup_of_le surv_le nd_y𝕆
  have z_not_in_surv : z ∉ surv := fun h =>
    z_undef (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr (Multiset.mem_of_le surv_le h)))
  have surv_y𝕆_nodup : (z ::ₘ surv).Nodup := Multiset.nodup_cons.mpr ⟨z_not_in_surv, surv_nodup⟩
  have h_ys_sub_vars : (D.dedup : Multiset Var) ⊆ (z ::ₘ surv) + y𝔹 := by
    intro w hw
    have hwD : w ∈ D := by simpa [Multiset.mem_dedup] using hw
    rcases D_mem w hwD with ⟨hO, hB⟩
    have hτ : βₗ w = 𝕆 ∨ βₗ w = 𝔹 := by cases βₗ w <;> simp
    rcases hτ with h | h
    · have : w ∈ surv := hO h
      simp [this]
    · have : w ∈ y𝔹 := hB h
      simp [this]
  have goal : β; ((z ::ₘ surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ dec_𝕆 D.dedup (C β F (βₗ[z ↦ 𝕆])) (βₗ[z ↦ 𝕆]) ∷ 𝕆 := by
    have h_upd_O : ∀ y ∈ z ::ₘ surv, (βₗ[z ↦ 𝕆]) y = 𝕆 := by
      intro y hy
      by_cases hyz : y = z
      · subst hyz; exact Function.update_self _ _ _
      · have hy_surv : y ∈ surv := by simpa [hyz] using hy
        have hy_y𝕆 : y ∈ y𝕆 := by
          have hle := Multiset.le_iff_count.mp surv_le y
          exact Multiset.count_pos.mp (Nat.lt_of_lt_of_le (Multiset.count_pos.mpr hy_surv) hle)
        rw [Function.update_of_ne hyz]
        exact y𝕆_𝕆 y hy_y𝕆
    have h_upd_B : ∀ y ∈ y𝔹, (βₗ[z ↦ 𝕆]) y = 𝔹 := by
      intro y hy
      by_cases hyz : y = z
      · subst hyz; exact (z_undef (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hy))).elim
      · rw [Function.update_of_ne hyz]
        exact y𝔹_𝔹 y hy
    refine @inductive_dec' β D.dedup (z ::ₘ surv) y𝔹 (C β F (βₗ[z ↦ 𝕆])) (βₗ[z ↦ 𝕆]) h_ys_sub_vars (List.nodup_dedup _) h_upd_O h_upd_B surv_y𝕆_nodup nd_y𝔹 ?_
    apply ih
    · exact Multiset.Nodup.filter _ surv_y𝕆_nodup
    · exact nd_y𝔹
    · -- All filtered elements have type 𝕆
      intro y hy
      have hy_mem : y ∈ z ::ₘ surv := Multiset.mem_filter.mp hy |>.1
      exact h_upd_O y hy_mem
    · -- All y𝔹 elements have type 𝔹
      intro y hy
      exact h_upd_B y hy
    · -- Filter subset of fv_of_fn_body
      intro y hy
      rw [Multiset.mem_toFinset] at hy
      have hy_mem : y ∈ z ::ₘ surv := Multiset.mem_filter.mp hy |>.1
      have hy_pred : y ∉ D.dedup ∨ y ∈ fv_of_fn_body (C β F (βₗ[z ↦ 𝕆])) := Multiset.mem_filter.mp hy |>.2
      rw [Multiset.mem_cons] at hy_mem
      rcases hy_mem with rfl | hy_surv
      · exact z_used
      · -- y ∈ surv, use surv_fv
        have hy_dec := surv_fv y hy_surv
        rw [heq] at hy_dec
        rw [FV_dec_𝕆_filter] at hy_dec
        rw [Finset.mem_union] at hy_dec
        rcases hy_dec with hy_dedup | hy_F
        · -- hy_dedup means y ∈ {y ∈ D.toFinset | ... ∧ y ∉ fv_of_fn_body ...}
          -- But filter requires y ∉ D.dedup ∨ y ∈ fv_of_fn_body, so y ∈ D.dedup implies y ∈ fv_of_fn_body
          -- This is a contradiction
          simp only [Finset.mem_filter] at hy_dedup
          have hy_not_FV := hy_dedup.2.2
          have hy_in_D := hy_dedup.1
          have hy_in_D' : y ∈ D := Multiset.mem_toFinset.mp hy_in_D
          have hy_in_dedup : y ∈ D.dedup := List.mem_dedup.mpr hy_in_D'
          simp [hy_in_dedup, hy_not_FV] at hy_pred
        · rw [FV_C_eq_FV] at hy_F
          exact hy_F
    · -- WF condition
      -- Need to show: filter ⊆ insert z (y𝕆 ∪ y𝔹)
      have hfilter_sub : (Multiset.filter (fun y => y ∉ D.dedup ∨ y ∈ fv_of_fn_body (C β F (βₗ[z ↦ 𝕆]))) (z ::ₘ surv)).toFinset ⊆ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) := by
        intro y hy
        rw [Multiset.mem_toFinset] at hy
        have hy_mem : y ∈ z ::ₘ surv := Multiset.mem_filter.mp hy |>.1
        rw [Multiset.mem_cons] at hy_mem
        rcases hy_mem with rfl | hy_surv
        · exact Finset.mem_insert_self _ _
        · -- y ∈ surv, and surv ≤ y𝕆
          have hy_y𝕆 : y ∈ y𝕆 := by
            have hle := Multiset.le_iff_count.mp surv_le y
            exact Multiset.count_pos.mp (Nat.lt_of_lt_of_le (Multiset.count_pos.mpr hy_surv) hle)
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hy_y𝕆))
      have hy𝔹_sub : y𝔹.toFinset ⊆ insert (z : Var) (y𝕆.toFinset ∪ y𝔹.toFinset) := by
        calc y𝔹.toFinset ⊆ y𝕆.toFinset ∪ y𝔹.toFinset := Finset.subset_union_right
          _ ⊆ insert (z : Var) (y𝕆.toFinset ∪ y𝔹.toFinset) := Finset.subset_insert _ _
      have hunion_sub : (Multiset.filter (fun y => y ∉ D.dedup ∨ y ∈ fv_of_fn_body (C β F (βₗ[z ↦ 𝕆]))) (z ::ₘ surv)).toFinset ∪ y𝔹.toFinset ⊆ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) := by
        exact Finset.union_subset hfilter_sub hy𝔹_sub
      apply wf_FV_sandwich _ hunion_sub F_wf
      · -- fv_of_fn_body F ⊆ filter.toFinset ∪ y𝔹.toFinset
        have hFV_sub := FV_sub_wf_context F_wf
        intro y hy
        rw [Finset.mem_union]
        have hy_ctx := hFV_sub hy
        rw [Finset.mem_insert] at hy_ctx
        rcases hy_ctx with rfl | hy_ctx
        · -- y = z
          left
          rw [Multiset.mem_toFinset]
          apply Multiset.mem_filter.mpr
          exact ⟨Multiset.mem_cons_self y surv, by
            rw [FV_C_eq_FV]
            exact Or.inr hy⟩
        · rcases Finset.mem_union.mp hy_ctx with hy_y𝕆 | hy_y𝔹
          · -- y ∈ y𝕆
            left
            rw [Multiset.mem_toFinset]
            have hy_y𝕆' : y ∈ y𝕆 := Multiset.mem_toFinset.mp hy_y𝕆
            have hy_surv : y ∈ surv := surv_covers y hy hy_y𝕆'
            apply Multiset.mem_filter.mpr
            constructor
            · exact Multiset.mem_cons_of_mem hy_surv
            · -- y ∉ D.dedup ∨ y ∈ fv_of_fn_body (C β F (βₗ[z ↦ 𝕆]))
              by_contra h_not
              push_neg at h_not
              obtain ⟨hy_dedup, hy_not_FV⟩ := h_not
              rw [FV_C_eq_FV] at hy_not_FV
              exact hy_not_FV hy
          · -- y ∈ y𝔹
            right
            exact Multiset.mem_toFinset.mpr (Multiset.mem_toFinset.mp hy_y𝔹)
  exact goal

/-- The `Linear.let` step for a translated application: `Oall` lists the owned parameter
positions (whose copies have been secured by the `inc`s emitted in front), `Ball` the
borrowed parameter positions, and `surv` the caller-owned variables handed on to the
continuation. -/
lemma C_app_let_step {β : Const → Var → LinType}
    {z : Var} {e : Expr} {F₂ : FnBody} {βₗ : Var → LinType}
    {Oall surv y𝔹 : Multiset Var} {Ball : List Var}
    (e_typed : β; (Oall {∶} 𝕆) + (((Ball : List Var) : Multiset Var) {∶} 𝔹) ⊩ ↑e ∷ 𝕆)
    (Ball_𝔹 : ∀ y ∈ Ball, βₗ y = 𝔹 → y ∈ y𝔹)
    (Ball_𝕆 : ∀ y ∈ Ball, βₗ y = 𝕆 → y ∈ surv)
    (F₂_typed : β; ((z ::ₘ surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ F₂ ∷ 𝕆) :
    β; ((Oall + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ (z ≔ᶠᵇ e;ᶠᵇ F₂) ∷ 𝕆 := by
  have hBBmem : ∀ w ∈ Ball.filter (fun y => βₗ y = 𝔹), w ∈ y𝔹 := by
    intro w hw
    exact Ball_𝔹 w (List.mem_of_mem_filter hw) (by simpa using List.of_mem_filter hw)
  have hBOmem : ∀ w ∈ Ball.filter (fun y => βₗ y = 𝕆), w ∈ surv := by
    intro w hw
    exact Ball_𝕆 w (List.mem_of_mem_filter hw) (by simpa using List.of_mem_filter hw)
  have hBall : ((Ball.filter (fun y => βₗ y = 𝔹) : List Var) : Multiset Var)
      + ((Ball.filter (fun y => βₗ y = 𝕆) : List Var) : Multiset Var)
      = ((Ball : List Var) : Multiset Var) := by
    rw [← Multiset.filter_coe, ← Multiset.filter_coe]
    have hcongr : Multiset.filter (fun y => βₗ y = 𝕆) (Ball : Multiset Var)
        = Multiset.filter (fun y => ¬ βₗ y = 𝔹) (Ball : Multiset Var) := by
      refine Multiset.filter_congr ?_
      intro y _
      constructor
      · intro h; rw [h]; decide
      · intro h; exact not_𝔹_iff_𝕆.mp h
    rw [hcongr]
    exact Multiset.filter_add_not _ _
  refine inductive_contract
    (ys := ((Ball.filter (fun y => βₗ y = 𝔹) : List Var) : Multiset Var)) ?_ ?_
  · intro w hw
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ (hBBmem w (by simpa using hw))))
  · have hsplit : (((Oall + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹))
        + (((Ball.filter (fun y => βₗ y = 𝔹) : List Var) : Multiset Var) {∶} 𝔹)
        = ((Oall {∶} 𝕆)
            + (((Ball.filter (fun y => βₗ y = 𝔹) : List Var) : Multiset Var) {∶} 𝔹))
          + ((surv {∶} 𝕆) + (y𝔹 {∶} 𝔹)) := by
      simp only [Multiset.map_add]
      simp [add_comm, add_left_comm, add_assoc]
    rw [hsplit]
    refine Linear.let (xs := Ball.filter (fun y => βₗ y = 𝕆)) ?_ ?_ ?_
    · intro tv htv
      simp only [Multiset.mem_coe, List.mem_map] at htv
      obtain ⟨w, hw, rfl⟩ := htv
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map_of_mem _ (hBOmem w hw)))
    · have hmap : (((Ball.filter (fun y => βₗ y = 𝔹) : List Var) : Multiset Var) {∶} 𝔹)
          + ((Ball.filter (fun y => βₗ y = 𝕆) : List Var) [∶] 𝔹)
          = (((Ball : List Var) : Multiset Var) {∶} 𝔹) := by
        rw [← hBall, Multiset.map_add]
        rfl
      rw [add_assoc, hmap]
      exact e_typed
    · have hcons : (z ∶ 𝕆) ::ₘ ((surv {∶} 𝕆) + (y𝔹 {∶} 𝔹))
          = ((z ::ₘ surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) := by
        simp [Multiset.map_cons, Multiset.cons_add]
      rw [hcons]
      exact F₂_typed


/-- The final step of the translation of a `let`-bound application: all arguments have
been processed, `D` records the variables for which a `dec` has been inserted into the
body, `Oall` the owned parameter positions and `Ball` the borrowed parameter positions,
and `surv` the variables owned by the caller that survive into the continuation. -/
lemma C_app_base {β : Const → Var → LinType} {δ : Program}
    {z : Var} {e : Expr} {F : FnBody} {βₗ : Var → LinType}
    {y𝕆 y𝔹 Oall surv : Multiset Var} {Ball D : List Var}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (z_used : z ∈ fv_of_fn_body F)
    (z_undef : z ∉ y𝕆.toFinset ∪ y𝔹.toFinset)
    (F_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) ⊢ʷᶠᵇ F)
    (e_typed : β; (Oall {∶} 𝕆) + (((Ball : List Var) : Multiset Var) {∶} 𝔹) ⊩ ↑e ∷ 𝕆)
    (Ball_mem : ∀ y ∈ Ball, (βₗ y = 𝕆 → y ∈ y𝕆) ∧ (βₗ y = 𝔹 → y ∈ y𝔹))
    (surv_le : surv ≤ y𝕆)
    (surv_fv : ∀ y ∈ surv, y ∈ fv_of_fn_body (dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ))
    (D_mem : ∀ w ∈ D, (βₗ w = 𝕆 → w ∈ surv) ∧ (βₗ w = 𝔹 → w ∈ y𝔹))
    (Ball_D : ∀ y ∈ Ball, y ∈ D)
    (surv_covers : ∀ w ∈ fv_of_fn_body F, w ∈ y𝕆 → w ∈ surv) :
    β; ((Oall + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
      (z ≔ᶠᵇ e;ᶠᵇ dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ) ∷ 𝕆 := by
  refine C_app_let_step (Ball := Ball) (βₗ := βₗ) e_typed ?_ ?_ ?_
  · exact fun y hy hb => (Ball_mem y hy).2 hb
  · exact fun y hy ho => (D_mem y (Ball_D y hy)).1 ho
  · exact C_app_dec_typing ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 z_used z_undef F_wf surv_le surv_fv
      D_mem surv_covers

/-- `dec_𝕆_var` never removes free variables. -/
lemma FV_sub_FV_dec_𝕆_var (y : Var) (G : FnBody) (βₗ : Var → LinType) :
    fv_of_fn_body G ⊆ fv_of_fn_body (dec_𝕆_var y G βₗ) := by
  unfold dec_𝕆_var
  split <;> simp [fv_of_fn_body]

/-- An owned variable is free in the body it is `dec`orated with. -/
lemma mem_FV_dec_𝕆_var {y : Var} (G : FnBody) {βₗ : Var → LinType} (h : βₗ y = 𝕆) :
    y ∈ fv_of_fn_body (dec_𝕆_var y G βₗ) := by
  by_cases hy : y ∈ fv_of_fn_body G
  · rw [dec_𝕆_var, if_neg (fun hp => hp.2 hy)]
    exact hy
  · rw [dec_𝕆_var, if_pos (And.intro h hy)]
    simp [fv_of_fn_body]

/-- A variable of the ambient context belongs to the owned or to the borrowed part
according to its type. -/
lemma mem_split_of_mem_union {βₗ : Var → LinType} {y𝕆 y𝔹 : Multiset Var} {w : Var}
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (hw : w ∈ y𝕆.toFinset ∪ y𝔹.toFinset) :
    (βₗ w = 𝕆 → w ∈ y𝕆) ∧ (βₗ w = 𝔹 → w ∈ y𝔹) := by
  rcases Finset.mem_union.mp hw with hw𝕆 | hw𝔹
  · exact ⟨fun _ => Multiset.mem_toFinset.mp hw𝕆, fun h => by simp_all⟩
  · exact ⟨fun h => by simp_all, fun _ => Multiset.mem_toFinset.mp hw𝔹⟩

/-- The induction over the argument list of a `let`-bound application. `pre` collects the
owned copies already secured for the arguments processed so far, `surv` the variables
owned by the caller that are still available, and `D` the variables for which a `dec` has
already been inserted into the body. -/
lemma C_app_gen {β : Const → Var → LinType} {δ : Program}
    {z : Var} {e : Expr} {F : FnBody} {βₗ : Var → LinType}
    {y𝕆 y𝔹 Oall : Multiset Var} {Ball : List Var}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (z_used : z ∈ fv_of_fn_body F)
    (z_undef : z ∉ y𝕆.toFinset ∪ y𝔹.toFinset)
    (F_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) ⊢ʷᶠᵇ F)
    (e_typed : β; (Oall {∶} 𝕆) + (((Ball : List Var) : Multiset Var) {∶} 𝔹) ⊩ ↑e ∷ 𝕆)
    (Ball_mem : ∀ y ∈ Ball, (βₗ y = 𝕆 → y ∈ y𝕆) ∧ (βₗ y = 𝔹 → y ∈ y𝔹)) :
    ∀ (args : List (Var × LinType)) (D : List Var) (pre surv : Multiset Var),
      pre + (((args.filter (fun p => p.2 = 𝕆)).map Prod.fst : List Var) : Multiset Var) = Oall →
      surv ≤ y𝕆 →
      (∀ y ∈ surv,
        y ∈ fv_of_fn_body (dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ) ∨ y ∈ args.map Prod.fst) →
      (∀ p ∈ args, (βₗ p.1 = 𝕆 → p.1 ∈ surv) ∧ (βₗ p.1 = 𝔹 → p.1 ∈ y𝔹)) →
      (∀ w ∈ D, (βₗ w = 𝕆 → w ∈ surv) ∧ (βₗ w = 𝔹 → w ∈ y𝔹)) →
      (∀ y ∈ Ball, y ∈ D ∨ (y, 𝔹) ∈ args) →
      (∀ w ∈ fv_of_fn_body F, w ∈ y𝕆 → w ∈ surv) →
      β; ((pre + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
        C_app args (z ≔ᶠᵇ e;ᶠᵇ dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ) βₗ ∷ 𝕆 := by
  intro args
  induction args with
  | nil =>
    intro D pre surv h_pre h_surv_le h_surv_used h_args_mem h_D h_Ball h_surv_covers
    simp only [List.filter_nil, List.map_nil, Multiset.coe_nil, add_zero] at h_pre
    subst h_pre
    simp only [C_app]
    refine C_app_base ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 z_used z_undef F_wf e_typed Ball_mem
      h_surv_le ?_ h_D ?_ h_surv_covers
    · intro y hy
      rcases h_surv_used y hy with h | h
      · exact h
      · simp at h
    · intro y hy
      rcases h_Ball y hy with h | h
      · exact h
      · simp at h
  | cons p rest ih_args =>
    intro D pre surv h_pre h_surv_le h_surv_used h_args_mem h_D h_Ball h_surv_covers
    obtain ⟨y, t⟩ := p
    have nd_surv : Multiset.Nodup surv := Multiset.nodup_of_le h_surv_le nd_y𝕆
    have hFVsub : fv_of_fn_body (C β F (βₗ[z ↦ 𝕆]))
        ⊆ fv_of_fn_body (dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ) := FV_sub_FV_dec_𝕆 _ _ _
    have hFVC : fv_of_fn_body (C β F (βₗ[z ↦ 𝕆])) = fv_of_fn_body F := FV_C_eq_FV _ _ _
    cases t with
    | 𝕆 =>
      have hmem_y : ((y, 𝕆) : Var × LinType) ∈ ((y, 𝕆) :: rest : List (Var × LinType)) :=
        List.mem_cons_self ..
      have h_pre' : (y ::ₘ pre)
          + (((rest.filter (fun p => p.2 = 𝕆)).map Prod.fst : List Var) : Multiset Var) = Oall := by
        rw [← h_pre]
        simp only [List.filter_cons, decide_true, if_true, List.map_cons]
        rw [← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]
      simp only [C_app, if_true, inc_𝕆_var]
      split_ifs
      · rename_i hcond
        obtain ⟨hy𝕆, hyV⟩ := hcond
        simp only [Finset.mem_union, List.mem_toFinset, not_or] at hyV
        obtain ⟨hy_rest, hy_body⟩ := hyV
        have hy_surv : y ∈ surv := (h_args_mem _ hmem_y).1 hy𝕆
        have hyD : y ∉ D := fun hD => hy_body (vars_sub_FV_dec_𝕆 D _ βₗ y hD hy𝕆)
        have hyF : y ∉ fv_of_fn_body F := fun hF => hy_body (hFVsub (hFVC ▸ hF))
        have hctx : pre + surv = (y ::ₘ pre) + surv.erase y := by
          conv_lhs => rw [← Multiset.cons_erase hy_surv]
          simp [Multiset.add_cons, Multiset.cons_add]
        rw [hctx]
        refine ih_args D (y ::ₘ pre) (surv.erase y) h_pre'
          ((Multiset.erase_le _ _).trans h_surv_le) ?_ ?_ ?_ ?_ ?_
        · intro w hw
          have hwne : w ≠ y := fun h => nd_surv.notMem_erase (h ▸ hw)
          rcases h_surv_used w (Multiset.mem_of_mem_erase hw) with h | h
          · exact Or.inl h
          · simp only [List.map_cons, List.mem_cons] at h
            rcases h with rfl | h
            · exact absurd rfl hwne
            · exact Or.inr h
        · intro q hq
          refine ⟨fun hq𝕆 => ?_, (h_args_mem q (List.mem_cons_of_mem _ hq)).2⟩
          have hqne : q.1 ≠ y := fun h => hy_rest (h ▸ List.mem_map_of_mem hq)
          exact Multiset.mem_erase_of_ne hqne |>.mpr ((h_args_mem q (List.mem_cons_of_mem _ hq)).1 hq𝕆)
        · intro w hw
          refine ⟨fun hw𝕆 => ?_, (h_D w hw).2⟩
          have hwne : w ≠ y := fun h => hyD (h ▸ hw)
          exact Multiset.mem_erase_of_ne hwne |>.mpr ((h_D w hw).1 hw𝕆)
        · intro w hw
          rcases h_Ball w hw with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h | h
            · exact absurd (congrArg Prod.snd h) (by simp)
            · exact Or.inr h
        · intro w hwF hw𝕆
          have hwne : w ≠ y := fun h => hyF (h ▸ hwF)
          exact Multiset.mem_erase_of_ne hwne |>.mpr (h_surv_covers w hwF hw𝕆)
      · rename_i hcond
        have hctx : ((y ∶ 𝕆) ::ₘ (((pre + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹)))
            = ((((y ::ₘ pre) + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹)) := by
          simp [Multiset.cons_add, Multiset.map_cons]
        have key : β; ((y ∶ 𝕆) ::ₘ (((pre + surv) {∶} 𝕆) + (y𝔹 {∶} 𝔹))) ⊩
            C_app rest (z ≔ᶠᵇ e;ᶠᵇ dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ) βₗ ∷ 𝕆 := by
          rw [hctx]
          refine ih_args D (y ::ₘ pre) surv h_pre' h_surv_le ?_ ?_ h_D ?_ h_surv_covers
          · intro w hw
            rcases h_surv_used w hw with h | h
            · exact Or.inl h
            · simp only [List.map_cons, List.mem_cons] at h
              rcases h with rfl | h
              · have hw𝕆 : βₗ w = 𝕆 := y𝕆_𝕆 w (Multiset.mem_of_le h_surv_le hw)
                push_neg at hcond
                rcases Finset.mem_union.mp (hcond hw𝕆) with h' | h'
                · exact Or.inr (List.mem_toFinset.mp h')
                · exact Or.inl h'
              · exact Or.inr h
          · exact fun q hq => h_args_mem q (List.mem_cons_of_mem _ hq)
          · intro w hw
            rcases h_Ball w hw with h | h
            · exact Or.inl h
            · rcases List.mem_cons.mp h with h | h
              · exact absurd (congrArg Prod.snd h) (by simp)
              · exact Or.inr h
        cases hβy : βₗ y with
        | 𝕆 =>
          have hy : y ∈ surv := (h_args_mem _ hmem_y).1 hβy
          exact Linear.inc_𝕆 (Multiset.mem_add.mpr (Or.inl
            (Multiset.mem_map_of_mem _ (Multiset.mem_add.mpr (Or.inr hy))))) key
        | 𝔹 =>
          have hy : y ∈ y𝔹 := (h_args_mem _ hmem_y).2 hβy
          exact Linear.inc_𝔹 (Multiset.mem_add.mpr (Or.inr
            (Multiset.mem_map_of_mem _ hy))) key
    | 𝔹 =>
      have hmem_y : ((y, 𝔹) : Var × LinType) ∈ ((y, 𝔹) :: rest : List (Var × LinType)) :=
        List.mem_cons_self ..
      have h_pre' : pre
          + (((rest.filter (fun p => p.2 = 𝕆)).map Prod.fst : List Var) : Multiset Var) = Oall := by
        rw [← h_pre]
        simp
      have hstep : dec_𝕆_var y (dec_𝕆 D (C β F (βₗ[z ↦ 𝕆])) βₗ) βₗ
          = dec_𝕆 (y :: D) (C β F (βₗ[z ↦ 𝕆])) βₗ := rfl
      simp only [C_app, if_neg (by decide : ¬((𝔹 : LinType) = 𝕆)), hstep]
      refine ih_args (y :: D) pre surv h_pre' h_surv_le ?_ ?_ ?_ ?_ h_surv_covers
      · intro w hw
        rcases h_surv_used w hw with h | h
        · exact Or.inl (FV_sub_FV_dec_𝕆_var y _ βₗ h)
        · simp only [List.map_cons, List.mem_cons] at h
          rcases h with rfl | h
          · have hw𝕆 : βₗ w = 𝕆 := y𝕆_𝕆 w (Multiset.mem_of_le h_surv_le hw)
            exact Or.inl (mem_FV_dec_𝕆_var _ hw𝕆)
          · exact Or.inr h
      · exact fun q hq => h_args_mem q (List.mem_cons_of_mem _ hq)
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨(h_args_mem _ hmem_y).1, (h_args_mem _ hmem_y).2⟩
        · exact h_D w hw
      · intro w hw
        rcases h_Ball w hw with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp h with h | h
          · have hwy : w = y := congrArg Prod.fst h
            exact Or.inl (hwy ▸ List.mem_cons_self ..)
          · exact Or.inr h

/-- Typing of the translation of a `let`-bound application, for an arbitrary expression
`e` whose free variables are exactly the variables of the argument list `args`. -/
lemma C_app_main {β : Const → Var → LinType} {δ : Program}
    {z : Var} {e : Expr} {F : FnBody} {βₗ : Var → LinType}
    {y𝕆 y𝔹 : Multiset Var} {args : List (Var × LinType)}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (z ≔ᶠᵇ e;ᶠᵇ F))
    (z_used : z ∈ fv_of_fn_body F)
    (z_undef : z ∉ y𝕆.toFinset ∪ y𝔹.toFinset)
    (F_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ insert z (y𝕆.toFinset ∪ y𝔹.toFinset) ⊢ʷᶠᵇ F)
    (e_fv_sub : ∀ w ∈ fv_of_expr e, w ∈ y𝕆.toFinset ∪ y𝔹.toFinset)
    (args_fv : ∀ p ∈ args, p.1 ∈ fv_of_expr e)
    (fv_args : ∀ w ∈ fv_of_expr e, w ∈ args.map Prod.fst)
    (e_typed : β;
      ((((args.filter (fun p => p.2 = 𝕆)).map Prod.fst : List Var) : Multiset Var) {∶} 𝕆)
      + ((((args.filter (fun p => p.2 = 𝔹)).map Prod.fst : List Var) : Multiset Var) {∶} 𝔹)
      ⊩ ↑e ∷ 𝕆) :
    β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
      C_app args (z ≔ᶠᵇ e;ᶠᵇ C β F (βₗ[z ↦ 𝕆])) βₗ ∷ 𝕆 := by
  have hBall : ∀ y ∈ (args.filter (fun p => p.2 = 𝔹)).map Prod.fst,
      (βₗ y = 𝕆 → y ∈ y𝕆) ∧ (βₗ y = 𝔹 → y ∈ y𝔹) := by
    intro w hw
    simp only [List.mem_map, List.mem_filter] at hw
    obtain ⟨q, ⟨hq, _⟩, rfl⟩ := hw
    exact mem_split_of_mem_union y𝕆_𝕆 y𝔹_𝔹 (e_fv_sub _ (args_fv q hq))
  have h := C_app_gen (β := β) (δ := δ) (z := z) (e := e) (F := F) (βₗ := βₗ)
    (y𝕆 := y𝕆) (y𝔹 := y𝔹)
    (Oall := (((args.filter (fun p => p.2 = 𝕆)).map Prod.fst : List Var) : Multiset Var))
    (Ball := (args.filter (fun p => p.2 = 𝔹)).map Prod.fst)
    ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 z_used z_undef F_wf e_typed hBall
    args [] 0 y𝕆 (by simp) le_rfl ?_ ?_ (by simp) ?_ (fun _ _ h => h)
  · simpa only [dec_𝕆, List.foldr_nil, zero_add] using h
  · intro w hw
    simp only [dec_𝕆, List.foldr_nil, FV_C_eq_FV]
    have := y𝕆_sub_FV (Multiset.mem_toFinset.mpr hw)
    simp only [fv_of_fn_body, Finset.mem_union, Finset.mem_erase] at this
    rcases this with h' | ⟨_, h'⟩
    · exact Or.inr (fv_args w h')
    · exact Or.inl h'
  · intro q hq
    exact mem_split_of_mem_union y𝕆_𝕆 y𝔹_𝔹 (e_fv_sub _ (args_fv q hq))
  · intro w hw
    simp only [List.mem_map, List.mem_filter] at hw
    obtain ⟨q, ⟨hq, hq𝔹⟩, rfl⟩ := hw
    right
    have hq' : q = (q.1, 𝔹) := by
      obtain ⟨a, b⟩ := q
      simp_all
    exact hq' ▸ hq


end CAppGeneral


lemma rc_let_const_app_full_aux {β : Const → Var → LinType} {δ : Program}
    {z : Var} {F : FnBody} {c : Const} {ys : List Var}
    {y𝕆 y𝔹 : Multiset Var} {βₗ : Var → LinType}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (z ≔ᶠᵇ c⟦ys…⟧;ᶠᵇ F))
    (wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ (z ≔ᶠᵇ c⟦ys…⟧;ᶠᵇ F)) :
    β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
      C_app (ys.map (fun y => (y, β c y)))
        (z ≔ᶠᵇ c⟦ys…⟧;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ ∷ 𝕆 := by
  cases wf with
  | let_const_app_full ys_def arity_eq z_used z_undef F_wf =>
    refine C_app_main (δ := δ) ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV z_used z_undef F_wf
      (fun w hw => ys_def hw) ?_ ?_ ?_
    · intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨v, hv, rfl⟩ := hp
      exact List.mem_toFinset.mpr hv
    · intro w hw
      simp only [fv_of_expr, List.mem_toFinset] at hw
      simpa using hw
    · rw [filter_map_args, filter_map_args, ← typed_list_split]
      exact Linear.const_app_full ys c

lemma rc_let_const_app_part_aux {β : Const → Var → LinType} {δ : Program}
    {z : Var} {F : FnBody} {c : Const} {ys : List Var}
    {y𝕆 y𝔹 : Multiset Var} {βₗ : Var → LinType}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹)
    (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (z ≔ᶠᵇ c⟦ys…, _⟧;ᶠᵇ F))
    (wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ (z ≔ᶠᵇ c⟦ys…, _⟧;ᶠᵇ F)) :
    β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
      C_app (ys.map (fun y => (y, β c y)))
        (z ≔ᶠᵇ c⟦ys…, _⟧;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ ∷ 𝕆 := by
  cases wf with
  | let_const_app_part ys_def no_𝔹_var z_used z_undef F_wf =>
    have h𝕆 : ∀ v : Var, β c v = 𝕆 := fun v => not_𝔹_iff_𝕆.mp (no_𝔹_var v)
    refine C_app_main (δ := δ) ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV z_used z_undef F_wf
      (fun w hw => ys_def hw) ?_ ?_ ?_
    · intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨v, hv, rfl⟩ := hp
      exact List.mem_toFinset.mpr hv
    · intro w hw
      simp only [fv_of_expr, List.mem_toFinset] at hw
      simpa using hw
    · rw [filter_map_args, filter_map_args]
      rw [List.filter_eq_self.mpr (by simp [h𝕆]), List.filter_eq_nil_iff.mpr (by simp [h𝕆])]
      simpa using Linear.const_app_part ys c

lemma rc_let_var_app_aux {β : Const → Var → LinType} {δ : Program}
    {z x y : Var} {F : FnBody} {y𝕆 y𝔹 : Multiset Var} {βₗ : Var → LinType}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ v ∈ y𝕆, βₗ v = 𝕆) (y𝔹_𝔹 : ∀ v ∈ y𝔹, βₗ v = 𝔹)
    (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (z ≔ᶠᵇ x⟦y⟧;ᶠᵇ F))
    (wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ (z ≔ᶠᵇ x⟦y⟧;ᶠᵇ F)) :
    β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
      C_app [(x, 𝕆), (y, 𝕆)]
        (z ≔ᶠᵇ x⟦y⟧;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ ∷ 𝕆 := by
  cases wf with
  | let_var_app x_def y_def z_used z_undef F_wf =>
    refine C_app_main (δ := δ) ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV z_used z_undef F_wf ?_ ?_ ?_ ?_
    · intro w hw
      simp only [fv_of_expr, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact x_def
      · exact y_def
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [fv_of_expr]
    · intro w hw
      simp only [fv_of_expr, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp
    · simpa using Linear.var_app x y

lemma rc_let_ctor_aux {β : Const → Var → LinType} {δ : Program}
    {z : Var} {i : Cnstr} {ys : List Var} {F : FnBody}
    {y𝕆 y𝔹 : Multiset Var} {βₗ : Var → LinType}
    (ih : ∀ {y𝕆 y𝔹 : Multiset Var},
      Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 → ∀ (βₗ : Var → LinType),
      (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
      (y𝕆.toFinset ⊆ fv_of_fn_body F) →
      (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
      β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆)
    (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
    (y𝕆_𝕆 : ∀ v ∈ y𝕆, βₗ v = 𝕆) (y𝔹_𝔹 : ∀ v ∈ y𝔹, βₗ v = 𝔹)
    (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (z ≔ᶠᵇ ⟪ys⟫i;ᶠᵇ F))
    (wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ (z ≔ᶠᵇ ⟪ys⟫i;ᶠᵇ F)) :
    β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩
      C_app (ys.map (fun y => (y, 𝕆)))
        (z ≔ᶠᵇ ⟪ys⟫i;ᶠᵇ C β F (Function.update βₗ z 𝕆)) βₗ ∷ 𝕆 := by
  cases wf with
  | let_ctor _ ys_def z_used z_undef F_wf =>
    refine C_app_main (δ := δ) (args := ys.map (fun y => (y, (fun _ : Var => (𝕆 : LinType)) y)))
      ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV z_used z_undef F_wf
      (fun w hw => ys_def hw) ?_ ?_ ?_
    · intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨v, hv, rfl⟩ := hp
      exact List.mem_toFinset.mpr hv
    · intro w hw
      simp only [fv_of_expr, List.mem_toFinset] at hw
      simpa using hw
    · rw [filter_map_args, filter_map_args]
      rw [List.filter_eq_self.mpr (by simp), List.filter_eq_nil_iff.mpr (by simp)]
      simpa using Linear.ctor_app ys i


theorem rc_insertion_correctness' {β : Const → Var → LinType} {δ : Program} {c : Const}
  {y𝕆 y𝔹 : Multiset Var}
  (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, β c y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, β c y = 𝔹)
  (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (δ c).fn_body) (wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ (δ c).fn_body)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β ((δ c).fn_body) (β c) ∷ 𝕆 :=
by
  generalize h_β : β c = βₗ at y𝕆_𝕆 y𝔹_𝔹 ⊢
  clear h_β
  simp only [Finset.subset_iff] at y𝕆_sub_FV
  generalize h_F : (δ c).fn_body = F at y𝕆_sub_FV wf ⊢
  clear h_F
  induction F using FnBody.rec (motive_2 := fun Fs => ∀ F ∈ Fs, ∀ (y𝕆 y𝔹 : Multiset Var) (βₗ : Var → LinType),
    Multiset.Nodup y𝕆 → Multiset.Nodup y𝔹 →
    (∀ y ∈ y𝕆, βₗ y = 𝕆) → (∀ y ∈ y𝔹, βₗ y = 𝔹) →
    (y𝕆.toFinset ⊆ fv_of_fn_body F) →
    (β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ F) →
    β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β F βₗ ∷ 𝕆) generalizing y𝕆 y𝔹 βₗ
  case ret x  =>
    unfold C
    unfold fv_of_fn_body at y𝕆_sub_FV
    cases wf with | ret wf_x_def =>
    simp only [Finset.mem_union, Multiset.mem_toFinset] at wf_x_def
    unfold inc_𝕆_var
    cases wf_x_def with
    | inl wf_x_def =>
      have : βₗ x = 𝕆 ∧ x ∉ (∅ : Finset Var) := ⟨y𝕆_𝕆 x wf_x_def, Finset.notMem_empty x⟩
      rw [if_pos this]
      have : y𝕆 = x ::ₘ 0 := by
        apply (nd_y𝕆.ext (Multiset.nodup_singleton x)).mpr
        intro a
        simp only [Multiset.mem_singleton]
        constructor
        · intro h
          exact Finset.mem_singleton.mp (y𝕆_sub_FV (Multiset.mem_toFinset.mpr h))
        · intro h
          rwa [h]
      rw [this]
      simp only [zero_add, Multiset.map_cons, Multiset.cons_add, Multiset.map_zero]
      rw [← Multiset.singleton_add]
      apply inductive_weakening
      apply Linear.ret
    | inr wf_x_def =>
      have : ¬(βₗ x = 𝕆 ∧ x ∉ (∅ : Finset Var)) := by
        simp only [not_and, not_not]
        intro h
        rw [y𝔹_𝔹 x wf_x_def] at h
        contradiction
      rw [if_neg this]
      apply Linear.inc_𝔹
      · apply Multiset.mem_add.mpr
        apply Or.inr
        exact Multiset.mem_map_of_mem _ wf_x_def
      have : y𝕆 = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intros y y_in_y𝕆
        have y_eq_x := Finset.mem_singleton.mp (y𝕆_sub_FV (Multiset.mem_toFinset.mpr y_in_y𝕆))
        have x_in_y𝕆 := y_eq_x ▸ y_in_y𝕆
        have h_𝕆 := y𝕆_𝕆 x x_in_y𝕆
        have h_𝔹 := y𝔹_𝔹 x wf_x_def
        rw [h_𝔹] at h_𝕆
        contradiction
      simp only [this, zero_add, Multiset.map_zero]
      rw [← Multiset.singleton_add]
      apply inductive_weakening
      apply Linear.ret
  case let_ y e F ih  =>
    have y𝕆_sub_FV' : ∀ ⦃x : Var⦄, x ∈ y𝕆 → x ∈ fv_of_fn_body (y ≔ᶠᵇ e;ᶠᵇ F) := by
      intros x x_in
      exact y𝕆_sub_FV (Multiset.mem_toFinset.mpr x_in)
    cases e with
    | proj i x =>
      unfold C
      split_ifs with h
      · have x_in_y𝕆 : x ∈ y𝕆 := by
          let h_sub := FV_sub_wf_context wf
          have h_free : x ∈ fv_of_fn_body (y ≔ᶠᵇ x[ᵉi];ᶠᵇ F) := by
            simp [fv_of_fn_body, fv_of_expr]
          have h_in_union := h_sub h_free
          simp only [Finset.mem_union, Multiset.mem_toFinset] at h_in_union
          cases h_in_union with
          | inl h_in => exact h_in
          | inr h_in =>
            have h_ty := y𝔹_𝔹 x h_in
            rw [h_ty] at h
            contradiction
        apply Linear.proj_𝕆
        · simpa
        unfold dec_𝕆_var
        split_ifs with h_1
        · rcases Multiset.exists_cons_of_mem x_in_y𝕆 with ⟨y𝕆', y𝕆_def⟩
          rw [y𝕆_def] at nd_y𝕆 y𝕆_𝕆 ⊢
          simp only [Multiset.map_cons, Multiset.cons_add]
          rw [Multiset.cons_swap]
          apply Linear.dec
          rw [←Multiset.cons_add]
          rw [←Multiset.map_cons (· ∶ 𝕆)]
          refine ih ?_ nd_y𝔹 (Function.update βₗ y 𝕆) ?_ ?_ ?_ ?_
          · cases wf
            rename_i z_undef x_def z_used F_wf
            rw [y𝕆_def] at z_undef
            simp only [Multiset.nodup_cons]
            simp_all only [Multiset.mem_toFinset, implies_true, true_and, Finset.mem_union, not_or, true_or]
            obtain ⟨left, right⟩ := z_undef
            apply And.intro
            · apply Aesop.BuiltinRules.not_intro
              intro a
              exact left (Multiset.mem_cons_of_mem a)
            · exact (Multiset.nodup_cons.mp nd_y𝕆).2
          · intros z z_in_y𝕆'
            rw [Multiset.mem_cons] at z_in_y𝕆'
            cases z_in_y𝕆' with
            | inl h =>
              subst h
              simp only [Function.update_self]
            | inr h_2 =>
              cases wf
              rename_i z_undef x_def z_used F_wf
              rw [y𝕆_def] at z_undef
              simp_all only [Finset.mem_union, Multiset.mem_toFinset, not_or]
              obtain ⟨left, right⟩ := z_undef
              have h_neq : z ≠ y := by
                intro h_eq
                rw [h_eq] at h_2
                exact left (Multiset.mem_cons_of_mem h_2)
              rw [Function.update_of_ne h_neq]
              exact y𝕆_𝕆 z (Multiset.mem_cons_of_mem h_2)
          · intros z z_in_y𝔹
            by_cases z = y
            · cases wf
              grind only [= Finset.mem_union, = Multiset.mem_toFinset]
            · cases wf
              grind
          · cases wf
            rename_i z_undef x_def z_used F_wf
            rw [y𝕆_def] at z_undef F_wf
            intro x_1 a
            simp_all only [Multiset.mem_toFinset, true_and, Finset.mem_union, not_or, true_or,
              Multiset.toFinset_cons, Finset.mem_insert]
            obtain ⟨left, right⟩ := z_undef
            cases a with
            | inl h =>
              subst h
              simp_all only
            | inr h_2 =>
              have h_fv := y𝕆_sub_FV (Or.inr h_2)
              simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at h_fv
              cases h_fv with
              | inl h_eq =>
                subst h_eq
                have h_not : x_1 ∉ y𝕆' := (Multiset.nodup_cons.mp nd_y𝕆).1
                contradiction
              | inr h_erase =>
                exact h_erase.2
          · cases wf
            simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union,
              Finset.mem_singleton, Finset.mem_erase] at y𝕆_sub_FV
            rename_i v z_undef z_used F_wf
            rw [y𝕆_def] at z_undef F_wf
            simp_all only [Multiset.mem_toFinset, true_and, ne_eq, Multiset.toFinset_cons, Finset.insert_union]
            have left_not_x : y ≠ x := by
              intro h_eq
              subst h_eq
              exact v (Finset.mem_insert_self y (y𝕆'.toFinset ∪ y𝔹.toFinset))
            have right_not_y𝕆' : y ∉ y𝕆'.toFinset ∪ y𝔹.toFinset := by
              intro h_mem
              exact v (Finset.mem_insert_of_mem h_mem)
            have h_high : insert y (y𝕆'.toFinset ∪ y𝔹.toFinset) ⊆ insert y (insert x (y𝕆'.toFinset ∪ y𝔹.toFinset)) := by
              intro u hu
              simp only [Finset.mem_insert, Finset.mem_union] at hu ⊢
              rcases hu with rfl | hu | hu
              · exact Or.inl rfl
              · exact Or.inr (Or.inr (Or.inl hu))
              · exact Or.inr (Or.inr (Or.inr hu))
            have h_low : fv_of_fn_body F ⊆ insert y (y𝕆'.toFinset ∪ y𝔹.toFinset) := by
              intro u hu
              have hu_sub := FV_sub_wf_context F_wf hu
              simp only [Finset.mem_insert, Finset.mem_union] at hu_sub ⊢
              rcases hu_sub with rfl | rfl | hu_sub | hu_sub
              · exact Or.inl rfl
              · have h_C : u ∉ fv_of_fn_body (C β F (Function.update βₗ y 𝕆)) := h_1
                rw [FV_C_eq_FV] at h_C
                contradiction
              · exact Or.inr (Or.inl hu_sub)
              · exact Or.inr (Or.inr hu_sub)
            exact wf_FV_sandwich h_low h_high F_wf
        · cases wf
          rename_i y_undef x_def y_used F_wf
          have h_eq : (y ∶ 𝕆) ::ₘ ((y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹)) = ((y ::ₘ y𝕆) {∶} 𝕆) + (y𝔹 {∶} 𝔹) := by
            simp only [Multiset.map_cons, Multiset.cons_add]
          rw [h_eq]
          refine ih ?_ nd_y𝔹 (Function.update βₗ y 𝕆) ?_ ?_ ?_ ?_
          · rw [Multiset.nodup_cons]
            apply And.intro
            · intro y_in_y𝕆
              have h_mem : y ∈ y𝕆.toFinset ∪ y𝔹.toFinset := by
                simp only [Finset.mem_union, Multiset.mem_toFinset]
                exact Or.inl y_in_y𝕆
              exact y_undef h_mem
            · exact nd_y𝕆
          · intros z_1 z_in_y𝕆'
            rw [Multiset.mem_cons] at z_in_y𝕆'
            cases z_in_y𝕆' with
            | inl h_eq =>
              subst h_eq
              simp only [Function.update_self]
            | inr h_2 =>
              have h_neq : z_1 ≠ y := by
                intro h_eq
                rw [h_eq] at h_2
                have h_mem : y ∈ y𝕆.toFinset ∪ y𝔹.toFinset := by
                  simp only [Finset.mem_union, Multiset.mem_toFinset]
                  exact Or.inl h_2
                exact y_undef h_mem
              rw [Function.update_of_ne h_neq]
              exact y𝕆_𝕆 z_1 h_2
          · intros z_1 z_in_y𝔹
            by_cases h_eq : z_1 = y
            · rw [h_eq] at z_in_y𝔹
              have h_mem : y ∈ y𝕆.toFinset ∪ y𝔹.toFinset := by
                simp only [Finset.mem_union, Multiset.mem_toFinset]
                exact Or.inr z_in_y𝔹
              exact False.elim (y_undef h_mem)
            · rw [Function.update_of_ne h_eq]
              exact y𝔹_𝔹 z_1 z_in_y𝔹
          · intro v_in a
            rw [Multiset.toFinset_cons, Finset.mem_insert] at a
            cases a with
            | inl h_eq =>
              subst h_eq
              exact y_used
            | inr h_2 =>
              have h_fv := y𝕆_sub_FV h_2
              simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at h_fv
              rcases h_fv with h_eq | h_erase
              · subst h_eq
                have h_eq_𝕆 : βₗ v_in = 𝕆 := y𝕆_𝕆 v_in (Multiset.mem_toFinset.mp h_2)
                have h_not : v_in ∈ fv_of_fn_body F := by
                  by_contra h_not_in
                  have h_C : v_in ∉ fv_of_fn_body (C β F (Function.update βₗ y 𝕆)) := by
                    rw [FV_C_eq_FV]
                    exact h_not_in
                  exact h_1 ⟨h_eq_𝕆, h_C⟩
                exact h_not
              · exact h_erase.2
          · have h_wf_eq : insert y (y𝕆.toFinset ∪ y𝔹.toFinset) = (y ::ₘ y𝕆).toFinset ∪ y𝔹.toFinset := by
              simp only [Multiset.toFinset_cons, Finset.insert_union]
            rw [←h_wf_eq]
            exact F_wf
      · cases wf
        rename_i y_undef x_def y_used F_wf
        apply Linear.proj_𝔹
        · simp only [Finset.mem_union, Multiset.mem_toFinset] at x_def
          cases x_def with
          | inl h_in =>
            have : βₗ x = 𝕆 := y𝕆_𝕆 x h_in
            contradiction
          | inr h_in =>
            simp only [Multiset.mem_add]
            apply Or.inr
            rw [Multiset.mem_map]
            exact ⟨x, h_in, rfl⟩
        have h_eq : (y ∶ 𝔹) ::ₘ ((y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹)) = (y𝕆 {∶} 𝕆) + ((y ::ₘ y𝔹) {∶} 𝔹) := by
          simp only [Multiset.map_cons, Multiset.add_comm, Multiset.cons_add]
        rw [h_eq]
        refine ih nd_y𝕆 ?_ (Function.update βₗ y 𝔹) ?_ ?_ ?_ ?_
        · rw [Multiset.nodup_cons]
          apply And.intro
          · intro y_in_y𝔹
            have h_mem : y ∈ y𝕆.toFinset ∪ y𝔹.toFinset := by
              simp only [Finset.mem_union, Multiset.mem_toFinset]
              exact Or.inr y_in_y𝔹
            exact y_undef h_mem
          · exact nd_y𝔹
        · intros z_1 z_in_y𝕆
          have h_neq : z_1 ≠ y := by
            intro h_eq
            rw [h_eq] at z_in_y𝕆
            have h_mem : y ∈ y𝕆.toFinset ∪ y𝔹.toFinset := by
              simp only [Finset.mem_union, Multiset.mem_toFinset]
              exact Or.inl z_in_y𝕆
            exact y_undef h_mem
          rw [Function.update_of_ne h_neq]
          exact y𝕆_𝕆 z_1 z_in_y𝕆
        · intros z_1 z_in_y𝔹'
          by_cases h_eq : z_1 = y
          · subst h_eq
            simp only [Function.update_self]
          · rw [Function.update_of_ne h_eq]
            rw [Multiset.mem_cons] at z_in_y𝔹'
            cases z_in_y𝔹' with
            | inl h_self => contradiction
            | inr h_mem => exact y𝔹_𝔹 z_1 h_mem
        · intro v_in a
          have h_in_toFinset : v_in ∈ y𝕆.toFinset := a
          have h_fv := y𝕆_sub_FV h_in_toFinset
          simp only [fv_of_fn_body, fv_of_expr, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at h_fv
          cases h_fv with
          | inl h_eq =>
            subst h_eq
            have : βₗ v_in = 𝕆 := y𝕆_𝕆 v_in (Multiset.mem_toFinset.mp a)
            contradiction
          | inr h_erase =>
            exact h_erase.2
        · have h_wf_eq : insert y (y𝕆.toFinset ∪ y𝔹.toFinset) = y𝕆.toFinset ∪ (y ::ₘ y𝔹).toFinset := by
            simp only [Multiset.toFinset_cons, Finset.union_insert]
          rw [←h_wf_eq]
          exact F_wf
    | const_app_full c' ys =>
      simp only [C]
      exact rc_let_const_app_full_aux ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV wf
    | const_app_part c' ys =>
      simp only [C]
      exact rc_let_const_app_part_aux ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV wf
    | var_app x z =>
      simp only [C]
      exact rc_let_var_app_aux ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV wf
    | ctor i ys =>
      simp only [C]
      exact rc_let_ctor_aux ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 y𝕆_sub_FV wf
  case «case» x Fs ih  =>
    unfold C
    have FV_sub_y𝕆_y𝔹 : (fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).val ⊆ y𝕆 + y𝔹 := by
      let h_sub := FV_sub_wf_context wf
      intros z z_in
      have h_in_union := h_sub z_in
      simp only [Finset.mem_union, Multiset.mem_toFinset] at h_in_union
      simp only [Multiset.mem_add]
      exact h_in_union
    cases wf with | case wf_x_def Fs_wf =>
    simp only [Finset.mem_union, Multiset.mem_toFinset] at wf_x_def
    cases wf_x_def
    apply Linear.case_𝕆
    · simpa
    swap
    apply Linear.case_𝔹
    · simpa
    · intro F a
      simp_all only [Multiset.mem_toFinset, List.mem_map]
      obtain ⟨w, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      subst right
      have h_sub : y𝕆 ⊆ ↑((fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).sort LE.le) := by
        intro z z_in
        rw [Multiset.mem_coe, Finset.mem_sort]
        exact y𝕆_sub_FV z_in
      have h_sub_vars : ↑((fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).sort LE.le) ⊆ y𝕆 + y𝔹 := by
        intro z z_in
        rw [Multiset.mem_coe, Finset.mem_sort] at z_in
        exact FV_sub_y𝕆_y𝔹 z_in
      have h_nodup : List.Nodup ((fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).sort LE.le) := Finset.sort_nodup _ _
      apply inductive_dec h_sub h_sub_vars h_nodup y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹
      let y𝕆' := Multiset.filter (fun y => y ∈ fv_of_fn_body (C β w βₗ)) y𝕆
      have nd_y𝕆' : y𝕆'.Nodup := Multiset.Nodup.filter _ nd_y𝕆
      have y𝕆'_𝕆 : ∀ y ∈ y𝕆', βₗ y = 𝕆 := by
        intros y hy
        exact y𝕆_𝕆 y (Multiset.mem_of_mem_filter hy)
      have y𝕆'_sub : y𝕆'.toFinset ⊆ fv_of_fn_body w := by
        intro z z_in
        rw [Multiset.mem_toFinset, Multiset.mem_filter] at z_in
        rw [FV_C_eq_FV] at z_in
        exact z_in.2
      have h_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆'.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ w := by
        have h_low : fv_of_fn_body w ⊆ y𝕆'.toFinset ∪ y𝔹.toFinset := by
          intro z z_in
          have h_mem := FV_sub_wf_context (Fs_wf w left) z_in
          simp only [Finset.mem_union] at h_mem ⊢
          rcases h_mem with h_mem | h_mem
          · apply Or.inl
            rw [Multiset.mem_toFinset, Multiset.mem_filter, ←Multiset.mem_toFinset]
            exact ⟨h_mem, by rw [FV_C_eq_FV]; exact z_in⟩
          · exact Or.inr h_mem
        have h_high : y𝕆'.toFinset ∪ y𝔹.toFinset ⊆ y𝕆.toFinset ∪ y𝔹.toFinset := by
          intro z z_in
          simp only [Finset.mem_union] at z_in ⊢
          rcases z_in with z_in | h_mem
          · apply Or.inl
            rw [Multiset.mem_toFinset, Multiset.mem_filter] at z_in
            rw [Multiset.mem_toFinset]
            exact z_in.1
          · exact Or.inr h_mem
        exact wf_FV_sandwich h_low h_high (Fs_wf w left)
      exact ih w left y𝕆' y𝔹 βₗ nd_y𝕆' nd_y𝔹 y𝕆'_𝕆 y𝔹_𝔹 y𝕆'_sub h_wf
    · intro F a
      simp_all only [Multiset.mem_toFinset, List.mem_map]
      obtain ⟨w, h_1⟩ := a
      obtain ⟨left, right⟩ := h_1
      subst right
      have h_sub : y𝕆 ⊆ ↑((fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).sort LE.le) := by
        intro z z_in
        rw [Multiset.mem_coe, Finset.mem_sort]
        exact y𝕆_sub_FV z_in
      have h_sub_vars : ↑((fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).sort LE.le) ⊆ y𝕆 + y𝔹 := by
        intro z z_in
        rw [Multiset.mem_coe, Finset.mem_sort] at z_in
        exact FV_sub_y𝕆_y𝔹 z_in
      have h_nodup : List.Nodup ((fv_of_fn_body (caseᶠᵇ x ofᶠᵇ Fs)).sort LE.le) := Finset.sort_nodup _ _
      apply inductive_dec h_sub h_sub_vars h_nodup y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹
      let y𝕆' := Multiset.filter (fun y => y ∈ fv_of_fn_body (C β w βₗ)) y𝕆
      have nd_y𝕆' : y𝕆'.Nodup := Multiset.Nodup.filter _ nd_y𝕆
      have y𝕆'_𝕆 : ∀ y ∈ y𝕆', βₗ y = 𝕆 := by
        intros y hy
        exact y𝕆_𝕆 y (Multiset.mem_of_mem_filter hy)
      have y𝕆'_sub : y𝕆'.toFinset ⊆ fv_of_fn_body w := by
        intro z z_in
        rw [Multiset.mem_toFinset, Multiset.mem_filter] at z_in
        rw [FV_C_eq_FV] at z_in
        exact z_in.2
      have h_wf : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆'.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ w := by
        have h_low : fv_of_fn_body w ⊆ y𝕆'.toFinset ∪ y𝔹.toFinset := by
          intro z z_in
          have h_mem := FV_sub_wf_context (Fs_wf w left) z_in
          simp only [Finset.mem_union] at h_mem ⊢
          rcases h_mem with h_mem | h_mem
          · apply Or.inl
            rw [Multiset.mem_toFinset, Multiset.mem_filter, ←Multiset.mem_toFinset]
            exact ⟨h_mem, by rw [FV_C_eq_FV]; exact z_in⟩
          · exact Or.inr h_mem
        have h_high : y𝕆'.toFinset ∪ y𝔹.toFinset ⊆ y𝕆.toFinset ∪ y𝔹.toFinset := by
          intro z z_in
          simp only [Finset.mem_union] at z_in ⊢
          rcases z_in with z_in | h_mem
          · apply Or.inl
            rw [Multiset.mem_toFinset, Multiset.mem_filter] at z_in
            rw [Multiset.mem_toFinset]
            exact z_in.1
          · exact Or.inr h_mem
        exact wf_FV_sandwich h_low h_high (Fs_wf w left)
      exact ih w left y𝕆' y𝔹 βₗ nd_y𝕆' nd_y𝔹 y𝕆'_𝕆 y𝔹_𝔹 y𝕆'_sub h_wf
  case «inc» x F ih  =>
    cases wf
  case «dec» x F ih  =>
    cases wf
  case nil =>
    simp_all only [List.not_mem_nil]
  case cons head tail ih_head ih_tail =>
    rename_i head_ih tail_ih F a y𝕆 y𝔹 βₗ a_1 a_2
    simp_all only [Multiset.mem_toFinset, List.mem_cons]
    cases a with
    | inl h =>
      subst h
      apply @head_ih
      · simp_all only
      · simp_all only
      · intro y a
        simp_all only
      · intro y a
        simp_all only
      · intro x a
        apply ih_head
        simp_all only [Multiset.mem_toFinset]
      · simp_all only
    | inr h_1 => simp_all only [implies_true]

theorem rc_insertion_correctness (β : Const → Var → LinType) (δ : Program) (wf : β ⊢ᵖʷ δ) : β ⊩ᵖ C_prog β δ := by
  cases wf with
  | program const_wf =>
  constructor
  intro c
  replace const_wf := const_wf c
  cases const_wf with
  | const wf nd_ys =>
  constructor
  simp only [C_prog]
  let ys := (δ c).ys
  let Γ := (↑(List.map (fun (y : Var) => y ∶ β c y) ys) : Multiset TypedVar)
  let y𝕆 := List.filter (fun y => β c y = 𝕆) ys
  let y𝔹 := List.filter (fun y => β c y = 𝔹) ys
  have y𝕆_𝕆 : ∀ y ∈ y𝕆, β c y = 𝕆 := by
    intros y hy
    simp only [y𝕆, List.mem_filter, decide_eq_true_iff] at hy
    exact hy.2
  have y𝔹_𝔹 : ∀ y ∈ y𝔹, β c y = 𝔹 := by
    intros y hy
    simp only [y𝔹, List.mem_filter, decide_eq_true_iff] at hy
    exact hy.2
  have y𝕆_sub_ys : (y𝕆 : Multiset Var) ⊆ ↑ys := by
    intro y hy
    simp only [Multiset.mem_coe, y𝕆, List.mem_filter, decide_eq_true_iff] at hy
    exact hy.1
  have y𝔹_sub_ys : (y𝔹 : Multiset Var) ⊆ ↑ys := by
    intro y hy
    simp only [Multiset.mem_coe, y𝔹, List.mem_filter, decide_eq_true_iff] at hy
    exact hy.1
  have ys_𝕆_sub_y𝕆 : ∀ y ∈ ys, β c y = 𝕆 → y ∈ y𝕆 := by
    intros y hy hty
    simp only [y𝕆, List.mem_filter, decide_eq_true_iff]
    exact ⟨hy, hty⟩
  have ys_𝔹_sub_y𝔹 : ∀ y ∈ ys, β c y = 𝔹 → y ∈ y𝔹 := by
    intros y hy hty
    simp only [y𝔹, List.mem_filter, decide_eq_true_iff]
    exact ⟨hy, hty⟩
  have nd_y𝕆 : Multiset.Nodup (y𝕆 : Multiset Var) := by
    rw [Multiset.coe_nodup]
    exact List.Nodup.filter _ nd_ys
  have nd_y𝔹 : Multiset.Nodup (y𝔹 : Multiset Var) := by
    rw [Multiset.coe_nodup]
    exact List.Nodup.filter _ nd_ys
  have ys_subdiv : ↑ys = (y𝕆 : Multiset Var) + (y𝔹 : Multiset Var) := by
    have this_subdiv : ∀ y ∈ (↑ys : Multiset Var), β c y = 𝔹 ↔ β c y ≠ 𝕆 := by
      intros y y_in_ys
      cases β c y <;> simp
    simp only [y𝕆, y𝔹, ← Multiset.filter_coe]
    have h_filter : Multiset.filter (fun y => β c y = 𝔹) ↑ys = Multiset.filter (fun y => β c y ≠ 𝕆) ↑ys := by
      apply Multiset.filter_congr
      intros y y_in_ys
      exact this_subdiv y y_in_ys
    rw [h_filter]
    exact (Multiset.filter_add_not (fun y => β c y = 𝕆) ↑ys).symm
  have Γ_subdiv : ↑(List.map (fun (y : Var) => y ∶ β c y) ys) = (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) := by
    have : ↑(List.map (fun (y : Var) => y ∶ β c y) ys) = Multiset.map (fun (y : Var) => y ∶ β c y) ↑ys := rfl
    rw [this]
    rw [ys_subdiv]
    simp only [Multiset.map_add]
    have : ∀ (τ : LinType) (yτ : Multiset Var), (∀ y ∈ yτ, β c y = τ) →
      ∀ y ∈ yτ, (y ∶ β c y) = (y ∶ τ) := by
      intros τ yτ h y y_in_yτ
      rw [h y y_in_yτ ]
    have h_map1 : Multiset.map (fun y => y ∶ β c y) ↑y𝕆 = Multiset.map (fun y => y ∶ 𝕆) ↑y𝕆 :=
      Multiset.map_congr rfl (this 𝕆 ↑y𝕆 y𝕆_𝕆)
    have h_map2 : Multiset.map (fun y => y ∶ β c y) ↑y𝔹 = Multiset.map (fun y => y ∶ 𝔹) ↑y𝔹 :=
      Multiset.map_congr rfl (this 𝔹 ↑y𝔹 y𝔹_𝔹)
    rw [h_map1, h_map2]
  have y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (dec_𝕆 ((δ c).ys) (C β ((δ c).fn_body) (β c)) (β c)) := by
    rw [Finset.subset_iff]
    intros y y_in_y𝕆
    simp only [y𝕆, List.mem_toFinset, List.mem_filter, decide_eq_true_iff] at y_in_y𝕆
    exact vars_sub_FV_dec_𝕆 ys (C β ((δ c).fn_body) (β c)) (β c) y y_in_y𝕆.left y_in_y𝕆.right
  rw [Γ_subdiv]
  unfold List.toFinset at wf
  rw [ys_subdiv] at wf
  have : ↑ys ⊆ (y𝕆 : Multiset Var) + (y𝔹 : Multiset Var) := by
    rw [ys_subdiv]
    exact Multiset.Subset.refl _
  apply inductive_dec y𝕆_sub_ys this nd_ys y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹
  let y𝕆' := Multiset.filter (fun (y : Var) => y ∈ fv_of_fn_body (C β ((δ c).fn_body) (β c))) y𝕆
  have y𝕆'_𝕆 : ∀ y ∈ y𝕆', β c y = 𝕆 := by
    intros y hy
    exact y𝕆_𝕆 y (Multiset.mem_of_mem_filter hy)
  have nd_y𝕆' : Multiset.Nodup y𝕆' := Multiset.Nodup.filter _ nd_y𝕆
  have y𝕆'_sub_y𝕆 : y𝕆' ⊆ y𝕆 := Multiset.filter_subset _ _
  have y𝕆'_sub_FV : y𝕆'.toFinset ⊆ fv_of_fn_body (δ c).fn_body := by
    rw [Finset.subset_iff]
    intros x x_in_yOrig
    rw [Multiset.mem_toFinset] at x_in_yOrig
    have h_in : x ∈ y𝕆 := y𝕆'_sub_y𝕆 x_in_yOrig
    have h_in_toFinset : x ∈ y𝕆.toFinset := List.mem_toFinset.mpr h_in
    rw [Finset.subset_iff] at y𝕆_sub_FV
    have h := y𝕆_sub_FV h_in_toFinset
    rw [FV_dec_𝕆_filter] at h
    simp only [List.mem_toFinset, Finset.mem_union, Finset.mem_filter] at h
    cases h with
    | inl h_in_dec =>
      have h_FV := (Multiset.mem_filter.mp x_in_yOrig).2
      exact absurd h_FV h_in_dec.2.2
    | inr h_in_FV =>
      rw [FV_C_eq_FV] at h_in_FV
      exact h_in_FV
  have wf' : β ;ʷᶠᵇ δ ;ʷᶠᵇ y𝕆'.toFinset ∪ y𝔹.toFinset ⊢ʷᶠᵇ (δ c).fn_body := by
    rw [Multiset.toFinset_add] at wf
    have h1 : fv_of_fn_body (δ c).fn_body ⊆ y𝕆'.toFinset ∪ y𝔹.toFinset := by
      have : fv_of_fn_body (δ c).fn_body ⊆ y𝕆.toFinset ∪ y𝔹.toFinset := FV_sub_wf_context wf
      rw [Finset.subset_iff] at this
      rw [Finset.subset_iff]
      intros x x_in_FV
      let := this x_in_FV
      simp only [Finset.mem_union, Multiset.mem_toFinset] at this ⊢
      cases this with
      | inl h_in =>
        rw [← FV_C_eq_FV] at x_in_FV
        have h_in' : x ∈ y𝕆 := List.mem_toFinset.mp h_in
        have h_in_y𝕆' : x ∈ y𝕆' := Multiset.mem_filter.mpr ⟨h_in', x_in_FV⟩
        exact Or.inl h_in_y𝕆'
      | inr h_in => exact Or.inr h_in
    have h2 : y𝕆'.toFinset ∪ y𝔹.toFinset ⊆ y𝕆.toFinset ∪ y𝔹.toFinset := by
      rw [Multiset.subset_iff] at y𝕆'_sub_y𝕆
      simp only [Finset.subset_iff, Finset.mem_union, Multiset.mem_toFinset]
      intros x h
      cases h with
      | inl h_in => exact Or.inl (Multiset.mem_toFinset.mpr (y𝕆'_sub_y𝕆 h_in))
      | inr h_in => exact Or.inr h_in
    exact wf_FV_sandwich h1 h2 wf
  exact rc_insertion_correctness' nd_y𝕆' nd_y𝔹 y𝕆'_𝕆 y𝔹_𝔹 y𝕆'_sub_FV wf'

end RcCorrectness
