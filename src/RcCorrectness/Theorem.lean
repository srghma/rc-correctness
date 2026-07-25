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
  apply Multiset.induction_on y𝔹
  { simp only [map_zero, add_zero]
    assumption }
  intros a s ih
  simp only [map_cons, add_cons]
  apply linear.weaken
  assumption

theorem C_app_rc_insertion_correctness {β : Const → Var → LinType} {βₗ : Var → LinType} {δ : Program}
  {y : Var} {e : Expr} {F : FnBody} {y𝕆 y𝔹 : Multiset Var} {Γ : List (Var × LinType)}
  (ih : ∀ (βₗ : Var → LinType),
    Multiset.Nodup y𝕆 →
    Multiset.Nodup y𝔹 →
    (∀ (y : Var), y ∈ y𝕆 → βₗ y = 𝕆) →
    (∀ (y : Var), y ∈ y𝔹 → βₗ y = 𝔹) →
    (β; δ; y𝕆.toFinset ∪ y𝔹.toFinset ⊢ F) →
    (∀ ⦃x : Var⦄, x ∈ y𝕆 → x ∈ fv_of_fn_body F) →
    (β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ ↑(C β F βₗ) ∷ 𝕆))
  (nd_y𝕆 : Multiset.Nodup y𝕆) (nd_y𝔹 : Multiset.Nodup y𝔹)
  (y𝕆_𝕆 : ∀ (y : Var), y ∈ y𝕆 → βₗ y = 𝕆)
  (y𝔹_𝔹 : ∀ (y : Var), y ∈ y𝔹 → βₗ y = 𝔹)
  (wf : β; δ; y𝕆.toFinset ∪ y𝔹.toFinset ⊢ (y ≔ e; F))
  (y𝕆_free : ∀ ⦃x : Var⦄, x ∈ y𝕆 → x ∈ fv_of_fn_body (y ≔ e; F))
  (ty : β; (Γ.map (λ (yτ : Var × LinType), yτ.1 ∶ yτ.2)) ⊩ e ∷ 𝕆)
  : (β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ ↑(C_app Γ (y ≔ e; C β F (βₗ[y↦𝕆])) βₗ) ∷ 𝕆) :=
by
  sorry



theorem rc_insertion_correctness' {β : Const → Var → LinType} {δ : Program} {c : Const}
  {y𝕆 y𝔹 : multiset Var}
  (nd_y𝕆 : Nodup y𝕆) (nd_y𝔹 : Nodup y𝔹)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, β c y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, β c y = 𝔹)
  (y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (δ c).F) (wf : β; δ; y𝕆.toFinset ∪ y𝔹.toFinset ⊢ (δ c).F)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β ((δ c).F) (β c) ∷ 𝕆 :=
by
  generalize h : β c = βₗ
  rw [h at *]
  clear h
  simp only [Finset.subset_iff, List.mem_toFinset] at y𝕆_sub_FV
  generalize h : (δ c).F = F
  rw [h at *]
  clear h
  induction F using FnBody.rec_wf generalizing y𝕆 y𝔹 βₗ
  case ret x  =>
    unfold C
    unfold fv_of_fn_body at y𝕆_sub_FV
    cases wf
    simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, mem_erase_dup, Finset.mem_mk] at wf_x_def
    unfold inc_𝕆_var
    cases wf_x_def
    { have : βₗ x = 𝕆 ∧ x ∉ Finset.empty, from ⟨y𝕆_𝕆 x wf_x_def, Finset.not_mem_empty x⟩
      rw [if_pos this]
      have : y𝕆 = x :: 0
      { rw [nodup_ext nd_y𝕆 (nodup_singleton x)]
        intro a
        split
        intro h
        { exact y𝕆_sub_FV h }
        { rw [mem_singleton] at h
          rwa h } }
      rw [this]
      simp only [Finset.singleton_val, Finset.insert_empty, zero_add, map_cons, cons_add, map_zero]
      rw [←singleton_add]
      apply inductive_weakening
      apply linear.ret }
    { have : ¬(βₗ x = 𝕆 ∧ x ∉ Finset.empty)
      { simp only [not_and]
        intro h
        rw [y𝔹_𝔹 x wf_x_def] at h
        simp only [] at h
        contradiction }
      rw [if_neg this]
      apply linear.inc_𝔹
      { apply mem_add.mpr
        apply Or.inr
        exact mem_map_of_mem _ wf_x_def }
      have : y𝕆 = ∅
      { apply eq_zero_of_forall_not_mem
        simp only [Finset.insert_empty, Finset.mem_singleton] at y𝕆_sub_FV
        intros y y_in_y𝕆
        have x_in_y𝕆, from (y𝕆_sub_FV y_in_y𝕆).subst y_in_y𝕆
        have dj : multiset.disjoint y𝕆 y𝔹
        { rw [disjoint_iff_ne]
          intros a a_in_y𝕆 b b_in_y𝔹 h
          rw [h at a_in_y𝕆]
          let := y𝕆_𝕆 b a_in_y𝕆
          rw [y𝔹_𝔹 b b_in_y𝔹] at this
          contradiction }
        let := disjoint_right.mp dj wf_x_def
        contradiction }
      simp only [this, empty_eq_zero, zero_add, map_zero]
      rw [←singleton_add]
      apply inductive_weakening
      apply linear.ret }
  case «let» y e F ih  =>
    with_cases { cases e }
    case RcCorrectness.Expr.proj : i x wf {
      unfold C
      split_ifs
      { have x_in_y𝕆 : x ∈ y𝕆
        { let := subset_iff.mp (FV_sub_wf_context wf)
        simp only [fv_of_fn_body, fv_of_expr, mem_union, Finset.singleton_val, to_finset_val,
            Finset.insert_empty, mem_erase_dup, Finset.erase_val,
            Finset.union_val, mem_singleton] at this
          have h : x ∈ y𝕆 ∨ x ∈ y𝔹, from this (Or.inl rfl)
          cases h
          { assumption }
          { rw [y𝔹_𝔹 x h_1] at h
            contradiction } }
        apply linear.proj_𝕆
        { simpa }
        unfold dec_𝕆_var
        split_ifs
        { rcases exists_cons_of_mem x_in_y𝕆 with ⟨y𝕆', y𝕆_def⟩
          rw [y𝕆_def at *]
          simp only [map_cons, cons_add]
          rw [cons_swap]
          apply linear.dec
          rw [←cons_add]
          rw [←map_cons (∶ 𝕆)]
          apply ih
          any_goals { assumption }
          { cases wf
            simp only [not_or_distrib, mem_ndinsert, mem_ndunion, to_finset_val
              mem_erase_dup, to_finset_cons, Finset.insert_val, Finset.mem_mk] at wf_z_undef
            simp only [nodup_cons] at ⊢ nd_y𝕆
            exact ⟨wf_z_undef.left.right, nd_y𝕆.right⟩ }
          { simp only [mem_cons]
            intros z z_in_y𝕆'
            cases z_in_y𝕆'
            { rw [z_in_y𝕆']
              rw [function.update_same ]}
            { by_cases z = y
              { rw [h, function.update_same] }
              { rw [function.update_noteq]
                { exact y𝕆_𝕆 z (mem_cons_of_mem z_in_y𝕆') }
                { assumption } } } }
          { intros z z_in_y𝔹
            by_cases z = y
            { cases wf
              simp [not_or_distrib] at wf_z_undef
              rw [h at z_in_y𝔹]
              exact absurd z_in_y𝔹 wf_z_undef.right }
            { rw [function.update_noteq]
              { exact y𝔹_𝔹 z z_in_y𝔹 }
              { assumption } } }
          { cases wf
            apply wf_FV_sandwich _ _ wf_F_wf
            { let := FV_sub_wf_context wf_F_wf
              rw [Finset.subset_iff at ⊢ this]
              simp only [mem_ndinsert, mem_ndunion, to_finset_val, Finset.insert_union, Finset.mem_union
                Finset.mem_insert, mem_erase_dup, to_finset_cons, Finset.insert_val, Finset.mem_mk, List.mem_toFinset] at ⊢ this
              intros z z_in_FV
              have h', from this z_in_FV
              repeat { cases h' }
              { exact Or.inl rfl }
              { rw [FV_C_eq_FV] at h_1
                exact absurd z_in_FV h_1.right }
              { exact Or.inr (Or.inl h') }
              { exact Or.inr (Or.inr h') } }
            { rw [Finset.subset_iff]
              simp only [mem_ndinsert, mem_ndunion, to_finset_val, Finset.insert_union, Finset.mem_union, Finset.mem_insert
                mem_erase_dup, to_finset_cons, Finset.insert_val, Finset.mem_mk, List.mem_toFinset]
              intros y h'
              repeat { cases h' }
              { exact Or.inl rfl }
              { exact Or.inr (Or.inl (Or.inr h')) }
              { exact Or.inr (Or.inr h') } } }
          { cases wf
            simp only [fv_of_fn_body, fv_of_expr, mem_cons, Finset.insert_empty, Finset.mem_union,
              Finset.mem_singleton, Finset.mem_erase] at ⊢ y𝕆_sub_FV
            intros z h'
            cases h'
            { rwa [h' ]}
            have h'', from y𝕆_sub_FV (Or.inr h')
            cases h''
            { rw [h'' at h']
              rw [nodup_cons at nd_y𝕆]
              exact absurd h' nd_y𝕆.left }
            { exact h''.right } } }
        simp only [not_and_distrib, not_not] at h_1
        rw [←ne.def, not_𝕆_iff_𝔹] at h_1
        cases h_1
        { rw [h] at h_1, contradiction }
        rw [←cons_add]
        rw [←map_cons (∶ 𝕆)]
        apply ih
        any_goals { assumption }
        { cases wf
          simp only [nodup_cons]
          simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val
            nodup_erase_dup, mem_erase_dup, Finset.mem_mk] at wf_z_undef
          exact ⟨wf_z_undef.left, nd_y𝕆⟩ }
        { simp only [mem_cons]
          intros z h'
          cases h'
          { rw [h', rw function.update_same ]}
          { by_cases eq : y = z
            { rw [eq, rw function.update_same ]}
            rw [function.update_noteq]
            { exact y𝕆_𝕆 z h' }
            symmetry
            assumption } }
        { intros z z_in_y𝔹
          by_cases z = y
          { cases wf
            simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup
              mem_erase_dup, Finset.mem_mk] at wf_z_undef
            rw [h at z_in_y𝔹]
            exact absurd z_in_y𝔹 wf_z_undef.right }
          { rw [function.update_noteq]
            { exact y𝔹_𝔹 z z_in_y𝔹 }
            { assumption } } }
        { cases wf
          apply wf_FV_sandwich _ _ wf_F_wf
          { let := FV_sub_wf_context wf_F_wf
            rw [Finset.subset_iff at ⊢ this]
            simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, Finset.insert_union
              Finset.mem_union, Finset.mem_insert, mem_erase_dup, to_finset_cons, Finset.mem_mk, List.mem_toFinset] at ⊢ this
            assumption }
          { rw [Finset.subset_iff]
            simp only [multiset.mem_erase_dup, multiset.mem_union, multiset.nodup_erase_dup, imp_self
              multiset.to_finset_val, multiset.List.mem_toFinset, multiset.to_finset_cons, Finset.insert_union
              Finset.mem_union, Finset.mem_insert, Finset.mem_mk, multiset.ndunion_eq_union, forall_true_iff] } }
        { cases wf
          simp only [mem_cons]
          simp only [fv_of_fn_body, fv_of_expr, Finset.insert_empty, Finset.mem_union,
            Finset.mem_singleton, Finset.mem_erase] at y𝕆_sub_FV
          intros z h'
          cases h'
          { rwa [h' ]}
          have h'', from y𝕆_sub_FV h'
          cases h''
          { rw [h'']
            rwa [FV_C_eq_FV] at h_1 }
          { exact h''.right } } }
      rw [←ne.def, not_𝕆_iff_𝔹] at h
      have x_in_y𝔹 : x ∈ y𝔹
      { let := subset_iff.mp (FV_sub_wf_context wf)
        simp only [fv_of_fn_body, fv_of_expr, mem_union, Finset.singleton_val, to_finset_val
          Finset.insert_empty, mem_erase_dup, Finset.erase_val,
          Finset.union_val, mem_singleton] at this
        have h : x ∈ y𝕆 ∨ x ∈ y𝔹, from this (Or.inl rfl)
        cases h
        { rw [y𝕆_𝕆 x h_1] at h
          contradiction }
        { assumption } }
      apply linear.proj_𝔹
      { simpa }
      rw [add_comm, ←cons_add, add_comm, ←map_cons (∶ 𝔹)]
      apply ih
      any_goals { assumption }
      { cases wf
        simp only [nodup_cons]
        simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val
          nodup_erase_dup, mem_erase_dup, Finset.mem_mk] at wf_z_undef
        exact ⟨wf_z_undef.right, nd_y𝔹⟩ }
      { intros z z_in_y𝕆
        by_cases z = y
        { cases wf
          simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val
            nodup_erase_dup, mem_erase_dup, Finset.mem_mk] at wf_z_undef
          rw [h at z_in_y𝕆]
          exact absurd z_in_y𝕆 wf_z_undef.left }
        { rw [function.update_noteq]
          { exact y𝕆_𝕆 z z_in_y𝕆 }
          { assumption } } }
      { simp only [mem_cons]
        intros z h'
        cases h'
        { rw [h', rw function.update_same ]}
        { by_cases eq : y = z
          { rw [eq, rw function.update_same ]}
          rw [function.update_noteq]
          { exact y𝔹_𝔹 z h' }
          symmetry
          assumption } }
      { cases wf
        apply wf_FV_sandwich _ _ wf_F_wf
        { let := FV_sub_wf_context wf_F_wf
          rw [Finset.subset_iff at ⊢ this]
          simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, Finset.mem_union, Finset.union_insert
            Finset.mem_insert, mem_erase_dup, to_finset_cons, Finset.mem_mk, List.mem_toFinset] at ⊢ this
          assumption }
        { rw [Finset.subset_iff]
          simp only [mem_erase_dup,mem_union, nodup_erase_dup, imp_self, to_finset_val, List.mem_toFinset, to_finset_cons
            Finset.mem_union, Finset.union_insert, Finset.mem_insert, Finset.mem_mk, ndunion_eq_union, forall_true_iff] } }
      { simp only [fv_of_fn_body, fv_of_expr, Finset.insert_empty, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase] at y𝕆_sub_FV
        intros z z_in_y𝕆
        have h', from y𝕆_sub_FV z_in_y𝕆
        cases h'
        { rw [h' at z_in_y𝕆]
          rw [y𝕆_𝕆 x z_in_y𝕆] at h
          contradiction }
        { exact h'.right } }
    case RcCorrectness.Expr.const_app_full : c' ys {
      unfold C
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV
      simp only [List.map_map]
      have : ∀ y ∈ ys, ((λ (yτ : Var × LinType), yτ.fst ∶ yτ.snd) ∘ (λ (y : Var), (y, β c' y))) y = (λ (y : Var), y ∶ β c' y) y
      { intros y' y'_in_ys
        refl }
      rw [List.map_congr this]
      exact linear.const_app_full β ys c'
    case RcCorrectness.Expr.const_app_part : c' ys {
      unfold C
      have : ∀ y ∈ ys, (y, β c' y) = (y, 𝕆)
      { cases wf
        intros y' y'_in_ys
        have not_𝔹, from wf_no_𝔹_var y'
        rw [not_𝔹_iff_𝕆 at not_𝔹]
        rw [not_𝔹 ]}
      rw [List.map_congr this]
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV
      rw [List.map_map]
      have : ∀ y ∈ ys, ((λ (yτ : Var × LinType), yτ.fst ∶ yτ.snd) ∘ (λ (y : Var), (y, 𝕆))) y = (λ (y : Var), y ∶ 𝕆) y
      { intros y' y'_in_ys
        refl }
      rw [List.map_congr this]
      exact linear.const_app_part β ys c'
    case RcCorrectness.Expr.var_app : x z {
      unfold C
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV
      simp only [List.map]
      exact linear.var_app β x z
    case RcCorrectness.Expr.ctor : i ys {
      unfold C
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV
      rw [List.map_map]
      have : ∀ y ∈ ys, ((λ (yτ : Var × LinType), yτ.fst ∶ yτ.snd) ∘ (λ (y : Var), (y, 𝕆))) y = (λ (y : Var), y ∶ 𝕆) y
      { intros y' y'_in_ys
        refl }
      rw [List.map_congr this]
      exact linear.ctor_app β ys i
  case «case» x Fs ih  =>
    unfold C
    have FV_sub_y𝕆_y𝔹 : (fv_of_fn_body (case x of Fs)).val ⊆ y𝕆 + y𝔹
    { let := FV_sub_wf_context wf
      rw [Finset.subset_def] at this
      rw [subset_iff at ⊢ this]
      simp only [mem_union, to_finset_val, mem_add, mem_erase_dup, Finset.union_val] at ⊢ this
      assumption }
    cases wf
    simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, mem_erase_dup, Finset.mem_mk] at wf_x_def
    cases wf_x_def
    apply linear.case_𝕆
    { simpa }
    swap
    apply linear.case_𝔹
    { simpa }
    all_goals {
      intros F' h
      rw [List.map_wf_eq_map] at h
      rw [List.mem_map] at h
      rcases h with ⟨F, ⟨F_in_Fs, F'_def⟩⟩
      rw [←F'_def]
      apply inductive_dec
      any_goals { assumption }
      { rw [subset_iff]
        rw [Finset.sort_eq]
        intros y y_in_y𝕆
        exact y𝕆_sub_FV y_in_y𝕆 }
      { simp only [Finset.sort_eq]
        assumption }
      { exact Finset.sort_nodup var_le (fv_of_fn_body (case x of Fs)) }
      apply ih
      any_goals { assumption }
      { apply nodup_filter
        assumption }
      { simp only [and_imp, mem_filter, Finset.mem_sort]
        intros y y_in_y𝕆 h
        exact y𝕆_𝕆 y y_in_y𝕆 }
      { have wf, from wf_Fs_wf F F_in_Fs
        apply wf_FV_sandwich _ _ wf
        { rw [Finset.subset_iff]
          rw [subset_iff at FV_sub_y𝕆_y𝔹]
          simp only [fv_of_fn_body, List.map_wf_eq_map, mem_ndinsert, mem_add, Finset.insert_val] at FV_sub_y𝕆_y𝔹
          simp [fv_of_fn_body, List.map_wf_eq_map, not_or_distrib]
          intros y y_in_FV
          replace FV_sub_y𝕆_y𝔹 := @FV_sub_y𝕆_y𝔹 y
          rw [←Finset.mem_def at FV_sub_y𝕆_y𝔹]
          simp only [exists_prop, List.mem_map, Finset.mem_join] at FV_sub_y𝕆_y𝔹
          rw [FV_C_eq_FV]
          have : ∃ (S : Finset Var), (∃ (a : FnBody), a ∈ Fs ∧ fv_of_fn_body a = S) ∧ y ∈ S
          { use fv_of_fn_body F, apply and.intro _ y_in_FV, use F, exact ⟨F_in_Fs, rfl⟩ }
          have : y ∈ y𝕆 ∨ y ∈ y𝔹, from FV_sub_y𝕆_y𝔹 (Or.inr this)
          cases this
          { exact Or.inr ⟨this_1, y_in_FV⟩ }
          { exact Or.inl this_1 } }
        { rw [Finset.subset_iff]
          simp only [mem_union, ndunion_eq_union, mem_filter, to_finset_val
            nodup_erase_dup, Finset.mem_union, mem_erase_dup, Finset.mem_mk, List.mem_toFinset]
          intros y h
          cases h
          { exact Or.inl (h.left) }
          { exact Or.inr h } } }
      { simp only [and_imp, mem_filter, FV_C_eq_FV, imp_self, forall_true_iff] }
  case «inc» x F ih  =>
    cases wf
  case «dec» x F ih  =>
    cases wf

theorem rc_insertion_correctness (β : Const → Var → LinType) (δ : Program) (wf : β ⊢ δ) : β ⊩ C_prog β δ :=
by
  cases wf
  split
  intro c
  replace wf_const_wf := wf_const_wf c
  cases wf_const_wf
  rename wf_const_wf_F_wf wf
  split
  simp only [C_prog]
  let ys := (δ c).ys
  let Γ := (↑(List.map (λ (y : Var), y ∶ β c y) ys) : multiset typed_var)
  let y𝕆 := filter (λ y, β c y = 𝕆) ys
  let y𝔹 := filter (λ y, β c y = 𝔹) ys
  obtain ⟨y𝕆_𝕆, y𝔹_𝔹⟩
    : (∀ y ∈ y𝕆, β c y = 𝕆) ∧ (∀ y ∈ y𝔹, β c y = 𝔹)
  { repeat { split }; { intros y h, rw (mem_filter.mp h).right } }
  obtain ⟨y𝕆_sub_ys, y𝔹_sub_ys⟩ : (y𝕆 ⊆ ys ∧ y𝔹 ⊆ ys)
  { repeat { split }; simp only [filter_subset] }
  obtain ⟨ys_𝕆_sub_y𝕆, ys_𝔹_sub_y𝔹⟩
    : (∀ y ∈ ys, β c y = 𝕆 → y ∈ y𝕆) ∧ (∀ y ∈ ys, β c y = 𝔹 → y ∈ y𝔹)
  { repeat { split }
    { intros y y_in_ys y_ty
      simp only [mem_filter, mem_coe], try rw ←coe_eq_coe, exact ⟨y_in_ys, y_ty⟩ } }
  obtain ⟨nd_y𝕆, nd_y𝔹⟩ : multiset.Nodup y𝕆 ∧ multiset.Nodup y𝔹
  { split; exact nodup_filter _ (coe_nodup.mpr wf_const_wf_nd_ys) }
  have ys_subdiv : ↑ys = y𝕆 + y𝔹
  { have : ∀ y ∈ (↑ys : multiset Var), β c y = 𝔹 ↔ β c y ≠ 𝕆
    { intros y y_in_ys
      split; intro h; cases β c y; simp at h ⊢; assumption }
    simp only [y𝕆, y𝔹]
    rw [filter_congr this]
    exact (filter_add_not ↑ys).symm }
  have Γ_subdiv : ↑(List.map (λ (y : Var), y ∶ β c y) ys) = (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹)
  { have : ↑(List.map (λ (y : Var), y ∶ β c y) ys) = map (λ (y : Var), y ∶ β c y) ↑ys
      from rfl
    rw [this]
    rw [ys_subdiv]
    simp only [map_add]
    have : ∀ (τ : LinType) (yτ : multiset Var), (∀ y ∈ yτ, β c y = τ) →
      ∀ y ∈ yτ, (y ∶ β c y) = (y ∶ τ)
    { intros τ yτ h y y_in_yτ
      rw [h y y_in_yτ ]}
    simp only [map_congr (this 𝕆 y𝕆 y𝕆_𝕆), map_congr (this 𝔹 y𝔹 y𝔹_𝔹)] }
  have y𝕆_sub_FV : y𝕆.toFinset ⊆ fv_of_fn_body (dec_𝕆 ((δ c).ys) (C β ((δ c).F) (β c)) (β c))
  { rw [Finset.subset_iff]
    intros y y_in_y𝕆
    simp only [mem_filter, mem_coe, List.mem_toFinset] at y_in_y𝕆
    exact vars_sub_FV_dec_𝕆 ys (C β ((δ c).F) (β c)) (β c) y y_in_y𝕆.left y_in_y𝕆.right }
  rw [Γ_subdiv]
  unfold List.toFinset at wf
  rw [ys_subdiv] at wf
  have : ↑ys ⊆ y𝕆 + y𝔹, { rw [ys_subdiv, exact subset.refl _ ]}
  apply inductive_dec y𝕆_sub_ys this wf_const_wf_nd_ys y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹
  let y𝕆' := filter (λ (y : Var), y ∈ fv_of_fn_body (C β ((δ c).F) (β c))) y𝕆
  have y𝕆'_𝕆 : ∀ y ∈ y𝕆', β c y = 𝕆
  { simp only [and_imp, mem_filter, mem_coe]
    intros y y_in_ys y_𝕆 y_in_FV
    assumption }
  have nd_y𝕆' : Nodup y𝕆', from nodup_filter _ nd_y𝕆
  have y𝕆'_sub_y𝕆 : y𝕆' ⊆ y𝕆, from filter_subset y𝕆
  have y𝕆'_sub_FV : y𝕆'.toFinset ⊆ fv_of_fn_body (δ c).F
  { rw [Finset.subset_iff, rw [Finset.subset_iff] at y𝕆_sub_FV, rw [subset_iff] at y𝕆'_sub_y𝕆]
    simp only [List.mem_toFinset], simp only [List.mem_toFinset] at y𝕆_sub_FV
    rw [FV_dec_𝕆_filter at y𝕆_sub_FV]
    intros x x_in_y𝕆'
    have h, from y𝕆_sub_FV (y𝕆'_sub_y𝕆 x_in_y𝕆')
    simp only [mem_filter, mem_coe] at x_in_y𝕆'
    simp only [List.List.mem_toFinset, Finset.mem_union, Finset.mem_filter] at h
    cases h
    { exact absurd x_in_y𝕆'.right h.right.right }
    rwa [FV_C_eq_FV] at h }
  have wf' : (β; δ; toFinset y𝕆' ∪ toFinset y𝔹 ⊢ (δ c).F)
  { rw [to_finset_add] at wf
    have h1 : fv_of_fn_body (δ c).F ⊆ toFinset y𝕆' ∪ toFinset y𝔹
    { have : fv_of_fn_body (δ c).F ⊆ toFinset y𝕆 ∪ toFinset y𝔹, from FV_sub_wf_context wf
      rw [Finset.subset_iff] at this
      rw [Finset.subset_iff]
      intros x x_in_FV
      let := this x_in_FV
      simp only [mem_filter, mem_coe, Finset.mem_union, List.mem_toFinset] at this ⊢
      cases this
      { rw [FV_C_eq_FV]
        exact Or.inl ⟨this_1, x_in_FV ⟩ }
      { exact Or.inr this_1 } }
    have h2 : toFinset y𝕆' ∪ toFinset y𝔹 ⊆ toFinset y𝕆 ∪ toFinset y𝔹
    { rw [subset_iff at y𝕆'_sub_y𝕆]
      simp only [Finset.subset_iff, Finset.mem_union, List.mem_toFinset]
      intros x h
      cases h
      { exact Or.inl (y𝕆'_sub_y𝕆 h) }
      { exact Or.inr h } }
    exact wf_FV_sandwich h1 h2 wf }
  exact rc_insertion_correctness' nd_y𝕆' nd_y𝔹 y𝕆'_𝕆 y𝔹_𝔹 y𝕆'_sub_FV wf'

end RcCorrectness
