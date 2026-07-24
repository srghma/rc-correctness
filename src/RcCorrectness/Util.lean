import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Perm

namespace List

theorem sizeof_lt_sizeof_of_mem {α} [SizeOf α] {a : α} {l : List α} (h : a ∈ l) : sizeOf a < sizeOf l := sorry

def map_wf {α β : Type _} [SizeOf α] (xs : List α) (f : ∀ (a : α), (sizeOf a < 1 + sizeOf xs) → β) : List β := sorry

lemma map_wf_eq_map {α β : Type _} [SizeOf α] {xs : List α} {f : α → β} : map_wf xs (fun a _ => f a) = map f xs := sorry

lemma sizeof_filter_le_sizeof {α : Type _} (p : α → Prop) [DecidablePred p] (xs : List α) : sizeOf (filter p xs) <= sizeOf xs := sorry

lemma all_map_bool_iff_all {α : Type _} (p : α → Bool) (xs : List α) : List.all (List.map p xs) id ↔ List.all xs p := sorry

def group {α : Type _} [s : Setoid α] [DecidableRel s.r] : List α → List (List α) := sorry

lemma sizeof_lt_of_length_lt {α : Type _} {xs ys : List α} (h : length xs < length ys) : sizeOf xs < sizeOf ys := sorry

@[elab_as_elim] def strong_induction_on {α : Type _} {p : List α → Sort _} :
  ∀ xs : List α, (∀ xs, (∀ ys, length ys < length xs → p ys) → p xs) → p xs := sorry

lemma length_filter_le_length {α : Type _} (p : α → Prop) [DecidablePred p] (xs : List α) :
  length (filter p xs) <= length xs := sorry

lemma filter_append_not_filter_perm {α : Type _} (p : α → Prop) [DecidablePred p] (xs : List α) :
  List.Perm (filter p xs ++ filter (not ∘ p) xs) xs := sorry

lemma length_filter_lt_length_cons {α : Type _} (p : α → Prop) [DecidablePred p] (x : α) (xs : List α) :
  length (filter p xs) < length (x :: xs) := sorry

lemma join_group_perm {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) : List.Perm (join (group xs)) xs := sorry

lemma group_equiv {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs : List α} :
  ∀ g, g ∈ group xs → ∀ x y, x ∈ g → y ∈ g → x ≈ y := sorry

lemma nil_not_mem_group {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) : [] ∉ group xs := sorry

lemma group_equiv_disjoint' {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  ∀ g1 g2, g1 ∈ group xs → g2 ∈ group xs → (∀ x1, x1 ∈ g1 → ∀ x2, x2 ∈ g2 → x1 ≈ x2) → g1 = g2 := sorry

lemma group_equiv_disjoint {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  ∀ g1 g2, g1 ∈ group xs → g2 ∈ group xs → g1 ≠ g2 → ∀ x1, x1 ∈ g1 → ∀ x2, x2 ∈ g2 → ¬(x1 ≈ x2) := sorry

lemma nodup_perm_group {α : Type _} [DecidableEq α] [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  Pairwise (fun a b => ¬List.Perm a b) (group xs) := sorry

lemma nodup_group {α : Type _} [DecidableEq α] [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  Nodup (group xs) := sorry

lemma pairwise_equiv_disjoint_group {α : Type _} [DecidableEq α] [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  Pairwise (fun g1 g2 : List α => ∀ x1, x1 ∈ g1 → ∀ x2, x2 ∈ g2 → ¬(x1 ≈ x2)) (group xs) := sorry

lemma pairwise_disjoint_group {α : Type _} [DecidableEq α] [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  Pairwise Disjoint (group xs) := sorry

lemma group_perm_iff_group_sub {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs ys : List α) :
  List.Perm (group xs) (group ys) ↔ group xs ⊆ group ys ∧ group ys ⊆ group xs := sorry

lemma filter_equiv_mem_group {α : Type _} [s : Setoid α] [DecidableRel s.r] {x : α} {xs : List α} (h : x ∈ xs) :
  filter (· ≈ x) xs ∈ group xs := sorry

lemma cons_eq_filter_of_group {α : Type _} [s : Setoid α] [DecidableRel s.r] {g_hd : α} {xs g_tl : List α}
  (h : (g_hd :: g_tl : List α) ∈ group xs) :
  (g_hd :: g_tl : List α) = filter (· ≈ g_hd) xs := sorry

lemma group_eq_of_mem_equiv {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs g1 g2 : List α}
  (h1 : g1 ∈ group xs) (h2 : g2 ∈ group xs) (h : ∃ x, x ∈ g1 ∧ ∃ y, y ∈ g2 ∧ x ≈ y) :
  g1 = g2 := sorry

lemma group_perm_of_perm {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs ys : List α} (h : List.Perm xs ys) :
  ∀ gx, gx ∈ group xs → ∃ gy, gy ∈ group ys ∧ List.Perm gx gy := sorry

lemma list_inj_on_of_nodup_map {α β : Type _} {f : α → β} {s : List α} (nd : Nodup (map f s))
  {x : α} (x_in_s : x ∈ s) {y : α} (y_in_s : y ∈ s) (f_eq : f x = f y) : x = y := sorry

end List

namespace Multiset

def group' {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) : Multiset (Multiset α) := sorry

lemma nodup_map_coe_of_perm_nodup {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List (List α)) (h : List.Pairwise (fun a b => ¬List.Perm a b) xs) :
  List.Nodup (List.map (fun (l : List α) => (l : Multiset α)) xs) := sorry

lemma group'_eq_of_perm {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs ys : List α} (h : List.Perm xs ys) : group' xs = group' ys := sorry

lemma join_group'_eq {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) : join (group' xs) = xs := sorry

lemma nil_not_mem_group' {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : List α) : ∅ ∉ group' xs := sorry

lemma group'_equiv {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs : List α} :
  ∀ g, g ∈ group' xs → ∀ x y, x ∈ g → y ∈ g → x ≈ y := sorry

lemma pairwise_equiv_disjoint_group' {α : Type _} [DecidableEq α] [s : Setoid α] [DecidableRel s.r] (xs : List α) :
  Pairwise (fun g1 g2 : Multiset α => ∀ x1, x1 ∈ g1 → ∀ x2, x2 ∈ g2 → ¬(x1 ≈ x2)) (group' xs) := sorry

lemma filter_equiv_mem_group' {α : Type _} [s : Setoid α] [DecidableRel s.r] {x : α} {xs : List α} (h : x ∈ xs) :
  filter (· ≈ x) xs ∈ group' xs := sorry

lemma subset_of_eq {α : Type _} {xs ys : Multiset α} (h : xs = ys) : xs ⊆ ys ∧ ys ⊆ xs := sorry

lemma cons_eq_filter_of_group' {α : Type _} [s : Setoid α] [DecidableRel s.r] {g_hd : α} {g_tl : Multiset α} {xs : List α}
  (h : Multiset.cons g_hd g_tl ∈ group' xs) :
  Multiset.cons g_hd g_tl = filter (· ≈ g_hd) xs := sorry

lemma group'_eq_of_mem_equiv {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs : List α} {g1 g2 : Multiset α}
  (h1 : g1 ∈ group' xs) (h2 : g2 ∈ group' xs) (h : ∃ x, x ∈ g1 ∧ ∃ y, y ∈ g2 ∧ x ≈ y) :
  g1 = g2 := sorry

def group {α : Type _} [s : Setoid α] [DecidableRel s.r] (m : Multiset α) : Multiset (Multiset α) := sorry

lemma join_group_eq {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : Multiset α) : join (group xs) = xs := sorry

lemma nil_not_mem_group {α : Type _} [s : Setoid α] [DecidableRel s.r] (xs : Multiset α) : ∅ ∉ group xs := sorry

lemma group_equiv {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs : Multiset α} :
  ∀ g, g ∈ group xs → ∀ x y, x ∈ g → y ∈ g → x ≈ y := sorry

lemma pairwise_equiv_disjoint_group {α : Type _} [DecidableEq α] [s : Setoid α] [DecidableRel s.r] (xs : Multiset α) :
  Pairwise (fun g1 g2 : Multiset α => ∀ x1, x1 ∈ g1 → ∀ x2, x2 ∈ g2 → ¬(x1 ≈ x2)) (group xs) := sorry

lemma filter_equiv_mem_group {α : Type _} [s : Setoid α] [DecidableRel s.r] {x : α} {xs : Multiset α} :
  x ∈ xs → filter (· ≈ x) xs ∈ group xs := sorry

lemma cons_eq_filter_of_group {α : Type _} [s : Setoid α] [DecidableRel s.r] {g_hd : α} {g_tl : Multiset α} {xs : Multiset α} :
  Multiset.cons g_hd g_tl ∈ group xs → Multiset.cons g_hd g_tl = filter (· ≈ g_hd) xs := sorry

lemma group_eq_of_mem_equiv {α : Type _} [s : Setoid α] [DecidableRel s.r] {xs g1 g2 : Multiset α} :
  g1 ∈ group xs → g2 ∈ group xs → (∃ x, x ∈ g1 ∧ ∃ y, y ∈ g2 ∧ x ≈ y) → g1 = g2 := sorry

@[simp] lemma filter_true {α : Type _} [DecidablePred (fun (_ : α) => True)] (s : Multiset α) :
  filter (fun _ => True) s = s := sorry

@[simp] lemma filter_false {α : Type _} [DecidablePred (fun (_ : α) => False)] (s : Multiset α) :
  filter (fun _ => False) s = ∅ := sorry

lemma disjoint_filter_filter {α : Type _} {p1 p2 : α → Prop} [DecidablePred p1] [DecidablePred p2] {s : Multiset α} :
  Disjoint (s.filter p1) (s.filter p2) ↔ ∀ x, x ∈ s → p1 x → ¬p2 x := sorry

lemma multiset_inj_on_of_nodup_map {α β : Type _} {f : α → β} {s : Multiset α} :
  Nodup (map f s) → ∀ x, x ∈ s → ∀ y, y ∈ s → f x = f y → x = y := sorry

lemma map_add_of_disjoint {α β : Type _} [DecidableEq α] (f1 f2 : α → β) {s1 s2 : Multiset α} (h : Disjoint s1 s2) :
  map f1 s1 + map f2 s2 = map (fun x => if x ∈ s1 then f1 x else f2 x) (s1 + s2) := sorry

end Multiset

namespace Finset

def join {α : Type _} [DecidableEq α] (xs : List (Finset α)) : Finset α := sorry

@[simp] theorem mem_join {α : Type _} [DecidableEq α] {x : α} {xs : List (Finset α)} : x ∈ join xs ↔ ∃ S, S ∈ xs ∧ x ∈ S := sorry

lemma erase_insert_eq_insert_erase {α : Type _} [DecidableEq α] {a b : α} (s : Finset α)
  (h : a ≠ b) :
  erase (insert a s) b = insert a (erase s b) := sorry

lemma sort_split {α : Type _} [DecidableEq α] (p : α → α → Prop) [DecidableRel p]
  [IsTrans α p] [IsAntisymm α p] [IsTotal α p]
  (a : α) (s : Finset α) :
  ∃ l r : List α, Finset.sort p (insert a s) = l ++ a :: r := sorry

lemma map_congr {α β : Type _} (f g : α ↪ β) {s : Finset α} : (∀ x, x ∈ s → f.1 x = g.1 x) → map f s = map g s := sorry

end Finset
