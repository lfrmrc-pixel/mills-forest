import Mathlib

/-!
# Weighted forests: compactness and the global mass recursion

This file contains the combinatorial core of the "forest" argument.

* `WForest.exists_path`: König's lemma for a forest on `ℕ` given by a finite set of
  roots and finite children sets. If every level is nonempty, there is an infinite
  path.
* `WForest.levels_nonempty`: the *global* counting step. Each good node passes at
  least a fraction `f k` of its weight to its children, and the bad nodes of a level
  carry total weight at most `β k`. If `β k ≤ L k / 2` and
  `L (k+1) ≤ f k * (L k / 2)`, then every level is nonempty.

Nothing here requires *every* node to have a good child: this is the point of the
argument.
-/

open Finset

namespace MillsForest

/-- A finitely branching forest on `ℕ`. -/
structure WForest where
  root : Finset ℕ
  children : ℕ → ℕ → Finset ℕ

namespace WForest

variable (F : WForest)

/-- Nodes at level `k`. -/
def level (F : WForest) : ℕ → Finset ℕ
  | 0 => F.root
  | k + 1 => (F.level k).biUnion (F.children k)

/-- Descendants of a node `p` placed at level `k`, after `m` further generations. -/
def sub (F : WForest) (k p : ℕ) : ℕ → Finset ℕ
  | 0 => {p}
  | m + 1 => (F.sub k p m).biUnion (F.children (k + m))

lemma level_add (k m : ℕ) :
    F.level (k + m) = (F.level k).biUnion (fun p => F.sub k p m) := by
  induction m with
  | zero => simp [sub]
  | succ m ih =>
    show (F.level (k + m)).biUnion (F.children (k + m)) = _
    rw [ih, Finset.biUnion_biUnion]
    rfl

lemma sub_succ' (k p m : ℕ) :
    F.sub k p (m + 1) = (F.children k p).biUnion (fun q => F.sub (k + 1) q m) := by
  induction m with
  | zero => simp [sub]
  | succ m ih =>
    show (F.sub k p (m + 1)).biUnion (F.children (k + (m + 1))) = _
    rw [ih, Finset.biUnion_biUnion]
    have h : k + (m + 1) = k + 1 + m := by omega
    rw [h]
    rfl

/-- A general pigeonhole step: if the nonemptiness of `t p m` is antitone in `m` and
`s` is finite, then nonemptiness of `⋃ p ∈ s, t p m` for every `m` forces a single
`p ∈ s` with `t p m` nonempty for every `m`. -/
lemma exists_forall_nonempty (s : Finset ℕ) (t : ℕ → ℕ → Finset ℕ)
    (hmono : ∀ p m, (t p (m + 1)).Nonempty → (t p m).Nonempty)
    (hall : ∀ m, (s.biUnion (fun p => t p m)).Nonempty) :
    ∃ p ∈ s, ∀ m, (t p m).Nonempty := by
  have hmono' : ∀ p m d, (t p (m + d)).Nonempty → (t p m).Nonempty := by
    intro p m d
    induction d with
    | zero => simp
    | succ d ih => intro h; exact ih (hmono p (m + d) h)
  by_contra hcon
  push_neg at hcon
  choose! g hg using hcon
  obtain ⟨x, hx⟩ := hall (s.sup g)
  rw [Finset.mem_biUnion] at hx
  obtain ⟨p, hp, hxp⟩ := hx
  have hle : g p ≤ s.sup g := Finset.le_sup hp
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hne : (t p (s.sup g)).Nonempty := ⟨x, hxp⟩
  rw [hd] at hne
  exact Finset.not_nonempty_iff_eq_empty.mpr (hg p hp) (hmono' p (g p) d hne)

lemma sub_nonempty_of_succ (k p m : ℕ) (h : (F.sub k p (m + 1)).Nonempty) :
    (F.sub k p m).Nonempty := by
  obtain ⟨x, hx⟩ := h
  simp only [sub, Finset.mem_biUnion] at hx
  obtain ⟨y, hy, -⟩ := hx
  exact ⟨y, hy⟩

/-- A node is *alive* if it has descendants in every later generation. -/
def Alive (F : WForest) (k p : ℕ) : Prop := ∀ m, (F.sub k p m).Nonempty

lemma exists_alive_root (hne : ∀ k, (F.level k).Nonempty) : ∃ p ∈ F.root, F.Alive 0 p := by
  apply exists_forall_nonempty F.root (fun p m => F.sub 0 p m)
  · intro p m h; exact F.sub_nonempty_of_succ 0 p m h
  · intro m
    have h := F.level_add 0 m
    rw [Nat.zero_add] at h
    have h0 : F.level 0 = F.root := rfl
    rw [h0] at h
    rw [← h]
    exact hne m

lemma exists_alive_child (k p : ℕ) (hp : F.Alive k p) :
    ∃ q ∈ F.children k p, F.Alive (k + 1) q := by
  apply exists_forall_nonempty (F.children k p) (fun q m => F.sub (k + 1) q m)
  · intro q m h; exact F.sub_nonempty_of_succ (k + 1) q m h
  · intro m
    rw [← F.sub_succ']
    exact hp (m + 1)

/-- **König's lemma** for the forest. -/
theorem exists_path (hne : ∀ k, (F.level k).Nonempty) :
    ∃ p : ℕ → ℕ, p 0 ∈ F.root ∧ ∀ k, p (k + 1) ∈ F.children k (p k) := by
  obtain ⟨p0, hp0, ha0⟩ := F.exists_alive_root hne
  have step : ∀ k p, F.Alive k p → ∃ q, q ∈ F.children k p ∧ F.Alive (k + 1) q :=
    fun k p hp => F.exists_alive_child k p hp
  choose! nxt hnxt using step
  let path : ℕ → ℕ := fun k => Nat.rec p0 (fun k pk => nxt k pk) k
  have alive : ∀ k, F.Alive k (path k) := by
    intro k
    induction k with
    | zero => exact ha0
    | succ k ih => exact (hnxt k (path k) ih).2
  exact ⟨path, hp0, fun k => (hnxt k (path k) (alive k)).1⟩

/-! ### The global mass recursion -/

/-- Total weight of level `k`. -/
noncomputable def mass (F : WForest) (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ := ∑ p ∈ F.level k, w k p

theorem mass_succ_ge (w : ℕ → ℕ → ℝ) (good : ℕ → ℕ → Bool) (f β : ℝ) (k : ℕ)
    (hw : ∀ n, 0 ≤ w (k + 1) n) (hf : 0 ≤ f)
    (hdisj : Set.PairwiseDisjoint (↑(F.level k) : Set ℕ) (F.children k))
    (hgood : ∀ p ∈ F.level k, good k p = true →
      f * w k p ≤ ∑ q ∈ F.children k p, w (k + 1) q)
    (hbad : ∑ p ∈ (F.level k).filter (fun p => good k p = false), w k p ≤ β) :
    f * (F.mass w k - β) ≤ F.mass w (k + 1) := by
  have h1 : F.mass w (k + 1) = ∑ p ∈ F.level k, ∑ q ∈ F.children k p, w (k + 1) q := by
    rw [mass, show F.level (k + 1) = (F.level k).biUnion (F.children k) from rfl]
    exact Finset.sum_biUnion hdisj
  have hsplit := Finset.sum_filter_add_sum_filter_not (F.level k)
    (fun p => good k p = true) (w k)
  have hnot : (F.level k).filter (fun p => ¬ (good k p = true)) =
      (F.level k).filter (fun p => good k p = false) := by
    congr 1; ext p; simp
  rw [hnot] at hsplit
  have h2 : f * ∑ p ∈ (F.level k).filter (fun p => good k p = true), w k p ≤
      ∑ p ∈ F.level k, ∑ q ∈ F.children k p, w (k + 1) q := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ (F.level k).filter (fun p => good k p = true), f * w k p
        ≤ ∑ p ∈ (F.level k).filter (fun p => good k p = true),
            ∑ q ∈ F.children k p, w (k + 1) q := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter] at hp
          exact hgood p hp.1 hp.2
      _ ≤ ∑ p ∈ F.level k, ∑ q ∈ F.children k p, w (k + 1) q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro p _ _
          exact Finset.sum_nonneg (fun q _ => hw q)
  have h3 : F.mass w k - β ≤ ∑ p ∈ (F.level k).filter (fun p => good k p = true), w k p := by
    unfold mass; linarith
  rw [h1]
  exact le_trans (mul_le_mul_of_nonneg_left h3 hf) h2

/-- **Global survival.** If at every level the bad nodes carry at most half of a lower
bound `L k` for the mass, and `L` is propagated by the good nodes, then no level is
empty. -/
theorem levels_nonempty (w : ℕ → ℕ → ℝ) (good : ℕ → ℕ → Bool) (f β L : ℕ → ℝ)
    (hw : ∀ k n, 0 ≤ w k n) (hf : ∀ k, 0 ≤ f k)
    (hdisj : ∀ k, Set.PairwiseDisjoint (↑(F.level k) : Set ℕ) (F.children k))
    (hgood : ∀ k, ∀ p ∈ F.level k, good k p = true →
      f k * w k p ≤ ∑ q ∈ F.children k p, w (k + 1) q)
    (hbad : ∀ k, ∑ p ∈ (F.level k).filter (fun p => good k p = false), w k p ≤ β k)
    (hL0 : L 0 ≤ F.mass w 0) (hLpos : ∀ k, 0 < L k)
    (hβ : ∀ k, β k ≤ L k / 2) (hLsucc : ∀ k, L (k + 1) ≤ f k * (L k / 2)) :
    ∀ k, (F.level k).Nonempty := by
  have hmass : ∀ k, L k ≤ F.mass w k := by
    intro k
    induction k with
    | zero => exact hL0
    | succ k ih =>
      have hrec := F.mass_succ_ge w good (f k) (β k) k (hw (k + 1)) (hf k) (hdisj k)
        (hgood k) (hbad k)
      have : L k / 2 ≤ F.mass w k - β k := by linarith [hβ k]
      calc L (k + 1) ≤ f k * (L k / 2) := hLsucc k
        _ ≤ f k * (F.mass w k - β k) := mul_le_mul_of_nonneg_left this (hf k)
        _ ≤ F.mass w (k + 1) := hrec
  intro k
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have h0 : F.mass w k = 0 := by unfold mass; rw [h]; simp
  linarith [hmass k, hLpos k]

end WForest

end MillsForest
