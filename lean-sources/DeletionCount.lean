import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card

/-! The deletion double count used in the finite polygon lower bounds.
A face of size k occurs in precisely n-k single-point deletions. -/
namespace PolygonDeletion
open Finset

theorem sum_surviving_faces {α : Type*} [DecidableEq α]
    (u : Finset α) (faces : Finset (Finset α)) (k : Nat)
    (inside : ∀ s ∈ faces, s ⊆ u) (rank : ∀ s ∈ faces, s.card = k) :
    ∑ x ∈ u, (faces.filter (fun s => x ∉ s)).card =
       faces.card * (u.card - k) := by
  classical
  calc
    _ = ∑ x ∈ u, ∑ s ∈ faces, if x ∉ s then 1 else 0 := by
      simp only [Finset.sum_boole, Nat.cast_id]
    _ = ∑ s ∈ faces, ∑ x ∈ u, if x ∉ s then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ s ∈ faces, (u.card - k) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.sum_boole]
      have hf : u.filter (fun x => x ∉ s) = u \ s := by ext x; simp
      rw [hf, Finset.card_sdiff_of_subset (inside s hs), rank s hs]
      exact Nat.cast_id _
    _ = _ := by simp

#print axioms sum_surviving_faces
end PolygonDeletion
