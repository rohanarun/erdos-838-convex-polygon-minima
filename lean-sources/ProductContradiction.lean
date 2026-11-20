import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite family of strict product inequalities cannot have balanced exponents. -/
namespace ConvexSubsets

open Finset

/-- A strict linear inequality in each row contradicts a positive combination
of the rows whose coefficient at every variable vanishes. -/
theorem balanced_linear_contradiction {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (w : ι → ℝ) (coeff : ι → κ → ℝ) (v : κ → ℝ)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, 0 < ∑ j, coeff i j * v j)
    (hbalance : ∀ j, ∑ i, w i * coeff i j = 0) : False := by
  have hpos : 0 < ∑ i, w i * ∑ j, coeff i j * v j :=
    sum_pos (fun i _ => mul_pos (hw i) (hrow i)) univ_nonempty
  simp_rw [mul_sum, ← mul_assoc] at hpos
  rw [sum_comm] at hpos
  simp_rw [← sum_mul, hbalance, zero_mul] at hpos
  simp at hpos

/-- The occurrence count of a variable in a degree-two monomial, with
repetition allowed. -/
def pairOccurrences {κ : Type*} [DecidableEq κ] (a b j : κ) : ℝ :=
  (if j = a then 1 else 0) + (if j = b then 1 else 0)

theorem sum_pairOccurrences {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : κ → ℝ) (a b : κ) :
    ∑ j, pairOccurrences a b j * v j = v a + v b := by
  simp [pairOccurrences, add_mul, sum_add_distrib, ite_mul]

/-- In each row, compare two products of two positive variables. If
weighted occurrence counts on the two sides match at every variable,
strict inequalities in all rows are impossible. -/
theorem balanced_pair_product_contradiction
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]
    (x : κ → ℝ) (w : ι → ℝ) (a b c d : ι → κ)
    (hx : ∀ j, 0 < x j) (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, x (a i) * x (b i) < x (c i) * x (d i))
    (hbalance : ∀ j,
      ∑ i, w i * pairOccurrences (c i) (d i) j =
      ∑ i, w i * pairOccurrences (a i) (b i) j) : False := by
  apply balanced_linear_contradiction w
    (fun i j => pairOccurrences (c i) (d i) j - pairOccurrences (a i) (b i) j)
    (fun j => Real.log (x j)) hw
  · intro i
    simp_rw [sub_mul, sum_sub_distrib, sum_pairOccurrences]
    apply sub_pos.mpr
    have h := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (mul_pos (hx (a i)) (hx (b i))))
      (Set.mem_Ioi.mpr (mul_pos (hx (c i)) (hx (d i)))) (hrow i)
    simpa [Real.log_mul (hx _).ne' (hx _).ne'] using h
  · intro j
    simp_rw [mul_sub, sum_sub_distrib, hbalance, sub_self]

#print axioms balanced_linear_contradiction
#print axioms balanced_pair_product_contradiction

end ConvexSubsets
