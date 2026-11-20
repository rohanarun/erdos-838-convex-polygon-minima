import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exclusions of enumerated thirteen-point order-type signatures over the reals.
The hypotheses use one bit per increasing triple in lexicographic order,
with bit one meaning a strictly positive signed area. -/
namespace ThirteenPointExclusions

def area (a b c : ℝ × ℝ) : ℝ :=
  (b.1-a.1)*(c.2-a.2) - (c.1-a.1)*(b.2-a.2)

/-- Zero-based lexicographic rank of (i,j,k) for i<j<k<13. The first difference
counts triples with smaller first index, the second counts pairs with smaller
second index, and the final term counts smaller third indices. -/
def lexRank (i j k : ℕ) : ℕ :=
  (286 - (13-i).choose 3) + ((12-i).choose 2 - (13-j).choose 2) + (k-j-1)

def Realizes (bits : ℕ) (p : Fin 13 → ℝ × ℝ) : Prop :=
  ∀ (i j k : Fin 13), i < j → j < k →
    0 < (if bits.testBit (285-lexRank i.val j.val k.val)
         then area (p i) (p j) (p k) else -area (p i) (p j) (p k))

theorem merge {a b c d : ℝ} (u : 0 < a ∧ a < b)
    (v : 0 < c ∧ c < d) : 0 < a*c ∧ a*c < b*d :=
  ⟨mul_pos u.1 v.1, lt_trans (mul_lt_mul_of_pos_right u.2 v.1)
    (mul_lt_mul_of_pos_left v.2 (lt_trans u.1 u.2))⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def signature_569 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000100001111100011111000011110111111111111111111111111111100011111000011110111111111111111111111111111000010110111111111111111111011011111011111111111111111111100111111111101000100000000001000100000000010110001110001101110

theorem no_realization_569 (p : Fin 13 → ℝ × ℝ) : ¬ Realizes signature_569 p := by
  intro h
  let v0_2_3 : ℝ := -area (p 0) (p 2) (p 3)
  have hv0_2_3 : 0 < v0_2_3 := by
    have hs := h 0 2 3 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 2 3)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 2 3) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_9 : ℝ := -area (p 0) (p 2) (p 9)
  have hv0_2_9 : 0 < v0_2_9 := by
    have hs := h 0 2 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 2 9)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 2 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_6 : ℝ := -area (p 0) (p 3) (p 6)
  have hv0_3_6 : 0 < v0_3_6 := by
    have hs := h 0 3 6 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 3 6)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_9 : ℝ := -area (p 0) (p 3) (p 9)
  have hv0_3_9 : 0 < v0_3_9 := by
    have hs := h 0 3 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 3 9)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_9 : ℝ := -area (p 0) (p 6) (p 9)
  have hv0_6_9 : 0 < v0_6_9 := by
    have hs := h 0 6 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 6 9)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_9 : ℝ := -area (p 0) (p 7) (p 9)
  have hv0_7_9 : 0 < v0_7_9 := by
    have hs := h 0 7 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 7 9)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_12 : ℝ := -area (p 0) (p 9) (p 12)
  have hv0_9_12 : 0 < v0_9_12 := by
    have hs := h 0 9 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 0 9 12)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 0 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_6 : ℝ := -area (p 2) (p 3) (p 6)
  have hv2_3_6 : 0 < v2_3_6 := by
    have hs := h 2 3 6 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 3 6)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_7 : ℝ := -area (p 2) (p 3) (p 7)
  have hv2_3_7 : 0 < v2_3_7 := by
    have hs := h 2 3 7 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 3 7)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_8 : ℝ := area (p 2) (p 3) (p 8)
  have hv2_3_8 : 0 < v2_3_8 := by
    have hs := h 2 3 8 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 3 8)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_12 : ℝ := area (p 2) (p 6) (p 12)
  have hv2_6_12 : 0 < v2_6_12 := by
    have hs := h 2 6 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 6 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_12 : ℝ := area (p 2) (p 9) (p 12)
  have hv2_9_12 : 0 < v2_9_12 := by
    have hs := h 2 9 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 9 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_12 : ℝ := area (p 2) (p 10) (p 12)
  have hv2_10_12 : 0 < v2_10_12 := by
    have hs := h 2 10 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 2 10 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 2 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_8 : ℝ := area (p 3) (p 7) (p 8)
  have hv3_7_8 : 0 < v3_7_8 := by
    have hs := h 3 7 8 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 3 7 8)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 3 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_9 : ℝ := area (p 3) (p 7) (p 9)
  have hv3_7_9 : 0 < v3_7_9 := by
    have hs := h 3 7 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 3 7 9)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 3 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_12 : ℝ := area (p 3) (p 7) (p 12)
  have hv3_7_12 : 0 < v3_7_12 := by
    have hs := h 3 7 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 3 7 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 3 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_9 : ℝ := area (p 3) (p 8) (p 9)
  have hv3_8_9 : 0 < v3_8_9 := by
    have hs := h 3 8 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 3 8 9)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 3 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_10 : ℝ := -area (p 3) (p 8) (p 10)
  have hv3_8_10 : 0 < v3_8_10 := by
    have hs := h 3 8 10 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 3 8 10)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 3 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_12 : ℝ := area (p 3) (p 8) (p 12)
  have hv3_8_12 : 0 < v3_8_12 := by
    have hs := h 3 8 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 3 8 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 3 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_9 : ℝ := area (p 6) (p 7) (p 9)
  have hv6_7_9 : 0 < v6_7_9 := by
    have hs := h 6 7 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 6 7 9)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 6 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_9_12 : ℝ := -area (p 6) (p 9) (p 12)
  have hv6_9_12 : 0 < v6_9_12 := by
    have hs := h 6 9 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 6 9 12)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 6 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_10_12 : ℝ := -area (p 6) (p 10) (p 12)
  have hv6_10_12 : 0 < v6_10_12 := by
    have hs := h 6 10 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 6 10 12)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 6 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_9 : ℝ := area (p 7) (p 8) (p 9)
  have hv7_8_9 : 0 < v7_8_9 := by
    have hs := h 7 8 9 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 7 8 9)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 7 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_9_12 : ℝ := -area (p 7) (p 9) (p 12)
  have hv7_9_12 : 0 < v7_9_12 := by
    have hs := h 7 9 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 7 9 12)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 7 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := -area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 8 9 10)) = false := by decide
    change 0 < (if signature_569.testBit (285-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_12 : ℝ := area (p 8) (p 10) (p 12)
  have hv8_10_12 : 0 < v8_10_12 := by
    have hs := h 8 10 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 8 10 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 8 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_12 : ℝ := area (p 9) (p 10) (p 12)
  have hv9_10_12 : 0 < v9_10_12 := by
    have hs := h 9 10 12 (by decide) (by decide)
    have bit : (signature_569.testBit (285-lexRank 9 10 12)) = true := by decide
    change 0 < (if signature_569.testBit (285-lexRank 9 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_2_3 * v0_6_9 ∧ v0_2_3 * v0_6_9 < v0_2_6 * v0_3_9 := by
    have ident : v0_2_6 * v0_3_9 = v0_2_3 * v0_6_9 + v0_2_9 * v0_3_6 := by
      dsimp only [v0_2_3, v0_2_6, v0_2_9, v0_3_6, v0_3_9, v0_6_9, area]
      ring
    refine ⟨mul_pos hv0_2_3 hv0_6_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_9 hv0_3_6)
  have row1 : 0 < v0_2_6 * v2_3_12 ∧ v0_2_6 * v2_3_12 < v0_2_3 * v2_6_12 := by
    have ident : v0_2_3 * v2_6_12 = v0_2_6 * v2_3_12 + v0_2_12 * v2_3_6 := by
      dsimp only [v0_2_3, v0_2_6, v0_2_12, v2_3_6, v2_3_12, v2_6_12, area]
      ring
    refine ⟨mul_pos hv0_2_6 hv2_3_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_3_6)
  have row2 : 0 < v2_3_8 * v3_7_12 ∧ v2_3_8 * v3_7_12 < v2_3_12 * v3_7_8 := by
    have ident : v2_3_12 * v3_7_8 = v2_3_8 * v3_7_12 + v2_3_7 * v3_8_12 := by
      dsimp only [v2_3_7, v2_3_8, v2_3_12, v3_7_8, v3_7_12, v3_8_12, area]
      ring
    refine ⟨mul_pos hv2_3_8 hv3_7_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_3_7 hv3_8_12)
  have row3 : 0 < v3_7_8 * v7_9_12 ∧ v3_7_8 * v7_9_12 < v3_7_12 * v7_8_9 := by
    have ident : v3_7_12 * v7_8_9 = v3_7_8 * v7_9_12 + v3_7_9 * v7_8_12 := by
      dsimp only [v3_7_8, v3_7_9, v3_7_12, v7_8_9, v7_8_12, v7_9_12, area]
      ring
    refine ⟨mul_pos hv3_7_8 hv7_9_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_7_9 hv7_8_12)
  have row4 : 0 < v2_8_10 * v3_8_9 ∧ v2_8_10 * v3_8_9 < v2_3_8 * v8_9_10 := by
    have ident : v2_3_8 * v8_9_10 = v2_8_10 * v3_8_9 + v2_8_9 * v3_8_10 := by
      dsimp only [v2_3_8, v2_8_9, v2_8_10, v3_8_9, v3_8_10, v8_9_10, area]
      ring
    refine ⟨mul_pos hv2_8_10 hv3_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_8_9 hv3_8_10)
  have row5 : 0 < v0_3_9 * v7_8_9 ∧ v0_3_9 * v7_8_9 < v0_7_9 * v3_8_9 := by
    have ident : v0_7_9 * v3_8_9 = v0_3_9 * v7_8_9 + v0_8_9 * v3_7_9 := by
      dsimp only [v0_3_9, v0_7_9, v0_8_9, v3_7_9, v3_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv0_3_9 hv7_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_9 hv3_7_9)
  have row6 : 0 < v0_7_9 * v6_9_12 ∧ v0_7_9 * v6_9_12 < v0_6_9 * v7_9_12 := by
    have ident : v0_6_9 * v7_9_12 = v0_7_9 * v6_9_12 + v0_9_12 * v6_7_9 := by
      dsimp only [v0_6_9, v0_7_9, v0_9_12, v6_7_9, v6_9_12, v7_9_12, area]
      ring
    refine ⟨mul_pos hv0_7_9 hv6_9_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_12 hv6_7_9)
  have row7 : 0 < v2_10_12 * v8_9_10 ∧ v2_10_12 * v8_9_10 < v2_8_10 * v9_10_12 := by
    have ident : v2_8_10 * v9_10_12 = v2_10_12 * v8_9_10 + v2_9_10 * v8_10_12 := by
      dsimp only [v2_8_10, v2_9_10, v2_10_12, v8_9_10, v8_10_12, v9_10_12, area]
      ring
    refine ⟨mul_pos hv2_10_12 hv8_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_9_10 hv8_10_12)
  have row8 : 0 < v2_6_12 * v9_10_12 ∧ v2_6_12 * v9_10_12 < v2_10_12 * v6_9_12 := by
    have ident : v2_10_12 * v6_9_12 = v2_6_12 * v9_10_12 + v2_9_12 * v6_10_12 := by
      dsimp only [v2_6_12, v2_9_12, v2_10_12, v6_9_12, v6_10_12, v9_10_12, area]
      ring
    refine ⟨mul_pos hv2_6_12 hv9_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_9_12 hv6_10_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_569
end ThirteenPointExclusions
