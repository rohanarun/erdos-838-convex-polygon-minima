import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exclusions of enumerated fourteen-point order-type signatures over the reals.
The hypotheses use one bit per increasing triple in lexicographic order,
with bit one meaning a strictly positive signed area. -/
namespace FourteenPointExclusions

def area (a b c : ℝ × ℝ) : ℝ :=
  (b.1-a.1)*(c.2-a.2) - (c.1-a.1)*(b.2-a.2)

/-- Zero-based lexicographic rank of (i,j,k) for i<j<k<14. The first difference
counts triples with smaller first index, the second counts pairs with smaller
second index, and the final term counts smaller third indices. -/
def lexRank (i j k : ℕ) : ℕ :=
  (364 - (14-i).choose 3) + ((13-i).choose 2 - (14-j).choose 2) + (k-j-1)

def Realizes (bits : ℕ) (p : Fin 14 → ℝ × ℝ) : Prop :=
  ∀ (i j k : Fin 14), i < j → j < k →
    0 < (if bits.testBit (363-lexRank i.val j.val k.val)
         then area (p i) (p j) (p k) else -area (p i) (p j) (p k))

theorem merge {a b c d : ℝ} (u : 0 < a ∧ a < b)
    (v : 0 < c ∧ c < d) : 0 < a*c ∧ a*c < b*d :=
  ⟨mul_pos u.1 v.1, lt_trans (mul_lt_mul_of_pos_right u.2 v.1)
    (mul_lt_mul_of_pos_left v.2 (lt_trans u.1 u.2))⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def signature_778_0 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111111111111111111000001011011111111111111111111010111111011111011111111111111111111111111111001111111111100100001000100000000000100001000100000000001011111100011111110001100000001110

theorem no_realization_778_0 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_778_0 p := by
  intro h
  let v0_1_4 : ℝ := -area (p 0) (p 1) (p 4)
  have hv0_1_4 : 0 < v0_1_4 := by
    have hs := h 0 1 4 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 1 4)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 1 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_10 : ℝ := -area (p 0) (p 4) (p 10)
  have hv0_4_10 : 0 < v0_4_10 := by
    have hs := h 0 4 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 4 10)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_11 : ℝ := -area (p 0) (p 4) (p 11)
  have hv0_4_11 : 0 < v0_4_11 := by
    have hs := h 0 4 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 4 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_4 : ℝ := area (p 1) (p 2) (p 4)
  have hv1_2_4 : 0 < v1_2_4 := by
    have hs := h 1 2 4 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 2 4)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_8 : ℝ := -area (p 1) (p 4) (p 8)
  have hv1_4_8 : 0 < v1_4_8 := by
    have hs := h 1 4 8 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 4 8)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_9 : ℝ := -area (p 1) (p 4) (p 9)
  have hv1_4_9 : 0 < v1_4_9 := by
    have hs := h 1 4 9 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 4 9)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_11 : ℝ := area (p 1) (p 4) (p 11)
  have hv1_4_11 : 0 < v1_4_11 := by
    have hs := h 1 4 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 4 11)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_8 : ℝ := -area (p 2) (p 4) (p 8)
  have hv2_4_8 : 0 < v2_4_8 := by
    have hs := h 2 4 8 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 4 8)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_9 : ℝ := -area (p 2) (p 4) (p 9)
  have hv2_4_9 : 0 < v2_4_9 := by
    have hs := h 2 4 9 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 4 9)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 4 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 4 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_11 : ℝ := -area (p 3) (p 4) (p 11)
  have hv3_4_11 : 0 < v3_4_11 := by
    have hs := h 3 4 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 4 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_9 : ℝ := area (p 4) (p 8) (p 9)
  have hv4_8_9 : 0 < v4_8_9 := by
    have hs := h 4 8 9 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 4 8 9)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 4 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_11 : ℝ := area (p 4) (p 8) (p 11)
  have hv4_8_11 : 0 < v4_8_11 := by
    have hs := h 4 8 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 4 8 11)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 4 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := -area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 4 10 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_778_0.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_778_0.testBit (363-lexRank 9 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_1_4 * v0_10_11 ∧ v0_1_4 * v0_10_11 < v0_1_10 * v0_4_11 := by
    have ident : v0_1_10 * v0_4_11 = v0_1_4 * v0_10_11 + v0_1_11 * v0_4_10 := by
      dsimp only [v0_1_4, v0_1_10, v0_1_11, v0_4_10, v0_4_11, v0_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_4 hv0_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_11 hv0_4_10)
  have row1 : 0 < v2_4_9 * v2_8_10 ∧ v2_4_9 * v2_8_10 < v2_4_8 * v2_9_10 := by
    have ident : v2_4_8 * v2_9_10 = v2_4_9 * v2_8_10 + v2_4_10 * v2_8_9 := by
      dsimp only [v2_4_8, v2_4_9, v2_4_10, v2_8_9, v2_8_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_4_9 hv2_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_4_10 hv2_8_9)
  have row2 : 0 < v3_4_11 * v3_9_10 ∧ v3_4_11 * v3_9_10 < v3_4_9 * v3_10_11 := by
    have ident : v3_4_9 * v3_10_11 = v3_4_11 * v3_9_10 + v3_4_10 * v3_9_11 := by
      dsimp only [v3_4_9, v3_4_10, v3_4_11, v3_9_10, v3_9_11, v3_10_11, area]
      ring
    refine ⟨mul_pos hv3_4_11 hv3_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_10 hv3_9_11)
  have row3 : 0 < v0_4_11 * v1_4_8 ∧ v0_4_11 * v1_4_8 < v0_1_4 * v4_8_11 := by
    have ident : v0_1_4 * v4_8_11 = v0_4_11 * v1_4_8 + v0_4_8 * v1_4_11 := by
      dsimp only [v0_1_4, v0_4_8, v0_4_11, v1_4_8, v1_4_11, v4_8_11, area]
      ring
    refine ⟨mul_pos hv0_4_11 hv1_4_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_4_8 hv1_4_11)
  have row4 : 0 < v1_4_9 * v2_4_8 ∧ v1_4_9 * v2_4_8 < v1_4_8 * v2_4_9 := by
    have ident : v1_4_8 * v2_4_9 = v1_4_9 * v2_4_8 + v1_2_4 * v4_8_9 := by
      dsimp only [v1_2_4, v1_4_8, v1_4_9, v2_4_8, v2_4_9, v4_8_9, area]
      ring
    refine ⟨mul_pos hv1_4_9 hv2_4_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_4 hv4_8_9)
  have row5 : 0 < v1_9_10 * v3_4_9 ∧ v1_9_10 * v3_4_9 < v1_4_9 * v3_9_10 := by
    have ident : v1_4_9 * v3_9_10 = v1_9_10 * v3_4_9 + v1_3_9 * v4_9_10 := by
      dsimp only [v1_3_9, v1_4_9, v1_9_10, v3_4_9, v3_9_10, v4_9_10, area]
      ring
    refine ⟨mul_pos hv1_9_10 hv3_4_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_9 hv4_9_10)
  have row6 : 0 < v0_1_10 * v9_10_11 ∧ v0_1_10 * v9_10_11 < v0_10_11 * v1_9_10 := by
    have ident : v0_10_11 * v1_9_10 = v0_1_10 * v9_10_11 + v0_9_10 * v1_10_11 := by
      dsimp only [v0_1_10, v0_9_10, v0_10_11, v1_9_10, v1_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_10 hv9_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_10 hv1_10_11)
  have row7 : 0 < v2_9_10 * v8_10_11 ∧ v2_9_10 * v8_10_11 < v2_8_10 * v9_10_11 := by
    have ident : v2_8_10 * v9_10_11 = v2_9_10 * v8_10_11 + v2_10_11 * v8_9_10 := by
      dsimp only [v2_8_10, v2_9_10, v2_10_11, v8_9_10, v8_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv2_9_10 hv8_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_11 hv8_9_10)
  have row8 : 0 < v3_10_11 * v4_8_11 ∧ v3_10_11 * v4_8_11 < v3_4_11 * v8_10_11 := by
    have ident : v3_4_11 * v8_10_11 = v3_10_11 * v4_8_11 + v3_8_11 * v4_10_11 := by
      dsimp only [v3_4_11, v3_8_11, v3_10_11, v4_8_11, v4_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv3_10_11 hv4_8_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_11 hv4_10_11)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_778_0

def signature_779_1 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111111111111111111000001011011111111111111111111010111111011111011111111111111111111111111111001111111111100100001000100000000000100001000100000000001001111100011111110001110000001110

theorem no_realization_779_1 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_779_1 p := by
  intro h
  let v0_1_4 : ℝ := -area (p 0) (p 1) (p 4)
  have hv0_1_4 : 0 < v0_1_4 := by
    have hs := h 0 1 4 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 1 4)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 1 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_10 : ℝ := -area (p 0) (p 4) (p 10)
  have hv0_4_10 : 0 < v0_4_10 := by
    have hs := h 0 4 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 4 10)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_11 : ℝ := -area (p 0) (p 4) (p 11)
  have hv0_4_11 : 0 < v0_4_11 := by
    have hs := h 0 4 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 4 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_4 : ℝ := area (p 1) (p 2) (p 4)
  have hv1_2_4 : 0 < v1_2_4 := by
    have hs := h 1 2 4 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 2 4)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_8 : ℝ := -area (p 1) (p 4) (p 8)
  have hv1_4_8 : 0 < v1_4_8 := by
    have hs := h 1 4 8 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 4 8)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_9 : ℝ := -area (p 1) (p 4) (p 9)
  have hv1_4_9 : 0 < v1_4_9 := by
    have hs := h 1 4 9 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 4 9)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_11 : ℝ := area (p 1) (p 4) (p 11)
  have hv1_4_11 : 0 < v1_4_11 := by
    have hs := h 1 4 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 4 11)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_8 : ℝ := -area (p 2) (p 4) (p 8)
  have hv2_4_8 : 0 < v2_4_8 := by
    have hs := h 2 4 8 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 4 8)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_9 : ℝ := -area (p 2) (p 4) (p 9)
  have hv2_4_9 : 0 < v2_4_9 := by
    have hs := h 2 4 9 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 4 9)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 4 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 4 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_11 : ℝ := -area (p 3) (p 4) (p 11)
  have hv3_4_11 : 0 < v3_4_11 := by
    have hs := h 3 4 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 4 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_9 : ℝ := area (p 4) (p 8) (p 9)
  have hv4_8_9 : 0 < v4_8_9 := by
    have hs := h 4 8 9 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 4 8 9)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 4 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_11 : ℝ := area (p 4) (p 8) (p 11)
  have hv4_8_11 : 0 < v4_8_11 := by
    have hs := h 4 8 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 4 8 11)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 4 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := -area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 4 10 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_779_1.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_779_1.testBit (363-lexRank 9 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_1_4 * v0_10_11 ∧ v0_1_4 * v0_10_11 < v0_1_10 * v0_4_11 := by
    have ident : v0_1_10 * v0_4_11 = v0_1_4 * v0_10_11 + v0_1_11 * v0_4_10 := by
      dsimp only [v0_1_4, v0_1_10, v0_1_11, v0_4_10, v0_4_11, v0_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_4 hv0_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_11 hv0_4_10)
  have row1 : 0 < v2_4_9 * v2_8_10 ∧ v2_4_9 * v2_8_10 < v2_4_8 * v2_9_10 := by
    have ident : v2_4_8 * v2_9_10 = v2_4_9 * v2_8_10 + v2_4_10 * v2_8_9 := by
      dsimp only [v2_4_8, v2_4_9, v2_4_10, v2_8_9, v2_8_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_4_9 hv2_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_4_10 hv2_8_9)
  have row2 : 0 < v3_4_11 * v3_9_10 ∧ v3_4_11 * v3_9_10 < v3_4_9 * v3_10_11 := by
    have ident : v3_4_9 * v3_10_11 = v3_4_11 * v3_9_10 + v3_4_10 * v3_9_11 := by
      dsimp only [v3_4_9, v3_4_10, v3_4_11, v3_9_10, v3_9_11, v3_10_11, area]
      ring
    refine ⟨mul_pos hv3_4_11 hv3_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_10 hv3_9_11)
  have row3 : 0 < v0_4_11 * v1_4_8 ∧ v0_4_11 * v1_4_8 < v0_1_4 * v4_8_11 := by
    have ident : v0_1_4 * v4_8_11 = v0_4_11 * v1_4_8 + v0_4_8 * v1_4_11 := by
      dsimp only [v0_1_4, v0_4_8, v0_4_11, v1_4_8, v1_4_11, v4_8_11, area]
      ring
    refine ⟨mul_pos hv0_4_11 hv1_4_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_4_8 hv1_4_11)
  have row4 : 0 < v1_4_9 * v2_4_8 ∧ v1_4_9 * v2_4_8 < v1_4_8 * v2_4_9 := by
    have ident : v1_4_8 * v2_4_9 = v1_4_9 * v2_4_8 + v1_2_4 * v4_8_9 := by
      dsimp only [v1_2_4, v1_4_8, v1_4_9, v2_4_8, v2_4_9, v4_8_9, area]
      ring
    refine ⟨mul_pos hv1_4_9 hv2_4_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_4 hv4_8_9)
  have row5 : 0 < v1_9_10 * v3_4_9 ∧ v1_9_10 * v3_4_9 < v1_4_9 * v3_9_10 := by
    have ident : v1_4_9 * v3_9_10 = v1_9_10 * v3_4_9 + v1_3_9 * v4_9_10 := by
      dsimp only [v1_3_9, v1_4_9, v1_9_10, v3_4_9, v3_9_10, v4_9_10, area]
      ring
    refine ⟨mul_pos hv1_9_10 hv3_4_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_9 hv4_9_10)
  have row6 : 0 < v0_1_10 * v9_10_11 ∧ v0_1_10 * v9_10_11 < v0_10_11 * v1_9_10 := by
    have ident : v0_10_11 * v1_9_10 = v0_1_10 * v9_10_11 + v0_9_10 * v1_10_11 := by
      dsimp only [v0_1_10, v0_9_10, v0_10_11, v1_9_10, v1_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_10 hv9_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_10 hv1_10_11)
  have row7 : 0 < v2_9_10 * v8_10_11 ∧ v2_9_10 * v8_10_11 < v2_8_10 * v9_10_11 := by
    have ident : v2_8_10 * v9_10_11 = v2_9_10 * v8_10_11 + v2_10_11 * v8_9_10 := by
      dsimp only [v2_8_10, v2_9_10, v2_10_11, v8_9_10, v8_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv2_9_10 hv8_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_11 hv8_9_10)
  have row8 : 0 < v3_10_11 * v4_8_11 ∧ v3_10_11 * v4_8_11 < v3_4_11 * v8_10_11 := by
    have ident : v3_4_11 * v8_10_11 = v3_10_11 * v4_8_11 + v3_8_11 * v4_10_11 := by
      dsimp only [v3_4_11, v3_8_11, v3_10_11, v4_8_11, v4_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv3_10_11 hv4_8_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_11 hv4_10_11)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_779_1

def signature_779_2 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111111111111111111000001011011111111111111111111010111111011111011111111111111111111111111111001111111111100100001000110000000000100001000100000000001011111100011111110001100000001110

theorem no_realization_779_2 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_779_2 p := by
  intro h
  let v0_2_3 : ℝ := -area (p 0) (p 2) (p 3)
  have hv0_2_3 : 0 < v0_2_3 := by
    have hs := h 0 2 3 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 2 3)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 2 3) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_5 : ℝ := -area (p 0) (p 2) (p 5)
  have hv0_2_5 : 0 < v0_2_5 := by
    have hs := h 0 2 5 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 2 5)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 2 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_10 : ℝ := -area (p 0) (p 2) (p 10)
  have hv0_2_10 : 0 < v0_2_10 := by
    have hs := h 0 2 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 2 10)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 2 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_5 : ℝ := -area (p 0) (p 3) (p 5)
  have hv0_3_5 : 0 < v0_3_5 := by
    have hs := h 0 3 5 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 3 5)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 3 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_10 : ℝ := -area (p 0) (p 3) (p 10)
  have hv0_3_10 : 0 < v0_3_10 := by
    have hs := h 0 3 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 3 10)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 3 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_10 : ℝ := -area (p 0) (p 5) (p 10)
  have hv0_5_10 : 0 < v0_5_10 := by
    have hs := h 0 5 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 5 10)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_10 : ℝ := -area (p 0) (p 7) (p 10)
  have hv0_7_10 : 0 < v0_7_10 := by
    have hs := h 0 7 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 7 10)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_10 : ℝ := -area (p 0) (p 8) (p 10)
  have hv0_8_10 : 0 < v0_8_10 := by
    have hs := h 0 8 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 8 10)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_12 : ℝ := -area (p 0) (p 10) (p 12)
  have hv0_10_12 : 0 < v0_10_12 := by
    have hs := h 0 10 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 0 10 12)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 0 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_5 : ℝ := -area (p 2) (p 3) (p 5)
  have hv2_3_5 : 0 < v2_3_5 := by
    have hs := h 2 3 5 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 3 5)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 3 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_7 : ℝ := -area (p 2) (p 3) (p 7)
  have hv2_3_7 : 0 < v2_3_7 := by
    have hs := h 2 3 7 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 3 7)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_8 : ℝ := area (p 2) (p 3) (p 8)
  have hv2_3_8 : 0 < v2_3_8 := by
    have hs := h 2 3 8 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 3 8)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_5_12 : ℝ := area (p 2) (p 5) (p 12)
  have hv2_5_12 : 0 < v2_5_12 := by
    have hs := h 2 5 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 5 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_11 : ℝ := area (p 2) (p 8) (p 11)
  have hv2_8_11 : 0 < v2_8_11 := by
    have hs := h 2 8 11 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 8 11)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_12 : ℝ := area (p 2) (p 10) (p 12)
  have hv2_10_12 : 0 < v2_10_12 := by
    have hs := h 2 10 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 10 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_11_12 : ℝ := area (p 2) (p 11) (p 12)
  have hv2_11_12 : 0 < v2_11_12 := by
    have hs := h 2 11 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 2 11 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 2 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_8 : ℝ := area (p 3) (p 7) (p 8)
  have hv3_7_8 : 0 < v3_7_8 := by
    have hs := h 3 7 8 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 3 7 8)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 3 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_10 : ℝ := area (p 3) (p 7) (p 10)
  have hv3_7_10 : 0 < v3_7_10 := by
    have hs := h 3 7 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 3 7 10)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 3 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_12 : ℝ := area (p 3) (p 7) (p 12)
  have hv3_7_12 : 0 < v3_7_12 := by
    have hs := h 3 7 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 3 7 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 3 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_10 : ℝ := area (p 3) (p 8) (p 10)
  have hv3_8_10 : 0 < v3_8_10 := by
    have hs := h 3 8 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 3 8 10)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 3 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_12 : ℝ := area (p 3) (p 8) (p 12)
  have hv3_8_12 : 0 < v3_8_12 := by
    have hs := h 3 8 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 3 8 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 3 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_10 : ℝ := area (p 5) (p 7) (p 10)
  have hv5_7_10 : 0 < v5_7_10 := by
    have hs := h 5 7 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 5 7 10)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 5 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_12 : ℝ := -area (p 5) (p 10) (p 12)
  have hv5_10_12 : 0 < v5_10_12 := by
    have hs := h 5 10 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 5 10 12)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 5 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_11_12 : ℝ := -area (p 5) (p 11) (p 12)
  have hv5_11_12 : 0 < v5_11_12 := by
    have hs := h 5 11 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 5 11 12)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 5 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_10 : ℝ := area (p 7) (p 8) (p 10)
  have hv7_8_10 : 0 < v7_8_10 := by
    have hs := h 7 8 10 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 7 8 10)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 7 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_12 : ℝ := -area (p 7) (p 10) (p 12)
  have hv7_10_12 : 0 < v7_10_12 := by
    have hs := h 7 10 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 7 10 12)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 7 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_11_12 : ℝ := area (p 8) (p 11) (p 12)
  have hv8_11_12 : 0 < v8_11_12 := by
    have hs := h 8 11 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 8 11 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 8 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v10_11_12 : ℝ := area (p 10) (p 11) (p 12)
  have hv10_11_12 : 0 < v10_11_12 := by
    have hs := h 10 11 12 (by decide) (by decide)
    have bit : (signature_779_2.testBit (363-lexRank 10 11 12)) = true := by decide
    change 0 < (if signature_779_2.testBit (363-lexRank 10 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_2_3 * v0_5_10 ∧ v0_2_3 * v0_5_10 < v0_2_5 * v0_3_10 := by
    have ident : v0_2_5 * v0_3_10 = v0_2_3 * v0_5_10 + v0_2_10 * v0_3_5 := by
      dsimp only [v0_2_3, v0_2_5, v0_2_10, v0_3_5, v0_3_10, v0_5_10, area]
      ring
    refine ⟨mul_pos hv0_2_3 hv0_5_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_10 hv0_3_5)
  have row1 : 0 < v0_2_5 * v2_3_12 ∧ v0_2_5 * v2_3_12 < v0_2_3 * v2_5_12 := by
    have ident : v0_2_3 * v2_5_12 = v0_2_5 * v2_3_12 + v0_2_12 * v2_3_5 := by
      dsimp only [v0_2_3, v0_2_5, v0_2_12, v2_3_5, v2_3_12, v2_5_12, area]
      ring
    refine ⟨mul_pos hv0_2_5 hv2_3_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_3_5)
  have row2 : 0 < v2_3_8 * v3_7_12 ∧ v2_3_8 * v3_7_12 < v2_3_12 * v3_7_8 := by
    have ident : v2_3_12 * v3_7_8 = v2_3_8 * v3_7_12 + v2_3_7 * v3_8_12 := by
      dsimp only [v2_3_7, v2_3_8, v2_3_12, v3_7_8, v3_7_12, v3_8_12, area]
      ring
    refine ⟨mul_pos hv2_3_8 hv3_7_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_3_7 hv3_8_12)
  have row3 : 0 < v3_7_8 * v7_10_12 ∧ v3_7_8 * v7_10_12 < v3_7_12 * v7_8_10 := by
    have ident : v3_7_12 * v7_8_10 = v3_7_8 * v7_10_12 + v3_7_10 * v7_8_12 := by
      dsimp only [v3_7_8, v3_7_10, v3_7_12, v7_8_10, v7_8_12, v7_10_12, area]
      ring
    refine ⟨mul_pos hv3_7_8 hv7_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_7_10 hv7_8_12)
  have row4 : 0 < v2_8_11 * v3_8_10 ∧ v2_8_11 * v3_8_10 < v2_3_8 * v8_10_11 := by
    have ident : v2_3_8 * v8_10_11 = v2_8_11 * v3_8_10 + v2_8_10 * v3_8_11 := by
      dsimp only [v2_3_8, v2_8_10, v2_8_11, v3_8_10, v3_8_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv2_8_11 hv3_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_8_10 hv3_8_11)
  have row5 : 0 < v0_3_10 * v7_8_10 ∧ v0_3_10 * v7_8_10 < v0_7_10 * v3_8_10 := by
    have ident : v0_7_10 * v3_8_10 = v0_3_10 * v7_8_10 + v0_8_10 * v3_7_10 := by
      dsimp only [v0_3_10, v0_7_10, v0_8_10, v3_7_10, v3_8_10, v7_8_10, area]
      ring
    refine ⟨mul_pos hv0_3_10 hv7_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_10 hv3_7_10)
  have row6 : 0 < v0_7_10 * v5_10_12 ∧ v0_7_10 * v5_10_12 < v0_5_10 * v7_10_12 := by
    have ident : v0_5_10 * v7_10_12 = v0_7_10 * v5_10_12 + v0_10_12 * v5_7_10 := by
      dsimp only [v0_5_10, v0_7_10, v0_10_12, v5_7_10, v5_10_12, v7_10_12, area]
      ring
    refine ⟨mul_pos hv0_7_10 hv5_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_10_12 hv5_7_10)
  have row7 : 0 < v2_11_12 * v8_10_11 ∧ v2_11_12 * v8_10_11 < v2_8_11 * v10_11_12 := by
    have ident : v2_8_11 * v10_11_12 = v2_11_12 * v8_10_11 + v2_10_11 * v8_11_12 := by
      dsimp only [v2_8_11, v2_10_11, v2_11_12, v8_10_11, v8_11_12, v10_11_12, area]
      ring
    refine ⟨mul_pos hv2_11_12 hv8_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_11 hv8_11_12)
  have row8 : 0 < v2_5_12 * v10_11_12 ∧ v2_5_12 * v10_11_12 < v2_11_12 * v5_10_12 := by
    have ident : v2_11_12 * v5_10_12 = v2_5_12 * v10_11_12 + v2_10_12 * v5_11_12 := by
      dsimp only [v2_5_12, v2_10_12, v2_11_12, v5_10_12, v5_11_12, v10_11_12, area]
      ring
    refine ⟨mul_pos hv2_5_12 hv10_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_12 hv5_11_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_779_2

def signature_779_3 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111111111111111111000001011011111111111111111111010111111011111011111111111111111111111111111011111111111100100001000100000000000100001000100000000001011111100011111110001100000001110

theorem no_realization_779_3 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_779_3 p := by
  intro h
  let v0_1_4 : ℝ := -area (p 0) (p 1) (p 4)
  have hv0_1_4 : 0 < v0_1_4 := by
    have hs := h 0 1 4 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 1 4)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 1 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_10 : ℝ := -area (p 0) (p 4) (p 10)
  have hv0_4_10 : 0 < v0_4_10 := by
    have hs := h 0 4 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 4 10)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_11 : ℝ := -area (p 0) (p 4) (p 11)
  have hv0_4_11 : 0 < v0_4_11 := by
    have hs := h 0 4 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 4 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_4 : ℝ := area (p 1) (p 2) (p 4)
  have hv1_2_4 : 0 < v1_2_4 := by
    have hs := h 1 2 4 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 2 4)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_8 : ℝ := -area (p 1) (p 4) (p 8)
  have hv1_4_8 : 0 < v1_4_8 := by
    have hs := h 1 4 8 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 4 8)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_9 : ℝ := -area (p 1) (p 4) (p 9)
  have hv1_4_9 : 0 < v1_4_9 := by
    have hs := h 1 4 9 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 4 9)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_11 : ℝ := area (p 1) (p 4) (p 11)
  have hv1_4_11 : 0 < v1_4_11 := by
    have hs := h 1 4 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 4 11)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_8 : ℝ := -area (p 2) (p 4) (p 8)
  have hv2_4_8 : 0 < v2_4_8 := by
    have hs := h 2 4 8 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 4 8)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_9 : ℝ := -area (p 2) (p 4) (p 9)
  have hv2_4_9 : 0 < v2_4_9 := by
    have hs := h 2 4 9 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 4 9)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 4 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 4 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_11 : ℝ := -area (p 3) (p 4) (p 11)
  have hv3_4_11 : 0 < v3_4_11 := by
    have hs := h 3 4 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 4 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_9 : ℝ := area (p 4) (p 8) (p 9)
  have hv4_8_9 : 0 < v4_8_9 := by
    have hs := h 4 8 9 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 4 8 9)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 4 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_11 : ℝ := area (p 4) (p 8) (p 11)
  have hv4_8_11 : 0 < v4_8_11 := by
    have hs := h 4 8 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 4 8 11)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 4 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := -area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 4 10 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_779_3.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_779_3.testBit (363-lexRank 9 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_1_4 * v0_10_11 ∧ v0_1_4 * v0_10_11 < v0_1_10 * v0_4_11 := by
    have ident : v0_1_10 * v0_4_11 = v0_1_4 * v0_10_11 + v0_1_11 * v0_4_10 := by
      dsimp only [v0_1_4, v0_1_10, v0_1_11, v0_4_10, v0_4_11, v0_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_4 hv0_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_11 hv0_4_10)
  have row1 : 0 < v2_4_9 * v2_8_10 ∧ v2_4_9 * v2_8_10 < v2_4_8 * v2_9_10 := by
    have ident : v2_4_8 * v2_9_10 = v2_4_9 * v2_8_10 + v2_4_10 * v2_8_9 := by
      dsimp only [v2_4_8, v2_4_9, v2_4_10, v2_8_9, v2_8_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_4_9 hv2_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_4_10 hv2_8_9)
  have row2 : 0 < v3_4_11 * v3_9_10 ∧ v3_4_11 * v3_9_10 < v3_4_9 * v3_10_11 := by
    have ident : v3_4_9 * v3_10_11 = v3_4_11 * v3_9_10 + v3_4_10 * v3_9_11 := by
      dsimp only [v3_4_9, v3_4_10, v3_4_11, v3_9_10, v3_9_11, v3_10_11, area]
      ring
    refine ⟨mul_pos hv3_4_11 hv3_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_10 hv3_9_11)
  have row3 : 0 < v0_4_11 * v1_4_8 ∧ v0_4_11 * v1_4_8 < v0_1_4 * v4_8_11 := by
    have ident : v0_1_4 * v4_8_11 = v0_4_11 * v1_4_8 + v0_4_8 * v1_4_11 := by
      dsimp only [v0_1_4, v0_4_8, v0_4_11, v1_4_8, v1_4_11, v4_8_11, area]
      ring
    refine ⟨mul_pos hv0_4_11 hv1_4_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_4_8 hv1_4_11)
  have row4 : 0 < v1_4_9 * v2_4_8 ∧ v1_4_9 * v2_4_8 < v1_4_8 * v2_4_9 := by
    have ident : v1_4_8 * v2_4_9 = v1_4_9 * v2_4_8 + v1_2_4 * v4_8_9 := by
      dsimp only [v1_2_4, v1_4_8, v1_4_9, v2_4_8, v2_4_9, v4_8_9, area]
      ring
    refine ⟨mul_pos hv1_4_9 hv2_4_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_4 hv4_8_9)
  have row5 : 0 < v1_9_10 * v3_4_9 ∧ v1_9_10 * v3_4_9 < v1_4_9 * v3_9_10 := by
    have ident : v1_4_9 * v3_9_10 = v1_9_10 * v3_4_9 + v1_3_9 * v4_9_10 := by
      dsimp only [v1_3_9, v1_4_9, v1_9_10, v3_4_9, v3_9_10, v4_9_10, area]
      ring
    refine ⟨mul_pos hv1_9_10 hv3_4_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_9 hv4_9_10)
  have row6 : 0 < v0_1_10 * v9_10_11 ∧ v0_1_10 * v9_10_11 < v0_10_11 * v1_9_10 := by
    have ident : v0_10_11 * v1_9_10 = v0_1_10 * v9_10_11 + v0_9_10 * v1_10_11 := by
      dsimp only [v0_1_10, v0_9_10, v0_10_11, v1_9_10, v1_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_10 hv9_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_10 hv1_10_11)
  have row7 : 0 < v2_9_10 * v8_10_11 ∧ v2_9_10 * v8_10_11 < v2_8_10 * v9_10_11 := by
    have ident : v2_8_10 * v9_10_11 = v2_9_10 * v8_10_11 + v2_10_11 * v8_9_10 := by
      dsimp only [v2_8_10, v2_9_10, v2_10_11, v8_9_10, v8_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv2_9_10 hv8_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_11 hv8_9_10)
  have row8 : 0 < v3_10_11 * v4_8_11 ∧ v3_10_11 * v4_8_11 < v3_4_11 * v8_10_11 := by
    have ident : v3_4_11 * v8_10_11 = v3_10_11 * v4_8_11 + v3_8_11 * v4_10_11 := by
      dsimp only [v3_4_11, v3_8_11, v3_10_11, v4_8_11, v4_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv3_10_11 hv4_8_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_11 hv4_10_11)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_779_3
end FourteenPointExclusions
