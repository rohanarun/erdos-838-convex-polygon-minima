import Exclusions14
namespace FourteenPointExclusions

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def signature_780_00 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000100111110011011110011011110111111111111110011110111111111111111001111111001111111011111111111111001111111111111111111001001011011111111111111001011010111111011111011111111111111001001010111111001111111111100100001000100000000000100001000100000000011111111100011111110001100000001110

theorem no_realization_780_00 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_00 p := by
  intro h
  let v0_1_7 : ℝ := -area (p 0) (p 1) (p 7)
  have hv0_1_7 : 0 < v0_1_7 := by
    have hs := h 0 1 7 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 1 7)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 1 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_8 : ℝ := -area (p 0) (p 7) (p 8)
  have hv0_7_8 : 0 < v0_7_8 := by
    have hs := h 0 7 8 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 7 8)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_10 : ℝ := -area (p 0) (p 7) (p 10)
  have hv0_7_10 : 0 < v0_7_10 := by
    have hs := h 0 7 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 7 10)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_11 : ℝ := -area (p 0) (p 7) (p 11)
  have hv0_7_11 : 0 < v0_7_11 := by
    have hs := h 0 7 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 7 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_7 : ℝ := area (p 1) (p 2) (p 7)
  have hv1_2_7 : 0 < v1_2_7 := by
    have hs := h 1 2 7 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 2 7)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 2 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_8 : ℝ := -area (p 1) (p 7) (p 8)
  have hv1_7_8 : 0 < v1_7_8 := by
    have hs := h 1 7 8 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 7 8)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_9 : ℝ := -area (p 1) (p 7) (p 9)
  have hv1_7_9 : 0 < v1_7_9 := by
    have hs := h 1 7 9 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 7 9)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_11 : ℝ := area (p 1) (p 7) (p 11)
  have hv1_7_11 : 0 < v1_7_11 := by
    have hs := h 1 7 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 7 11)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_8 : ℝ := -area (p 2) (p 7) (p 8)
  have hv2_7_8 : 0 < v2_7_8 := by
    have hs := h 2 7 8 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 7 8)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_9 : ℝ := -area (p 2) (p 7) (p 9)
  have hv2_7_9 : 0 < v2_7_9 := by
    have hs := h 2 7 9 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 7 9)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_10 : ℝ := area (p 2) (p 7) (p 10)
  have hv2_7_10 : 0 < v2_7_10 := by
    have hs := h 2 7 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 7 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_9 : ℝ := -area (p 3) (p 7) (p 9)
  have hv3_7_9 : 0 < v3_7_9 := by
    have hs := h 3 7 9 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 7 9)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_10 : ℝ := area (p 3) (p 7) (p 10)
  have hv3_7_10 : 0 < v3_7_10 := by
    have hs := h 3 7 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 7 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := -area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 7 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_9 : ℝ := area (p 7) (p 8) (p 9)
  have hv7_8_9 : 0 < v7_8_9 := by
    have hs := h 7 8 9 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 7 8 9)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 7 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_11 : ℝ := area (p 7) (p 8) (p 11)
  have hv7_8_11 : 0 < v7_8_11 := by
    have hs := h 7 8 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 7 8 11)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 7 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_9_10 : ℝ := area (p 7) (p 9) (p 10)
  have hv7_9_10 : 0 < v7_9_10 := by
    have hs := h 7 9 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 7 9 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 7 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_11 : ℝ := -area (p 7) (p 10) (p 11)
  have hv7_10_11 : 0 < v7_10_11 := by
    have hs := h 7 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 7 10 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 7 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_780_00.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_780_00.testBit (363-lexRank 9 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_1_7 * v0_10_11 ∧ v0_1_7 * v0_10_11 < v0_1_10 * v0_7_11 := by
    have ident : v0_1_10 * v0_7_11 = v0_1_7 * v0_10_11 + v0_1_11 * v0_7_10 := by
      dsimp only [v0_1_7, v0_1_10, v0_1_11, v0_7_10, v0_7_11, v0_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_7 hv0_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_11 hv0_7_10)
  have row1 : 0 < v2_7_9 * v2_8_10 ∧ v2_7_9 * v2_8_10 < v2_7_8 * v2_9_10 := by
    have ident : v2_7_8 * v2_9_10 = v2_7_9 * v2_8_10 + v2_7_10 * v2_8_9 := by
      dsimp only [v2_7_8, v2_7_9, v2_7_10, v2_8_9, v2_8_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_7_9 hv2_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_7_10 hv2_8_9)
  have row2 : 0 < v3_7_11 * v3_9_10 ∧ v3_7_11 * v3_9_10 < v3_7_9 * v3_10_11 := by
    have ident : v3_7_9 * v3_10_11 = v3_7_11 * v3_9_10 + v3_7_10 * v3_9_11 := by
      dsimp only [v3_7_9, v3_7_10, v3_7_11, v3_9_10, v3_9_11, v3_10_11, area]
      ring
    refine ⟨mul_pos hv3_7_11 hv3_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_7_10 hv3_9_11)
  have row3 : 0 < v0_7_11 * v1_7_8 ∧ v0_7_11 * v1_7_8 < v0_1_7 * v7_8_11 := by
    have ident : v0_1_7 * v7_8_11 = v0_7_11 * v1_7_8 + v0_7_8 * v1_7_11 := by
      dsimp only [v0_1_7, v0_7_8, v0_7_11, v1_7_8, v1_7_11, v7_8_11, area]
      ring
    refine ⟨mul_pos hv0_7_11 hv1_7_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_7_8 hv1_7_11)
  have row4 : 0 < v1_7_9 * v2_7_8 ∧ v1_7_9 * v2_7_8 < v1_7_8 * v2_7_9 := by
    have ident : v1_7_8 * v2_7_9 = v1_7_9 * v2_7_8 + v1_2_7 * v7_8_9 := by
      dsimp only [v1_2_7, v1_7_8, v1_7_9, v2_7_8, v2_7_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv1_7_9 hv2_7_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_7 hv7_8_9)
  have row5 : 0 < v1_9_10 * v3_7_9 ∧ v1_9_10 * v3_7_9 < v1_7_9 * v3_9_10 := by
    have ident : v1_7_9 * v3_9_10 = v1_9_10 * v3_7_9 + v1_3_9 * v7_9_10 := by
      dsimp only [v1_3_9, v1_7_9, v1_9_10, v3_7_9, v3_9_10, v7_9_10, area]
      ring
    refine ⟨mul_pos hv1_9_10 hv3_7_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_9 hv7_9_10)
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
  have row8 : 0 < v3_10_11 * v7_8_11 ∧ v3_10_11 * v7_8_11 < v3_7_11 * v8_10_11 := by
    have ident : v3_7_11 * v8_10_11 = v3_10_11 * v7_8_11 + v3_8_11 * v7_10_11 := by
      dsimp only [v3_7_11, v3_8_11, v3_10_11, v7_8_11, v7_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv3_10_11 hv7_8_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_11 hv7_10_11)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_00

def signature_780_01 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000001000111110101011110101011111011111100011111111110111111111111111010111111010111111101111110001111111111111111111111111010001011101111110001011111111010111111011111101111110001001111111010111111001111000100011111101000100000000011111111111111100011101000100000000011110001100000001110

theorem no_realization_780_01 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_01 p := by
  intro h
  let v0_1_6 : ℝ := -area (p 0) (p 1) (p 6)
  have hv0_1_6 : 0 < v0_1_6 := by
    have hs := h 0 1 6 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 1 6)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 1 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_8 : ℝ := -area (p 0) (p 6) (p 8)
  have hv0_6_8 : 0 < v0_6_8 := by
    have hs := h 0 6 8 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 6 8)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_10 : ℝ := -area (p 0) (p 6) (p 10)
  have hv0_6_10 : 0 < v0_6_10 := by
    have hs := h 0 6 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 6 10)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_11 : ℝ := -area (p 0) (p 6) (p 11)
  have hv0_6_11 : 0 < v0_6_11 := by
    have hs := h 0 6 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 6 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_6 : ℝ := area (p 1) (p 2) (p 6)
  have hv1_2_6 : 0 < v1_2_6 := by
    have hs := h 1 2 6 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 2 6)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_8 : ℝ := -area (p 1) (p 6) (p 8)
  have hv1_6_8 : 0 < v1_6_8 := by
    have hs := h 1 6 8 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 6 8)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_9 : ℝ := -area (p 1) (p 6) (p 9)
  have hv1_6_9 : 0 < v1_6_9 := by
    have hs := h 1 6 9 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 6 9)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_11 : ℝ := area (p 1) (p 6) (p 11)
  have hv1_6_11 : 0 < v1_6_11 := by
    have hs := h 1 6 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 6 11)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_8 : ℝ := -area (p 2) (p 6) (p 8)
  have hv2_6_8 : 0 < v2_6_8 := by
    have hs := h 2 6 8 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 6 8)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_9 : ℝ := -area (p 2) (p 6) (p 9)
  have hv2_6_9 : 0 < v2_6_9 := by
    have hs := h 2 6 9 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 6 9)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_10 : ℝ := area (p 2) (p 6) (p 10)
  have hv2_6_10 : 0 < v2_6_10 := by
    have hs := h 2 6 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 6 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_9 : ℝ := -area (p 3) (p 6) (p 9)
  have hv3_6_9 : 0 < v3_6_9 := by
    have hs := h 3 6 9 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 6 9)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_10 : ℝ := area (p 3) (p 6) (p 10)
  have hv3_6_10 : 0 < v3_6_10 := by
    have hs := h 3 6 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 6 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_11 : ℝ := -area (p 3) (p 6) (p 11)
  have hv3_6_11 : 0 < v3_6_11 := by
    have hs := h 3 6 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 6 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_8_9 : ℝ := area (p 6) (p 8) (p 9)
  have hv6_8_9 : 0 < v6_8_9 := by
    have hs := h 6 8 9 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 6 8 9)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 6 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_8_11 : ℝ := area (p 6) (p 8) (p 11)
  have hv6_8_11 : 0 < v6_8_11 := by
    have hs := h 6 8 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 6 8 11)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 6 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_9_10 : ℝ := area (p 6) (p 9) (p 10)
  have hv6_9_10 : 0 < v6_9_10 := by
    have hs := h 6 9 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 6 9 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 6 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_10_11 : ℝ := -area (p 6) (p 10) (p 11)
  have hv6_10_11 : 0 < v6_10_11 := by
    have hs := h 6 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 6 10 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 6 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_780_01.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_780_01.testBit (363-lexRank 9 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_1_6 * v0_10_11 ∧ v0_1_6 * v0_10_11 < v0_1_10 * v0_6_11 := by
    have ident : v0_1_10 * v0_6_11 = v0_1_6 * v0_10_11 + v0_1_11 * v0_6_10 := by
      dsimp only [v0_1_6, v0_1_10, v0_1_11, v0_6_10, v0_6_11, v0_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_6 hv0_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_11 hv0_6_10)
  have row1 : 0 < v2_6_9 * v2_8_10 ∧ v2_6_9 * v2_8_10 < v2_6_8 * v2_9_10 := by
    have ident : v2_6_8 * v2_9_10 = v2_6_9 * v2_8_10 + v2_6_10 * v2_8_9 := by
      dsimp only [v2_6_8, v2_6_9, v2_6_10, v2_8_9, v2_8_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_6_9 hv2_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_6_10 hv2_8_9)
  have row2 : 0 < v3_6_11 * v3_9_10 ∧ v3_6_11 * v3_9_10 < v3_6_9 * v3_10_11 := by
    have ident : v3_6_9 * v3_10_11 = v3_6_11 * v3_9_10 + v3_6_10 * v3_9_11 := by
      dsimp only [v3_6_9, v3_6_10, v3_6_11, v3_9_10, v3_9_11, v3_10_11, area]
      ring
    refine ⟨mul_pos hv3_6_11 hv3_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_6_10 hv3_9_11)
  have row3 : 0 < v0_6_11 * v1_6_8 ∧ v0_6_11 * v1_6_8 < v0_1_6 * v6_8_11 := by
    have ident : v0_1_6 * v6_8_11 = v0_6_11 * v1_6_8 + v0_6_8 * v1_6_11 := by
      dsimp only [v0_1_6, v0_6_8, v0_6_11, v1_6_8, v1_6_11, v6_8_11, area]
      ring
    refine ⟨mul_pos hv0_6_11 hv1_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_6_8 hv1_6_11)
  have row4 : 0 < v1_6_9 * v2_6_8 ∧ v1_6_9 * v2_6_8 < v1_6_8 * v2_6_9 := by
    have ident : v1_6_8 * v2_6_9 = v1_6_9 * v2_6_8 + v1_2_6 * v6_8_9 := by
      dsimp only [v1_2_6, v1_6_8, v1_6_9, v2_6_8, v2_6_9, v6_8_9, area]
      ring
    refine ⟨mul_pos hv1_6_9 hv2_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_6 hv6_8_9)
  have row5 : 0 < v1_9_10 * v3_6_9 ∧ v1_9_10 * v3_6_9 < v1_6_9 * v3_9_10 := by
    have ident : v1_6_9 * v3_9_10 = v1_9_10 * v3_6_9 + v1_3_9 * v6_9_10 := by
      dsimp only [v1_3_9, v1_6_9, v1_9_10, v3_6_9, v3_9_10, v6_9_10, area]
      ring
    refine ⟨mul_pos hv1_9_10 hv3_6_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_9 hv6_9_10)
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
  have row8 : 0 < v3_10_11 * v6_8_11 ∧ v3_10_11 * v6_8_11 < v3_6_11 * v8_10_11 := by
    have ident : v3_6_11 * v8_10_11 = v3_10_11 * v6_8_11 + v3_8_11 * v6_10_11 := by
      dsimp only [v3_6_11, v3_8_11, v3_10_11, v6_8_11, v6_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv3_10_11 hv6_8_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_11 hv6_10_11)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_01

def signature_780_02 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111111111111111111000001011011111111111111111111010111111011111011111111111111111111111111111001111111111100100001000110000000000100001000100000000001001111100011111110001110000001110

theorem no_realization_780_02 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_02 p := by
  intro h
  let v0_1_4 : ℝ := -area (p 0) (p 1) (p 4)
  have hv0_1_4 : 0 < v0_1_4 := by
    have hs := h 0 1 4 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 1 4)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 1 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_10 : ℝ := -area (p 0) (p 4) (p 10)
  have hv0_4_10 : 0 < v0_4_10 := by
    have hs := h 0 4 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 4 10)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_11 : ℝ := -area (p 0) (p 4) (p 11)
  have hv0_4_11 : 0 < v0_4_11 := by
    have hs := h 0 4 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 4 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_4 : ℝ := area (p 1) (p 2) (p 4)
  have hv1_2_4 : 0 < v1_2_4 := by
    have hs := h 1 2 4 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 2 4)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_8 : ℝ := -area (p 1) (p 4) (p 8)
  have hv1_4_8 : 0 < v1_4_8 := by
    have hs := h 1 4 8 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 4 8)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_9 : ℝ := -area (p 1) (p 4) (p 9)
  have hv1_4_9 : 0 < v1_4_9 := by
    have hs := h 1 4 9 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 4 9)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_11 : ℝ := area (p 1) (p 4) (p 11)
  have hv1_4_11 : 0 < v1_4_11 := by
    have hs := h 1 4 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 4 11)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_8 : ℝ := -area (p 2) (p 4) (p 8)
  have hv2_4_8 : 0 < v2_4_8 := by
    have hs := h 2 4 8 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 4 8)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_9 : ℝ := -area (p 2) (p 4) (p 9)
  have hv2_4_9 : 0 < v2_4_9 := by
    have hs := h 2 4 9 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 4 9)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 4 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 4 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_11 : ℝ := -area (p 3) (p 4) (p 11)
  have hv3_4_11 : 0 < v3_4_11 := by
    have hs := h 3 4 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 4 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_9 : ℝ := area (p 4) (p 8) (p 9)
  have hv4_8_9 : 0 < v4_8_9 := by
    have hs := h 4 8 9 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 4 8 9)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 4 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_11 : ℝ := area (p 4) (p 8) (p 11)
  have hv4_8_11 : 0 < v4_8_11 := by
    have hs := h 4 8 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 4 8 11)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 4 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := -area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 4 10 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_780_02.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_780_02.testBit (363-lexRank 9 10 11) then _ else _) at hs
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

#print axioms no_realization_780_02

def signature_780_03 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111111111111111111000001011011111111111111111111010111111011111011111111111111111111111111111011111111111100100001000110000000000100001000100000000001011111100011111110001100000001110

theorem no_realization_780_03 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_03 p := by
  intro h
  let v0_1_4 : ℝ := -area (p 0) (p 1) (p 4)
  have hv0_1_4 : 0 < v0_1_4 := by
    have hs := h 0 1 4 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 1 4)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 1 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_10 : ℝ := -area (p 0) (p 4) (p 10)
  have hv0_4_10 : 0 < v0_4_10 := by
    have hs := h 0 4 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 4 10)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_11 : ℝ := -area (p 0) (p 4) (p 11)
  have hv0_4_11 : 0 < v0_4_11 := by
    have hs := h 0 4 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 4 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_4 : ℝ := area (p 1) (p 2) (p 4)
  have hv1_2_4 : 0 < v1_2_4 := by
    have hs := h 1 2 4 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 2 4)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_8 : ℝ := -area (p 1) (p 4) (p 8)
  have hv1_4_8 : 0 < v1_4_8 := by
    have hs := h 1 4 8 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 4 8)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_9 : ℝ := -area (p 1) (p 4) (p 9)
  have hv1_4_9 : 0 < v1_4_9 := by
    have hs := h 1 4 9 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 4 9)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_11 : ℝ := area (p 1) (p 4) (p 11)
  have hv1_4_11 : 0 < v1_4_11 := by
    have hs := h 1 4 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 4 11)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_8 : ℝ := -area (p 2) (p 4) (p 8)
  have hv2_4_8 : 0 < v2_4_8 := by
    have hs := h 2 4 8 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 4 8)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_9 : ℝ := -area (p 2) (p 4) (p 9)
  have hv2_4_9 : 0 < v2_4_9 := by
    have hs := h 2 4 9 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 4 9)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 4 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 4 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_11 : ℝ := -area (p 3) (p 4) (p 11)
  have hv3_4_11 : 0 < v3_4_11 := by
    have hs := h 3 4 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 4 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_9 : ℝ := area (p 4) (p 8) (p 9)
  have hv4_8_9 : 0 < v4_8_9 := by
    have hs := h 4 8 9 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 4 8 9)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 4 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_11 : ℝ := area (p 4) (p 8) (p 11)
  have hv4_8_11 : 0 < v4_8_11 := by
    have hs := h 4 8 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 4 8 11)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 4 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := -area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 4 10 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_780_03.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_780_03.testBit (363-lexRank 9 10 11) then _ else _) at hs
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

#print axioms no_realization_780_03

def signature_780_04 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111110011011110000011110111111111111111011110111111111111111001111111000001111011111111111111111111111111111111111000001011011111111111111001011010111111011111011111111111111111111111111111001111111111100100001000100000000000100001000100000000001011111100011111110001100000001110

theorem no_realization_780_04 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_04 p := by
  intro h
  let v0_1_4 : ℝ := -area (p 0) (p 1) (p 4)
  have hv0_1_4 : 0 < v0_1_4 := by
    have hs := h 0 1 4 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 1 4)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 1 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_10 : ℝ := -area (p 0) (p 1) (p 10)
  have hv0_1_10 : 0 < v0_1_10 := by
    have hs := h 0 1 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 1 10)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 1 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_11 : ℝ := -area (p 0) (p 1) (p 11)
  have hv0_1_11 : 0 < v0_1_11 := by
    have hs := h 0 1 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 1 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 1 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_7 : ℝ := -area (p 0) (p 4) (p 7)
  have hv0_4_7 : 0 < v0_4_7 := by
    have hs := h 0 4 7 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 4 7)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_10 : ℝ := -area (p 0) (p 4) (p 10)
  have hv0_4_10 : 0 < v0_4_10 := by
    have hs := h 0 4 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 4 10)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_11 : ℝ := -area (p 0) (p 4) (p 11)
  have hv0_4_11 : 0 < v0_4_11 := by
    have hs := h 0 4 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 4 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_4 : ℝ := area (p 1) (p 2) (p 4)
  have hv1_2_4 : 0 < v1_2_4 := by
    have hs := h 1 2 4 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 2 4)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_9 : ℝ := -area (p 1) (p 3) (p 9)
  have hv1_3_9 : 0 < v1_3_9 := by
    have hs := h 1 3 9 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 3 9)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_7 : ℝ := -area (p 1) (p 4) (p 7)
  have hv1_4_7 : 0 < v1_4_7 := by
    have hs := h 1 4 7 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 4 7)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_9 : ℝ := -area (p 1) (p 4) (p 9)
  have hv1_4_9 : 0 < v1_4_9 := by
    have hs := h 1 4 9 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 4 9)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_11 : ℝ := area (p 1) (p 4) (p 11)
  have hv1_4_11 : 0 < v1_4_11 := by
    have hs := h 1 4 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 4 11)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_10 : ℝ := area (p 1) (p 9) (p 10)
  have hv1_9_10 : 0 < v1_9_10 := by
    have hs := h 1 9 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 9 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_7 : ℝ := -area (p 2) (p 4) (p 7)
  have hv2_4_7 : 0 < v2_4_7 := by
    have hs := h 2 4 7 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 4 7)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_9 : ℝ := -area (p 2) (p 4) (p 9)
  have hv2_4_9 : 0 < v2_4_9 := by
    have hs := h 2 4 9 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 4 9)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 4 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_9 : ℝ := area (p 2) (p 7) (p 9)
  have hv2_7_9 : 0 < v2_7_9 := by
    have hs := h 2 7 9 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 7 9)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_10 : ℝ := area (p 2) (p 7) (p 10)
  have hv2_7_10 : 0 < v2_7_10 := by
    have hs := h 2 7 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 7 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_11 : ℝ := area (p 2) (p 10) (p 11)
  have hv2_10_11 : 0 < v2_10_11 := by
    have hs := h 2 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 2 10 11)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 2 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 4 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_11 : ℝ := -area (p 3) (p 4) (p 11)
  have hv3_4_11 : 0 < v3_4_11 := by
    have hs := h 3 4 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 4 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 4 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := -area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 7 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 9 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 9 11)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_11 : ℝ := -area (p 3) (p 10) (p 11)
  have hv3_10_11 : 0 < v3_10_11 := by
    have hs := h 3 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 3 10 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 3 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_9 : ℝ := area (p 4) (p 7) (p 9)
  have hv4_7_9 : 0 < v4_7_9 := by
    have hs := h 4 7 9 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 4 7 9)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 4 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_11 : ℝ := area (p 4) (p 7) (p 11)
  have hv4_7_11 : 0 < v4_7_11 := by
    have hs := h 4 7 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 4 7 11)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 4 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := -area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 4 10 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_9_10 : ℝ := area (p 7) (p 9) (p 10)
  have hv7_9_10 : 0 < v7_9_10 := by
    have hs := h 7 9 10 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 7 9 10)) = true := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 7 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_11 : ℝ := -area (p 7) (p 10) (p 11)
  have hv7_10_11 : 0 < v7_10_11 := by
    have hs := h 7 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 7 10 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 7 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_11 : ℝ := -area (p 9) (p 10) (p 11)
  have hv9_10_11 : 0 < v9_10_11 := by
    have hs := h 9 10 11 (by decide) (by decide)
    have bit : (signature_780_04.testBit (363-lexRank 9 10 11)) = false := by decide
    change 0 < (if signature_780_04.testBit (363-lexRank 9 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_1_4 * v0_10_11 ∧ v0_1_4 * v0_10_11 < v0_1_10 * v0_4_11 := by
    have ident : v0_1_10 * v0_4_11 = v0_1_4 * v0_10_11 + v0_1_11 * v0_4_10 := by
      dsimp only [v0_1_4, v0_1_10, v0_1_11, v0_4_10, v0_4_11, v0_10_11, area]
      ring
    refine ⟨mul_pos hv0_1_4 hv0_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_11 hv0_4_10)
  have row1 : 0 < v2_4_9 * v2_7_10 ∧ v2_4_9 * v2_7_10 < v2_4_7 * v2_9_10 := by
    have ident : v2_4_7 * v2_9_10 = v2_4_9 * v2_7_10 + v2_4_10 * v2_7_9 := by
      dsimp only [v2_4_7, v2_4_9, v2_4_10, v2_7_9, v2_7_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_4_9 hv2_7_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_4_10 hv2_7_9)
  have row2 : 0 < v3_4_11 * v3_9_10 ∧ v3_4_11 * v3_9_10 < v3_4_9 * v3_10_11 := by
    have ident : v3_4_9 * v3_10_11 = v3_4_11 * v3_9_10 + v3_4_10 * v3_9_11 := by
      dsimp only [v3_4_9, v3_4_10, v3_4_11, v3_9_10, v3_9_11, v3_10_11, area]
      ring
    refine ⟨mul_pos hv3_4_11 hv3_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_10 hv3_9_11)
  have row3 : 0 < v0_4_11 * v1_4_7 ∧ v0_4_11 * v1_4_7 < v0_1_4 * v4_7_11 := by
    have ident : v0_1_4 * v4_7_11 = v0_4_11 * v1_4_7 + v0_4_7 * v1_4_11 := by
      dsimp only [v0_1_4, v0_4_7, v0_4_11, v1_4_7, v1_4_11, v4_7_11, area]
      ring
    refine ⟨mul_pos hv0_4_11 hv1_4_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_4_7 hv1_4_11)
  have row4 : 0 < v1_4_9 * v2_4_7 ∧ v1_4_9 * v2_4_7 < v1_4_7 * v2_4_9 := by
    have ident : v1_4_7 * v2_4_9 = v1_4_9 * v2_4_7 + v1_2_4 * v4_7_9 := by
      dsimp only [v1_2_4, v1_4_7, v1_4_9, v2_4_7, v2_4_9, v4_7_9, area]
      ring
    refine ⟨mul_pos hv1_4_9 hv2_4_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_4 hv4_7_9)
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
  have row7 : 0 < v2_9_10 * v7_10_11 ∧ v2_9_10 * v7_10_11 < v2_7_10 * v9_10_11 := by
    have ident : v2_7_10 * v9_10_11 = v2_9_10 * v7_10_11 + v2_10_11 * v7_9_10 := by
      dsimp only [v2_7_10, v2_9_10, v2_10_11, v7_9_10, v7_10_11, v9_10_11, area]
      ring
    refine ⟨mul_pos hv2_9_10 hv7_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_11 hv7_9_10)
  have row8 : 0 < v3_10_11 * v4_7_11 ∧ v3_10_11 * v4_7_11 < v3_4_11 * v7_10_11 := by
    have ident : v3_4_11 * v7_10_11 = v3_10_11 * v4_7_11 + v3_7_11 * v4_10_11 := by
      dsimp only [v3_4_11, v3_7_11, v3_10_11, v4_7_11, v4_10_11, v7_10_11, area]
      ring
    refine ⟨mul_pos hv3_10_11 hv4_7_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_7_11 hv4_10_11)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_04

def signature_780_05 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100000111111001011110000011110010111101011111111110111111111111111110101111000000111101011110101111111111011111111111111000000011001010110101111111111000111111011111111111111111111111111111111111111111010111111111100000111100011011111100000111100000000000000000000011111111110000001110

theorem no_realization_780_05 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_05 p := by
  intro h
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_7 : ℝ := -area (p 0) (p 2) (p 7)
  have hv0_2_7 : 0 < v0_2_7 := by
    have hs := h 0 2 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 2 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 2 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_4 : ℝ := -area (p 0) (p 3) (p 4)
  have hv0_3_4 : 0 < v0_3_4 := by
    have hs := h 0 3 4 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 3 4)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 3 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_7 : ℝ := -area (p 0) (p 3) (p 7)
  have hv0_3_7 : 0 < v0_3_7 := by
    have hs := h 0 3 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 3 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_5 : ℝ := -area (p 0) (p 4) (p 5)
  have hv0_4_5 : 0 < v0_4_5 := by
    have hs := h 0 4 5 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 4 5)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 4 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_6 : ℝ := -area (p 0) (p 4) (p 6)
  have hv0_4_6 : 0 < v0_4_6 := by
    have hs := h 0 4 6 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 4 6)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_7 : ℝ := -area (p 0) (p 4) (p 7)
  have hv0_4_7 : 0 < v0_4_7 := by
    have hs := h 0 4 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 4 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_6 : ℝ := -area (p 0) (p 5) (p 6)
  have hv0_5_6 : 0 < v0_5_6 := by
    have hs := h 0 5 6 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 5 6)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_7 : ℝ := -area (p 0) (p 5) (p 7)
  have hv0_5_7 : 0 < v0_5_7 := by
    have hs := h 0 5 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 5 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_7 : ℝ := -area (p 0) (p 6) (p 7)
  have hv0_6_7 : 0 < v0_6_7 := by
    have hs := h 0 6 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 6 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_12 : ℝ := -area (p 0) (p 6) (p 12)
  have hv0_6_12 : 0 < v0_6_12 := by
    have hs := h 0 6 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 6 12)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_11 : ℝ := -area (p 0) (p 7) (p 11)
  have hv0_7_11 : 0 < v0_7_11 := by
    have hs := h 0 7 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 7 11)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_12 : ℝ := -area (p 0) (p 7) (p 12)
  have hv0_7_12 : 0 < v0_7_12 := by
    have hs := h 0 7 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 0 7 12)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 0 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_7 : ℝ := -area (p 2) (p 3) (p 7)
  have hv2_3_7 : 0 < v2_3_7 := by
    have hs := h 2 3 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 2 3 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 2 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_5_6 : ℝ := area (p 2) (p 5) (p 6)
  have hv2_5_6 : 0 < v2_5_6 := by
    have hs := h 2 5 6 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 2 5 6)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 2 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_7 : ℝ := -area (p 2) (p 6) (p 7)
  have hv2_6_7 : 0 < v2_6_7 := by
    have hs := h 2 6 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 2 6 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 2 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_12 : ℝ := area (p 2) (p 6) (p 12)
  have hv2_6_12 : 0 < v2_6_12 := by
    have hs := h 2 6 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 2 6 12)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 2 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_12 : ℝ := area (p 2) (p 7) (p 12)
  have hv2_7_12 : 0 < v2_7_12 := by
    have hs := h 2 7 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 2 7 12)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 2 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_6 : ℝ := -area (p 3) (p 4) (p 6)
  have hv3_4_6 : 0 < v3_4_6 := by
    have hs := h 3 4 6 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 4 6)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_7 : ℝ := -area (p 3) (p 4) (p 7)
  have hv3_4_7 : 0 < v3_4_7 := by
    have hs := h 3 4 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 4 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_12 : ℝ := area (p 3) (p 4) (p 12)
  have hv3_4_12 : 0 < v3_4_12 := by
    have hs := h 3 4 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 4 12)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_6 : ℝ := -area (p 3) (p 5) (p 6)
  have hv3_5_6 : 0 < v3_5_6 := by
    have hs := h 3 5 6 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 5 6)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_7 : ℝ := -area (p 3) (p 5) (p 7)
  have hv3_5_7 : 0 < v3_5_7 := by
    have hs := h 3 5 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 5 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_11 : ℝ := -area (p 3) (p 5) (p 11)
  have hv3_5_11 : 0 < v3_5_11 := by
    have hs := h 3 5 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 5 11)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_7 : ℝ := -area (p 3) (p 6) (p 7)
  have hv3_6_7 : 0 < v3_6_7 := by
    have hs := h 3 6 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 6 7)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_11 : ℝ := area (p 3) (p 6) (p 11)
  have hv3_6_11 : 0 < v3_6_11 := by
    have hs := h 3 6 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 6 11)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_12 : ℝ := area (p 3) (p 6) (p 12)
  have hv3_6_12 : 0 < v3_6_12 := by
    have hs := h 3 6 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 6 12)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 7 11)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_12 : ℝ := area (p 3) (p 7) (p 12)
  have hv3_7_12 : 0 < v3_7_12 := by
    have hs := h 3 7 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 3 7 12)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 3 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_6_7 : ℝ := area (p 4) (p 6) (p 7)
  have hv4_6_7 : 0 < v4_6_7 := by
    have hs := h 4 6 7 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 4 6 7)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 4 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_11 : ℝ := area (p 5) (p 6) (p 11)
  have hv5_6_11 : 0 < v5_6_11 := by
    have hs := h 5 6 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 5 6 11)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 5 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_12 : ℝ := area (p 5) (p 6) (p 12)
  have hv5_6_12 : 0 < v5_6_12 := by
    have hs := h 5 6 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 5 6 12)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 5 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_11 : ℝ := area (p 5) (p 7) (p 11)
  have hv5_7_11 : 0 < v5_7_11 := by
    have hs := h 5 7 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 5 7 11)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 5 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_11 : ℝ := area (p 6) (p 7) (p 11)
  have hv6_7_11 : 0 < v6_7_11 := by
    have hs := h 6 7 11 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 6 7 11)) = true := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 6 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_11_12 : ℝ := -area (p 6) (p 11) (p 12)
  have hv6_11_12 : 0 < v6_11_12 := by
    have hs := h 6 11 12 (by decide) (by decide)
    have bit : (signature_780_05.testBit (363-lexRank 6 11 12)) = false := by decide
    change 0 < (if signature_780_05.testBit (363-lexRank 6 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v2_6_12 * v0_2_7 ∧ v2_6_12 * v0_2_7 < v2_7_12 * v0_2_6 := by
    have ident : v2_7_12 * v0_2_6 = v2_6_12 * v0_2_7 + v0_2_12 * v2_6_7 := by
      dsimp only [v0_2_6, v0_2_7, v0_2_12, v2_6_7, v2_6_12, v2_7_12, area]
      ring
    refine ⟨mul_pos hv2_6_12 hv0_2_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_6_7)
  have row1 : 0 < v3_6_11 * v5_7_11 ∧ v3_6_11 * v5_7_11 < v5_6_11 * v3_7_11 := by
    have ident : v5_6_11 * v3_7_11 = v3_6_11 * v5_7_11 + v6_7_11 * v3_5_11 := by
      dsimp only [v3_5_11, v3_6_11, v3_7_11, v5_6_11, v5_7_11, v6_7_11, area]
      ring
    refine ⟨mul_pos hv3_6_11 hv5_7_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv6_7_11 hv3_5_11)
  have row2 : 0 < v0_4_6 * v3_4_7 ∧ v0_4_6 * v3_4_7 < v3_4_6 * v0_4_7 := by
    have ident : v3_4_6 * v0_4_7 = v0_4_6 * v3_4_7 + v4_6_7 * v0_3_4 := by
      dsimp only [v0_3_4, v0_4_6, v0_4_7, v3_4_6, v3_4_7, v4_6_7, area]
      ring
    refine ⟨mul_pos hv0_4_6 hv3_4_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_6_7 hv0_3_4)
  have row3 : 0 < v0_2_6 * v5_6_12 ∧ v0_2_6 * v5_6_12 < v2_6_12 * v0_5_6 := by
    have ident : v2_6_12 * v0_5_6 = v0_2_6 * v5_6_12 + v2_5_6 * v0_6_12 := by
      dsimp only [v0_2_6, v0_5_6, v0_6_12, v2_5_6, v2_6_12, v5_6_12, area]
      ring
    refine ⟨mul_pos hv0_2_6 hv5_6_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_5_6 hv0_6_12)
  have row4 : 0 < v3_6_12 * v5_6_11 ∧ v3_6_12 * v5_6_11 < v5_6_12 * v3_6_11 := by
    have ident : v5_6_12 * v3_6_11 = v3_6_12 * v5_6_11 + v6_11_12 * v3_5_6 := by
      dsimp only [v3_5_6, v3_6_11, v3_6_12, v5_6_11, v5_6_12, v6_11_12, area]
      ring
    refine ⟨mul_pos hv3_6_12 hv5_6_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv6_11_12 hv3_5_6)
  have row5 : 0 < v3_7_12 * v3_4_6 ∧ v3_7_12 * v3_4_6 < v3_6_12 * v3_4_7 := by
    have ident : v3_6_12 * v3_4_7 = v3_7_12 * v3_4_6 + v3_4_12 * v3_6_7 := by
      dsimp only [v3_4_6, v3_4_7, v3_4_12, v3_6_7, v3_6_12, v3_7_12, area]
      ring
    refine ⟨mul_pos hv3_7_12 hv3_4_6, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_12 hv3_6_7)
  have row6 : 0 < v2_7_12 * v0_3_7 ∧ v2_7_12 * v0_3_7 < v0_2_7 * v3_7_12 := by
    have ident : v0_2_7 * v3_7_12 = v2_7_12 * v0_3_7 + v2_3_7 * v0_7_12 := by
      dsimp only [v0_2_7, v0_3_7, v0_7_12, v2_3_7, v2_7_12, v3_7_12, area]
      ring
    refine ⟨mul_pos hv2_7_12 hv0_3_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_3_7 hv0_7_12)
  have row7 : 0 < v3_7_11 * v0_5_7 ∧ v3_7_11 * v0_5_7 < v5_7_11 * v0_3_7 := by
    have ident : v5_7_11 * v0_3_7 = v3_7_11 * v0_5_7 + v0_7_11 * v3_5_7 := by
      dsimp only [v0_3_7, v0_5_7, v0_7_11, v3_5_7, v3_7_11, v5_7_11, area]
      ring
    refine ⟨mul_pos hv3_7_11 hv0_5_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_7_11 hv3_5_7)
  have row8 : 0 < v0_4_7 * v0_5_6 ∧ v0_4_7 * v0_5_6 < v0_4_6 * v0_5_7 := by
    have ident : v0_4_6 * v0_5_7 = v0_4_7 * v0_5_6 + v0_4_5 * v0_6_7 := by
      dsimp only [v0_4_5, v0_4_6, v0_4_7, v0_5_6, v0_5_7, v0_6_7, area]
      ring
    refine ⟨mul_pos hv0_4_7 hv0_5_6, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_4_5 hv0_6_7)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_05

def signature_780_06 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100010111110001011110000011110111111111111111011110111111111111111000111111000001111011111111111111111111011111111111111000001011011111111111111111111010111111011111011111111111111111111111111111001111111111100100001000100000000000100001000100000000001011111100011111110001100000001110

theorem no_realization_780_06 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_06 p := by
  intro h
  let v0_1_5 : ℝ := -area (p 0) (p 1) (p 5)
  have hv0_1_5 : 0 < v0_1_5 := by
    have hs := h 0 1 5 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 1 5)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 1 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_7 : ℝ := -area (p 0) (p 1) (p 7)
  have hv0_1_7 : 0 < v0_1_7 := by
    have hs := h 0 1 7 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 1 7)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 1 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_12 : ℝ := -area (p 0) (p 1) (p 12)
  have hv0_1_12 : 0 < v0_1_12 := by
    have hs := h 0 1 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 1 12)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 1 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_5 : ℝ := -area (p 0) (p 3) (p 5)
  have hv0_3_5 : 0 < v0_3_5 := by
    have hs := h 0 3 5 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 3 5)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 3 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_7 : ℝ := -area (p 0) (p 5) (p 7)
  have hv0_5_7 : 0 < v0_5_7 := by
    have hs := h 0 5 7 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 5 7)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_8 : ℝ := -area (p 0) (p 5) (p 8)
  have hv0_5_8 : 0 < v0_5_8 := by
    have hs := h 0 5 8 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 5 8)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_10 : ℝ := -area (p 0) (p 5) (p 10)
  have hv0_5_10 : 0 < v0_5_10 := by
    have hs := h 0 5 10 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 5 10)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_11 : ℝ := -area (p 0) (p 5) (p 11)
  have hv0_5_11 : 0 < v0_5_11 := by
    have hs := h 0 5 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 5 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_12 : ℝ := -area (p 0) (p 5) (p 12)
  have hv0_5_12 : 0 < v0_5_12 := by
    have hs := h 0 5 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 5 12)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_8 : ℝ := -area (p 0) (p 7) (p 8)
  have hv0_7_8 : 0 < v0_7_8 := by
    have hs := h 0 7 8 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 7 8)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_10 : ℝ := -area (p 0) (p 7) (p 10)
  have hv0_7_10 : 0 < v0_7_10 := by
    have hs := h 0 7 10 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 7 10)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_12 : ℝ := -area (p 0) (p 7) (p 12)
  have hv0_7_12 : 0 < v0_7_12 := by
    have hs := h 0 7 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 7 12)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_10 : ℝ := -area (p 0) (p 8) (p 10)
  have hv0_8_10 : 0 < v0_8_10 := by
    have hs := h 0 8 10 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 8 10)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_7 : ℝ := -area (p 1) (p 3) (p 7)
  have hv1_3_7 : 0 < v1_3_7 := by
    have hs := h 1 3 7 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 3 7)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_11 : ℝ := area (p 1) (p 5) (p 11)
  have hv1_5_11 : 0 < v1_5_11 := by
    have hs := h 1 5 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 5 11)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_12 : ℝ := area (p 1) (p 5) (p 12)
  have hv1_5_12 : 0 < v1_5_12 := by
    have hs := h 1 5 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 5 12)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_8 : ℝ := area (p 1) (p 7) (p 8)
  have hv1_7_8 : 0 < v1_7_8 := by
    have hs := h 1 7 8 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 7 8)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_11 : ℝ := area (p 1) (p 7) (p 11)
  have hv1_7_11 : 0 < v1_7_11 := by
    have hs := h 1 7 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 7 11)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_12 : ℝ := area (p 1) (p 7) (p 12)
  have hv1_7_12 : 0 < v1_7_12 := by
    have hs := h 1 7 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 7 12)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_7 : ℝ := area (p 3) (p 5) (p 7)
  have hv3_5_7 : 0 < v3_5_7 := by
    have hs := h 3 5 7 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 3 5 7)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 3 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_8 : ℝ := area (p 3) (p 5) (p 8)
  have hv3_5_8 : 0 < v3_5_8 := by
    have hs := h 3 5 8 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 3 5 8)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 3 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_11 : ℝ := area (p 3) (p 5) (p 11)
  have hv3_5_11 : 0 < v3_5_11 := by
    have hs := h 3 5 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 3 5 11)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 3 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_8 : ℝ := area (p 3) (p 7) (p 8)
  have hv3_7_8 : 0 < v3_7_8 := by
    have hs := h 3 7 8 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 3 7 8)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 3 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 3 7 11)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := -area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 3 8 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_10 : ℝ := area (p 5) (p 7) (p 10)
  have hv5_7_10 : 0 < v5_7_10 := by
    have hs := h 5 7 10 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 5 7 10)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 5 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_11 : ℝ := -area (p 5) (p 7) (p 11)
  have hv5_7_11 : 0 < v5_7_11 := by
    have hs := h 5 7 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 5 7 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 5 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_12 : ℝ := -area (p 5) (p 7) (p 12)
  have hv5_7_12 : 0 < v5_7_12 := by
    have hs := h 5 7 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 5 7 12)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 5 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_11 : ℝ := -area (p 5) (p 8) (p 11)
  have hv5_8_11 : 0 < v5_8_11 := by
    have hs := h 5 8 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 5 8 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 5 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_11 : ℝ := -area (p 5) (p 10) (p 11)
  have hv5_10_11 : 0 < v5_10_11 := by
    have hs := h 5 10 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 5 10 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 5 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_11_12 : ℝ := -area (p 5) (p 11) (p 12)
  have hv5_11_12 : 0 < v5_11_12 := by
    have hs := h 5 11 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 5 11 12)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 5 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_11 : ℝ := -area (p 7) (p 8) (p 11)
  have hv7_8_11 : 0 < v7_8_11 := by
    have hs := h 7 8 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 7 8 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 7 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_11 : ℝ := -area (p 7) (p 10) (p 11)
  have hv7_10_11 : 0 < v7_10_11 := by
    have hs := h 7 10 11 (by decide) (by decide)
    have bit : (signature_780_06.testBit (363-lexRank 7 10 11)) = false := by decide
    change 0 < (if signature_780_06.testBit (363-lexRank 7 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v1_7_12 * v0_5_12 ∧ v1_7_12 * v0_5_12 < v1_5_12 * v0_7_12 := by
    have ident : v1_5_12 * v0_7_12 = v1_7_12 * v0_5_12 + v0_1_12 * v5_7_12 := by
      dsimp only [v0_1_12, v0_5_12, v0_7_12, v1_5_12, v1_7_12, v5_7_12, area]
      ring
    refine ⟨mul_pos hv1_7_12 hv0_5_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_12 hv5_7_12)
  have row1 : 0 < v3_7_11 * v3_5_8 ∧ v3_7_11 * v3_5_8 < v3_7_8 * v3_5_11 := by
    have ident : v3_7_8 * v3_5_11 = v3_7_11 * v3_5_8 + v3_5_7 * v3_8_11 := by
      dsimp only [v3_5_7, v3_5_8, v3_5_11, v3_7_8, v3_7_11, v3_8_11, area]
      ring
    refine ⟨mul_pos hv3_7_11 hv3_5_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_5_7 hv3_8_11)
  have row2 : 0 < v0_7_10 * v5_10_11 ∧ v0_7_10 * v5_10_11 < v7_10_11 * v0_5_10 := by
    have ident : v7_10_11 * v0_5_10 = v0_7_10 * v5_10_11 + v5_7_10 * v0_10_11 := by
      dsimp only [v0_5_10, v0_7_10, v0_10_11, v5_7_10, v5_10_11, v7_10_11, area]
      ring
    refine ⟨mul_pos hv0_7_10 hv5_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv5_7_10 hv0_10_11)
  have row3 : 0 < v0_7_12 * v1_7_8 ∧ v0_7_12 * v1_7_8 < v1_7_12 * v0_7_8 := by
    have ident : v1_7_12 * v0_7_8 = v0_7_12 * v1_7_8 + v7_8_12 * v0_1_7 := by
      dsimp only [v0_1_7, v0_7_8, v0_7_12, v1_7_8, v1_7_12, v7_8_12, area]
      ring
    refine ⟨mul_pos hv0_7_12 hv1_7_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv7_8_12 hv0_1_7)
  have row4 : 0 < v1_7_11 * v3_7_8 ∧ v1_7_11 * v3_7_8 < v1_7_8 * v3_7_11 := by
    have ident : v1_7_8 * v3_7_11 = v1_7_11 * v3_7_8 + v1_3_7 * v7_8_11 := by
      dsimp only [v1_3_7, v1_7_8, v1_7_11, v3_7_8, v3_7_11, v7_8_11, area]
      ring
    refine ⟨mul_pos hv1_7_11 hv3_7_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_7 hv7_8_11)
  have row5 : 0 < v1_5_11 * v7_10_11 ∧ v1_5_11 * v7_10_11 < v1_7_11 * v5_10_11 := by
    have ident : v1_7_11 * v5_10_11 = v1_5_11 * v7_10_11 + v1_10_11 * v5_7_11 := by
      dsimp only [v1_5_11, v1_7_11, v1_10_11, v5_7_11, v5_10_11, v7_10_11, area]
      ring
    refine ⟨mul_pos hv1_5_11 hv7_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_10_11 hv5_7_11)
  have row6 : 0 < v1_5_12 * v0_5_11 ∧ v1_5_12 * v0_5_11 < v0_5_12 * v1_5_11 := by
    have ident : v0_5_12 * v1_5_11 = v1_5_12 * v0_5_11 + v5_11_12 * v0_1_5 := by
      dsimp only [v0_1_5, v0_5_11, v0_5_12, v1_5_11, v1_5_12, v5_11_12, area]
      ring
    refine ⟨mul_pos hv1_5_12 hv0_5_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv5_11_12 hv0_1_5)
  have row7 : 0 < v3_5_11 * v0_5_8 ∧ v3_5_11 * v0_5_8 < v3_5_8 * v0_5_11 := by
    have ident : v3_5_8 * v0_5_11 = v3_5_11 * v0_5_8 + v0_3_5 * v5_8_11 := by
      dsimp only [v0_3_5, v0_5_8, v0_5_11, v3_5_8, v3_5_11, v5_8_11, area]
      ring
    refine ⟨mul_pos hv3_5_11 hv0_5_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_3_5 hv5_8_11)
  have row8 : 0 < v0_5_10 * v0_7_8 ∧ v0_5_10 * v0_7_8 < v0_7_10 * v0_5_8 := by
    have ident : v0_7_10 * v0_5_8 = v0_5_10 * v0_7_8 + v0_8_10 * v0_5_7 := by
      dsimp only [v0_5_7, v0_5_8, v0_5_10, v0_7_8, v0_7_10, v0_8_10, area]
      ring
    refine ⟨mul_pos hv0_5_10 hv0_7_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_10 hv0_5_7)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_06

def signature_780_07 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100010111111001011110000011110010111101011111111110111111111111111110101111000000111101011110101111111111001111111111111000000011001010110101111111111000111111011111111111111111111111111111111111111111010111111111100000111100011011111100000111100000000000000000000011111111110000001110

theorem no_realization_780_07 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_07 p := by
  intro h
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_7 : ℝ := -area (p 0) (p 2) (p 7)
  have hv0_2_7 : 0 < v0_2_7 := by
    have hs := h 0 2 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 2 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 2 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_4 : ℝ := -area (p 0) (p 3) (p 4)
  have hv0_3_4 : 0 < v0_3_4 := by
    have hs := h 0 3 4 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 3 4)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 3 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_7 : ℝ := -area (p 0) (p 3) (p 7)
  have hv0_3_7 : 0 < v0_3_7 := by
    have hs := h 0 3 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 3 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_5 : ℝ := -area (p 0) (p 4) (p 5)
  have hv0_4_5 : 0 < v0_4_5 := by
    have hs := h 0 4 5 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 4 5)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 4 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_6 : ℝ := -area (p 0) (p 4) (p 6)
  have hv0_4_6 : 0 < v0_4_6 := by
    have hs := h 0 4 6 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 4 6)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_7 : ℝ := -area (p 0) (p 4) (p 7)
  have hv0_4_7 : 0 < v0_4_7 := by
    have hs := h 0 4 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 4 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_6 : ℝ := -area (p 0) (p 5) (p 6)
  have hv0_5_6 : 0 < v0_5_6 := by
    have hs := h 0 5 6 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 5 6)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_7 : ℝ := -area (p 0) (p 5) (p 7)
  have hv0_5_7 : 0 < v0_5_7 := by
    have hs := h 0 5 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 5 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_7 : ℝ := -area (p 0) (p 6) (p 7)
  have hv0_6_7 : 0 < v0_6_7 := by
    have hs := h 0 6 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 6 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_12 : ℝ := -area (p 0) (p 6) (p 12)
  have hv0_6_12 : 0 < v0_6_12 := by
    have hs := h 0 6 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 6 12)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_11 : ℝ := -area (p 0) (p 7) (p 11)
  have hv0_7_11 : 0 < v0_7_11 := by
    have hs := h 0 7 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 7 11)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_12 : ℝ := -area (p 0) (p 7) (p 12)
  have hv0_7_12 : 0 < v0_7_12 := by
    have hs := h 0 7 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 0 7 12)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 0 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_7 : ℝ := -area (p 2) (p 3) (p 7)
  have hv2_3_7 : 0 < v2_3_7 := by
    have hs := h 2 3 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 2 3 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 2 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_5_6 : ℝ := area (p 2) (p 5) (p 6)
  have hv2_5_6 : 0 < v2_5_6 := by
    have hs := h 2 5 6 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 2 5 6)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 2 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_7 : ℝ := -area (p 2) (p 6) (p 7)
  have hv2_6_7 : 0 < v2_6_7 := by
    have hs := h 2 6 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 2 6 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 2 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_12 : ℝ := area (p 2) (p 6) (p 12)
  have hv2_6_12 : 0 < v2_6_12 := by
    have hs := h 2 6 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 2 6 12)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 2 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_12 : ℝ := area (p 2) (p 7) (p 12)
  have hv2_7_12 : 0 < v2_7_12 := by
    have hs := h 2 7 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 2 7 12)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 2 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_6 : ℝ := -area (p 3) (p 4) (p 6)
  have hv3_4_6 : 0 < v3_4_6 := by
    have hs := h 3 4 6 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 4 6)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_7 : ℝ := -area (p 3) (p 4) (p 7)
  have hv3_4_7 : 0 < v3_4_7 := by
    have hs := h 3 4 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 4 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_12 : ℝ := area (p 3) (p 4) (p 12)
  have hv3_4_12 : 0 < v3_4_12 := by
    have hs := h 3 4 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 4 12)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_6 : ℝ := -area (p 3) (p 5) (p 6)
  have hv3_5_6 : 0 < v3_5_6 := by
    have hs := h 3 5 6 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 5 6)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_7 : ℝ := -area (p 3) (p 5) (p 7)
  have hv3_5_7 : 0 < v3_5_7 := by
    have hs := h 3 5 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 5 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_11 : ℝ := -area (p 3) (p 5) (p 11)
  have hv3_5_11 : 0 < v3_5_11 := by
    have hs := h 3 5 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 5 11)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_7 : ℝ := -area (p 3) (p 6) (p 7)
  have hv3_6_7 : 0 < v3_6_7 := by
    have hs := h 3 6 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 6 7)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_11 : ℝ := area (p 3) (p 6) (p 11)
  have hv3_6_11 : 0 < v3_6_11 := by
    have hs := h 3 6 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 6 11)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_12 : ℝ := area (p 3) (p 6) (p 12)
  have hv3_6_12 : 0 < v3_6_12 := by
    have hs := h 3 6 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 6 12)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 7 11)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_12 : ℝ := area (p 3) (p 7) (p 12)
  have hv3_7_12 : 0 < v3_7_12 := by
    have hs := h 3 7 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 3 7 12)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 3 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_6_7 : ℝ := area (p 4) (p 6) (p 7)
  have hv4_6_7 : 0 < v4_6_7 := by
    have hs := h 4 6 7 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 4 6 7)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 4 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_11 : ℝ := area (p 5) (p 6) (p 11)
  have hv5_6_11 : 0 < v5_6_11 := by
    have hs := h 5 6 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 5 6 11)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 5 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_12 : ℝ := area (p 5) (p 6) (p 12)
  have hv5_6_12 : 0 < v5_6_12 := by
    have hs := h 5 6 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 5 6 12)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 5 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_11 : ℝ := area (p 5) (p 7) (p 11)
  have hv5_7_11 : 0 < v5_7_11 := by
    have hs := h 5 7 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 5 7 11)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 5 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_11 : ℝ := area (p 6) (p 7) (p 11)
  have hv6_7_11 : 0 < v6_7_11 := by
    have hs := h 6 7 11 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 6 7 11)) = true := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 6 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_11_12 : ℝ := -area (p 6) (p 11) (p 12)
  have hv6_11_12 : 0 < v6_11_12 := by
    have hs := h 6 11 12 (by decide) (by decide)
    have bit : (signature_780_07.testBit (363-lexRank 6 11 12)) = false := by decide
    change 0 < (if signature_780_07.testBit (363-lexRank 6 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v2_6_12 * v0_2_7 ∧ v2_6_12 * v0_2_7 < v2_7_12 * v0_2_6 := by
    have ident : v2_7_12 * v0_2_6 = v2_6_12 * v0_2_7 + v0_2_12 * v2_6_7 := by
      dsimp only [v0_2_6, v0_2_7, v0_2_12, v2_6_7, v2_6_12, v2_7_12, area]
      ring
    refine ⟨mul_pos hv2_6_12 hv0_2_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_6_7)
  have row1 : 0 < v3_6_11 * v5_7_11 ∧ v3_6_11 * v5_7_11 < v5_6_11 * v3_7_11 := by
    have ident : v5_6_11 * v3_7_11 = v3_6_11 * v5_7_11 + v6_7_11 * v3_5_11 := by
      dsimp only [v3_5_11, v3_6_11, v3_7_11, v5_6_11, v5_7_11, v6_7_11, area]
      ring
    refine ⟨mul_pos hv3_6_11 hv5_7_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv6_7_11 hv3_5_11)
  have row2 : 0 < v0_4_6 * v3_4_7 ∧ v0_4_6 * v3_4_7 < v3_4_6 * v0_4_7 := by
    have ident : v3_4_6 * v0_4_7 = v0_4_6 * v3_4_7 + v4_6_7 * v0_3_4 := by
      dsimp only [v0_3_4, v0_4_6, v0_4_7, v3_4_6, v3_4_7, v4_6_7, area]
      ring
    refine ⟨mul_pos hv0_4_6 hv3_4_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_6_7 hv0_3_4)
  have row3 : 0 < v0_2_6 * v5_6_12 ∧ v0_2_6 * v5_6_12 < v2_6_12 * v0_5_6 := by
    have ident : v2_6_12 * v0_5_6 = v0_2_6 * v5_6_12 + v2_5_6 * v0_6_12 := by
      dsimp only [v0_2_6, v0_5_6, v0_6_12, v2_5_6, v2_6_12, v5_6_12, area]
      ring
    refine ⟨mul_pos hv0_2_6 hv5_6_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_5_6 hv0_6_12)
  have row4 : 0 < v3_6_12 * v5_6_11 ∧ v3_6_12 * v5_6_11 < v5_6_12 * v3_6_11 := by
    have ident : v5_6_12 * v3_6_11 = v3_6_12 * v5_6_11 + v6_11_12 * v3_5_6 := by
      dsimp only [v3_5_6, v3_6_11, v3_6_12, v5_6_11, v5_6_12, v6_11_12, area]
      ring
    refine ⟨mul_pos hv3_6_12 hv5_6_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv6_11_12 hv3_5_6)
  have row5 : 0 < v3_7_12 * v3_4_6 ∧ v3_7_12 * v3_4_6 < v3_6_12 * v3_4_7 := by
    have ident : v3_6_12 * v3_4_7 = v3_7_12 * v3_4_6 + v3_4_12 * v3_6_7 := by
      dsimp only [v3_4_6, v3_4_7, v3_4_12, v3_6_7, v3_6_12, v3_7_12, area]
      ring
    refine ⟨mul_pos hv3_7_12 hv3_4_6, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_12 hv3_6_7)
  have row6 : 0 < v2_7_12 * v0_3_7 ∧ v2_7_12 * v0_3_7 < v0_2_7 * v3_7_12 := by
    have ident : v0_2_7 * v3_7_12 = v2_7_12 * v0_3_7 + v2_3_7 * v0_7_12 := by
      dsimp only [v0_2_7, v0_3_7, v0_7_12, v2_3_7, v2_7_12, v3_7_12, area]
      ring
    refine ⟨mul_pos hv2_7_12 hv0_3_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_3_7 hv0_7_12)
  have row7 : 0 < v3_7_11 * v0_5_7 ∧ v3_7_11 * v0_5_7 < v5_7_11 * v0_3_7 := by
    have ident : v5_7_11 * v0_3_7 = v3_7_11 * v0_5_7 + v0_7_11 * v3_5_7 := by
      dsimp only [v0_3_7, v0_5_7, v0_7_11, v3_5_7, v3_7_11, v5_7_11, area]
      ring
    refine ⟨mul_pos hv3_7_11 hv0_5_7, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_7_11 hv3_5_7)
  have row8 : 0 < v0_4_7 * v0_5_6 ∧ v0_4_7 * v0_5_6 < v0_4_6 * v0_5_7 := by
    have ident : v0_4_6 * v0_5_7 = v0_4_7 * v0_5_6 + v0_4_5 * v0_6_7 := by
      dsimp only [v0_4_5, v0_4_6, v0_4_7, v0_5_6, v0_5_7, v0_6_7, area]
      ring
    refine ⟨mul_pos hv0_4_7 hv0_5_6, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_4_5 hv0_6_7)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_07

def signature_780_08 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100100111110010111110000011110111111111111110011111111111111111111001011111000001111011111111111111001111111111111111111000001011011111111111111001011111111011011111011111111111111111111111111111011111111111100100001000100000000000100001000100000000011111111100011110100001000001101110

theorem no_realization_780_08 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_08 p := by
  intro h
  let v0_1_5 : ℝ := -area (p 0) (p 1) (p 5)
  have hv0_1_5 : 0 < v0_1_5 := by
    have hs := h 0 1 5 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 1 5)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 1 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_8 : ℝ := -area (p 0) (p 1) (p 8)
  have hv0_1_8 : 0 < v0_1_8 := by
    have hs := h 0 1 8 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 1 8)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 1 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_12 : ℝ := -area (p 0) (p 1) (p 12)
  have hv0_1_12 : 0 < v0_1_12 := by
    have hs := h 0 1 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 1 12)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 1 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_5 : ℝ := -area (p 0) (p 3) (p 5)
  have hv0_3_5 : 0 < v0_3_5 := by
    have hs := h 0 3 5 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 3 5)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 3 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_8 : ℝ := -area (p 0) (p 5) (p 8)
  have hv0_5_8 : 0 < v0_5_8 := by
    have hs := h 0 5 8 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 5 8)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_9 : ℝ := -area (p 0) (p 5) (p 9)
  have hv0_5_9 : 0 < v0_5_9 := by
    have hs := h 0 5 9 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 5 9)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 5 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_10 : ℝ := -area (p 0) (p 5) (p 10)
  have hv0_5_10 : 0 < v0_5_10 := by
    have hs := h 0 5 10 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 5 10)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_11 : ℝ := -area (p 0) (p 5) (p 11)
  have hv0_5_11 : 0 < v0_5_11 := by
    have hs := h 0 5 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 5 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_12 : ℝ := -area (p 0) (p 5) (p 12)
  have hv0_5_12 : 0 < v0_5_12 := by
    have hs := h 0 5 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 5 12)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_10 : ℝ := -area (p 0) (p 8) (p 10)
  have hv0_8_10 : 0 < v0_8_10 := by
    have hs := h 0 8 10 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 8 10)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_12 : ℝ := -area (p 0) (p 8) (p 12)
  have hv0_8_12 : 0 < v0_8_12 := by
    have hs := h 0 8 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 8 12)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_8 : ℝ := -area (p 1) (p 3) (p 8)
  have hv1_3_8 : 0 < v1_3_8 := by
    have hs := h 1 3 8 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 3 8)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_11 : ℝ := area (p 1) (p 5) (p 11)
  have hv1_5_11 : 0 < v1_5_11 := by
    have hs := h 1 5 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 5 11)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_12 : ℝ := area (p 1) (p 5) (p 12)
  have hv1_5_12 : 0 < v1_5_12 := by
    have hs := h 1 5 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 5 12)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_9 : ℝ := area (p 1) (p 8) (p 9)
  have hv1_8_9 : 0 < v1_8_9 := by
    have hs := h 1 8 9 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 8 9)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_11 : ℝ := area (p 1) (p 8) (p 11)
  have hv1_8_11 : 0 < v1_8_11 := by
    have hs := h 1 8 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 8 11)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_12 : ℝ := area (p 1) (p 8) (p 12)
  have hv1_8_12 : 0 < v1_8_12 := by
    have hs := h 1 8 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 8 12)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_8 : ℝ := area (p 3) (p 5) (p 8)
  have hv3_5_8 : 0 < v3_5_8 := by
    have hs := h 3 5 8 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 3 5 8)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 3 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_9 : ℝ := area (p 3) (p 5) (p 9)
  have hv3_5_9 : 0 < v3_5_9 := by
    have hs := h 3 5 9 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 3 5 9)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 3 5 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_11 : ℝ := area (p 3) (p 5) (p 11)
  have hv3_5_11 : 0 < v3_5_11 := by
    have hs := h 3 5 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 3 5 11)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 3 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_9 : ℝ := area (p 3) (p 8) (p 9)
  have hv3_8_9 : 0 < v3_8_9 := by
    have hs := h 3 8 9 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 3 8 9)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 3 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 3 8 11)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := -area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 3 9 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_10 : ℝ := area (p 5) (p 8) (p 10)
  have hv5_8_10 : 0 < v5_8_10 := by
    have hs := h 5 8 10 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 5 8 10)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 5 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_11 : ℝ := -area (p 5) (p 8) (p 11)
  have hv5_8_11 : 0 < v5_8_11 := by
    have hs := h 5 8 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 5 8 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 5 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_12 : ℝ := -area (p 5) (p 8) (p 12)
  have hv5_8_12 : 0 < v5_8_12 := by
    have hs := h 5 8 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 5 8 12)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 5 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_9_11 : ℝ := -area (p 5) (p 9) (p 11)
  have hv5_9_11 : 0 < v5_9_11 := by
    have hs := h 5 9 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 5 9 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 5 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_11 : ℝ := -area (p 5) (p 10) (p 11)
  have hv5_10_11 : 0 < v5_10_11 := by
    have hs := h 5 10 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 5 10 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 5 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_11_12 : ℝ := -area (p 5) (p 11) (p 12)
  have hv5_11_12 : 0 < v5_11_12 := by
    have hs := h 5 11 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 5 11 12)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 5 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_11 : ℝ := -area (p 8) (p 9) (p 11)
  have hv8_9_11 : 0 < v8_9_11 := by
    have hs := h 8 9 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 8 9 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 8 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_12 : ℝ := area (p 8) (p 9) (p 12)
  have hv8_9_12 : 0 < v8_9_12 := by
    have hs := h 8 9 12 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 8 9 12)) = true := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 8 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_780_08.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_780_08.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v1_8_12 * v0_5_12 ∧ v1_8_12 * v0_5_12 < v1_5_12 * v0_8_12 := by
    have ident : v1_5_12 * v0_8_12 = v1_8_12 * v0_5_12 + v0_1_12 * v5_8_12 := by
      dsimp only [v0_1_12, v0_5_12, v0_8_12, v1_5_12, v1_8_12, v5_8_12, area]
      ring
    refine ⟨mul_pos hv1_8_12 hv0_5_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_12 hv5_8_12)
  have row1 : 0 < v3_8_11 * v3_5_9 ∧ v3_8_11 * v3_5_9 < v3_8_9 * v3_5_11 := by
    have ident : v3_8_9 * v3_5_11 = v3_8_11 * v3_5_9 + v3_5_8 * v3_9_11 := by
      dsimp only [v3_5_8, v3_5_9, v3_5_11, v3_8_9, v3_8_11, v3_9_11, area]
      ring
    refine ⟨mul_pos hv3_8_11 hv3_5_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_5_8 hv3_9_11)
  have row2 : 0 < v0_8_10 * v5_10_11 ∧ v0_8_10 * v5_10_11 < v8_10_11 * v0_5_10 := by
    have ident : v8_10_11 * v0_5_10 = v0_8_10 * v5_10_11 + v5_8_10 * v0_10_11 := by
      dsimp only [v0_5_10, v0_8_10, v0_10_11, v5_8_10, v5_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv0_8_10 hv5_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv5_8_10 hv0_10_11)
  have row3 : 0 < v0_8_12 * v1_8_9 ∧ v0_8_12 * v1_8_9 < v1_8_12 * v0_8_9 := by
    have ident : v1_8_12 * v0_8_9 = v0_8_12 * v1_8_9 + v8_9_12 * v0_1_8 := by
      dsimp only [v0_1_8, v0_8_9, v0_8_12, v1_8_9, v1_8_12, v8_9_12, area]
      ring
    refine ⟨mul_pos hv0_8_12 hv1_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv8_9_12 hv0_1_8)
  have row4 : 0 < v1_8_11 * v3_8_9 ∧ v1_8_11 * v3_8_9 < v1_8_9 * v3_8_11 := by
    have ident : v1_8_9 * v3_8_11 = v1_8_11 * v3_8_9 + v1_3_8 * v8_9_11 := by
      dsimp only [v1_3_8, v1_8_9, v1_8_11, v3_8_9, v3_8_11, v8_9_11, area]
      ring
    refine ⟨mul_pos hv1_8_11 hv3_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_8 hv8_9_11)
  have row5 : 0 < v1_5_11 * v8_10_11 ∧ v1_5_11 * v8_10_11 < v1_8_11 * v5_10_11 := by
    have ident : v1_8_11 * v5_10_11 = v1_5_11 * v8_10_11 + v1_10_11 * v5_8_11 := by
      dsimp only [v1_5_11, v1_8_11, v1_10_11, v5_8_11, v5_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv1_5_11 hv8_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_10_11 hv5_8_11)
  have row6 : 0 < v1_5_12 * v0_5_11 ∧ v1_5_12 * v0_5_11 < v0_5_12 * v1_5_11 := by
    have ident : v0_5_12 * v1_5_11 = v1_5_12 * v0_5_11 + v5_11_12 * v0_1_5 := by
      dsimp only [v0_1_5, v0_5_11, v0_5_12, v1_5_11, v1_5_12, v5_11_12, area]
      ring
    refine ⟨mul_pos hv1_5_12 hv0_5_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv5_11_12 hv0_1_5)
  have row7 : 0 < v3_5_11 * v0_5_9 ∧ v3_5_11 * v0_5_9 < v3_5_9 * v0_5_11 := by
    have ident : v3_5_9 * v0_5_11 = v3_5_11 * v0_5_9 + v0_3_5 * v5_9_11 := by
      dsimp only [v0_3_5, v0_5_9, v0_5_11, v3_5_9, v3_5_11, v5_9_11, area]
      ring
    refine ⟨mul_pos hv3_5_11 hv0_5_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_3_5 hv5_9_11)
  have row8 : 0 < v0_5_10 * v0_8_9 ∧ v0_5_10 * v0_8_9 < v0_8_10 * v0_5_9 := by
    have ident : v0_8_10 * v0_5_9 = v0_5_10 * v0_8_9 + v0_9_10 * v0_5_8 := by
      dsimp only [v0_5_8, v0_5_9, v0_5_10, v0_8_9, v0_8_10, v0_9_10, area]
      ring
    refine ⟨mul_pos hv0_5_10 hv0_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_10 hv0_5_8)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_08

def signature_780_09 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100100111110010111110010011110111111111111110011111111111111111111001011111001001111011111111111111001111111111111111111001001011011111111111111001011111111011011111011111111111111001001111111111001111111111100100001000100000000000100001000100000000011111111100011110000001000001111110

theorem no_realization_780_09 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_09 p := by
  intro h
  let v0_1_13 : ℝ := -area (p 0) (p 1) (p 13)
  have hv0_1_13 : 0 < v0_1_13 := by
    have hs := h 0 1 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 1 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 1 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_8 : ℝ := -area (p 0) (p 7) (p 8)
  have hv0_7_8 : 0 < v0_7_8 := by
    have hs := h 0 7 8 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 7 8)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_13 : ℝ := -area (p 0) (p 7) (p 13)
  have hv0_7_13 : 0 < v0_7_13 := by
    have hs := h 0 7 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 7 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 7 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_10 : ℝ := -area (p 0) (p 8) (p 10)
  have hv0_8_10 : 0 < v0_8_10 := by
    have hs := h 0 8 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 8 10)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_13 : ℝ := -area (p 0) (p 8) (p 13)
  have hv0_8_13 : 0 < v0_8_13 := by
    have hs := h 0 8 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 8 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 8 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_13 : ℝ := -area (p 0) (p 10) (p 13)
  have hv0_10_13 : 0 < v0_10_13 := by
    have hs := h 0 10 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 10 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 10 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_11_13 : ℝ := -area (p 0) (p 11) (p 13)
  have hv0_11_13 : 0 < v0_11_13 := by
    have hs := h 0 11 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 0 11 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 0 11 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_5 : ℝ := -area (p 1) (p 3) (p 5)
  have hv1_3_5 : 0 < v1_3_5 := by
    have hs := h 1 3 5 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 3 5)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 3 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_8 : ℝ := -area (p 1) (p 3) (p 8)
  have hv1_3_8 : 0 < v1_3_8 := by
    have hs := h 1 3 8 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 3 8)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_10 : ℝ := area (p 1) (p 3) (p 10)
  have hv1_3_10 : 0 < v1_3_10 := by
    have hs := h 1 3 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 3 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 3 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_11 : ℝ := area (p 1) (p 3) (p 11)
  have hv1_3_11 : 0 < v1_3_11 := by
    have hs := h 1 3 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 3 11)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 3 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_13 : ℝ := area (p 1) (p 3) (p 13)
  have hv1_3_13 : 0 < v1_3_13 := by
    have hs := h 1 3 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 3 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 3 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_10 : ℝ := area (p 1) (p 5) (p 10)
  have hv1_5_10 : 0 < v1_5_10 := by
    have hs := h 1 5 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 5 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_13 : ℝ := area (p 1) (p 5) (p 13)
  have hv1_5_13 : 0 < v1_5_13 := by
    have hs := h 1 5 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 5 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 5 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_10 : ℝ := area (p 1) (p 7) (p 10)
  have hv1_7_10 : 0 < v1_7_10 := by
    have hs := h 1 7 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 7 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_11 : ℝ := area (p 1) (p 7) (p 11)
  have hv1_7_11 : 0 < v1_7_11 := by
    have hs := h 1 7 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 7 11)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_13 : ℝ := area (p 1) (p 7) (p 13)
  have hv1_7_13 : 0 < v1_7_13 := by
    have hs := h 1 7 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 7 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 7 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_10 : ℝ := area (p 1) (p 8) (p 10)
  have hv1_8_10 : 0 < v1_8_10 := by
    have hs := h 1 8 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 8 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_9_13 : ℝ := area (p 1) (p 9) (p 13)
  have hv1_9_13 : 0 < v1_9_13 := by
    have hs := h 1 9 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 9 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 9 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_13 : ℝ := area (p 1) (p 10) (p 13)
  have hv1_10_13 : 0 < v1_10_13 := by
    have hs := h 1 10 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 10 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 10 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_11_13 : ℝ := area (p 1) (p 11) (p 13)
  have hv1_11_13 : 0 < v1_11_13 := by
    have hs := h 1 11 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 1 11 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 1 11 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_8 : ℝ := area (p 3) (p 5) (p 8)
  have hv3_5_8 : 0 < v3_5_8 := by
    have hs := h 3 5 8 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 5 8)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_11 : ℝ := area (p 3) (p 5) (p 11)
  have hv3_5_11 : 0 < v3_5_11 := by
    have hs := h 3 5 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 5 11)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := -area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 7 11)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_9 : ℝ := area (p 3) (p 8) (p 9)
  have hv3_8_9 : 0 < v3_8_9 := by
    have hs := h 3 8 9 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 8 9)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_10 : ℝ := area (p 3) (p 8) (p 10)
  have hv3_8_10 : 0 < v3_8_10 := by
    have hs := h 3 8 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 8 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 8 11)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_13 : ℝ := area (p 3) (p 8) (p 13)
  have hv3_8_13 : 0 < v3_8_13 := by
    have hs := h 3 8 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 8 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 8 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := -area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 9 11)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_13 : ℝ := area (p 3) (p 9) (p 13)
  have hv3_9_13 : 0 < v3_9_13 := by
    have hs := h 3 9 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 9 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 9 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_13 : ℝ := area (p 3) (p 10) (p 13)
  have hv3_10_13 : 0 < v3_10_13 := by
    have hs := h 3 10 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 10 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 10 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_11_13 : ℝ := area (p 3) (p 11) (p 13)
  have hv3_11_13 : 0 < v3_11_13 := by
    have hs := h 3 11 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 3 11 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 3 11 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_10 : ℝ := area (p 5) (p 7) (p 10)
  have hv5_7_10 : 0 < v5_7_10 := by
    have hs := h 5 7 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 5 7 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 5 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_9 : ℝ := -area (p 5) (p 8) (p 9)
  have hv5_8_9 : 0 < v5_8_9 := by
    have hs := h 5 8 9 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 5 8 9)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 5 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_10 : ℝ := area (p 5) (p 8) (p 10)
  have hv5_8_10 : 0 < v5_8_10 := by
    have hs := h 5 8 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 5 8 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 5 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_10 : ℝ := area (p 7) (p 8) (p 10)
  have hv7_8_10 : 0 < v7_8_10 := by
    have hs := h 7 8 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 7 8 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 7 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_13 : ℝ := area (p 7) (p 8) (p 13)
  have hv7_8_13 : 0 < v7_8_13 := by
    have hs := h 7 8 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 7 8 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 7 8 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_11_13 : ℝ := area (p 7) (p 11) (p 13)
  have hv7_11_13 : 0 < v7_11_13 := by
    have hs := h 7 11 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 7 11 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 7 11 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 8 9 10)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_13 : ℝ := -area (p 8) (p 10) (p 13)
  have hv8_10_13 : 0 < v8_10_13 := by
    have hs := h 8 10 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 8 10 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 8 10 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_11_13 : ℝ := -area (p 8) (p 11) (p 13)
  have hv8_11_13 : 0 < v8_11_13 := by
    have hs := h 8 11 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 8 11 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 8 11 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_13 : ℝ := -area (p 9) (p 10) (p 13)
  have hv9_10_13 : 0 < v9_10_13 := by
    have hs := h 9 10 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 9 10 13)) = false := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 9 10 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v10_11_13 : ℝ := area (p 10) (p 11) (p 13)
  have hv10_11_13 : 0 < v10_11_13 := by
    have hs := h 10 11 13 (by decide) (by decide)
    have bit : (signature_780_09.testBit (363-lexRank 10 11 13)) = true := by decide
    change 0 < (if signature_780_09.testBit (363-lexRank 10 11 13) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v1_3_5 * v1_10_13 ∧ v1_3_5 * v1_10_13 < v1_3_13 * v1_5_10 := by
    have ident : v1_3_13 * v1_5_10 = v1_3_5 * v1_10_13 + v1_3_10 * v1_5_13 := by
      dsimp only [v1_3_5, v1_3_10, v1_3_13, v1_5_10, v1_5_13, v1_10_13, area]
      ring
    refine ⟨mul_pos hv1_3_5 hv1_10_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_10 hv1_5_13)
  have row1 : 0 < v1_7_10 * v1_11_13 ∧ v1_7_10 * v1_11_13 < v1_7_11 * v1_10_13 := by
    have ident : v1_7_11 * v1_10_13 = v1_7_10 * v1_11_13 + v1_7_13 * v1_10_11 := by
      dsimp only [v1_7_10, v1_7_11, v1_7_13, v1_10_11, v1_10_13, v1_11_13, area]
      ring
    refine ⟨mul_pos hv1_7_10 hv1_11_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_7_13 hv1_10_11)
  have row2 : 0 < v1_3_11 * v3_5_8 ∧ v1_3_11 * v3_5_8 < v1_3_5 * v3_8_11 := by
    have ident : v1_3_5 * v3_8_11 = v1_3_11 * v3_5_8 + v1_3_8 * v3_5_11 := by
      dsimp only [v1_3_5, v1_3_8, v1_3_11, v3_5_8, v3_5_11, v3_8_11, area]
      ring
    refine ⟨mul_pos hv1_3_11 hv3_5_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_8 hv3_5_11)
  have row3 : 0 < v3_8_11 * v3_9_13 ∧ v3_8_11 * v3_9_13 < v3_8_9 * v3_11_13 := by
    have ident : v3_8_9 * v3_11_13 = v3_8_11 * v3_9_13 + v3_8_13 * v3_9_11 := by
      dsimp only [v3_8_9, v3_8_11, v3_8_13, v3_9_11, v3_9_13, v3_11_13, area]
      ring
    refine ⟨mul_pos hv3_8_11 hv3_9_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_13 hv3_9_11)
  have row4 : 0 < v0_8_10 * v7_8_13 ∧ v0_8_10 * v7_8_13 < v0_8_13 * v7_8_10 := by
    have ident : v0_8_13 * v7_8_10 = v0_8_10 * v7_8_13 + v0_7_8 * v8_10_13 := by
      dsimp only [v0_7_8, v0_8_10, v0_8_13, v7_8_10, v7_8_13, v8_10_13, area]
      ring
    refine ⟨mul_pos hv0_8_10 hv7_8_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_7_8 hv8_10_13)
  have row5 : 0 < v3_8_9 * v5_8_10 ∧ v3_8_9 * v5_8_10 < v3_5_8 * v8_9_10 := by
    have ident : v3_5_8 * v8_9_10 = v3_8_9 * v5_8_10 + v3_8_10 * v5_8_9 := by
      dsimp only [v3_5_8, v3_8_9, v3_8_10, v5_8_9, v5_8_10, v8_9_10, area]
      ring
    refine ⟨mul_pos hv3_8_9 hv5_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_8_10 hv5_8_9)
  have row6 : 0 < v0_10_13 * v8_9_10 ∧ v0_10_13 * v8_9_10 < v0_8_10 * v9_10_13 := by
    have ident : v0_8_10 * v9_10_13 = v0_10_13 * v8_9_10 + v0_9_10 * v8_10_13 := by
      dsimp only [v0_8_10, v0_9_10, v0_10_13, v8_9_10, v8_10_13, v9_10_13, area]
      ring
    refine ⟨mul_pos hv0_10_13 hv8_9_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_10 hv8_10_13)
  have row7 : 0 < v1_5_10 * v7_8_10 ∧ v1_5_10 * v7_8_10 < v1_7_10 * v5_8_10 := by
    have ident : v1_7_10 * v5_8_10 = v1_5_10 * v7_8_10 + v1_8_10 * v5_7_10 := by
      dsimp only [v1_5_10, v1_7_10, v1_8_10, v5_7_10, v5_8_10, v7_8_10, area]
      ring
    refine ⟨mul_pos hv1_5_10 hv7_8_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_8_10 hv5_7_10)
  have row8 : 0 < v1_7_11 * v3_11_13 ∧ v1_7_11 * v3_11_13 < v1_3_11 * v7_11_13 := by
    have ident : v1_3_11 * v7_11_13 = v1_7_11 * v3_11_13 + v1_11_13 * v3_7_11 := by
      dsimp only [v1_3_11, v1_7_11, v1_11_13, v3_7_11, v3_11_13, v7_11_13, area]
      ring
    refine ⟨mul_pos hv1_7_11 hv3_11_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_11_13 hv3_7_11)
  have row9 : 0 < v0_11_13 * v1_10_13 ∧ v0_11_13 * v1_10_13 < v0_10_13 * v1_11_13 := by
    have ident : v0_10_13 * v1_11_13 = v0_11_13 * v1_10_13 + v0_1_13 * v10_11_13 := by
      dsimp only [v0_1_13, v0_10_13, v0_11_13, v1_10_13, v1_11_13, v10_11_13, area]
      ring
    refine ⟨mul_pos hv0_11_13 hv1_10_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_13 hv10_11_13)
  have row10 : 0 < v0_8_13 * v7_11_13 ∧ v0_8_13 * v7_11_13 < v0_11_13 * v7_8_13 := by
    have ident : v0_11_13 * v7_8_13 = v0_8_13 * v7_11_13 + v0_7_13 * v8_11_13 := by
      dsimp only [v0_7_13, v0_8_13, v0_11_13, v7_8_13, v7_11_13, v8_11_13, area]
      ring
    refine ⟨mul_pos hv0_8_13 hv7_11_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_7_13 hv8_11_13)
  have row11 : 0 < v1_3_13 * v9_10_13 ∧ v1_3_13 * v9_10_13 < v1_10_13 * v3_9_13 := by
    have ident : v1_10_13 * v3_9_13 = v1_3_13 * v9_10_13 + v1_9_13 * v3_10_13 := by
      dsimp only [v1_3_13, v1_9_13, v1_10_13, v3_9_13, v3_10_13, v9_10_13, area]
      ring
    refine ⟨mul_pos hv1_3_13 hv9_10_13, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_9_13 hv3_10_13)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) (merge (merge row8 row9) (merge row10 row11)))
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_09

def signature_780_10 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000100100111110010111110010011110111111111111110011111111111111111111001011111001001111011111111111111001111111111111111111001001011011111111111111001011111111011011111011111111111111001001111111111001111111111100100001000100000000000100001000100000000011111111100011110100001000001101110

theorem no_realization_780_10 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_10 p := by
  intro h
  let v0_1_5 : ℝ := -area (p 0) (p 1) (p 5)
  have hv0_1_5 : 0 < v0_1_5 := by
    have hs := h 0 1 5 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 1 5)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 1 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_8 : ℝ := -area (p 0) (p 1) (p 8)
  have hv0_1_8 : 0 < v0_1_8 := by
    have hs := h 0 1 8 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 1 8)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 1 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_1_12 : ℝ := -area (p 0) (p 1) (p 12)
  have hv0_1_12 : 0 < v0_1_12 := by
    have hs := h 0 1 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 1 12)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 1 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_5 : ℝ := -area (p 0) (p 3) (p 5)
  have hv0_3_5 : 0 < v0_3_5 := by
    have hs := h 0 3 5 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 3 5)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 3 5) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_8 : ℝ := -area (p 0) (p 5) (p 8)
  have hv0_5_8 : 0 < v0_5_8 := by
    have hs := h 0 5 8 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 5 8)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_9 : ℝ := -area (p 0) (p 5) (p 9)
  have hv0_5_9 : 0 < v0_5_9 := by
    have hs := h 0 5 9 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 5 9)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 5 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_10 : ℝ := -area (p 0) (p 5) (p 10)
  have hv0_5_10 : 0 < v0_5_10 := by
    have hs := h 0 5 10 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 5 10)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_11 : ℝ := -area (p 0) (p 5) (p 11)
  have hv0_5_11 : 0 < v0_5_11 := by
    have hs := h 0 5 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 5 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_5_12 : ℝ := -area (p 0) (p 5) (p 12)
  have hv0_5_12 : 0 < v0_5_12 := by
    have hs := h 0 5 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 5 12)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_10 : ℝ := -area (p 0) (p 8) (p 10)
  have hv0_8_10 : 0 < v0_8_10 := by
    have hs := h 0 8 10 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 8 10)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_12 : ℝ := -area (p 0) (p 8) (p 12)
  have hv0_8_12 : 0 < v0_8_12 := by
    have hs := h 0 8 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 8 12)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_10 : ℝ := -area (p 0) (p 9) (p 10)
  have hv0_9_10 : 0 < v0_9_10 := by
    have hs := h 0 9 10 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 9 10)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_10_11 : ℝ := -area (p 0) (p 10) (p 11)
  have hv0_10_11 : 0 < v0_10_11 := by
    have hs := h 0 10 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 0 10 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 0 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_8 : ℝ := -area (p 1) (p 3) (p 8)
  have hv1_3_8 : 0 < v1_3_8 := by
    have hs := h 1 3 8 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 3 8)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_11 : ℝ := area (p 1) (p 5) (p 11)
  have hv1_5_11 : 0 < v1_5_11 := by
    have hs := h 1 5 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 5 11)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_12 : ℝ := area (p 1) (p 5) (p 12)
  have hv1_5_12 : 0 < v1_5_12 := by
    have hs := h 1 5 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 5 12)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_9 : ℝ := area (p 1) (p 8) (p 9)
  have hv1_8_9 : 0 < v1_8_9 := by
    have hs := h 1 8 9 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 8 9)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_11 : ℝ := area (p 1) (p 8) (p 11)
  have hv1_8_11 : 0 < v1_8_11 := by
    have hs := h 1 8 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 8 11)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_12 : ℝ := area (p 1) (p 8) (p 12)
  have hv1_8_12 : 0 < v1_8_12 := by
    have hs := h 1 8 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 8 12)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_11 : ℝ := area (p 1) (p 10) (p 11)
  have hv1_10_11 : 0 < v1_10_11 := by
    have hs := h 1 10 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 1 10 11)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 1 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_8 : ℝ := area (p 3) (p 5) (p 8)
  have hv3_5_8 : 0 < v3_5_8 := by
    have hs := h 3 5 8 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 3 5 8)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 3 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_9 : ℝ := area (p 3) (p 5) (p 9)
  have hv3_5_9 : 0 < v3_5_9 := by
    have hs := h 3 5 9 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 3 5 9)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 3 5 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_5_11 : ℝ := area (p 3) (p 5) (p 11)
  have hv3_5_11 : 0 < v3_5_11 := by
    have hs := h 3 5 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 3 5 11)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 3 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_9 : ℝ := area (p 3) (p 8) (p 9)
  have hv3_8_9 : 0 < v3_8_9 := by
    have hs := h 3 8 9 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 3 8 9)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 3 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_11 : ℝ := area (p 3) (p 8) (p 11)
  have hv3_8_11 : 0 < v3_8_11 := by
    have hs := h 3 8 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 3 8 11)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 3 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_11 : ℝ := -area (p 3) (p 9) (p 11)
  have hv3_9_11 : 0 < v3_9_11 := by
    have hs := h 3 9 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 3 9 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 3 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_10 : ℝ := area (p 5) (p 8) (p 10)
  have hv5_8_10 : 0 < v5_8_10 := by
    have hs := h 5 8 10 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 5 8 10)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 5 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_11 : ℝ := -area (p 5) (p 8) (p 11)
  have hv5_8_11 : 0 < v5_8_11 := by
    have hs := h 5 8 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 5 8 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 5 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_8_12 : ℝ := -area (p 5) (p 8) (p 12)
  have hv5_8_12 : 0 < v5_8_12 := by
    have hs := h 5 8 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 5 8 12)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 5 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_9_11 : ℝ := -area (p 5) (p 9) (p 11)
  have hv5_9_11 : 0 < v5_9_11 := by
    have hs := h 5 9 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 5 9 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 5 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_11 : ℝ := -area (p 5) (p 10) (p 11)
  have hv5_10_11 : 0 < v5_10_11 := by
    have hs := h 5 10 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 5 10 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 5 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_11_12 : ℝ := -area (p 5) (p 11) (p 12)
  have hv5_11_12 : 0 < v5_11_12 := by
    have hs := h 5 11 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 5 11 12)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 5 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_11 : ℝ := -area (p 8) (p 9) (p 11)
  have hv8_9_11 : 0 < v8_9_11 := by
    have hs := h 8 9 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 8 9 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 8 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_12 : ℝ := area (p 8) (p 9) (p 12)
  have hv8_9_12 : 0 < v8_9_12 := by
    have hs := h 8 9 12 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 8 9 12)) = true := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 8 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_11 : ℝ := -area (p 8) (p 10) (p 11)
  have hv8_10_11 : 0 < v8_10_11 := by
    have hs := h 8 10 11 (by decide) (by decide)
    have bit : (signature_780_10.testBit (363-lexRank 8 10 11)) = false := by decide
    change 0 < (if signature_780_10.testBit (363-lexRank 8 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v1_8_12 * v0_5_12 ∧ v1_8_12 * v0_5_12 < v1_5_12 * v0_8_12 := by
    have ident : v1_5_12 * v0_8_12 = v1_8_12 * v0_5_12 + v0_1_12 * v5_8_12 := by
      dsimp only [v0_1_12, v0_5_12, v0_8_12, v1_5_12, v1_8_12, v5_8_12, area]
      ring
    refine ⟨mul_pos hv1_8_12 hv0_5_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_1_12 hv5_8_12)
  have row1 : 0 < v3_8_11 * v3_5_9 ∧ v3_8_11 * v3_5_9 < v3_8_9 * v3_5_11 := by
    have ident : v3_8_9 * v3_5_11 = v3_8_11 * v3_5_9 + v3_5_8 * v3_9_11 := by
      dsimp only [v3_5_8, v3_5_9, v3_5_11, v3_8_9, v3_8_11, v3_9_11, area]
      ring
    refine ⟨mul_pos hv3_8_11 hv3_5_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_5_8 hv3_9_11)
  have row2 : 0 < v0_8_10 * v5_10_11 ∧ v0_8_10 * v5_10_11 < v8_10_11 * v0_5_10 := by
    have ident : v8_10_11 * v0_5_10 = v0_8_10 * v5_10_11 + v5_8_10 * v0_10_11 := by
      dsimp only [v0_5_10, v0_8_10, v0_10_11, v5_8_10, v5_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv0_8_10 hv5_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv5_8_10 hv0_10_11)
  have row3 : 0 < v0_8_12 * v1_8_9 ∧ v0_8_12 * v1_8_9 < v1_8_12 * v0_8_9 := by
    have ident : v1_8_12 * v0_8_9 = v0_8_12 * v1_8_9 + v8_9_12 * v0_1_8 := by
      dsimp only [v0_1_8, v0_8_9, v0_8_12, v1_8_9, v1_8_12, v8_9_12, area]
      ring
    refine ⟨mul_pos hv0_8_12 hv1_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv8_9_12 hv0_1_8)
  have row4 : 0 < v1_8_11 * v3_8_9 ∧ v1_8_11 * v3_8_9 < v1_8_9 * v3_8_11 := by
    have ident : v1_8_9 * v3_8_11 = v1_8_11 * v3_8_9 + v1_3_8 * v8_9_11 := by
      dsimp only [v1_3_8, v1_8_9, v1_8_11, v3_8_9, v3_8_11, v8_9_11, area]
      ring
    refine ⟨mul_pos hv1_8_11 hv3_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_8 hv8_9_11)
  have row5 : 0 < v1_5_11 * v8_10_11 ∧ v1_5_11 * v8_10_11 < v1_8_11 * v5_10_11 := by
    have ident : v1_8_11 * v5_10_11 = v1_5_11 * v8_10_11 + v1_10_11 * v5_8_11 := by
      dsimp only [v1_5_11, v1_8_11, v1_10_11, v5_8_11, v5_10_11, v8_10_11, area]
      ring
    refine ⟨mul_pos hv1_5_11 hv8_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_10_11 hv5_8_11)
  have row6 : 0 < v1_5_12 * v0_5_11 ∧ v1_5_12 * v0_5_11 < v0_5_12 * v1_5_11 := by
    have ident : v0_5_12 * v1_5_11 = v1_5_12 * v0_5_11 + v5_11_12 * v0_1_5 := by
      dsimp only [v0_1_5, v0_5_11, v0_5_12, v1_5_11, v1_5_12, v5_11_12, area]
      ring
    refine ⟨mul_pos hv1_5_12 hv0_5_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv5_11_12 hv0_1_5)
  have row7 : 0 < v3_5_11 * v0_5_9 ∧ v3_5_11 * v0_5_9 < v3_5_9 * v0_5_11 := by
    have ident : v3_5_9 * v0_5_11 = v3_5_11 * v0_5_9 + v0_3_5 * v5_9_11 := by
      dsimp only [v0_3_5, v0_5_9, v0_5_11, v3_5_9, v3_5_11, v5_9_11, area]
      ring
    refine ⟨mul_pos hv3_5_11 hv0_5_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_3_5 hv5_9_11)
  have row8 : 0 < v0_5_10 * v0_8_9 ∧ v0_5_10 * v0_8_9 < v0_8_10 * v0_5_9 := by
    have ident : v0_8_10 * v0_5_9 = v0_5_10 * v0_8_9 + v0_9_10 * v0_5_8 := by
      dsimp only [v0_5_8, v0_5_9, v0_5_10, v0_8_9, v0_8_10, v0_9_10, area]
      ring
    refine ⟨mul_pos hv0_5_10 hv0_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_9_10 hv0_5_8)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) row8)
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_10

def signature_780_11 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000000000000101000111110100111110100011111011111100011111111111111111111111111010011111010000111101111110000111111111111111111111111010000111101111110000111111111111110111111111101111110000111111111111111111111011000010011111100100010010000011111111111111111100000000000000000001101100001110000001

theorem no_realization_780_11 (p : Fin 14 → ℝ × ℝ) : ¬ Realizes signature_780_11 p := by
  intro h
  let v1_2_6 : ℝ := area (p 1) (p 2) (p 6)
  have hv1_2_6 : 0 < v1_2_6 := by
    have hs := h 1 2 6 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 2 6)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_7 : ℝ := -area (p 1) (p 2) (p 7)
  have hv1_2_7 : 0 < v1_2_7 := by
    have hs := h 1 2 7 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 2 7)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 2 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_9 : ℝ := -area (p 1) (p 2) (p 9)
  have hv1_2_9 : 0 < v1_2_9 := by
    have hs := h 1 2 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 2 9)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 2 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_4_6 : ℝ := area (p 1) (p 4) (p 6)
  have hv1_4_6 : 0 < v1_4_6 := by
    have hs := h 1 4 6 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 4 6)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_7 : ℝ := -area (p 1) (p 6) (p 7)
  have hv1_6_7 : 0 < v1_6_7 := by
    have hs := h 1 6 7 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 6 7)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_9 : ℝ := -area (p 1) (p 6) (p 9)
  have hv1_6_9 : 0 < v1_6_9 := by
    have hs := h 1 6 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 6 9)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_10 : ℝ := area (p 1) (p 6) (p 10)
  have hv1_6_10 : 0 < v1_6_10 := by
    have hs := h 1 6 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 6 10)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_11 : ℝ := area (p 1) (p 6) (p 11)
  have hv1_6_11 : 0 < v1_6_11 := by
    have hs := h 1 6 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 6 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_9 : ℝ := area (p 1) (p 7) (p 9)
  have hv1_7_9 : 0 < v1_7_9 := by
    have hs := h 1 7 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 7 9)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_12 : ℝ := area (p 1) (p 7) (p 12)
  have hv1_7_12 : 0 < v1_7_12 := by
    have hs := h 1 7 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 1 7 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 1 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_10 : ℝ := -area (p 2) (p 4) (p 10)
  have hv2_4_10 : 0 < v2_4_10 := by
    have hs := h 2 4 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 4 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_5_10 : ℝ := area (p 2) (p 5) (p 10)
  have hv2_5_10 : 0 < v2_5_10 := by
    have hs := h 2 5 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 5 10)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_5_11 : ℝ := area (p 2) (p 5) (p 11)
  have hv2_5_11 : 0 < v2_5_11 := by
    have hs := h 2 5 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 5 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_5_12 : ℝ := area (p 2) (p 5) (p 12)
  have hv2_5_12 : 0 < v2_5_12 := by
    have hs := h 2 5 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 5 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_10 : ℝ := -area (p 2) (p 6) (p 10)
  have hv2_6_10 : 0 < v2_6_10 := by
    have hs := h 2 6 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 6 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_11 : ℝ := area (p 2) (p 6) (p 11)
  have hv2_6_11 : 0 < v2_6_11 := by
    have hs := h 2 6 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 6 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_9 : ℝ := area (p 2) (p 7) (p 9)
  have hv2_7_9 : 0 < v2_7_9 := by
    have hs := h 2 7 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 7 9)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_12 : ℝ := area (p 2) (p 7) (p 12)
  have hv2_7_12 : 0 < v2_7_12 := by
    have hs := h 2 7 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 7 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_11_12 : ℝ := area (p 2) (p 11) (p 12)
  have hv2_11_12 : 0 < v2_11_12 := by
    have hs := h 2 11 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 2 11 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 2 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_6 : ℝ := area (p 3) (p 4) (p 6)
  have hv3_4_6 : 0 < v3_4_6 := by
    have hs := h 3 4 6 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 4 6)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_7 : ℝ := -area (p 3) (p 4) (p 7)
  have hv3_4_7 : 0 < v3_4_7 := by
    have hs := h 3 4 7 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 4 7)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 4 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_9 : ℝ := -area (p 3) (p 4) (p 9)
  have hv3_4_9 : 0 < v3_4_9 := by
    have hs := h 3 4 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 4 9)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 4 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_10 : ℝ := -area (p 3) (p 4) (p 10)
  have hv3_4_10 : 0 < v3_4_10 := by
    have hs := h 3 4 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 4 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 4 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_9 : ℝ := area (p 3) (p 7) (p 9)
  have hv3_7_9 : 0 < v3_7_9 := by
    have hs := h 3 7 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 7 9)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_10 : ℝ := area (p 3) (p 7) (p 10)
  have hv3_7_10 : 0 < v3_7_10 := by
    have hs := h 3 7 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 7 10)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_12 : ℝ := area (p 3) (p 7) (p 12)
  have hv3_7_12 : 0 < v3_7_12 := by
    have hs := h 3 7 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 7 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_9_10 : ℝ := -area (p 3) (p 9) (p 10)
  have hv3_9_10 : 0 < v3_9_10 := by
    have hs := h 3 9 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 3 9 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 3 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_5_7 : ℝ := -area (p 4) (p 5) (p 7)
  have hv4_5_7 : 0 < v4_5_7 := by
    have hs := h 4 5 7 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 5 7)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 5 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_5_10 : ℝ := area (p 4) (p 5) (p 10)
  have hv4_5_10 : 0 < v4_5_10 := by
    have hs := h 4 5 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 5 10)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 5 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_5_11 : ℝ := area (p 4) (p 5) (p 11)
  have hv4_5_11 : 0 < v4_5_11 := by
    have hs := h 4 5 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 5 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 5 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_6_9 : ℝ := -area (p 4) (p 6) (p 9)
  have hv4_6_9 : 0 < v4_6_9 := by
    have hs := h 4 6 9 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 6 9)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_6_10 : ℝ := -area (p 4) (p 6) (p 10)
  have hv4_6_10 : 0 < v4_6_10 := by
    have hs := h 4 6 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 6 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_6_11 : ℝ := area (p 4) (p 6) (p 11)
  have hv4_6_11 : 0 < v4_6_11 := by
    have hs := h 4 6 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 6 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_10 : ℝ := area (p 4) (p 7) (p 10)
  have hv4_7_10 : 0 < v4_7_10 := by
    have hs := h 4 7 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 7 10)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_11 : ℝ := area (p 4) (p 7) (p 11)
  have hv4_7_11 : 0 < v4_7_11 := by
    have hs := h 4 7 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 7 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_12 : ℝ := area (p 4) (p 7) (p 12)
  have hv4_7_12 : 0 < v4_7_12 := by
    have hs := h 4 7 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 7 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_9_10 : ℝ := area (p 4) (p 9) (p 10)
  have hv4_9_10 : 0 < v4_9_10 := by
    have hs := h 4 9 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 9 10)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_11 : ℝ := area (p 4) (p 10) (p 11)
  have hv4_10_11 : 0 < v4_10_11 := by
    have hs := h 4 10 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 4 10 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 4 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_10 : ℝ := -area (p 5) (p 6) (p 10)
  have hv5_6_10 : 0 < v5_6_10 := by
    have hs := h 5 6 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 5 6 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 5 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_11 : ℝ := area (p 5) (p 6) (p 11)
  have hv5_6_11 : 0 < v5_6_11 := by
    have hs := h 5 6 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 5 6 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 5 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_7_12 : ℝ := area (p 5) (p 7) (p 12)
  have hv5_7_12 : 0 < v5_7_12 := by
    have hs := h 5 7 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 5 7 12)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 5 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_11 : ℝ := area (p 5) (p 10) (p 11)
  have hv5_10_11 : 0 < v5_10_11 := by
    have hs := h 5 10 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 5 10 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 5 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_12 : ℝ := -area (p 5) (p 10) (p 12)
  have hv5_10_12 : 0 < v5_10_12 := by
    have hs := h 5 10 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 5 10 12)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 5 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_11_12 : ℝ := -area (p 5) (p 11) (p 12)
  have hv5_11_12 : 0 < v5_11_12 := by
    have hs := h 5 11 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 5 11 12)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 5 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_9_11 : ℝ := area (p 6) (p 9) (p 11)
  have hv6_9_11 : 0 < v6_9_11 := by
    have hs := h 6 9 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 6 9 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 6 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_10_11 : ℝ := area (p 6) (p 10) (p 11)
  have hv6_10_11 : 0 < v6_10_11 := by
    have hs := h 6 10 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 6 10 11)) = true := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 6 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_9_10 : ℝ := -area (p 7) (p 9) (p 10)
  have hv7_9_10 : 0 < v7_9_10 := by
    have hs := h 7 9 10 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 7 9 10)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 7 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_9_12 : ℝ := -area (p 7) (p 9) (p 12)
  have hv7_9_12 : 0 < v7_9_12 := by
    have hs := h 7 9 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 7 9 12)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 7 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_11 : ℝ := -area (p 7) (p 10) (p 11)
  have hv7_10_11 : 0 < v7_10_11 := by
    have hs := h 7 10 11 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 7 10 11)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 7 10 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_12 : ℝ := -area (p 7) (p 10) (p 12)
  have hv7_10_12 : 0 < v7_10_12 := by
    have hs := h 7 10 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 7 10 12)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 7 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_11_12 : ℝ := -area (p 7) (p 11) (p 12)
  have hv7_11_12 : 0 < v7_11_12 := by
    have hs := h 7 11 12 (by decide) (by decide)
    have bit : (signature_780_11.testBit (363-lexRank 7 11 12)) = false := by decide
    change 0 < (if signature_780_11.testBit (363-lexRank 7 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v1_2_6 * v1_7_9 ∧ v1_2_6 * v1_7_9 < v1_2_7 * v1_6_9 := by
    have ident : v1_2_7 * v1_6_9 = v1_2_6 * v1_7_9 + v1_2_9 * v1_6_7 := by
      dsimp only [v1_2_6, v1_2_7, v1_2_9, v1_6_7, v1_6_9, v1_7_9, area]
      ring
    refine ⟨mul_pos hv1_2_6 hv1_7_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_9 hv1_6_7)
  have row1 : 0 < v3_4_9 * v3_7_10 ∧ v3_4_9 * v3_7_10 < v3_4_10 * v3_7_9 := by
    have ident : v3_4_10 * v3_7_9 = v3_4_9 * v3_7_10 + v3_4_7 * v3_9_10 := by
      dsimp only [v3_4_7, v3_4_9, v3_4_10, v3_7_9, v3_7_10, v3_9_10, area]
      ring
    refine ⟨mul_pos hv3_4_9 hv3_7_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_7 hv3_9_10)
  have row2 : 0 < v3_4_10 * v4_6_9 ∧ v3_4_10 * v4_6_9 < v3_4_9 * v4_6_10 := by
    have ident : v3_4_9 * v4_6_10 = v3_4_10 * v4_6_9 + v3_4_6 * v4_9_10 := by
      dsimp only [v3_4_6, v3_4_9, v3_4_10, v4_6_9, v4_6_10, v4_9_10, area]
      ring
    refine ⟨mul_pos hv3_4_10 hv4_6_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_4_6 hv4_9_10)
  have row3 : 0 < v4_5_10 * v4_7_11 ∧ v4_5_10 * v4_7_11 < v4_5_11 * v4_7_10 := by
    have ident : v4_5_11 * v4_7_10 = v4_5_10 * v4_7_11 + v4_5_7 * v4_10_11 := by
      dsimp only [v4_5_7, v4_5_10, v4_5_11, v4_7_10, v4_7_11, v4_10_11, area]
      ring
    refine ⟨mul_pos hv4_5_10 hv4_7_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_5_7 hv4_10_11)
  have row4 : 0 < v2_5_12 * v5_10_11 ∧ v2_5_12 * v5_10_11 < v2_5_10 * v5_11_12 := by
    have ident : v2_5_10 * v5_11_12 = v2_5_12 * v5_10_11 + v2_5_11 * v5_10_12 := by
      dsimp only [v2_5_10, v2_5_11, v2_5_12, v5_10_11, v5_10_12, v5_11_12, area]
      ring
    refine ⟨mul_pos hv2_5_12 hv5_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_5_11 hv5_10_12)
  have row5 : 0 < v1_6_11 * v2_6_10 ∧ v1_6_11 * v2_6_10 < v1_2_6 * v6_10_11 := by
    have ident : v1_2_6 * v6_10_11 = v1_6_11 * v2_6_10 + v1_6_10 * v2_6_11 := by
      dsimp only [v1_2_6, v1_6_10, v1_6_11, v2_6_10, v2_6_11, v6_10_11, area]
      ring
    refine ⟨mul_pos hv1_6_11 hv2_6_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_6_10 hv2_6_11)
  have row6 : 0 < v1_6_9 * v4_6_11 ∧ v1_6_9 * v4_6_11 < v1_6_11 * v4_6_9 := by
    have ident : v1_6_11 * v4_6_9 = v1_6_9 * v4_6_11 + v1_4_6 * v6_9_11 := by
      dsimp only [v1_4_6, v1_6_9, v1_6_11, v4_6_9, v4_6_11, v6_9_11, area]
      ring
    refine ⟨mul_pos hv1_6_9 hv4_6_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_4_6 hv6_9_11)
  have row7 : 0 < v1_2_7 * v7_9_12 ∧ v1_2_7 * v7_9_12 < v1_7_9 * v2_7_12 := by
    have ident : v1_7_9 * v2_7_12 = v1_2_7 * v7_9_12 + v1_7_12 * v2_7_9 := by
      dsimp only [v1_2_7, v1_7_9, v1_7_12, v2_7_9, v2_7_12, v7_9_12, area]
      ring
    refine ⟨mul_pos hv1_2_7 hv7_9_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_7_12 hv2_7_9)
  have row8 : 0 < v3_7_9 * v7_10_12 ∧ v3_7_9 * v7_10_12 < v3_7_10 * v7_9_12 := by
    have ident : v3_7_10 * v7_9_12 = v3_7_9 * v7_10_12 + v3_7_12 * v7_9_10 := by
      dsimp only [v3_7_9, v3_7_10, v3_7_12, v7_9_10, v7_9_12, v7_10_12, area]
      ring
    refine ⟨mul_pos hv3_7_9 hv7_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_7_12 hv7_9_10)
  have row9 : 0 < v4_7_10 * v7_11_12 ∧ v4_7_10 * v7_11_12 < v4_7_11 * v7_10_12 := by
    have ident : v4_7_11 * v7_10_12 = v4_7_10 * v7_11_12 + v4_7_12 * v7_10_11 := by
      dsimp only [v4_7_10, v4_7_11, v4_7_12, v7_10_11, v7_10_12, v7_11_12, area]
      ring
    refine ⟨mul_pos hv4_7_10 hv7_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_7_12 hv7_10_11)
  have row10 : 0 < v2_5_10 * v4_6_10 ∧ v2_5_10 * v4_6_10 < v2_6_10 * v4_5_10 := by
    have ident : v2_6_10 * v4_5_10 = v2_5_10 * v4_6_10 + v2_4_10 * v5_6_10 := by
      dsimp only [v2_4_10, v2_5_10, v2_6_10, v4_5_10, v4_6_10, v5_6_10, area]
      ring
    refine ⟨mul_pos hv2_5_10 hv4_6_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_4_10 hv5_6_10)
  have row11 : 0 < v4_5_11 * v6_10_11 ∧ v4_5_11 * v6_10_11 < v4_6_11 * v5_10_11 := by
    have ident : v4_6_11 * v5_10_11 = v4_5_11 * v6_10_11 + v4_10_11 * v5_6_11 := by
      dsimp only [v4_5_11, v4_6_11, v4_10_11, v5_6_11, v5_10_11, v6_10_11, area]
      ring
    refine ⟨mul_pos hv4_5_11 hv6_10_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_10_11 hv5_6_11)
  have row12 : 0 < v2_7_12 * v5_11_12 ∧ v2_7_12 * v5_11_12 < v2_5_12 * v7_11_12 := by
    have ident : v2_5_12 * v7_11_12 = v2_7_12 * v5_11_12 + v2_11_12 * v5_7_12 := by
      dsimp only [v2_5_12, v2_7_12, v2_11_12, v5_7_12, v5_11_12, v7_11_12, area]
      ring
    refine ⟨mul_pos hv2_7_12 hv5_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_11_12 hv5_7_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) (merge (merge (merge row8 row9) (merge row10 row11)) row12))
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_780_11
end FourteenPointExclusions
