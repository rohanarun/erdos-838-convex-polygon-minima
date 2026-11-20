import Exclude569
namespace ThirteenPointExclusions

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

def signature_570_1 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000000001111101001111000011111001111001111111111111111111111011111000111111011111011111111111111111111000000111001111001011111111111011111111111111111111111111111111100101011111111100010011111111100011000000000000000001110

theorem no_realization_570_1 (p : Fin 13 → ℝ × ℝ) : ¬ Realizes signature_570_1 p := by
  intro h
  let v1_2_6 : ℝ := -area (p 1) (p 2) (p 6)
  have hv1_2_6 : 0 < v1_2_6 := by
    have hs := h 1 2 6 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 2 6)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_7 : ℝ := -area (p 1) (p 2) (p 7)
  have hv1_2_7 : 0 < v1_2_7 := by
    have hs := h 1 2 7 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 2 7)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 2 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_8 : ℝ := -area (p 1) (p 2) (p 8)
  have hv1_2_8 : 0 < v1_2_8 := by
    have hs := h 1 2 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 2 8)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 2 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_10 : ℝ := area (p 1) (p 2) (p 10)
  have hv1_2_10 : 0 < v1_2_10 := by
    have hs := h 1 2 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 2 10)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 2 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_2_11 : ℝ := area (p 1) (p 2) (p 11)
  have hv1_2_11 : 0 < v1_2_11 := by
    have hs := h 1 2 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 2 11)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 2 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_6 : ℝ := area (p 1) (p 3) (p 6)
  have hv1_3_6 : 0 < v1_3_6 := by
    have hs := h 1 3 6 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 3 6)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_3_8 : ℝ := -area (p 1) (p 3) (p 8)
  have hv1_3_8 : 0 < v1_3_8 := by
    have hs := h 1 3 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 3 8)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_6 : ℝ := area (p 1) (p 5) (p 6)
  have hv1_5_6 : 0 < v1_5_6 := by
    have hs := h 1 5 6 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 5 6)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 5 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_8 : ℝ := -area (p 1) (p 5) (p 8)
  have hv1_5_8 : 0 < v1_5_8 := by
    have hs := h 1 5 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 5 8)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 5 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_5_12 : ℝ := area (p 1) (p 5) (p 12)
  have hv1_5_12 : 0 < v1_5_12 := by
    have hs := h 1 5 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 5 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 5 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_8 : ℝ := -area (p 1) (p 6) (p 8)
  have hv1_6_8 : 0 < v1_6_8 := by
    have hs := h 1 6 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 6 8)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_11 : ℝ := area (p 1) (p 6) (p 11)
  have hv1_6_11 : 0 < v1_6_11 := by
    have hs := h 1 6 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 6 11)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_6_12 : ℝ := area (p 1) (p 6) (p 12)
  have hv1_6_12 : 0 < v1_6_12 := by
    have hs := h 1 6 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 6 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_8 : ℝ := area (p 1) (p 7) (p 8)
  have hv1_7_8 : 0 < v1_7_8 := by
    have hs := h 1 7 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 7 8)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_10 : ℝ := area (p 1) (p 7) (p 10)
  have hv1_7_10 : 0 < v1_7_10 := by
    have hs := h 1 7 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 7 10)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_11 : ℝ := area (p 1) (p 7) (p 11)
  have hv1_7_11 : 0 < v1_7_11 := by
    have hs := h 1 7 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 7 11)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_7_12 : ℝ := area (p 1) (p 7) (p 12)
  have hv1_7_12 : 0 < v1_7_12 := by
    have hs := h 1 7 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 7 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_10 : ℝ := area (p 1) (p 8) (p 10)
  have hv1_8_10 : 0 < v1_8_10 := by
    have hs := h 1 8 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 8 10)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_11 : ℝ := area (p 1) (p 8) (p 11)
  have hv1_8_11 : 0 < v1_8_11 := by
    have hs := h 1 8 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 8 11)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_8_12 : ℝ := area (p 1) (p 8) (p 12)
  have hv1_8_12 : 0 < v1_8_12 := by
    have hs := h 1 8 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 8 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_10_12 : ℝ := area (p 1) (p 10) (p 12)
  have hv1_10_12 : 0 < v1_10_12 := by
    have hs := h 1 10 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 10 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v1_11_12 : ℝ := area (p 1) (p 11) (p 12)
  have hv1_11_12 : 0 < v1_11_12 := by
    have hs := h 1 11 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 1 11 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 1 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_6 : ℝ := area (p 2) (p 3) (p 6)
  have hv2_3_6 : 0 < v2_3_6 := by
    have hs := h 2 3 6 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 3 6)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_7 : ℝ := -area (p 2) (p 3) (p 7)
  have hv2_3_7 : 0 < v2_3_7 := by
    have hs := h 2 3 7 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 3 7)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_8 : ℝ := area (p 2) (p 3) (p 8)
  have hv2_3_8 : 0 < v2_3_8 := by
    have hs := h 2 3 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 3 8)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_7 : ℝ := -area (p 2) (p 6) (p 7)
  have hv2_6_7 : 0 < v2_6_7 := by
    have hs := h 2 6 7 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 6 7)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_8 : ℝ := area (p 2) (p 6) (p 8)
  have hv2_6_8 : 0 < v2_6_8 := by
    have hs := h 2 6 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 6 8)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_10 : ℝ := area (p 2) (p 6) (p 10)
  have hv2_6_10 : 0 < v2_6_10 := by
    have hs := h 2 6 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 6 10)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_12 : ℝ := area (p 2) (p 6) (p 12)
  have hv2_6_12 : 0 < v2_6_12 := by
    have hs := h 2 6 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 6 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_8 : ℝ := area (p 2) (p 7) (p 8)
  have hv2_7_8 : 0 < v2_7_8 := by
    have hs := h 2 7 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 7 8)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_10 : ℝ := area (p 2) (p 7) (p 10)
  have hv2_7_10 : 0 < v2_7_10 := by
    have hs := h 2 7 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 7 10)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_11 : ℝ := area (p 2) (p 7) (p 11)
  have hv2_7_11 : 0 < v2_7_11 := by
    have hs := h 2 7 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 7 11)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_12 : ℝ := area (p 2) (p 7) (p 12)
  have hv2_7_12 : 0 < v2_7_12 := by
    have hs := h 2 7 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 7 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_12 : ℝ := area (p 2) (p 8) (p 12)
  have hv2_8_12 : 0 < v2_8_12 := by
    have hs := h 2 8 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 2 8 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 2 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_8 : ℝ := -area (p 3) (p 6) (p 8)
  have hv3_6_8 : 0 < v3_6_8 := by
    have hs := h 3 6 8 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 3 6 8)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 3 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_10 : ℝ := -area (p 3) (p 6) (p 10)
  have hv3_6_10 : 0 < v3_6_10 := by
    have hs := h 3 6 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 3 6 10)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 3 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_6_12 : ℝ := area (p 3) (p 6) (p 12)
  have hv3_6_12 : 0 < v3_6_12 := by
    have hs := h 3 6 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 3 6 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 3 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_12 : ℝ := area (p 3) (p 8) (p 12)
  have hv3_8_12 : 0 < v3_8_12 := by
    have hs := h 3 8 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 3 8 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 3 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_11_12 : ℝ := area (p 3) (p 11) (p 12)
  have hv3_11_12 : 0 < v3_11_12 := by
    have hs := h 3 11 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 3 11 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 3 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_11 : ℝ := area (p 5) (p 6) (p 11)
  have hv5_6_11 : 0 < v5_6_11 := by
    have hs := h 5 6 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 5 6 11)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 5 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_6_12 : ℝ := -area (p 5) (p 6) (p 12)
  have hv5_6_12 : 0 < v5_6_12 := by
    have hs := h 5 6 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 5 6 12)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 5 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v5_10_12 : ℝ := -area (p 5) (p 10) (p 12)
  have hv5_10_12 : 0 < v5_10_12 := by
    have hs := h 5 10 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 5 10 12)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 5 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_8_12 : ℝ := area (p 6) (p 8) (p 12)
  have hv6_8_12 : 0 < v6_8_12 := by
    have hs := h 6 8 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 6 8 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 6 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_10_12 : ℝ := area (p 6) (p 10) (p 12)
  have hv6_10_12 : 0 < v6_10_12 := by
    have hs := h 6 10 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 6 10 12)) = true := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 6 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_11_12 : ℝ := -area (p 6) (p 11) (p 12)
  have hv6_11_12 : 0 < v6_11_12 := by
    have hs := h 6 11 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 6 11 12)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 6 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_10 : ℝ := -area (p 7) (p 8) (p 10)
  have hv7_8_10 : 0 < v7_8_10 := by
    have hs := h 7 8 10 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 7 8 10)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 7 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_11 : ℝ := -area (p 7) (p 8) (p 11)
  have hv7_8_11 : 0 < v7_8_11 := by
    have hs := h 7 8 11 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 7 8 11)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 7 8 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_11_12 : ℝ := -area (p 7) (p 11) (p 12)
  have hv7_11_12 : 0 < v7_11_12 := by
    have hs := h 7 11 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 7 11 12)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 7 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_11_12 : ℝ := -area (p 8) (p 11) (p 12)
  have hv8_11_12 : 0 < v8_11_12 := by
    have hs := h 8 11 12 (by decide) (by decide)
    have bit : (signature_570_1.testBit (285-lexRank 8 11 12)) = false := by decide
    change 0 < (if signature_570_1.testBit (285-lexRank 8 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v1_2_6 * v1_8_11 ∧ v1_2_6 * v1_8_11 < v1_2_8 * v1_6_11 := by
    have ident : v1_2_8 * v1_6_11 = v1_2_6 * v1_8_11 + v1_2_11 * v1_6_8 := by
      dsimp only [v1_2_6, v1_2_8, v1_2_11, v1_6_8, v1_6_11, v1_8_11, area]
      ring
    refine ⟨mul_pos hv1_2_6 hv1_8_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_11 hv1_6_8)
  have row1 : 0 < v1_5_6 * v1_8_12 ∧ v1_5_6 * v1_8_12 < v1_5_12 * v1_6_8 := by
    have ident : v1_5_12 * v1_6_8 = v1_5_6 * v1_8_12 + v1_5_8 * v1_6_12 := by
      dsimp only [v1_5_6, v1_5_8, v1_5_12, v1_6_8, v1_6_12, v1_8_12, area]
      ring
    refine ⟨mul_pos hv1_5_6 hv1_8_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_5_8 hv1_6_12)
  have row2 : 0 < v1_7_8 * v1_10_12 ∧ v1_7_8 * v1_10_12 < v1_7_10 * v1_8_12 := by
    have ident : v1_7_10 * v1_8_12 = v1_7_8 * v1_10_12 + v1_7_12 * v1_8_10 := by
      dsimp only [v1_7_8, v1_7_10, v1_7_12, v1_8_10, v1_8_12, v1_10_12, area]
      ring
    refine ⟨mul_pos hv1_7_8 hv1_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_7_12 hv1_8_10)
  have row3 : 0 < v1_2_6 * v2_7_10 ∧ v1_2_6 * v2_7_10 < v1_2_7 * v2_6_10 := by
    have ident : v1_2_7 * v2_6_10 = v1_2_6 * v2_7_10 + v1_2_10 * v2_6_7 := by
      dsimp only [v1_2_6, v1_2_7, v1_2_10, v2_6_7, v2_6_10, v2_7_10, area]
      ring
    refine ⟨mul_pos hv1_2_6 hv2_7_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_10 hv2_6_7)
  have row4 : 0 < v2_3_8 * v2_7_12 ∧ v2_3_8 * v2_7_12 < v2_3_12 * v2_7_8 := by
    have ident : v2_3_12 * v2_7_8 = v2_3_8 * v2_7_12 + v2_3_7 * v2_8_12 := by
      dsimp only [v2_3_7, v2_3_8, v2_3_12, v2_7_8, v2_7_12, v2_8_12, area]
      ring
    refine ⟨mul_pos hv2_3_8 hv2_7_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_3_7 hv2_8_12)
  have row5 : 0 < v2_3_12 * v3_6_8 ∧ v2_3_12 * v3_6_8 < v2_3_6 * v3_8_12 := by
    have ident : v2_3_6 * v3_8_12 = v2_3_12 * v3_6_8 + v2_3_8 * v3_6_12 := by
      dsimp only [v2_3_6, v2_3_8, v2_3_12, v3_6_8, v3_6_12, v3_8_12, area]
      ring
    refine ⟨mul_pos hv2_3_12 hv3_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_3_8 hv3_6_12)
  have row6 : 0 < v1_6_8 * v2_3_6 ∧ v1_6_8 * v2_3_6 < v1_2_6 * v3_6_8 := by
    have ident : v1_2_6 * v3_6_8 = v1_6_8 * v2_3_6 + v1_3_6 * v2_6_8 := by
      dsimp only [v1_2_6, v1_3_6, v1_6_8, v2_3_6, v2_6_8, v3_6_8, area]
      ring
    refine ⟨mul_pos hv1_6_8 hv2_3_6, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_6 hv2_6_8)
  have row7 : 0 < v1_6_11 * v5_6_12 ∧ v1_6_11 * v5_6_12 < v1_5_6 * v6_11_12 := by
    have ident : v1_5_6 * v6_11_12 = v1_6_11 * v5_6_12 + v1_6_12 * v5_6_11 := by
      dsimp only [v1_5_6, v1_6_11, v1_6_12, v5_6_11, v5_6_12, v6_11_12, area]
      ring
    refine ⟨mul_pos hv1_6_11 hv5_6_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_6_12 hv5_6_11)
  have row8 : 0 < v2_6_10 * v3_6_12 ∧ v2_6_10 * v3_6_12 < v2_3_6 * v6_10_12 := by
    have ident : v2_3_6 * v6_10_12 = v2_6_10 * v3_6_12 + v2_6_12 * v3_6_10 := by
      dsimp only [v2_3_6, v2_6_10, v2_6_12, v3_6_10, v3_6_12, v6_10_12, area]
      ring
    refine ⟨mul_pos hv2_6_10 hv3_6_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_6_12 hv3_6_10)
  have row9 : 0 < v1_7_10 * v2_7_8 ∧ v1_7_10 * v2_7_8 < v1_7_8 * v2_7_10 := by
    have ident : v1_7_8 * v2_7_10 = v1_7_10 * v2_7_8 + v1_2_7 * v7_8_10 := by
      dsimp only [v1_2_7, v1_7_8, v1_7_10, v2_7_8, v2_7_10, v7_8_10, area]
      ring
    refine ⟨mul_pos hv1_7_10 hv2_7_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_2_7 hv7_8_10)
  have row10 : 0 < v1_2_7 * v7_11_12 ∧ v1_2_7 * v7_11_12 < v1_7_11 * v2_7_12 := by
    have ident : v1_7_11 * v2_7_12 = v1_2_7 * v7_11_12 + v1_7_12 * v2_7_11 := by
      dsimp only [v1_2_7, v1_7_11, v1_7_12, v2_7_11, v2_7_12, v7_11_12, area]
      ring
    refine ⟨mul_pos hv1_2_7 hv7_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_7_12 hv2_7_11)
  have row11 : 0 < v1_2_8 * v3_6_8 ∧ v1_2_8 * v3_6_8 < v1_6_8 * v2_3_8 := by
    have ident : v1_6_8 * v2_3_8 = v1_2_8 * v3_6_8 + v1_3_8 * v2_6_8 := by
      dsimp only [v1_2_8, v1_3_8, v1_6_8, v2_3_8, v2_6_8, v3_6_8, area]
      ring
    refine ⟨mul_pos hv1_2_8 hv3_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_3_8 hv2_6_8)
  have row12 : 0 < v1_7_11 * v8_11_12 ∧ v1_7_11 * v8_11_12 < v1_8_11 * v7_11_12 := by
    have ident : v1_8_11 * v7_11_12 = v1_7_11 * v8_11_12 + v1_11_12 * v7_8_11 := by
      dsimp only [v1_7_11, v1_8_11, v1_11_12, v7_8_11, v7_11_12, v8_11_12, area]
      ring
    refine ⟨mul_pos hv1_7_11 hv8_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_11_12 hv7_8_11)
  have row13 : 0 < v1_5_12 * v6_10_12 ∧ v1_5_12 * v6_10_12 < v1_10_12 * v5_6_12 := by
    have ident : v1_10_12 * v5_6_12 = v1_5_12 * v6_10_12 + v1_6_12 * v5_10_12 := by
      dsimp only [v1_5_12, v1_6_12, v1_10_12, v5_6_12, v5_10_12, v6_10_12, area]
      ring
    refine ⟨mul_pos hv1_5_12 hv6_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv1_6_12 hv5_10_12)
  have row14 : 0 < v3_8_12 * v6_11_12 ∧ v3_8_12 * v6_11_12 < v3_6_12 * v8_11_12 := by
    have ident : v3_6_12 * v8_11_12 = v3_8_12 * v6_11_12 + v3_11_12 * v6_8_12 := by
      dsimp only [v3_6_12, v3_8_12, v3_11_12, v6_8_12, v6_11_12, v8_11_12, area]
      ring
    refine ⟨mul_pos hv3_8_12 hv6_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv3_11_12 hv6_8_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row6))) (merge (merge (merge row7 row8) (merge row9 row10)) (merge (merge row11 row12) (merge row13 row14))))
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_570_1

def signature_570_2 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000100001111100011111000011110111111111111111111111111111100011111000011110111111111111111111111111111000010110111111111111111111011011111011111111111111111111100111111111101000100000000001000100000000010010001110001111110

theorem no_realization_570_2 (p : Fin 13 → ℝ × ℝ) : ¬ Realizes signature_570_2 p := by
  intro h
  let v0_2_3 : ℝ := -area (p 0) (p 2) (p 3)
  have hv0_2_3 : 0 < v0_2_3 := by
    have hs := h 0 2 3 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 2 3)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 2 3) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_9 : ℝ := -area (p 0) (p 2) (p 9)
  have hv0_2_9 : 0 < v0_2_9 := by
    have hs := h 0 2 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 2 9)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 2 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_6 : ℝ := -area (p 0) (p 3) (p 6)
  have hv0_3_6 : 0 < v0_3_6 := by
    have hs := h 0 3 6 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 3 6)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_3_9 : ℝ := -area (p 0) (p 3) (p 9)
  have hv0_3_9 : 0 < v0_3_9 := by
    have hs := h 0 3 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 3 9)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 3 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_9 : ℝ := -area (p 0) (p 6) (p 9)
  have hv0_6_9 : 0 < v0_6_9 := by
    have hs := h 0 6 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 6 9)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_9 : ℝ := -area (p 0) (p 7) (p 9)
  have hv0_7_9 : 0 < v0_7_9 := by
    have hs := h 0 7 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 7 9)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_9_12 : ℝ := -area (p 0) (p 9) (p 12)
  have hv0_9_12 : 0 < v0_9_12 := by
    have hs := h 0 9 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 0 9 12)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 0 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_6 : ℝ := -area (p 2) (p 3) (p 6)
  have hv2_3_6 : 0 < v2_3_6 := by
    have hs := h 2 3 6 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 3 6)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_7 : ℝ := -area (p 2) (p 3) (p 7)
  have hv2_3_7 : 0 < v2_3_7 := by
    have hs := h 2 3 7 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 3 7)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 3 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_8 : ℝ := area (p 2) (p 3) (p 8)
  have hv2_3_8 : 0 < v2_3_8 := by
    have hs := h 2 3 8 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 3 8)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 3 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_12 : ℝ := area (p 2) (p 6) (p 12)
  have hv2_6_12 : 0 < v2_6_12 := by
    have hs := h 2 6 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 6 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 6 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_10 : ℝ := area (p 2) (p 8) (p 10)
  have hv2_8_10 : 0 < v2_8_10 := by
    have hs := h 2 8 10 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 8 10)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_12 : ℝ := area (p 2) (p 9) (p 12)
  have hv2_9_12 : 0 < v2_9_12 := by
    have hs := h 2 9 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 9 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_12 : ℝ := area (p 2) (p 10) (p 12)
  have hv2_10_12 : 0 < v2_10_12 := by
    have hs := h 2 10 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 2 10 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 2 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_8 : ℝ := area (p 3) (p 7) (p 8)
  have hv3_7_8 : 0 < v3_7_8 := by
    have hs := h 3 7 8 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 3 7 8)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 3 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_9 : ℝ := area (p 3) (p 7) (p 9)
  have hv3_7_9 : 0 < v3_7_9 := by
    have hs := h 3 7 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 3 7 9)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 3 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_12 : ℝ := area (p 3) (p 7) (p 12)
  have hv3_7_12 : 0 < v3_7_12 := by
    have hs := h 3 7 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 3 7 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 3 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_9 : ℝ := area (p 3) (p 8) (p 9)
  have hv3_8_9 : 0 < v3_8_9 := by
    have hs := h 3 8 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 3 8 9)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 3 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_10 : ℝ := -area (p 3) (p 8) (p 10)
  have hv3_8_10 : 0 < v3_8_10 := by
    have hs := h 3 8 10 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 3 8 10)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 3 8 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_8_12 : ℝ := area (p 3) (p 8) (p 12)
  have hv3_8_12 : 0 < v3_8_12 := by
    have hs := h 3 8 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 3 8 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 3 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_9 : ℝ := area (p 6) (p 7) (p 9)
  have hv6_7_9 : 0 < v6_7_9 := by
    have hs := h 6 7 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 6 7 9)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 6 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_9_12 : ℝ := -area (p 6) (p 9) (p 12)
  have hv6_9_12 : 0 < v6_9_12 := by
    have hs := h 6 9 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 6 9 12)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 6 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_10_12 : ℝ := -area (p 6) (p 10) (p 12)
  have hv6_10_12 : 0 < v6_10_12 := by
    have hs := h 6 10 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 6 10 12)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 6 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_9 : ℝ := area (p 7) (p 8) (p 9)
  have hv7_8_9 : 0 < v7_8_9 := by
    have hs := h 7 8 9 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 7 8 9)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 7 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_9_12 : ℝ := -area (p 7) (p 9) (p 12)
  have hv7_9_12 : 0 < v7_9_12 := by
    have hs := h 7 9 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 7 9 12)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 7 9 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_9_10 : ℝ := -area (p 8) (p 9) (p 10)
  have hv8_9_10 : 0 < v8_9_10 := by
    have hs := h 8 9 10 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 8 9 10)) = false := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 8 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_12 : ℝ := area (p 8) (p 10) (p 12)
  have hv8_10_12 : 0 < v8_10_12 := by
    have hs := h 8 10 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 8 10 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 8 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v9_10_12 : ℝ := area (p 9) (p 10) (p 12)
  have hv9_10_12 : 0 < v9_10_12 := by
    have hs := h 9 10 12 (by decide) (by decide)
    have bit : (signature_570_2.testBit (285-lexRank 9 10 12)) = true := by decide
    change 0 < (if signature_570_2.testBit (285-lexRank 9 10 12) then _ else _) at hs
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

#print axioms no_realization_570_2

def signature_570_3 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000100001111100101111000011110111111111111011111111111111100111111000011110111111111111111111111111111000010010111111111111010011111001111011111111111111111111100111111111101000110000000001000100000000011110001110000001110

theorem no_realization_570_3 (p : Fin 13 → ℝ × ℝ) : ¬ Realizes signature_570_3 p := by
  intro h
  let v0_2_3 : ℝ := -area (p 0) (p 2) (p 3)
  have hv0_2_3 : 0 < v0_2_3 := by
    have hs := h 0 2 3 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 2 3)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 2 3) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_4 : ℝ := -area (p 0) (p 2) (p 4)
  have hv0_2_4 : 0 < v0_2_4 := by
    have hs := h 0 2 4 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 2 4)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_8 : ℝ := -area (p 0) (p 2) (p 8)
  have hv0_2_8 : 0 < v0_2_8 := by
    have hs := h 0 2 8 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 2 8)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 2 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_11 : ℝ := -area (p 0) (p 2) (p 11)
  have hv0_2_11 : 0 < v0_2_11 := by
    have hs := h 0 2 11 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 2 11)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 2 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_6 : ℝ := -area (p 0) (p 4) (p 6)
  have hv0_4_6 : 0 < v0_4_6 := by
    have hs := h 0 4 6 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 4 6)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_8 : ℝ := -area (p 0) (p 6) (p 8)
  have hv0_6_8 : 0 < v0_6_8 := by
    have hs := h 0 6 8 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 6 8)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_8 : ℝ := -area (p 0) (p 7) (p 8)
  have hv0_7_8 : 0 < v0_7_8 := by
    have hs := h 0 7 8 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 7 8)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_12 : ℝ := -area (p 0) (p 8) (p 12)
  have hv0_8_12 : 0 < v0_8_12 := by
    have hs := h 0 8 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 0 8 12)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 0 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_4 : ℝ := area (p 2) (p 3) (p 4)
  have hv2_3_4 : 0 < v2_3_4 := by
    have hs := h 2 3 4 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 3 4)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 3 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_6 : ℝ := -area (p 2) (p 3) (p 6)
  have hv2_3_6 : 0 < v2_3_6 := by
    have hs := h 2 3 6 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 3 6)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_11 : ℝ := area (p 2) (p 3) (p 11)
  have hv2_3_11 : 0 < v2_3_11 := by
    have hs := h 2 3 11 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 3 11)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 3 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_12 : ℝ := area (p 2) (p 4) (p 12)
  have hv2_4_12 : 0 < v2_4_12 := by
    have hs := h 2 4 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 4 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_7 : ℝ := area (p 2) (p 6) (p 7)
  have hv2_6_7 : 0 < v2_6_7 := by
    have hs := h 2 6 7 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 6 7)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_9 : ℝ := area (p 2) (p 6) (p 9)
  have hv2_6_9 : 0 < v2_6_9 := by
    have hs := h 2 6 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 6 9)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_11 : ℝ := area (p 2) (p 6) (p 11)
  have hv2_6_11 : 0 < v2_6_11 := by
    have hs := h 2 6 11 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 6 11)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 6 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_9 : ℝ := area (p 2) (p 7) (p 9)
  have hv2_7_9 : 0 < v2_7_9 := by
    have hs := h 2 7 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 7 9)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_11 : ℝ := area (p 2) (p 7) (p 11)
  have hv2_7_11 : 0 < v2_7_11 := by
    have hs := h 2 7 11 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 7 11)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_11 : ℝ := area (p 2) (p 9) (p 11)
  have hv2_9_11 : 0 < v2_9_11 := by
    have hs := h 2 9 11 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 9 11)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 9 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_11_12 : ℝ := area (p 2) (p 11) (p 12)
  have hv2_11_12 : 0 < v2_11_12 := by
    have hs := h 2 11 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 2 11 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 2 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_12 : ℝ := area (p 3) (p 4) (p 12)
  have hv3_4_12 : 0 < v3_4_12 := by
    have hs := h 3 4 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 3 4 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 3 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_11 : ℝ := -area (p 3) (p 7) (p 11)
  have hv3_7_11 : 0 < v3_7_11 := by
    have hs := h 3 7 11 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 3 7 11)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 3 7 11) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_11_12 : ℝ := area (p 3) (p 11) (p 12)
  have hv3_11_12 : 0 < v3_11_12 := by
    have hs := h 3 11 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 3 11 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 3 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_8 : ℝ := area (p 4) (p 7) (p 8)
  have hv4_7_8 : 0 < v4_7_8 := by
    have hs := h 4 7 8 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 4 7 8)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 4 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_12 : ℝ := area (p 4) (p 7) (p 12)
  have hv4_7_12 : 0 < v4_7_12 := by
    have hs := h 4 7 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 4 7 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 4 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_12 : ℝ := area (p 4) (p 8) (p 12)
  have hv4_8_12 : 0 < v4_8_12 := by
    have hs := h 4 8 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 4 8 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 4 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_11_12 : ℝ := area (p 4) (p 11) (p 12)
  have hv4_11_12 : 0 < v4_11_12 := by
    have hs := h 4 11 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 4 11 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 4 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_8 : ℝ := -area (p 6) (p 7) (p 8)
  have hv6_7_8 : 0 < v6_7_8 := by
    have hs := h 6 7 8 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 6 7 8)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 6 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_9 : ℝ := area (p 6) (p 7) (p 9)
  have hv6_7_9 : 0 < v6_7_9 := by
    have hs := h 6 7 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 6 7 9)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 6 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_8_9 : ℝ := area (p 6) (p 8) (p 9)
  have hv6_8_9 : 0 < v6_8_9 := by
    have hs := h 6 8 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 6 8 9)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 6 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_9 : ℝ := area (p 7) (p 8) (p 9)
  have hv7_8_9 : 0 < v7_8_9 := by
    have hs := h 7 8 9 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 7 8 9)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 7 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_11_12 : ℝ := area (p 7) (p 11) (p 12)
  have hv7_11_12 : 0 < v7_11_12 := by
    have hs := h 7 11 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 7 11 12)) = true := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 7 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_11_12 : ℝ := -area (p 8) (p 11) (p 12)
  have hv8_11_12 : 0 < v8_11_12 := by
    have hs := h 8 11 12 (by decide) (by decide)
    have bit : (signature_570_3.testBit (285-lexRank 8 11 12)) = false := by decide
    change 0 < (if signature_570_3.testBit (285-lexRank 8 11 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_2_4 * v0_6_8 ∧ v0_2_4 * v0_6_8 < v0_2_6 * v0_4_8 := by
    have ident : v0_2_6 * v0_4_8 = v0_2_4 * v0_6_8 + v0_2_8 * v0_4_6 := by
      dsimp only [v0_2_4, v0_2_6, v0_2_8, v0_4_6, v0_4_8, v0_6_8, area]
      ring
    refine ⟨mul_pos hv0_2_4 hv0_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_8 hv0_4_6)
  have row1 : 0 < v0_2_3 * v2_4_12 ∧ v0_2_3 * v2_4_12 < v0_2_4 * v2_3_12 := by
    have ident : v0_2_4 * v2_3_12 = v0_2_3 * v2_4_12 + v0_2_12 * v2_3_4 := by
      dsimp only [v0_2_3, v0_2_4, v0_2_12, v2_3_4, v2_3_12, v2_4_12, area]
      ring
    refine ⟨mul_pos hv0_2_3 hv2_4_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_3_4)
  have row2 : 0 < v0_2_6 * v2_3_11 ∧ v0_2_6 * v2_3_11 < v0_2_3 * v2_6_11 := by
    have ident : v0_2_3 * v2_6_11 = v0_2_6 * v2_3_11 + v0_2_11 * v2_3_6 := by
      dsimp only [v0_2_3, v0_2_6, v0_2_11, v2_3_6, v2_3_11, v2_6_11, area]
      ring
    refine ⟨mul_pos hv0_2_6 hv2_3_11, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_11 hv2_3_6)
  have row3 : 0 < v2_6_11 * v2_7_9 ∧ v2_6_11 * v2_7_9 < v2_6_9 * v2_7_11 := by
    have ident : v2_6_9 * v2_7_11 = v2_6_11 * v2_7_9 + v2_6_7 * v2_9_11 := by
      dsimp only [v2_6_7, v2_6_9, v2_6_11, v2_7_9, v2_7_11, v2_9_11, area]
      ring
    refine ⟨mul_pos hv2_6_11 hv2_7_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_6_7 hv2_9_11)
  have row4 : 0 < v0_4_8 * v7_8_12 ∧ v0_4_8 * v7_8_12 < v0_7_8 * v4_8_12 := by
    have ident : v0_7_8 * v4_8_12 = v0_4_8 * v7_8_12 + v0_8_12 * v4_7_8 := by
      dsimp only [v0_4_8, v0_7_8, v0_8_12, v4_7_8, v4_8_12, v7_8_12, area]
      ring
    refine ⟨mul_pos hv0_4_8 hv7_8_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_12 hv4_7_8)
  have row5 : 0 < v0_7_8 * v6_8_9 ∧ v0_7_8 * v6_8_9 < v0_6_8 * v7_8_9 := by
    have ident : v0_6_8 * v7_8_9 = v0_7_8 * v6_8_9 + v0_8_9 * v6_7_8 := by
      dsimp only [v0_6_8, v0_7_8, v0_8_9, v6_7_8, v6_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv0_7_8 hv6_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_9 hv6_7_8)
  have row6 : 0 < v2_6_9 * v7_8_9 ∧ v2_6_9 * v7_8_9 < v2_7_9 * v6_8_9 := by
    have ident : v2_7_9 * v6_8_9 = v2_6_9 * v7_8_9 + v2_8_9 * v6_7_9 := by
      dsimp only [v2_6_9, v2_7_9, v2_8_9, v6_7_9, v6_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv2_6_9 hv7_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_8_9 hv6_7_9)
  have row7 : 0 < v2_7_11 * v3_11_12 ∧ v2_7_11 * v3_11_12 < v2_3_11 * v7_11_12 := by
    have ident : v2_3_11 * v7_11_12 = v2_7_11 * v3_11_12 + v2_11_12 * v3_7_11 := by
      dsimp only [v2_3_11, v2_7_11, v2_11_12, v3_7_11, v3_11_12, v7_11_12, area]
      ring
    refine ⟨mul_pos hv2_7_11 hv3_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_11_12 hv3_7_11)
  have row8 : 0 < v2_3_12 * v4_11_12 ∧ v2_3_12 * v4_11_12 < v2_4_12 * v3_11_12 := by
    have ident : v2_4_12 * v3_11_12 = v2_3_12 * v4_11_12 + v2_11_12 * v3_4_12 := by
      dsimp only [v2_3_12, v2_4_12, v2_11_12, v3_4_12, v3_11_12, v4_11_12, area]
      ring
    refine ⟨mul_pos hv2_3_12 hv4_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_11_12 hv3_4_12)
  have row9 : 0 < v4_8_12 * v7_11_12 ∧ v4_8_12 * v7_11_12 < v4_11_12 * v7_8_12 := by
    have ident : v4_11_12 * v7_8_12 = v4_8_12 * v7_11_12 + v4_7_12 * v8_11_12 := by
      dsimp only [v4_7_12, v4_8_12, v4_11_12, v7_8_12, v7_11_12, v8_11_12, area]
      ring
    refine ⟨mul_pos hv4_8_12 hv7_11_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_7_12 hv8_11_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) (merge row8 row9))
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_570_3

def signature_570_4 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000100001111100101111000011110111111111111011111111111111100111111000011110111111111111111111111111111000010110111111111111010111111011111011111111111111111111100111111111101000100000000001000100000000011110001110001001110

theorem no_realization_570_4 (p : Fin 13 → ℝ × ℝ) : ¬ Realizes signature_570_4 p := by
  intro h
  let v0_2_3 : ℝ := -area (p 0) (p 2) (p 3)
  have hv0_2_3 : 0 < v0_2_3 := by
    have hs := h 0 2 3 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 2 3)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 2 3) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_4 : ℝ := -area (p 0) (p 2) (p 4)
  have hv0_2_4 : 0 < v0_2_4 := by
    have hs := h 0 2 4 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 2 4)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_8 : ℝ := -area (p 0) (p 2) (p 8)
  have hv0_2_8 : 0 < v0_2_8 := by
    have hs := h 0 2 8 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 2 8)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 2 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_10 : ℝ := -area (p 0) (p 2) (p 10)
  have hv0_2_10 : 0 < v0_2_10 := by
    have hs := h 0 2 10 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 2 10)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 2 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_6 : ℝ := -area (p 0) (p 4) (p 6)
  have hv0_4_6 : 0 < v0_4_6 := by
    have hs := h 0 4 6 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 4 6)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_8 : ℝ := -area (p 0) (p 6) (p 8)
  have hv0_6_8 : 0 < v0_6_8 := by
    have hs := h 0 6 8 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 6 8)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_8 : ℝ := -area (p 0) (p 7) (p 8)
  have hv0_7_8 : 0 < v0_7_8 := by
    have hs := h 0 7 8 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 7 8)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_12 : ℝ := -area (p 0) (p 8) (p 12)
  have hv0_8_12 : 0 < v0_8_12 := by
    have hs := h 0 8 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 0 8 12)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 0 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_4 : ℝ := area (p 2) (p 3) (p 4)
  have hv2_3_4 : 0 < v2_3_4 := by
    have hs := h 2 3 4 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 3 4)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 3 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_6 : ℝ := -area (p 2) (p 3) (p 6)
  have hv2_3_6 : 0 < v2_3_6 := by
    have hs := h 2 3 6 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 3 6)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_10 : ℝ := area (p 2) (p 3) (p 10)
  have hv2_3_10 : 0 < v2_3_10 := by
    have hs := h 2 3 10 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 3 10)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 3 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_12 : ℝ := area (p 2) (p 4) (p 12)
  have hv2_4_12 : 0 < v2_4_12 := by
    have hs := h 2 4 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 4 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_7 : ℝ := area (p 2) (p 6) (p 7)
  have hv2_6_7 : 0 < v2_6_7 := by
    have hs := h 2 6 7 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 6 7)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_9 : ℝ := area (p 2) (p 6) (p 9)
  have hv2_6_9 : 0 < v2_6_9 := by
    have hs := h 2 6 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 6 9)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_10 : ℝ := area (p 2) (p 6) (p 10)
  have hv2_6_10 : 0 < v2_6_10 := by
    have hs := h 2 6 10 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 6 10)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_9 : ℝ := area (p 2) (p 7) (p 9)
  have hv2_7_9 : 0 < v2_7_9 := by
    have hs := h 2 7 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 7 9)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_10 : ℝ := area (p 2) (p 7) (p 10)
  have hv2_7_10 : 0 < v2_7_10 := by
    have hs := h 2 7 10 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 7 10)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_12 : ℝ := area (p 2) (p 10) (p 12)
  have hv2_10_12 : 0 < v2_10_12 := by
    have hs := h 2 10 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 2 10 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 2 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_12 : ℝ := area (p 3) (p 4) (p 12)
  have hv3_4_12 : 0 < v3_4_12 := by
    have hs := h 3 4 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 3 4 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 3 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_10 : ℝ := -area (p 3) (p 7) (p 10)
  have hv3_7_10 : 0 < v3_7_10 := by
    have hs := h 3 7 10 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 3 7 10)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 3 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_12 : ℝ := area (p 3) (p 10) (p 12)
  have hv3_10_12 : 0 < v3_10_12 := by
    have hs := h 3 10 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 3 10 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 3 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_8 : ℝ := area (p 4) (p 7) (p 8)
  have hv4_7_8 : 0 < v4_7_8 := by
    have hs := h 4 7 8 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 4 7 8)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 4 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_12 : ℝ := area (p 4) (p 7) (p 12)
  have hv4_7_12 : 0 < v4_7_12 := by
    have hs := h 4 7 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 4 7 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 4 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_12 : ℝ := area (p 4) (p 8) (p 12)
  have hv4_8_12 : 0 < v4_8_12 := by
    have hs := h 4 8 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 4 8 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 4 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_12 : ℝ := area (p 4) (p 10) (p 12)
  have hv4_10_12 : 0 < v4_10_12 := by
    have hs := h 4 10 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 4 10 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 4 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_8 : ℝ := -area (p 6) (p 7) (p 8)
  have hv6_7_8 : 0 < v6_7_8 := by
    have hs := h 6 7 8 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 6 7 8)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 6 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_9 : ℝ := area (p 6) (p 7) (p 9)
  have hv6_7_9 : 0 < v6_7_9 := by
    have hs := h 6 7 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 6 7 9)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 6 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_8_9 : ℝ := area (p 6) (p 8) (p 9)
  have hv6_8_9 : 0 < v6_8_9 := by
    have hs := h 6 8 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 6 8 9)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 6 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_9 : ℝ := area (p 7) (p 8) (p 9)
  have hv7_8_9 : 0 < v7_8_9 := by
    have hs := h 7 8 9 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 7 8 9)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 7 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_12 : ℝ := area (p 7) (p 10) (p 12)
  have hv7_10_12 : 0 < v7_10_12 := by
    have hs := h 7 10 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 7 10 12)) = true := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 7 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_12 : ℝ := -area (p 8) (p 10) (p 12)
  have hv8_10_12 : 0 < v8_10_12 := by
    have hs := h 8 10 12 (by decide) (by decide)
    have bit : (signature_570_4.testBit (285-lexRank 8 10 12)) = false := by decide
    change 0 < (if signature_570_4.testBit (285-lexRank 8 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_2_4 * v0_6_8 ∧ v0_2_4 * v0_6_8 < v0_2_6 * v0_4_8 := by
    have ident : v0_2_6 * v0_4_8 = v0_2_4 * v0_6_8 + v0_2_8 * v0_4_6 := by
      dsimp only [v0_2_4, v0_2_6, v0_2_8, v0_4_6, v0_4_8, v0_6_8, area]
      ring
    refine ⟨mul_pos hv0_2_4 hv0_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_8 hv0_4_6)
  have row1 : 0 < v0_2_3 * v2_4_12 ∧ v0_2_3 * v2_4_12 < v0_2_4 * v2_3_12 := by
    have ident : v0_2_4 * v2_3_12 = v0_2_3 * v2_4_12 + v0_2_12 * v2_3_4 := by
      dsimp only [v0_2_3, v0_2_4, v0_2_12, v2_3_4, v2_3_12, v2_4_12, area]
      ring
    refine ⟨mul_pos hv0_2_3 hv2_4_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_3_4)
  have row2 : 0 < v0_2_6 * v2_3_10 ∧ v0_2_6 * v2_3_10 < v0_2_3 * v2_6_10 := by
    have ident : v0_2_3 * v2_6_10 = v0_2_6 * v2_3_10 + v0_2_10 * v2_3_6 := by
      dsimp only [v0_2_3, v0_2_6, v0_2_10, v2_3_6, v2_3_10, v2_6_10, area]
      ring
    refine ⟨mul_pos hv0_2_6 hv2_3_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_10 hv2_3_6)
  have row3 : 0 < v2_6_10 * v2_7_9 ∧ v2_6_10 * v2_7_9 < v2_6_9 * v2_7_10 := by
    have ident : v2_6_9 * v2_7_10 = v2_6_10 * v2_7_9 + v2_6_7 * v2_9_10 := by
      dsimp only [v2_6_7, v2_6_9, v2_6_10, v2_7_9, v2_7_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_6_10 hv2_7_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_6_7 hv2_9_10)
  have row4 : 0 < v0_4_8 * v7_8_12 ∧ v0_4_8 * v7_8_12 < v0_7_8 * v4_8_12 := by
    have ident : v0_7_8 * v4_8_12 = v0_4_8 * v7_8_12 + v0_8_12 * v4_7_8 := by
      dsimp only [v0_4_8, v0_7_8, v0_8_12, v4_7_8, v4_8_12, v7_8_12, area]
      ring
    refine ⟨mul_pos hv0_4_8 hv7_8_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_12 hv4_7_8)
  have row5 : 0 < v0_7_8 * v6_8_9 ∧ v0_7_8 * v6_8_9 < v0_6_8 * v7_8_9 := by
    have ident : v0_6_8 * v7_8_9 = v0_7_8 * v6_8_9 + v0_8_9 * v6_7_8 := by
      dsimp only [v0_6_8, v0_7_8, v0_8_9, v6_7_8, v6_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv0_7_8 hv6_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_9 hv6_7_8)
  have row6 : 0 < v2_6_9 * v7_8_9 ∧ v2_6_9 * v7_8_9 < v2_7_9 * v6_8_9 := by
    have ident : v2_7_9 * v6_8_9 = v2_6_9 * v7_8_9 + v2_8_9 * v6_7_9 := by
      dsimp only [v2_6_9, v2_7_9, v2_8_9, v6_7_9, v6_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv2_6_9 hv7_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_8_9 hv6_7_9)
  have row7 : 0 < v2_7_10 * v3_10_12 ∧ v2_7_10 * v3_10_12 < v2_3_10 * v7_10_12 := by
    have ident : v2_3_10 * v7_10_12 = v2_7_10 * v3_10_12 + v2_10_12 * v3_7_10 := by
      dsimp only [v2_3_10, v2_7_10, v2_10_12, v3_7_10, v3_10_12, v7_10_12, area]
      ring
    refine ⟨mul_pos hv2_7_10 hv3_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_12 hv3_7_10)
  have row8 : 0 < v2_3_12 * v4_10_12 ∧ v2_3_12 * v4_10_12 < v2_4_12 * v3_10_12 := by
    have ident : v2_4_12 * v3_10_12 = v2_3_12 * v4_10_12 + v2_10_12 * v3_4_12 := by
      dsimp only [v2_3_12, v2_4_12, v2_10_12, v3_4_12, v3_10_12, v4_10_12, area]
      ring
    refine ⟨mul_pos hv2_3_12 hv4_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_12 hv3_4_12)
  have row9 : 0 < v4_8_12 * v7_10_12 ∧ v4_8_12 * v7_10_12 < v4_10_12 * v7_8_12 := by
    have ident : v4_10_12 * v7_8_12 = v4_8_12 * v7_10_12 + v4_7_12 * v8_10_12 := by
      dsimp only [v4_7_12, v4_8_12, v4_10_12, v7_8_12, v7_10_12, v8_10_12, area]
      ring
    refine ⟨mul_pos hv4_8_12 hv7_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_7_12 hv8_10_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) (merge row8 row9))
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_570_4

def signature_570_5 : ℕ := 0b0000000000000000000000000000000000000000000000000000000000000000000100001111100101111000011110111111111111011111111111111100111111000011110111111111111111111111111111000010110111111111111010111111011111011111111111111111111100111111111101000110000000001000100000000011110001110000001110

theorem no_realization_570_5 (p : Fin 13 → ℝ × ℝ) : ¬ Realizes signature_570_5 p := by
  intro h
  let v0_2_3 : ℝ := -area (p 0) (p 2) (p 3)
  have hv0_2_3 : 0 < v0_2_3 := by
    have hs := h 0 2 3 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 2 3)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 2 3) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_4 : ℝ := -area (p 0) (p 2) (p 4)
  have hv0_2_4 : 0 < v0_2_4 := by
    have hs := h 0 2 4 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 2 4)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 2 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_6 : ℝ := -area (p 0) (p 2) (p 6)
  have hv0_2_6 : 0 < v0_2_6 := by
    have hs := h 0 2 6 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 2 6)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 2 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_8 : ℝ := -area (p 0) (p 2) (p 8)
  have hv0_2_8 : 0 < v0_2_8 := by
    have hs := h 0 2 8 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 2 8)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 2 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_10 : ℝ := -area (p 0) (p 2) (p 10)
  have hv0_2_10 : 0 < v0_2_10 := by
    have hs := h 0 2 10 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 2 10)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 2 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_2_12 : ℝ := -area (p 0) (p 2) (p 12)
  have hv0_2_12 : 0 < v0_2_12 := by
    have hs := h 0 2 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 2 12)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 2 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_6 : ℝ := -area (p 0) (p 4) (p 6)
  have hv0_4_6 : 0 < v0_4_6 := by
    have hs := h 0 4 6 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 4 6)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 4 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_4_8 : ℝ := -area (p 0) (p 4) (p 8)
  have hv0_4_8 : 0 < v0_4_8 := by
    have hs := h 0 4 8 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 4 8)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 4 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_6_8 : ℝ := -area (p 0) (p 6) (p 8)
  have hv0_6_8 : 0 < v0_6_8 := by
    have hs := h 0 6 8 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 6 8)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 6 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_7_8 : ℝ := -area (p 0) (p 7) (p 8)
  have hv0_7_8 : 0 < v0_7_8 := by
    have hs := h 0 7 8 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 7 8)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_9 : ℝ := -area (p 0) (p 8) (p 9)
  have hv0_8_9 : 0 < v0_8_9 := by
    have hs := h 0 8 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 8 9)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v0_8_12 : ℝ := -area (p 0) (p 8) (p 12)
  have hv0_8_12 : 0 < v0_8_12 := by
    have hs := h 0 8 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 0 8 12)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 0 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_4 : ℝ := area (p 2) (p 3) (p 4)
  have hv2_3_4 : 0 < v2_3_4 := by
    have hs := h 2 3 4 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 3 4)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 3 4) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_6 : ℝ := -area (p 2) (p 3) (p 6)
  have hv2_3_6 : 0 < v2_3_6 := by
    have hs := h 2 3 6 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 3 6)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 3 6) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_10 : ℝ := area (p 2) (p 3) (p 10)
  have hv2_3_10 : 0 < v2_3_10 := by
    have hs := h 2 3 10 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 3 10)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 3 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_3_12 : ℝ := area (p 2) (p 3) (p 12)
  have hv2_3_12 : 0 < v2_3_12 := by
    have hs := h 2 3 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 3 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 3 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_4_12 : ℝ := area (p 2) (p 4) (p 12)
  have hv2_4_12 : 0 < v2_4_12 := by
    have hs := h 2 4 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 4 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_7 : ℝ := area (p 2) (p 6) (p 7)
  have hv2_6_7 : 0 < v2_6_7 := by
    have hs := h 2 6 7 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 6 7)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 6 7) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_9 : ℝ := area (p 2) (p 6) (p 9)
  have hv2_6_9 : 0 < v2_6_9 := by
    have hs := h 2 6 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 6 9)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 6 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_6_10 : ℝ := area (p 2) (p 6) (p 10)
  have hv2_6_10 : 0 < v2_6_10 := by
    have hs := h 2 6 10 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 6 10)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 6 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_9 : ℝ := area (p 2) (p 7) (p 9)
  have hv2_7_9 : 0 < v2_7_9 := by
    have hs := h 2 7 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 7 9)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_7_10 : ℝ := area (p 2) (p 7) (p 10)
  have hv2_7_10 : 0 < v2_7_10 := by
    have hs := h 2 7 10 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 7 10)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_8_9 : ℝ := area (p 2) (p 8) (p 9)
  have hv2_8_9 : 0 < v2_8_9 := by
    have hs := h 2 8 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 8 9)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_9_10 : ℝ := area (p 2) (p 9) (p 10)
  have hv2_9_10 : 0 < v2_9_10 := by
    have hs := h 2 9 10 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 9 10)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 9 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v2_10_12 : ℝ := area (p 2) (p 10) (p 12)
  have hv2_10_12 : 0 < v2_10_12 := by
    have hs := h 2 10 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 2 10 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 2 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_4_12 : ℝ := area (p 3) (p 4) (p 12)
  have hv3_4_12 : 0 < v3_4_12 := by
    have hs := h 3 4 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 3 4 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 3 4 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_7_10 : ℝ := -area (p 3) (p 7) (p 10)
  have hv3_7_10 : 0 < v3_7_10 := by
    have hs := h 3 7 10 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 3 7 10)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 3 7 10) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v3_10_12 : ℝ := area (p 3) (p 10) (p 12)
  have hv3_10_12 : 0 < v3_10_12 := by
    have hs := h 3 10 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 3 10 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 3 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_8 : ℝ := area (p 4) (p 7) (p 8)
  have hv4_7_8 : 0 < v4_7_8 := by
    have hs := h 4 7 8 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 4 7 8)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 4 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_7_12 : ℝ := area (p 4) (p 7) (p 12)
  have hv4_7_12 : 0 < v4_7_12 := by
    have hs := h 4 7 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 4 7 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 4 7 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_8_12 : ℝ := area (p 4) (p 8) (p 12)
  have hv4_8_12 : 0 < v4_8_12 := by
    have hs := h 4 8 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 4 8 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 4 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v4_10_12 : ℝ := area (p 4) (p 10) (p 12)
  have hv4_10_12 : 0 < v4_10_12 := by
    have hs := h 4 10 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 4 10 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 4 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_8 : ℝ := -area (p 6) (p 7) (p 8)
  have hv6_7_8 : 0 < v6_7_8 := by
    have hs := h 6 7 8 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 6 7 8)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 6 7 8) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_7_9 : ℝ := area (p 6) (p 7) (p 9)
  have hv6_7_9 : 0 < v6_7_9 := by
    have hs := h 6 7 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 6 7 9)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 6 7 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v6_8_9 : ℝ := area (p 6) (p 8) (p 9)
  have hv6_8_9 : 0 < v6_8_9 := by
    have hs := h 6 8 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 6 8 9)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 6 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_9 : ℝ := area (p 7) (p 8) (p 9)
  have hv7_8_9 : 0 < v7_8_9 := by
    have hs := h 7 8 9 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 7 8 9)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 7 8 9) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_8_12 : ℝ := area (p 7) (p 8) (p 12)
  have hv7_8_12 : 0 < v7_8_12 := by
    have hs := h 7 8 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 7 8 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 7 8 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v7_10_12 : ℝ := area (p 7) (p 10) (p 12)
  have hv7_10_12 : 0 < v7_10_12 := by
    have hs := h 7 10 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 7 10 12)) = true := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 7 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  let v8_10_12 : ℝ := -area (p 8) (p 10) (p 12)
  have hv8_10_12 : 0 < v8_10_12 := by
    have hs := h 8 10 12 (by decide) (by decide)
    have bit : (signature_570_5.testBit (285-lexRank 8 10 12)) = false := by decide
    change 0 < (if signature_570_5.testBit (285-lexRank 8 10 12) then _ else _) at hs
    simpa only [bit, Bool.false_eq_true, if_false, if_true] using hs
  have row0 : 0 < v0_2_4 * v0_6_8 ∧ v0_2_4 * v0_6_8 < v0_2_6 * v0_4_8 := by
    have ident : v0_2_6 * v0_4_8 = v0_2_4 * v0_6_8 + v0_2_8 * v0_4_6 := by
      dsimp only [v0_2_4, v0_2_6, v0_2_8, v0_4_6, v0_4_8, v0_6_8, area]
      ring
    refine ⟨mul_pos hv0_2_4 hv0_6_8, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_8 hv0_4_6)
  have row1 : 0 < v0_2_3 * v2_4_12 ∧ v0_2_3 * v2_4_12 < v0_2_4 * v2_3_12 := by
    have ident : v0_2_4 * v2_3_12 = v0_2_3 * v2_4_12 + v0_2_12 * v2_3_4 := by
      dsimp only [v0_2_3, v0_2_4, v0_2_12, v2_3_4, v2_3_12, v2_4_12, area]
      ring
    refine ⟨mul_pos hv0_2_3 hv2_4_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_12 hv2_3_4)
  have row2 : 0 < v0_2_6 * v2_3_10 ∧ v0_2_6 * v2_3_10 < v0_2_3 * v2_6_10 := by
    have ident : v0_2_3 * v2_6_10 = v0_2_6 * v2_3_10 + v0_2_10 * v2_3_6 := by
      dsimp only [v0_2_3, v0_2_6, v0_2_10, v2_3_6, v2_3_10, v2_6_10, area]
      ring
    refine ⟨mul_pos hv0_2_6 hv2_3_10, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_2_10 hv2_3_6)
  have row3 : 0 < v2_6_10 * v2_7_9 ∧ v2_6_10 * v2_7_9 < v2_6_9 * v2_7_10 := by
    have ident : v2_6_9 * v2_7_10 = v2_6_10 * v2_7_9 + v2_6_7 * v2_9_10 := by
      dsimp only [v2_6_7, v2_6_9, v2_6_10, v2_7_9, v2_7_10, v2_9_10, area]
      ring
    refine ⟨mul_pos hv2_6_10 hv2_7_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_6_7 hv2_9_10)
  have row4 : 0 < v0_4_8 * v7_8_12 ∧ v0_4_8 * v7_8_12 < v0_7_8 * v4_8_12 := by
    have ident : v0_7_8 * v4_8_12 = v0_4_8 * v7_8_12 + v0_8_12 * v4_7_8 := by
      dsimp only [v0_4_8, v0_7_8, v0_8_12, v4_7_8, v4_8_12, v7_8_12, area]
      ring
    refine ⟨mul_pos hv0_4_8 hv7_8_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_12 hv4_7_8)
  have row5 : 0 < v0_7_8 * v6_8_9 ∧ v0_7_8 * v6_8_9 < v0_6_8 * v7_8_9 := by
    have ident : v0_6_8 * v7_8_9 = v0_7_8 * v6_8_9 + v0_8_9 * v6_7_8 := by
      dsimp only [v0_6_8, v0_7_8, v0_8_9, v6_7_8, v6_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv0_7_8 hv6_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv0_8_9 hv6_7_8)
  have row6 : 0 < v2_6_9 * v7_8_9 ∧ v2_6_9 * v7_8_9 < v2_7_9 * v6_8_9 := by
    have ident : v2_7_9 * v6_8_9 = v2_6_9 * v7_8_9 + v2_8_9 * v6_7_9 := by
      dsimp only [v2_6_9, v2_7_9, v2_8_9, v6_7_9, v6_8_9, v7_8_9, area]
      ring
    refine ⟨mul_pos hv2_6_9 hv7_8_9, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_8_9 hv6_7_9)
  have row7 : 0 < v2_7_10 * v3_10_12 ∧ v2_7_10 * v3_10_12 < v2_3_10 * v7_10_12 := by
    have ident : v2_3_10 * v7_10_12 = v2_7_10 * v3_10_12 + v2_10_12 * v3_7_10 := by
      dsimp only [v2_3_10, v2_7_10, v2_10_12, v3_7_10, v3_10_12, v7_10_12, area]
      ring
    refine ⟨mul_pos hv2_7_10 hv3_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_12 hv3_7_10)
  have row8 : 0 < v2_3_12 * v4_10_12 ∧ v2_3_12 * v4_10_12 < v2_4_12 * v3_10_12 := by
    have ident : v2_4_12 * v3_10_12 = v2_3_12 * v4_10_12 + v2_10_12 * v3_4_12 := by
      dsimp only [v2_3_12, v2_4_12, v2_10_12, v3_4_12, v3_10_12, v4_10_12, area]
      ring
    refine ⟨mul_pos hv2_3_12 hv4_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv2_10_12 hv3_4_12)
  have row9 : 0 < v4_8_12 * v7_10_12 ∧ v4_8_12 * v7_10_12 < v4_10_12 * v7_8_12 := by
    have ident : v4_10_12 * v7_8_12 = v4_8_12 * v7_10_12 + v4_7_12 * v8_10_12 := by
      dsimp only [v4_7_12, v4_8_12, v4_10_12, v7_8_12, v7_10_12, v8_10_12, area]
      ring
    refine ⟨mul_pos hv4_8_12 hv7_10_12, ?_⟩
    rw [ident]
    exact lt_add_of_pos_right _ (mul_pos hv4_7_12 hv8_10_12)
  have strict := (merge (merge (merge (merge row0 row1) (merge row2 row3)) (merge (merge row4 row5) (merge row6 row7))) (merge row8 row9))
  exact (ne_of_lt strict.2) (by ac_rfl)

#print axioms no_realization_570_5
end ThirteenPointExclusions
