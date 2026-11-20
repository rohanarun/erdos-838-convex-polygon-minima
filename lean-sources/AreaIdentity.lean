import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-! Signed doubled areas of actual planar points obey the three-term
Grassmann-Plücker identity used in the twelve-point exclusion. -/
namespace PolygonAreas

def bracket (a b c : ℝ × ℝ) : ℝ :=
  (b.1-a.1)*(c.2-a.2)-(c.1-a.1)*(b.2-a.2)

theorem area_relation (a b c d e : ℝ × ℝ) :
    bracket a b c * bracket a d e - bracket a b d * bracket a c e +
    bracket a b e * bracket a c d = 0 := by
  unfold bracket
  ring

theorem isolated_term_larger {x y z : ℝ} (rel : x+y+z=0)
    (signs : (0 < x ∧ y < 0 ∧ z < 0) ∨ (x < 0 ∧ 0 < y ∧ 0 < z)) :
    |y| < |x| := by
  rcases signs with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · rw [abs_of_pos hx, abs_of_neg hy]
    linarith
  · rw [abs_of_neg hx, abs_of_pos hy]
    linarith

#print axioms area_relation
#print axioms isolated_term_larger
end PolygonAreas
