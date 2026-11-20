import FiniteWitnesses

namespace FinitePolygonWitnesses

def point13 : Nat → Pt
  | 0 => (27, 29)
  | 1 => (131, 0)
  | 2 => (68, 45)
  | 3 => (103, 33)
  | 4 => (0, 20)
  | 5 => (79, 90)
  | 6 => (99, 39)
  | 7 => (123, 7)
  | 8 => (42, 31)
  | 9 => (90, 134)
  | 10 => (72, 78)
  | 11 => (72, 73)
  | 12 => (56, 31)
  | _ => (0, 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem general_position_13 :
    (triples 13).all (noncollinear point13) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profile_13 :
    profile 13 (forbidden point13 13) =
      [1, 13, 78, 286, 241, 41, 2, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

theorem polygon_count_13 :
    ((profile 13 (forbidden point13 13)).drop 3).sum = 570 := by
  rw [profile_13]
  decide

#print axioms general_position_13
#print axioms profile_13
#print axioms polygon_count_13

end FinitePolygonWitnesses
