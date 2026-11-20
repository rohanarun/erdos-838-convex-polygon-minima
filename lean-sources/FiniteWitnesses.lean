import Lean

/-! Exact integer certificates for finite instances of Erdős problem 838.
A subset of planar points in general position is in convex position iff no
selected point lies inside point a triangle of three other selected points
(planar Carathéodory). The finite certificates below check this criterion
and check general position by signed determinants. -/

namespace FinitePolygonWitnesses

abbrev Pt := Int × Int

def det (point : Nat → Pt) (i j k : Nat) : Int :=
  let a := point i
  let b := point j
  let c := point k
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

def combinations {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, a :: as =>
      (combinations n as).map (a :: ·) ++ combinations (n + 1) as

def triples (n : Nat) := combinations 3 (List.range n)
def quads (n : Nat) := combinations 4 (List.range n)

def noncollinear (point : Nat → Pt) : List Nat → Bool
  | [a,b,c] => det point a b c != 0
  | _ => false

def inside (point : Nat → Pt) (p a b c : Nat) : Bool :=
  let u := det point a b p
  let v := det point b c p
  let w := det point c a p
  (u > 0 && v > 0 && w > 0) || (u < 0 && v < 0 && w < 0)

def concave (point : Nat → Pt) : List Nat → Bool
  | [a,b,c,d] => inside point a b c d || inside point b c d a ||
                    inside point c d a b || inside point d a b c
  | _ => false

def mask (vertices : List Nat) : Nat :=
  vertices.foldl (fun m i => m ||| (1 <<< i)) 0

def forbidden (point : Nat → Pt) (n : Nat) := ((quads n).filter (concave point)).map mask

/-- The k-th entry counts the size-k masks avoiding every concave quadruple. -/
def profile (n : Nat) (blocks : List Nat) : List Nat :=
  let valid := (List.range (2 ^ n)).filter (fun m =>
    blocks.all (fun q => (m &&& q) != q))
  let sizes := valid.map (fun m =>
    ((List.range n).filter (fun i => m.testBit i)).length)
  (List.range (n + 1)).map (fun k => sizes.count k)

def point10 : Nat → Pt
  | 0 => (0, 0)
  | 1 => (50, 40)
  | 2 => (34, 38)
  | 3 => (30, 39)
  | 4 => (13, 18)
  | 5 => (7, 12)
  | 6 => (18, 31)
  | 7 => (11, 41)
  | 8 => (11, 51)
  | 9 => (6, 69)
  | _ => (0, 0)

theorem general_position_10 :
    (triples 10).all (noncollinear point10) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profile_10 :
    profile 10 (forbidden point10 10) = [1, 10, 45, 120, 66, 3, 0, 0, 0, 0, 0] := by decide +kernel

theorem polygon_count_10 :
    ((profile 10 (forbidden point10 10)).drop 3).sum = 189 := by
  rw [profile_10]
  decide

#print axioms general_position_10
#print axioms polygon_count_10

def point11 : Nat → Pt
  | 0 => (4, 0)
  | 1 => (45, 30)
  | 2 => (9, 37)
  | 3 => (24, 26)
  | 4 => (12, 29)
  | 5 => (8, 19)
  | 6 => (30, 29)
  | 7 => (21, 23)
  | 8 => (5, 41)
  | 9 => (0, 49)
  | 10 => (7, 12)
  | _ => (0, 0)

theorem general_position_11 :
    (triples 11).all (noncollinear point11) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profile_11 :
    profile 11 (forbidden point11 11) = [1, 11, 55, 165, 108, 10, 0, 0, 0, 0, 0, 0] := by decide +kernel

theorem polygon_count_11 :
    ((profile 11 (forbidden point11 11)).drop 3).sum = 283 := by
  rw [profile_11]
  decide

#print axioms general_position_11
#print axioms polygon_count_11

def point12 : Nat → Pt
  | 0 => (0, 0)
  | 1 => (72, 12)
  | 2 => (26, 18)
  | 3 => (51, 24)
  | 4 => (12, 9)
  | 5 => (45, 28)
  | 6 => (34, 28)
  | 7 => (28, 30)
  | 8 => (24, 45)
  | 9 => (21, 66)
  | 10 => (22, 16)
  | 11 => (24, 50)
  | _ => (0, 0)

theorem general_position_12 :
    (triples 12).all (noncollinear point12) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem profile_12 :
    profile 12 (forbidden point12 12) = [1, 12, 66, 220, 165, 22, 1, 0, 0, 0, 0, 0, 0] := by decide +kernel

theorem polygon_count_12 :
    ((profile 12 (forbidden point12 12)).drop 3).sum = 408 := by
  rw [profile_12]
  decide

#print axioms general_position_12
#print axioms polygon_count_12

end FinitePolygonWitnesses
