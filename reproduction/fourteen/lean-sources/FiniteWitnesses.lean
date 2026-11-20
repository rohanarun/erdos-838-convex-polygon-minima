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

end FinitePolygonWitnesses
