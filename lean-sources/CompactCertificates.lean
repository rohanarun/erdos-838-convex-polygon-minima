import Lean

/-! Finite checks on the six orientation signatures retained by the deletion
enumerator and their short Grassmann–Plücker contradiction certificates. -/
namespace ConvexSubsets.CompactCertificates

open Lean Elab Term Meta

/-- The elaborator reads the expanded include_str literal and quotes plain
Boolean/natural data. It checks textual format only. The mathematics below
is checked by the kernel on those literals. -/
private meta def inputText (stx : Syntax) : TermElabM String := do
  let e ← elabTerm stx (some (mkConst ``String))
  let some text := getStringValue? (← whnf e) | throwError "expected included string"
  return text

elab "targetData% " input:term : term => do
  let text ← inputText input
  let mut result : List (List Bool) := []
  for line in (text.splitOn "\n").filter (·.startsWith "TARGET ") do
    let ["TARGET","166","20",s] := line.splitOn " " | throwError "invalid TARGET row"
    let some signs := s.toList.mapM (fun ch =>
      if ch == '0' then some false else if ch == '1' then some true else none)
      | throwError "invalid sign"
    result := signs :: result
  return toExpr result.reverse

elab "rowsData% " input:term : term => do
  let text ← inputText input
  let mut result : List (List Nat) := []
  for line in (text.splitOn "\n").filter (· != "") do
    let some row := (line.splitOn " ").mapM String.toNat? | throwError "invalid integer"
    result := row :: result
  return toExpr result.reverse

def targets : List (List Bool) := targetData% (include_str "deletion/signatures.txt")
def certificates : List (List (List Nat)) := [
  rowsData% (include_str "compact-0.txt"), rowsData% (include_str "compact-1.txt"),
  rowsData% (include_str "compact-2.txt"), rowsData% (include_str "compact-3.txt"),
  rowsData% (include_str "compact-4.txt"), rowsData% (include_str "compact-5.txt")]

/-- Number of earlier increasing triples in lexicographic order. First skip
all smaller initial labels, then all smaller middle labels, then the shorter
suffix of last labels. -/
def tripleRank (i j k : Nat) : Nat :=
  let choose3 := fun m : Nat => m * (m-1) * (m-2) / 6
  let choose2 := fun m : Nat => m * (m-1) / 2
  (220 - choose3 (12-i)) + (choose2 (11-i) - choose2 (12-j)) + (k-j-1)

def insertSorted (n : Nat) : List Nat → List Nat
  | [] => [n]
  | a :: tail => if n ≤ a then n :: a :: tail else a :: insertSorted n tail

def sorted (l : List Nat) := l.foldr insertSorted []

structure Bracket where
  idx : Nat
  positive : Bool

def lookup (bits : Array Bool) (x y z : Nat) : Option Bracket := do
  let [i,j,k] := sorted [x,y,z] | none
  guard (i < j && j < k && k < 12)
  let idx := tripleRank i j k
  let sign ← bits[idx]?
  let reverse := (decide (x > y) != decide (x > z)) != decide (y > z)
  return ⟨idx, sign != reverse⟩

abbrev Comparison := (Nat × Nat) × (Nat × Nat)

def parseComparison (bits : Array Bool) (row : List Nat) : Option Comparison := do
  let [a,b,c,d,e,dominant,smaller,1] := row | none
  guard (b < c && c < d && d < e)
  let bc ← lookup bits a b c
  let de ← lookup bits a d e
  let bd ← lookup bits a b d
  let ce ← lookup bits a c e
  let be ← lookup bits a b e
  let cd ← lookup bits a c d
  let products := #[(bc.idx,de.idx), (bd.idx,ce.idx), (be.idx,cd.idx)]
  -- Signed terms in [abc][ade] - [abd][ace] + [abe][acd].
  let signs := #[bc.positive == de.positive, bd.positive != ce.positive,
                 be.positive == cd.positive]
  let isolated ← signs[dominant]?
  guard ((List.range 3).all fun j => j == dominant || signs[j]! != isolated)
  guard (smaller != dominant)
  return (← products[dominant]?, ← products[smaller]?)

def checkTarget (bits : List Bool) (certificate : List (List Nat)) : Bool := Id.run do
  if bits.length != 220 then return false
  let some rows := certificate.mapM (parseComparison bits.toArray) | return false
  let lhs := rows.flatMap fun r => [r.1.1,r.1.2]
  let rhs := rows.flatMap fun r => [r.2.1,r.2.2]
  return !rows.isEmpty && sorted lhs == sorted rhs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every actual TARGET row, in output order, has a nonempty list of strict
comparisons with matching numerator and denominator bracket multisets. -/
theorem allSix :
    targets.length = 6 ∧ targets.Nodup ∧
    certificates.map List.length = [10,11,10,11,10,10] ∧
    (targets.zip certificates).all (fun p => checkTarget p.1 p.2) = true := by
  decide +kernel

/-- Independent finite check that the closed-form rank used in lookup
agrees, for every increasing triple, with the source lexicographic order. -/
theorem rankEnumeration :
    let ts := (List.range 12).flatMap fun i =>
      (List.range 12).flatMap fun j => (List.range 12).filterMap fun k =>
        if i < j && j < k then some (tripleRank i j k) else none
    ts = List.range 220 := by decide +kernel

#print axioms rankEnumeration
#print axioms allSix

end ConvexSubsets.CompactCertificates
