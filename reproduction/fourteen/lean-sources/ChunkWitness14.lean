import ChunkWitnessBase
namespace FinitePolygonWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem profile_14 : profile 14 (forbidden point14 14) = [1,14,91,364,350,64,2,0,0,0,0,0,0,0,0] := by
  rw [bad14_eq]
  unfold profile
  change (List.range 15).map (fun k => (((List.range 16384).filter passes14).map (fun m => ((List.range 14).filter (fun i => m.testBit i)).length)).count k) = _
  rw [List.range_eq_range' (n := 16384), block128_0]
  decide +kernel
theorem polygon_count_14 : ((profile 14 (forbidden point14 14)).drop 3).sum = 780 := by rw [profile_14]; decide
#print axioms polygon_count_14
end FinitePolygonWitnesses
