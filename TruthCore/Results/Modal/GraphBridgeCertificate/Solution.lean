import TruthCore.Modal.GraphBridgeCertificate
import TruthCore.Results.Modal.GraphBridge.Solution

namespace TruthCore.Results.Modal.GraphBridgeCertificate
universe u v

/-- Assembly of the ten frozen reusable graph bridge facts, not new discovery. -/
theorem certificate : TruthCore.Modal.GraphBridgeCertificate.{u, v} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ F => GraphBridge.frame_roundtrip F
  · exact fun _ G => GraphBridge.digraph_roundtrip G
  · exact fun _ F a b => GraphBridge.adjacency_iff_access F a b
  · exact fun _ F a b => GraphBridge.arrow_iff_access F a b
  · exact fun _ F => GraphBridge.quiver_is_thin F
  · exact fun _ F a b => GraphBridge.reachable_iff_reflTransGen F a b
  · exact fun _ F hr ht a b => GraphBridge.reachable_iff_access F hr ht a b
  · exact fun _ _ F ht V φ a b hp hb => GraphBridge.box_along_paths F ht V φ a b hp hb
  · exact fun _ F ht he a b hab => GraphBridge.successor_cones F ht he a b hab
  · exact GraphBridge.nil_path_boundary

end TruthCore.Results.Modal.GraphBridgeCertificate
