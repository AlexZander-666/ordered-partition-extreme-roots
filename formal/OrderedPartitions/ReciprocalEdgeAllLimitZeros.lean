import OrderedPartitions.ReciprocalEdgeOscillation
import OrderedPartitions.ReciprocalEdgeLadderAssembly

/-! All limiting multisections have a single strictly interlaced ladder of simple zeros. -/
noncomputable section
namespace OrderedPartitions.ReciprocalSector

theorem all_limit_zeros {j : ℕ} (hj : 2 ≤ j) : ∃ L, ZeroLadder j L :=
  ladder_of_unbounded hj (ReciprocalEdge.unbounded_section_zeros hj)

#print axioms all_limit_zeros
end OrderedPartitions.ReciprocalSector
