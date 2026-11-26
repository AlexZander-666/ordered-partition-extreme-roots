import OrderedPartitions.ReciprocalEdgeBinomial
import OrderedPartitions.ReciprocalEdgeEulerSections

/-! Every complex zero of the limiting Mittag–Leffler multisections is real and negative. -/
noncomputable section
namespace OrderedPartitions.ReciprocalEdge

/-- Reality for the actual entire functions, uniformly in the choice of threshold and residue. -/
theorem all_section_zeros_negative {j : ℕ} (hj : 2≤j) (r : Fin j) {w : ℂ}
    (zero : reciprocalLimit j r w=0) : w.im=0 ∧ w.re<0 := by
  apply negative_zeros_of_sectors hj _ r zero
  intro z up i k ik
  cases j with
  | zero => omega
  | succ d =>
    apply limit_sectors (by omega) i k
    apply Filter.Eventually.of_forall
    intro N
    exact ReciprocalSector.binomial_chain N up.le (show 0≤1/(N:ℝ) by positivity) i k ik.le

#print axioms all_section_zeros_negative
end OrderedPartitions.ReciprocalEdge
