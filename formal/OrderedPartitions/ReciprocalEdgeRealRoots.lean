import OrderedPartitions.ReciprocalEdgeBinomial
import OrderedPartitions.ReciprocalEdgeEulerSections
import OrderedPartitions.ReciprocalEdgeSimple

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex Filter OrderedPartitions.ReciprocalEdge

theorem actual_chain {j : ℕ} (hj : 1≤j) {z : ℂ} (up : 0≤z.im)
    (i k : Fin j) (ik : i≤k) :
    Sector z (reciprocalLimit j i z) (reciprocalLimit j k z) := by
  apply limit_sectors hj
  apply Filter.Eventually.of_forall
  intro N
  cases j with
  | zero => omega
  | succ d => exact binomial_chain N up (by positivity : 0≤1/(N:ℝ)) i k ik

/-- Every negative real zero of the factorial multisections has nonzero derivative. -/
theorem section_simple {j : ℕ} (hj : 1≤j) (r : Fin j) {x : ℝ} (hx : x<0)
    (zero : reciprocalLimit j r x=0) : deriv (reciprocalLimit j r) x ≠ 0 := by
  cases j with
  | zero => omega
  | succ d =>
    apply section_simple_of_chain (fun _ hz i k ik ↦ actual_chain hj hz.le i k ik) r hx zero

/-- Two consecutively indexed sections have no common negative real zero. -/
theorem no_adjacent_zero {j r : ℕ} (lo : r+1<j) {x : ℝ} (hx : x<0)
    (zero : reciprocalLimit j (r+1) x=0) : reciprocalLimit j r x≠0 := by
  have hx' : (x:ℂ)≠0 := by exact_mod_cast hx.ne
  have jn : (j:ℂ)≠0 := by exact_mod_cast (by omega : j≠0)
  have der := section_simple (by omega : 1≤j) (⟨r+1,lo⟩ : Fin j) hx zero
  rw [previous_multisection (by omega : 1≤j), zero, mul_zero, zero_add]
  exact mul_ne_zero (mul_ne_zero jn hx') der

/-- The last and first sections cannot share a negative real zero. -/
theorem no_wrap_zero {j : ℕ} (hj : 1≤j) {x : ℝ} (hx : x<0)
    (zero : reciprocalLimit j 0 x=0) : reciprocalLimit j (j-1) x≠0 := by
  have jn : (j:ℂ)≠0 := by exact_mod_cast (by omega : j≠0)
  rw [last_multisection hj]
  exact mul_ne_zero jn (section_simple hj (⟨0,by omega⟩ : Fin j) hx zero)

#print axioms actual_chain
#print axioms section_simple
#print axioms no_adjacent_zero
#print axioms no_wrap_zero
end OrderedPartitions.ReciprocalSector
