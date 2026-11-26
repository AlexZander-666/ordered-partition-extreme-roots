import OrderedPartitions.ReciprocalEdgeAllLimitZeros
import OrderedPartitions.ReciprocalEdgeLadderPrefix

/-! Canonical finite prefixes in the actual rank rows for every fixed threshold. -/

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Filter Set OrderedPartitions.ReciprocalEdge
open scoped Topology

private theorem prefix_mem {j r d k : ℕ} {ρ ε ε' : ℝ} {c t u : Fin k → ℝ}
    (ht : OriginalOuterPrefix j r d ρ ε c t) (hu : OriginalOuterPrefix j r d ρ ε' c u)
    (i : Fin k) : t i ∈ range u := by
  by_contra h
  have small := hu.remaining (t i) (ht.zero i) (fun a eq ↦
    h ⟨a,(Complex.ofReal_inj.mp eq).symm⟩)
  exact (ht.selected i).not_gt small

theorem original_prefix_unique {j r d k : ℕ} {ρ ε ε' : ℝ} {c t u : Fin k → ℝ}
    (ht : OriginalOuterPrefix j r d ρ ε c t) (hu : OriginalOuterPrefix j r d ρ ε' c u) :
    t = u := by
  apply (ht.ordered.range_inj hu.ordered).mp
  exact Set.Subset.antisymm (by rintro _ ⟨i,rfl⟩; exact prefix_mem ht hu i)
    (by rintro _ ⟨i,rfl⟩; exact prefix_mem hu ht i)

/-- One choice of actual rank roots works for every positive accuracy simultaneously. -/
theorem ZeroLadder.original_branches {j : ℕ} (hj : 2 ≤ j) {L : Fin j → ℕ → ℝ}
    (h : ZeroLadder j L) (k : ℕ) :
    ∃ t : ℕ → Fin j → Fin k → ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, ∀ r : Fin j,
      OriginalOuterPrefix j r d (prefixRadius L r k) ε (fun i : Fin k ↦ -L r i) (t d r) := by
  classical
  let P (d : ℕ) (r : Fin j) (ε : ℝ) (t : Fin k → ℝ) :=
    OriginalOuterPrefix j r d (prefixRadius L r k) ε (fun i : Fin k ↦ -L r i) t
  let t (d : ℕ) (r : Fin j) := if H : ∃ t, P d r 1 t then H.choose else fun _ ↦ 0
  refine ⟨t,fun ε ep ↦ ?_⟩
  filter_upwards [h.original_prefix hj k one_pos,h.original_prefix hj k ep] with d base approx
  intro r
  have base' : ∃ t, P d r 1 t := base r
  have fixed : P d r 1 (t d r) := by simp only [t,dif_pos base']; exact base'.choose_spec
  obtain ⟨u,hu⟩ := approx r
  exact original_prefix_unique fixed hu ▸ hu

/-- Uniform in the finitely many residue classes at a fixed threshold; the integer
at which the assertion begins may depend on the threshold, the prefix and the accuracy. -/
theorem all_original_branches {j : ℕ} (hj : 2 ≤ j) :
    ∃ L, ZeroLadder j L ∧ ∀ k : ℕ, ∃ t : ℕ → Fin j → Fin k → ℝ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, ∀ r : Fin j,
      OriginalOuterPrefix j r d (prefixRadius L r k) ε (fun i : Fin k ↦ -L r i) (t d r) := by
  obtain ⟨L,h⟩ := all_limit_zeros hj
  exact ⟨L,h,h.original_branches hj⟩

#print axioms original_prefix_unique
#print axioms all_original_branches
end OrderedPartitions.ReciprocalSector
