import OrderedPartitions.ReciprocalEdgeLadderAssembly
import OrderedPartitions.ReciprocalEdgeOuterPrefix

/-! Transfer any finite prefix of the full zero ladder to true ordered-partition rows. -/

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Filter Metric OrderedPartitions.ReciprocalEdge
open scoped Topology

/-- Halfway between the last selected modulus (zero for the empty prefix) and the next. -/
def prefixRadius {j : ℕ} (L : Fin j → ℕ → ℝ) (r : Fin j) : ℕ → ℝ
  | 0 => L r 0 / 2
  | k+1 => (L r k + L r (k+1))/2

theorem ZeroLadder.limit_prefix {j : ℕ} {L : Fin j → ℕ → ℝ}
    (h : ZeroLadder j L) (r : Fin j) (k : ℕ) :
    LimitPrefix j r (prefixRadius L r k) (fun i : Fin k ↦ -L r i) := by
  have lt : prefixRadius L r k < L r k := by
    cases k with
    | zero => simpa [prefixRadius] using half_lt_self (h.positive r 0)
    | succ k =>
      simp only [prefixRadius]
      linarith only [h.increasing r (Nat.lt_succ_self k)]
  have pos : 0 < prefixRadius L r k := by
    cases k with
    | zero => exact half_pos (h.positive r 0)
    | succ k => exact half_pos (add_pos (h.positive r k) (h.positive r (k+1)))
  refine ⟨pos,fun _ _ hij ↦ neg_lt_neg (h.increasing r hij),?_,?_,?_,?_⟩
  · intro i
    refine ⟨neg_lt_neg ?_,neg_lt_zero.mpr (h.positive r i)⟩
    cases k with
    | zero => exact Fin.elim0 i
    | succ k =>
      simp only [prefixRadius]
      linarith only [(h.increasing r).monotone (Nat.le_of_lt_succ i.isLt),
        h.increasing r (Nat.lt_succ_self k)]
  · intro i
    simpa only [Complex.ofReal_neg] using (h.roots r _).mpr ⟨i,rfl⟩
  · intro i
    simpa only [Complex.ofReal_neg] using h.simple r i
  · intro w hw zero
    obtain ⟨n,rfl⟩ := (h.roots r w).mp zero
    have bound := mem_closedBall.mp hw
    rw [dist_zero_right, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (h.positive r n)] at bound
    have nk : n < k := by
      by_contra! rev
      exact (lt.trans_le ((h.increasing r).monotone rev)).not_ge bound
    exact ⟨⟨n,nk⟩, by simp⟩

/-- All residues simultaneously, with thresholds depending on the fixed prefix and accuracy. -/
theorem ZeroLadder.original_prefix {j : ℕ} (hj : 2 ≤ j) {L : Fin j → ℕ → ℝ}
    (h : ZeroLadder j L) (k : ℕ) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∀ r : Fin j, ∃ t : Fin k → ℝ,
      OriginalOuterPrefix j r d (prefixRadius L r k) ε (fun i : Fin k ↦ -L r i) t :=
  eventually_all.mpr fun r ↦ eventually_original_outer_prefix hj r.isLt (h.limit_prefix r k) positive

#print axioms ZeroLadder.limit_prefix
#print axioms ZeroLadder.original_prefix
end OrderedPartitions.ReciprocalSector
