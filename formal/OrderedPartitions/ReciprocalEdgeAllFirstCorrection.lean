import OrderedPartitions.ReciprocalEdgeAllOriginalPrefix
import OrderedPartitions.ReciprocalEdgeFirstCorrectionRoot

/-! The first correction along the *indexed extreme roots* of the true rows. -/

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Filter OrderedPartitions.ReciprocalEdge
open scoped Topology

/-- Reciprocal coordinate of an actual rank root. -/
def reciprocalBranch {j k : ℕ} (t : ℕ → Fin j → Fin k → ℝ) (r : Fin j) (i : Fin k)
    (d : ℕ) : ℝ := reciprocalArgumentScale j d / t d r i

/-- The largest-modulus roots, the leading limit, and the signed first correction
in the original and reciprocal coordinates all refer to the same indexing. -/
structure OriginalAsymptoticPrefix {j k : ℕ} (L : Fin j → ℕ → ℝ)
    (t : ℕ → Fin j → Fin k → ℝ) : Prop where
  certified : ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, ∀ r : Fin j,
    OriginalOuterPrefix j r d (prefixRadius L r k) ε (fun i : Fin k ↦ -L r i) (t d r)
  reciprocal : ∀ (r : Fin j) (i : Fin k), Tendsto (reciprocalBranch t r i) atTop (𝓝 (-L r i))
  original : ∀ (r : Fin j) (i : Fin k), Tendsto (fun d ↦ t d r i / reciprocalArgumentScale j d)
    atTop (𝓝 (1/(-L r i)))
  reciprocal_correction : ∀ (r : Fin j) (i : Fin k), let c := (-L r i : ℝ)
    Tendsto (fun d : ℕ ↦ (d:ℂ)*((reciprocalBranch t r i d:ℂ)-(c:ℂ))) atTop
      (𝓝 (-(reciprocalCorrection j r c) / deriv (reciprocalLimit j r) (c:ℂ)))
  original_correction : ∀ (r : Fin j) (i : Fin k), let c := (-L r i : ℝ)
    Tendsto (fun d : ℕ ↦ (d:ℂ)*(((t d r i:ℂ)/(reciprocalArgumentScale j d:ℂ)) - 1/(c:ℂ)))
      atTop (𝓝 (reciprocalCorrection j r c / ((c:ℂ)^2*deriv (reciprocalLimit j r) (c:ℂ))))

theorem all_original_first_correction {j : ℕ} (hj : 2 ≤ j) :
    ∃ L, ZeroLadder j L ∧ ∀ k, ∃ t, @OriginalAsymptoticPrefix j k L t := by
  obtain ⟨L,ladder,all⟩ := all_original_branches hj
  refine ⟨L,ladder,?_⟩
  intro k
  obtain ⟨t,certified⟩ := all k
  have cv (r : Fin j) (i : Fin k) : Tendsto (reciprocalBranch t r i) atTop (𝓝 (-L r i)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hp
    exact (certified ε hp).mono fun d hh ↦ (hh r).near i
  have zero (r : Fin j) (i : Fin k) : reciprocalLimit j r ((-L r i : ℝ):ℂ) = 0 := by
    simpa only [Complex.ofReal_neg] using (ladder.roots r _).mpr ⟨i,rfl⟩
  have simple (r : Fin j) (i : Fin k) : deriv (reciprocalLimit j r) ((-L r i : ℝ):ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg] using ladder.simple r i
  have correction (r : Fin j) (i : Fin k) := @simple_zero_first_correction j r hj
    (-L r i) (zero r i) (simple r i) (reciprocalBranch t r i) (cv r i)
  have roots (r : Fin j) (i : Fin k) : ∀ᶠ d in atTop,
      reciprocalValue j r d (reciprocalBranch t r i d:ℂ) = 0 := by
    filter_upwards [eventually_ge_atTop 1,certified 1 one_pos] with d hd hh
    have pos := reciprocalArgumentScale_pos j hd
    have neg := (hh r).negative i
    have nz : (reciprocalBranch t r i d:ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (div_ne_zero pos.ne' neg.ne)
    apply (reciprocal_zero_iff_original_complex hj r.isLt hd nz).mpr
    rw [reciprocalBranch,Complex.ofReal_div,scaled_inverse_involutive
      (Complex.ofReal_ne_zero.mpr pos.ne') (Complex.ofReal_ne_zero.mpr neg.ne)]
    exact (hh r).zero i
  refine ⟨t,certified,cv,?_,fun r i ↦ correction r i (roots r i),?_⟩
  · intro r i
    simpa only [reciprocalBranch, one_div, inv_div] using (cv r i).inv₀
      (neg_ne_zero.mpr (ladder.positive r i).ne')
  · intro r i
    let c : ℝ := -L r i
    let x := reciprocalBranch t r i
    have cn : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr (ladder.positive r i).ne')
    have cx : Tendsto (fun d ↦ (x d:ℂ)) atTop (𝓝 (c:ℂ)) :=
      (Complex.continuous_ofReal.tendsto c).comp (cv r i)
    have result := (correction r i (roots r i)).neg.div (cx.mul_const (c:ℂ)) (mul_ne_zero cn cn)
    have val : -(-(reciprocalCorrection j r c)/deriv (reciprocalLimit j r) (c:ℂ)) /
        ((c:ℂ)*(c:ℂ)) = reciprocalCorrection j r c / ((c:ℂ)^2 * deriv (reciprocalLimit j r) (c:ℂ)) := by
      ring
    rw [val] at result
    apply result.congr'
    filter_upwards [cx.eventually (eventually_ne_nhds cn)] with d xn
    change -((d:ℂ)*((x d:ℂ)-(c:ℂ)))/((x d:ℂ)*(c:ℂ)) =
      (d:ℂ)*(((t d r i:ℂ)/(reciprocalArgumentScale j d:ℂ))-1/(c:ℂ))
    rw [show ((t d r i:ℂ)/(reciprocalArgumentScale j d:ℂ)) = 1/(x d:ℂ) by
      simp only [x,reciprocalBranch,Complex.ofReal_div,one_div,inv_div]]
    field_simp
    ring

#print axioms all_original_first_correction
end OrderedPartitions.ReciprocalSector
