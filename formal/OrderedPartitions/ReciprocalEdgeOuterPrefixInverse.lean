import OrderedPartitions.ReciprocalEdgeRootTransfer

/-! The reciprocal coordinate, its derivative, and the modulus cutoff on original roots. -/

noncomputable section

namespace OrderedPartitions.ReciprocalEdge

open Filter Polynomial
open scoped Topology

abbrev originalValue (j r d : ℕ) : ℂ → ℂ :=
  (row (j*d+r) j).eval₂ Complex.ofRealHom

abbrev reciprocalValue (j r d : ℕ) : ℂ → ℂ :=
  (reciprocalRow j r d).eval₂ Complex.ofRealHom

theorem reciprocalPrefactor_pos {j r d : ℕ} (hd : 1 ≤ d) : 0 < reciprocalPrefactor j r d := by
  have pd : 0 < (d : ℝ) := by exact_mod_cast hd
  have slope := edgeScale_pos j
  unfold reciprocalPrefactor
  positivity

theorem reciprocal_zero_iff_original_complex {j r d : ℕ} (hj : 2 ≤ j) (hr : r < j)
    (hd : 1 ≤ d) {w : ℂ} (hw : w ≠ 0) :
    reciprocalValue j r d w = 0 ↔
      originalValue j r d ((reciprocalArgumentScale j d : ℂ)/w) = 0 := by
  have s : (reciprocalArgumentScale j d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (reciprocalArgumentScale_pos j hd).ne'
  have v : (reciprocalPrefactor j r d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (reciprocalPrefactor_pos hd).ne'
  have formula := eval₂_reciprocalRow (S := ℂ) hj hr hd w hw
  change reciprocalValue j r d w = (reciprocalPrefactor j r d : ℂ)*
    (w/(reciprocalArgumentScale j d : ℂ))^d*
    originalValue j r d ((reciprocalArgumentScale j d : ℂ)/w) at formula
  rw [formula, mul_eq_zero]
  exact or_iff_right (mul_ne_zero v (pow_ne_zero d (div_ne_zero hw s)))

/-- At a reciprocal zero, a nonzero derivative transfers to the original complex root. -/
theorem original_simple_of_reciprocal {j r d : ℕ} (hj : 2 ≤ j) (hr : r < j)
    (hd : 1 ≤ d) {w : ℂ} (hw : w ≠ 0) (zero : reciprocalValue j r d w = 0)
    (simple : deriv (reciprocalValue j r d) w ≠ 0) :
    originalValue j r d ((reciprocalArgumentScale j d : ℂ)/w) = 0 ∧
      deriv (originalValue j r d) ((reciprocalArgumentScale j d : ℂ)/w) ≠ 0 := by
  let s : ℂ := reciprocalArgumentScale j d
  let v : ℂ := reciprocalPrefactor j r d
  have pzero : originalValue j r d (s/w) = 0 :=
    (reciprocal_zero_iff_original_complex hj hr hd hw).mp zero
  refine ⟨pzero, fun vanish ↦ simple ?_⟩
  have pD : Differentiable ℂ (originalValue j r d) := by
    rw [show originalValue j r d =
        fun z ↦ ((row (j*d+r) j).map Complex.ofRealHom).eval z from
      funext (fun _ ↦ Polynomial.eval₂_eq_eval_map _)]
    exact Polynomial.differentiable _
  have Q : HasDerivAt (originalValue j r d) 0 (s/w) := vanish ▸ (pD _).hasDerivAt
  have inner := (hasDerivAt_const w s).div (hasDerivAt_id w) hw
  have composition : HasDerivAt (fun z : ℂ ↦ originalValue j r d (s/z)) 0 w := by
    simpa only [Function.comp_def, zero_mul] using Q.comp w inner
  have weight := (((hasDerivAt_id w).div_const s).pow d).const_mul v
  have product := weight.mul composition
  simp only [Pi.pow_apply, id_eq, pzero, mul_zero, add_zero] at product
  have agree : reciprocalValue j r d =ᶠ[𝓝 w]
      fun z : ℂ ↦ v*(z/s)^d*originalValue j r d (s/z) := by
    filter_upwards [eventually_ne_nhds hw] with z hz
    exact eval₂_reciprocalRow (S := ℂ) hj hr hd z hz
  exact (product.congr_of_eventuallyEq agree).deriv

/-- Inversion reverses the order on the negative half-axis. -/
theorem scaled_inverse_lt {s x y : ℝ} (hs : 0 < s) (hyx : y < x) (hx : x < 0) :
    s/x < s/y := by
  have h : s / (-y) < s / (-x) := by
    apply (div_lt_div_iff₀ (by linarith : 0 < -y) (by linarith : 0 < -x)).mpr
    exact mul_lt_mul_of_pos_left (neg_lt_neg hyx) hs
  simpa only [div_neg, neg_neg] using neg_lt_neg h

theorem scaled_inverse_involutive {K : Type*} [Field K] {s z : K}
    (hs : s ≠ 0) (hz : z ≠ 0) : s / (s / z) = z := by
  field_simp

/-- The original roots above the modulus cutoff are precisely the nonzero
reciprocals of roots in the closed normalized disk, including its boundary. -/
theorem reciprocal_norm_cutoff {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) {z : ℂ} (hz : z ≠ 0) :
    ‖((s : ℂ)/z)‖ ≤ ρ ↔ s/ρ ≤ ‖z‖ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    div_le_iff₀ (norm_pos_iff.mpr hz), div_le_iff₀ hρ, mul_comm ρ]

#print axioms reciprocal_zero_iff_original_complex
#print axioms original_simple_of_reciprocal
#print axioms scaled_inverse_lt
#print axioms reciprocal_norm_cutoff

end OrderedPartitions.ReciprocalEdge
