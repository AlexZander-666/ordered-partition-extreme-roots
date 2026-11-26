import OrderedPartitions.ReciprocalEdgeMajorant
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Uniform convergence of the original scaled reciprocals on every complex disk. -/

noncomputable section
open Filter Finset
open scoped Topology

namespace OrderedPartitions.ReciprocalEdge

/-- The entire-function limit of the scaled reciprocal row. -/
def reciprocalLimit (j r : ℕ) (w : ℂ) : ℂ :=
  ∑' h : ℕ, Complex.ofReal (1 / ((r+j*h).factorial : ℝ)) * w^h

/-- For each fixed threshold and residue, the true reciprocal polynomials converge
to `reciprocalLimit` uniformly on every closed disk. -/
theorem reciprocal_uniformly_on_closedBall {j : ℕ} (hj : 2 ≤ j) (r : ℕ) (R : ℝ) :
    TendstoUniformlyOn (fun d w ↦ (reciprocalRow j r d).eval₂ Complex.ofRealHom w)
      (reciprocalLimit j r) atTop (Metric.closedBall (0 : ℂ) R) := by
  let S := ↥(Metric.closedBall (0 : ℂ) R)
  let K : ℝ := 4 * ((j+r+1 : ℕ) : ℝ)
  let radius := max (1 : ℝ) R
  have K_pos : 0 < K := by dsimp [K]; positivity
  have radius_pos : 0 < radius := zero_lt_one.trans_le (le_max_left _ _)
  let power (h : ℕ) : BoundedContinuousFunction S ℂ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ (z : ℂ)^h, continuous_subtype_val.pow h⟩
  let F (d h : ℕ) : BoundedContinuousFunction S ℂ := (scaledReciprocalCoeff j r d h : ℂ) • power h
  let G (h : ℕ) : BoundedContinuousFunction S ℂ :=
    Complex.ofReal (1 / ((r+j*h).factorial : ℝ)) • power h
  let bound (h : ℕ) := K^r * ((K^j * radius)^h / (h.factorial : ℝ))
  have hsum : Summable bound := (Real.summable_pow_div_factorial (K^j * radius)).mul_left _
  have term_limit (h : ℕ) : Tendsto (fun d ↦ F d h) atTop (𝓝 (G h)) := by
    have scalar : Tendsto (fun d : ℕ ↦ (scaledReciprocalCoeff j r d h : ℂ)) atTop
        (𝓝 (Complex.ofReal (1 / ((r+j*h).factorial : ℝ)))) := by
      simpa only [Function.comp_def] using
        (Complex.continuous_ofReal.tendsto _).comp (original_fixed_coefficient_limit hj r h)
    exact scalar.smul (tendsto_const_nhds (x := power h))
  have power_bound (h : ℕ) : ‖power h‖ ≤ radius^h := by
    refine (BoundedContinuousFunction.norm_le (pow_nonneg radius_pos.le h)).mpr ?_
    intro w
    change ‖(w : ℂ)^h‖ ≤ radius^h
    rw [norm_pow]
    have below : ‖(w : ℂ)‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
    exact pow_le_pow_left₀ (norm_nonneg _) (below.trans (le_max_right _ _)) h
  have dominated : ∀ᶠ d : ℕ in atTop, ∀ h, ‖F d h‖ ≤ bound h := by
    filter_upwards [eventually_ge_atTop 1] with d hd h
    have coeff := scaled_coeff_factorial_bound hj hd r h
    have m_ge : h ≤ r+j*h := by
      have step := Nat.mul_le_mul_right h (show 1 ≤ j by omega)
      simpa using step.trans (Nat.le_add_left (j*h) r)
    calc
      ‖F d h‖ ≤ ‖(scaledReciprocalCoeff j r d h : ℂ)‖ * ‖power h‖ := norm_smul_le _ _
      _ ≤ (K^(r+j*h) / ((r+j*h).factorial : ℝ)) * radius^h := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg coeff.1]
        exact mul_le_mul coeff.2 (power_bound h) (norm_nonneg _) (by positivity)
      _ ≤ (K^(r+j*h) / (h.factorial : ℝ)) * radius^h := by
        have fact : (h.factorial : ℝ) ≤ ((r+j*h).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le m_ge
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
          (by positivity) fact) (by positivity)
      _ = bound h := by
        dsimp only [bound]
        rw [pow_add, pow_mul, mul_pow]
        ring
  have close := tendsto_tsum_of_dominated_convergence hsum term_limit dominated
  have limit_bound (h : ℕ) : ‖G h‖ ≤ bound h :=
    le_of_tendsto (term_limit h).norm (dominated.mono (fun _ hu ↦ hu h))
  have target_sum : Summable G := hsum.of_norm_bounded limit_bound
  have eval_source (d : ℕ) (w : S) : (∑' h, F d h) w =
      (reciprocalRow j r d).eval₂ Complex.ofRealHom (w : ℂ) := by
    have finite (h : ℕ) (outside : h ∉ range (d+1)) : F d h = 0 := by
      have beyond : ¬ h ≤ d := fun le ↦ outside (mem_range.mpr (Nat.lt_succ_of_le le))
      simp [F, scaledReciprocalCoeff, beyond]
    rw [tsum_eq_sum finite, reciprocalRow, Polynomial.eval₂_finsetSum]
    simp only [BoundedContinuousFunction.sum_apply]
    apply sum_congr rfl
    intro h _
    rw [Polynomial.eval₂_monomial]
    rfl
  have eval_target (w : S) : (∑' h, G h) w = reciprocalLimit j r (w : ℂ) := by
    exact (BoundedContinuousFunction.evalCLM ℂ w).map_tsum target_sum
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have on_disk := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp close
  convert on_disk using 1
  · funext d w
    exact (eval_source d w).symm
  · funext w
    exact (eval_target w).symm

#print axioms reciprocal_uniformly_on_closedBall

end OrderedPartitions.ReciprocalEdge
