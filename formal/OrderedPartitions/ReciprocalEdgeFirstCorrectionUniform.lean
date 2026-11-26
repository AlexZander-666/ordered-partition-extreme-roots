import OrderedPartitions.ReciprocalEdgeFirstCorrectionMajorant
import OrderedPartitions.ReciprocalEdgeUniform

/-! Compact-uniform convergence of the first correction for the original reciprocal rows. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Filter Finset
open scoped Topology

/-- The entire first-correction function. -/
def reciprocalCorrection (j r : ℕ) (w : ℂ) : ℂ :=
  ∑' h : ℕ, (reciprocalCorrectionCoeff j r h : ℂ)*w^h

/-- The original reciprocal error multiplied by the positive rank quotient d. -/
def reciprocalFirstDifference (j r d : ℕ) (w : ℂ) : ℂ :=
  (d:ℂ)*((reciprocalRow j r d).eval₂ Complex.ofRealHom w-reciprocalLimit j r w)

/-- The two-term expansion holds uniformly on each bounded closed disk. -/
theorem reciprocal_uniform_first_correction {j : ℕ} (hj : 2 ≤ j) (r : ℕ) (R : ℝ) :
    TendstoUniformlyOn (reciprocalFirstDifference j r) (reciprocalCorrection j r) atTop
      (Metric.closedBall (0:ℂ) R) := by
  let S := ↥(Metric.closedBall (0:ℂ) R)
  let K : ℝ := 16*((j+r+1:ℕ):ℝ)
  let radius := max (1:ℝ) R
  have Kp : 0 < K := by dsimp [K]; positivity
  have K1 : 1 ≤ K := by
    have k : (1:ℝ)≤((j+r+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1≤j+r+1)
    dsimp [K]; linarith
  have rp : 0 < radius := zero_lt_one.trans_le (le_max_left _ _)
  let coeffLimit (h : ℕ) : ℝ := 1/((r+j*h).factorial:ℝ)
  let power (h : ℕ) : BoundedContinuousFunction S ℂ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ (z:ℂ)^h, continuous_subtype_val.pow h⟩
  let F (d h : ℕ) : BoundedContinuousFunction S ℂ :=
    Complex.ofReal ((d:ℝ)*(scaledReciprocalCoeff j r d h-coeffLimit h)) • power h
  let G (h : ℕ) : BoundedContinuousFunction S ℂ := (reciprocalCorrectionCoeff j r h:ℂ) • power h
  let B (h : ℕ) : ℝ := 3*K^r*((K^j*radius)^h/(h.factorial:ℝ))
  have bs : Summable B := (Real.summable_pow_div_factorial (K^j*radius)).mul_left _
  have L (h : ℕ) : Tendsto (fun d ↦ F d h) atTop (𝓝 (G h)) := by
    have scalar := (Complex.continuous_ofReal.tendsto _).comp
      (original_coefficient_first_correction hj r h)
    exact scalar.smul (tendsto_const_nhds (x := power h))
  have m_ge (h : ℕ) : h ≤ r+j*h := by
    have step := Nat.mul_le_mul_right h (show 1 ≤ j by omega)
    simpa using step.trans (Nat.le_add_left (j*h) r)
  have fact_ge (h : ℕ) : (h.factorial:ℝ) ≤ ((r+j*h).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (m_ge h)
  have power_bound (h : ℕ) : ‖power h‖ ≤ radius^h := by
    refine (BoundedContinuousFunction.norm_le (pow_nonneg rp.le h)).mpr ?_
    intro w
    change ‖(w:ℂ)^h‖ ≤ radius^h
    rw [norm_pow]
    have below := Metric.mem_closedBall.mp w.property
    rw [dist_zero_right] at below
    exact pow_le_pow_left₀ (norm_nonneg _) (below.trans (le_max_right _ _)) h
  have major (h : ℕ) : (3*K^(r+j*h)/((r+j*h).factorial:ℝ))*radius^h ≤ B h := by
    calc
      _ ≤ (3*K^(r+j*h)/(h.factorial:ℝ))*radius^h :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
          (by positivity) (fact_ge h)) (by positivity)
      _ = _ := by dsimp only [B]; rw [pow_add, pow_mul, mul_pow]; ring
  have bound : ∀ᶠ d : ℕ in atTop, ∀ h, ‖F d h‖ ≤ B h := by
    filter_upwards [eventually_ge_atTop 1] with d hd h
    calc
      ‖F d h‖ ≤ ‖Complex.ofReal ((d:ℝ)*(scaledReciprocalCoeff j r d h-coeffLimit h))‖ *
          ‖power h‖ := norm_smul_le _ _
      _ ≤ (3*K^(r+j*h)/((r+j*h).factorial:ℝ))*radius^h := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤d)]
        exact mul_le_mul (first_correction_factorial_bound hj hd r h)
          (power_bound h) (norm_nonneg _) (by positivity)
      _ ≤ _ := major h
  have approx := tendsto_tsum_of_dominated_convergence bs L bound
  have target_sum : Summable G :=
    bs.of_norm_bounded (fun h ↦ le_of_tendsto (L h).norm (bound.mono (fun _ hu ↦ hu h)))
  have eval_target (w : S) : (∑' h, G h) w = reciprocalCorrection j r (w:ℂ) :=
    (BoundedContinuousFunction.evalCLM ℂ w).map_tsum target_sum
  have eval_source : ∀ᶠ d : ℕ in atTop, ∀ w : S, (∑' h, F d h) w =
      reciprocalFirstDifference j r d (w:ℂ) := by
    filter_upwards [bound] with d bd w
    have SF : Summable (F d) := bs.of_norm_bounded bd
    let a (h : ℕ) : ℂ := (scaledReciprocalCoeff j r d h:ℂ)*(w:ℂ)^h
    let b (h : ℕ) : ℂ := (coeffLimit h:ℂ)*(w:ℂ)^h
    have a_support (h : ℕ) (hu : h ∉ range (d+1)) : a h = 0 := by
      have beyond : ¬ h ≤ d := fun le ↦ hu (mem_range.mpr (Nat.lt_succ_of_le le))
      simp [a, scaledReciprocalCoeff, beyond]
    have sa : Summable a := summable_of_ne_finset_zero a_support
    have sb : Summable b := bs.of_norm_bounded (fun h ↦ by
      have wle : ‖(w:ℂ)‖ ≤ radius :=
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property : ‖(w:ℂ)‖ ≤ R).trans
          (le_max_right _ _)
      change ‖((coeffLimit h:ℂ)*(w:ℂ)^h)‖ ≤ B h
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by dsimp [coeffLimit]; positivity), norm_pow]
      refine (mul_le_mul (div_le_div_of_nonneg_right ?_ (by positivity))
        (pow_le_pow_left₀ (norm_nonneg _) wle _) (by positivity) (by positivity)).trans (major h)
      have kp : 1 ≤ K^(r+j*h) := one_le_pow₀ K1
      linarith)
    have val_a : ∑' h, a h = (reciprocalRow j r d).eval₂ Complex.ofRealHom (w:ℂ) := by
      rw [tsum_eq_sum a_support, reciprocalRow, Polynomial.eval₂_finsetSum]
      exact sum_congr rfl (fun h _ ↦ by simp [a, Polynomial.eval₂_monomial])
    rw [show (∑' h, F d h) w = ∑' h, (F d h) w from (BoundedContinuousFunction.evalCLM ℂ w).map_tsum SF]
    have term (h : ℕ) : (F d h) w = (d:ℂ)*(a h-b h) := by
      simp only [F, BoundedContinuousFunction.smul_apply, smul_eq_mul, Complex.ofReal_mul,
        Complex.ofReal_natCast, Complex.ofReal_sub, a, b]
      change _ * (w:ℂ)^h = _
      ring
    simp_rw [term]
    rw [tsum_mul_left, sa.tsum_sub sb, val_a]
    rfl
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have at_disk := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp approx
  have equal : (fun d ↦ fun w : S ↦ (∑' h, F d h) w) =ᶠ[atTop]
      fun d w ↦ reciprocalFirstDifference j r d (w:ℂ) :=
    eval_source.mono (fun d h ↦ funext h)
  intro u hu
  filter_upwards [at_disk u hu, equal] with d h eq w
  change (reciprocalCorrection j r (w:ℂ), reciprocalFirstDifference j r d (w:ℂ)) ∈ u
  rw [← eval_target w, ← congrFun eq w]
  exact h w

#print axioms reciprocal_uniform_first_correction

end OrderedPartitions.ReciprocalEdge
