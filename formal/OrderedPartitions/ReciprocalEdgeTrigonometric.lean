import OrderedPartitions.ReciprocalEdgeRootTransfer
import OrderedPartitions.ReciprocalEdgeEvaluation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Explicit reciprocal limiting zeros for both parities at threshold two. -/

noncomputable section
open Filter Set Metric
open scoped Topology
namespace OrderedPartitions.ReciprocalEdge

theorem even_limit_cos (z : ℂ) : reciprocalLimit 2 0 (-(z^2)) = Complex.cos z := by
  rw [reciprocalLimit, Complex.cos_eq_tsum]
  apply tsum_congr
  intro n
  rw [show -(z^2) = (-1 : ℂ)*z^2 by ring, mul_pow]
  simp only [Nat.zero_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
    pow_mul]
  ring

theorem odd_limit_sin (z : ℂ) : z * reciprocalLimit 2 1 (-(z^2)) = Complex.sin z := by
  rw [reciprocalLimit, Complex.sin_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show -(z^2) = (-1 : ℂ)*z^2 by ring, mul_pow]
  rw [Nat.add_comm 1 (2*n), pow_succ]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  ring


private theorem neg_sq_deriv (y : ℂ) :
    HasDerivAt (fun w : ℂ ↦ -(w^2)) (-(2*y)) y := by
  simpa [Pi.neg_def] using (hasDerivAt_pow 2 y).neg

theorem even_simple_zero (y : ℂ) (hy : Complex.cos y = 0) :
    reciprocalLimit 2 0 (-(y^2)) = 0 ∧ deriv (reciprocalLimit 2 0) (-(y^2)) ≠ 0 := by
  refine ⟨(even_limit_cos y).trans hy, ?_⟩
  intro vanishes
  have chain := ((reciprocal_limit_holomorphic (j := 2) (by decide) 0 _).hasDerivAt).comp y
    (neg_sq_deriv y)
  simp only [Function.comp_def, even_limit_cos, vanishes, zero_mul] at chain
  have eq := chain.unique (Complex.hasDerivAt_cos y)
  have bad := Complex.sin_sq_add_cos_sq y
  rw [hy, neg_eq_zero.mp eq.symm] at bad
  norm_num at bad

theorem odd_simple_zero (y : ℂ) (ny : y ≠ 0) (hy : Complex.sin y = 0) :
    reciprocalLimit 2 1 (-(y^2)) = 0 ∧ deriv (reciprocalLimit 2 1) (-(y^2)) ≠ 0 := by
  have zero : reciprocalLimit 2 1 (-(y^2)) = 0 :=
    (mul_eq_zero.mp ((odd_limit_sin y).trans hy)).resolve_left ny
  refine ⟨zero, ?_⟩
  intro vanishes
  have chain := ((reciprocal_limit_holomorphic (j := 2) (by decide) 1 _).hasDerivAt).comp y
    (neg_sq_deriv y)
  have product := (hasDerivAt_id y).mul chain
  simp only [Pi.mul_def, Function.comp_def, id_eq, odd_limit_sin, zero, vanishes, zero_mul, mul_zero,
    add_zero] at product
  have eq := product.unique (Complex.hasDerivAt_sin y)
  have bad := Complex.sin_sq_add_cos_sq y
  rw [hy, ← eq] at bad
  norm_num at bad

#print axioms even_simple_zero
#print axioms odd_simple_zero


private theorem transfer_two {r : ℕ} (hr : r < 2) {y : ℝ} (hy : 0 < y)
    (zero : reciprocalLimit 2 r (-((y : ℂ)^2)) = 0)
    (simple : deriv (reciprocalLimit 2 r) (-((y : ℂ)^2)) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ t : ℝ, t < 0 ∧ (row (2*d+r) 2).eval t = 0 ∧
      dist (t / (d : ℝ)^2) (-(32/9) / y^2) < ε := by
  let c := -(y^2)
  have hc : c < 0 := neg_neg_of_pos (sq_pos_of_pos hy)
  have cv : ContinuousAt (fun x : ℝ ↦ (32/9) / x) c :=
    continuousAt_const.div continuousAt_id hc.ne
  obtain ⟨δ, hδ, close⟩ := Metric.continuousAt_iff.mp cv ε hε
  have hzero : reciprocalLimit 2 r (c : ℂ) = 0 := by simpa [c] using zero
  have hsimple : deriv (reciprocalLimit 2 r) (c : ℂ) ≠ 0 := by simpa [c] using simple
  filter_upwards [original_negative_root_near_reciprocal_zero (by decide : 2 ≤ 2) hr hc hzero
    hsimple hδ, eventually_ge_atTop 1] with d ex hd
  obtain ⟨x, negx, nearby, root⟩ := ex
  refine ⟨reciprocalArgumentScale 2 d / x,
    div_neg_of_pos_of_neg (reciprocalArgumentScale_pos 2 hd) negx, root, ?_⟩
  have dn : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have scale : reciprocalArgumentScale 2 d / x / (d : ℝ)^2 = (32/9) / x := by
    norm_num [reciprocalArgumentScale, edgeScale, Nat.factorial]
    field_simp
    ring
  rw [scale]
  simpa only [c, div_neg, neg_div] using close nearby

/-- The even rows have an original zero within every prescribed normalized tolerance
of each of the cosine constants indexed by k = 0, 1, ... . -/
theorem even_original_root_near_cosine_constant (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ t : ℝ, t < 0 ∧ (row (2*d) 2).eval t = 0 ∧
      dist (t/(d : ℝ)^2) (-(32/9)/(Real.pi/2+k*Real.pi)^2) < ε := by
  let y : ℝ := Real.pi/2 + k*Real.pi
  have pos : 0 < y := by dsimp [y]; positivity
  have cy : Complex.cos (y : ℂ) = 0 := by
    rw [← Complex.ofReal_cos, Complex.ofReal_eq_zero]
    simp [y, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two]
  have h := even_simple_zero _ cy
  simpa only [Nat.add_zero] using transfer_two (r := 0) (by decide) pos h.1 h.2 hε

/-- The odd rows have an original zero within every prescribed normalized tolerance
of each of the nonzero sine constants. -/
theorem odd_original_root_near_sine_constant (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∃ t : ℝ, t < 0 ∧ (row (2*d+1) 2).eval t = 0 ∧
      dist (t/(d : ℝ)^2) (-(32/9)/(((k+1 : ℕ) : ℝ)*Real.pi)^2) < ε := by
  let y : ℝ := ((k+1 : ℕ) : ℝ)*Real.pi
  have pos : 0 < y := by dsimp [y]; positivity
  have sy : Complex.sin (y : ℂ) = 0 := by
    rw [← Complex.ofReal_sin, Complex.ofReal_eq_zero]
    exact Real.sin_nat_mul_pi _
  have h := odd_simple_zero (y : ℂ) (Complex.ofReal_ne_zero.mpr pos.ne') sy
  exact transfer_two (r := 1) (by decide) pos h.1 h.2 hε

#print axioms even_original_root_near_cosine_constant
#print axioms odd_original_root_near_sine_constant

end OrderedPartitions.ReciprocalEdge
