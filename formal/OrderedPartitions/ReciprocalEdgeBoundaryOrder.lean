import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-! An analytic function mapping an upper half-neighborhood to the closed upper
half-plane has at most a simple boundary zero unless its germ vanishes. -/
noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex Filter Set
open scoped Topology Real

private theorem boundary_ray {f g : ℂ → ℂ} {x : ℝ} {m : ℕ} (cg : ContinuousAt g (x:ℂ))
    (factor : ∀ᶠ w in 𝓝 (x:ℂ), f w = (w-x)^m*g w)
    (up : ∀ᶠ w in 𝓝 (x:ℂ), 0<w.im → 0≤(f w).im) {v : ℂ} (pos : 0<v.im) :
    0 ≤ (v^m*g x).im := by
  let path (t : ℝ) : ℂ := x + (t:ℂ)*v
  have lim : Tendsto path (𝓝[>] 0) (𝓝 (x:ℂ)) := by
    have h : Continuous path := by unfold path; fun_prop
    simpa [path] using h.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have limIm : Tendsto (fun t ↦ (v^m*g (path t)).im) (𝓝[>] 0) (𝓝 (v^m*g x).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp ((cg.tendsto.comp lim).const_mul _)
  apply ge_of_tendsto limIm
  filter_upwards [lim.eventually factor, lim.eventually up, self_mem_nhdsWithin]
    with t fac upper (ht : 0<t)
  have im : 0<(path t).im := by simpa [path, Complex.add_im, Complex.mul_im] using mul_pos ht pos
  have good := upper im
  rw [fac] at good
  have line : (path t-(x:ℂ))^m*g (path t) = (t^m:ℝ)*(v^m*g (path t)) := by
    simp [path, mul_pow, mul_assoc]
  rw [line, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at good
  exact nonneg_of_mul_nonneg_right good (pow_pos ht m)

/-- The inward vertical ray gives the sign of a continuous linear factor. -/
theorem boundary_linear_sign {g : ℂ→ℂ} {x : ℝ} (cg : ContinuousAt g (x:ℂ))
    (up : ∀ᶠ w in 𝓝 (x:ℂ), 0<w.im → 0≤((w-x)*g w).im) : 0≤(g x).re := by
  have h := boundary_ray (f:=fun w ↦ (w-x)*g w) (m:=1) cg
    (Filter.Eventually.of_forall fun w ↦ by simp)
    up (show 0<I.im by simp)
  simpa using h

private def unitArg (t : ℝ) : ℂ := exp ((t:ℂ)*I)

private theorem ray_angle {f g : ℂ→ℂ} {x : ℝ} {m : ℕ} (hm : 2≤m)
    (cg : ContinuousAt g (x:ℂ)) (factor : ∀ᶠ w in 𝓝 (x:ℂ), f w = (w-x)^m*g w)
    (up : ∀ᶠ w in 𝓝 (x:ℂ), 0<w.im → 0≤(f w).im)
    {a : ℝ} (ha : 0<a) (hb : a<2*Real.pi) :
    0 ≤ (unitArg a*g x).im := by
  have hm' : (2:ℝ)≤m := by exact_mod_cast hm
  have mp : (0:ℝ)<m := by linarith
  have pos : 0<(unitArg (a/m)).im := by
    rw [unitArg, exp_ofReal_mul_I_im]
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos ha mp)
    exact (div_lt_iff₀ mp).mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hm') Real.pi_pos.le])
  have power : unitArg (a/m)^m = unitArg a := by
    unfold unitArg
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    have ne : (m:ℂ)≠0 := by exact_mod_cast (by omega : m≠0)
    field_simp [ne]
  exact power ▸ boundary_ray cg factor up pos

theorem boundary_order_le_one {f : ℂ→ℂ} {x : ℝ} (analytic : AnalyticAt ℂ f (x:ℂ))
    (nontrivial : ¬∀ᶠ w in 𝓝 (x:ℂ), f w=0)
    (up : ∀ᶠ w in 𝓝 (x:ℂ), 0<w.im → 0≤(f w).im) :
    analyticOrderAt f (x:ℂ) ≤ 1 := by
  obtain ⟨m,g,ag,ng,fac⟩ := analytic.exists_eventuallyEq_pow_smul_nonzero_iff.mpr nontrivial
  have ord : analyticOrderAt f (x:ℂ) = m := analytic.analyticOrderAt_eq_natCast.mpr ⟨g,ag,ng,fac⟩
  rw [ord]
  change (m:ℕ∞) ≤ ((1:ℕ):ℕ∞)
  apply (ENat.natCast_le_natCast).mpr
  by_contra! hm
  have pos (a : ℝ) (ha : 0<a) (hb : a<2*Real.pi) := ray_angle hm ag.continuousAt fac up ha hb
  have van (a : ℝ) (ha : 0<a) (hb : a<Real.pi) : (unitArg a*g x).im=0 := by
    have h1 := pos a ha (by linarith [Real.pi_pos])
    have h2 := pos (a+Real.pi) (by linarith [Real.pi_pos]) (by linarith)
    have neg : unitArg (a+Real.pi) = -unitArg a := by
      simp [unitArg, add_mul, exp_add]
    rw [neg, neg_mul, neg_im] at h2
    linarith
  have h1 := van (Real.pi/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 := van (Real.pi/4) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have re : (g x).re=0 := by
    simpa [unitArg, mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] using h1
  have im : (g x).im=0 := by
    rw [mul_im, re, mul_zero, add_zero, unitArg, exp_ofReal_mul_I_re, Real.cos_pi_div_four] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by positivity)
  exact ng (Complex.ext (by simpa using re) (by simpa using im))

#print axioms boundary_order_le_one
end OrderedPartitions.ReciprocalSector
