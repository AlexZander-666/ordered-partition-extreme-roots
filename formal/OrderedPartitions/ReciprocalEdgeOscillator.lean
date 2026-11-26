import OrderedPartitions.ReciprocalEdgeActualZeros
import Mathlib.Analysis.Complex.RealDeriv

/-! Real cyclic primitives and the nondecaying exponential mode. -/
noncomputable section
namespace OrderedPartitions.ReciprocalEdge
open Set Filter Complex
open scoped Topology

def oscillatingSection (j r : ℕ) (t : ℝ) : ℝ := t^r*(reciprocalLimit j r ((-(t^j):ℝ):ℂ)).re

private theorem real_section (j r : ℕ) (x : ℝ) :
    (((reciprocalLimit j r x).re:ℝ):ℂ) = reciprocalLimit j r x := by
  have s := section_conj j r (x:ℂ)
  have eq : star (reciprocalLimit j r x)=reciprocalLimit j r x := by simpa using s.symm
  obtain ⟨y,ey⟩ := Complex.conj_eq_iff_real.mp eq
  rw [ey]
  rfl

private theorem section_comp_deriv {j : ℕ} (hj : 2≤j) (r : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (reciprocalLimit j r ((-(s^j):ℝ):ℂ)).re)
      ((deriv (reciprocalLimit j r) ((-(t^j):ℝ):ℂ)).re * (-((j:ℝ)*t^(j-1)))) t :=
  ((reciprocal_limit_holomorphic hj r _).hasDerivAt.real_of_complex).comp t (hasDerivAt_pow j t).neg

/-- Moving one residue forward integrates the previous real oscillating section. -/
theorem next_section_deriv {j : ℕ} (hj : 2≤j) (r : ℕ) (t : ℝ) :
    HasDerivAt (oscillatingSection j (r+1)) (oscillatingSection j r t) t := by
  have p := (hasDerivAt_pow (r+1) t).mul (section_comp_deriv hj (r+1) t)
  have e := congrArg Complex.re (previous_multisection (by omega : 1≤j) r ((-(t^j):ℝ):ℂ))
  simp [Complex.mul_re] at e
  apply p.congr_deriv
  symm
  unfold oscillatingSection
  push_cast
  have rp : ((t:ℂ)^j).re=t^j := by rw [←Complex.ofReal_pow,Complex.ofReal_re]
  have ip : ((t:ℂ)^j).im=0 := by rw [←Complex.ofReal_pow,Complex.ofReal_im]
  rw [rp,ip] at e
  rw [e,pow_succ]
  have powId : t * t^(j-1) = t^j := by rw [←pow_succ'];congr 1;omega
  linear_combination (t^r*(j:ℝ)*(deriv (reciprocalLimit j (r+1)) (-(t:ℂ)^j)).re)*powId

/-- A full cycle changes the sign of the derivative relation. -/
theorem initial_section_deriv {j : ℕ} (hj : 2≤j) (t : ℝ) :
    HasDerivAt (oscillatingSection j 0) (-(oscillatingSection j (j-1) t)) t := by
  have p := section_comp_deriv hj 0 t
  have e := congrArg Complex.re (last_multisection (by omega : 1≤j) ((-(t^j):ℝ):ℂ))
  simp [Complex.mul_re] at e
  rw [show oscillatingSection j 0 = (fun s : ℝ ↦ (reciprocalLimit j 0 ((-(s^j):ℝ):ℂ)).re) by funext s;simp [oscillatingSection]]
  unfold oscillatingSection
  apply p.congr_deriv
  push_cast
  rw [e]
  ring

/-- Some component stays away from zero at arbitrarily large times. -/
theorem oscillator_not_all_decay {j : ℕ} (hj : 2≤j) :
    ¬ ∀ r : Fin j, Tendsto (oscillatingSection j r) atTop (𝓝 0) := by
  intro allLim
  let theta := Real.pi/(j:ℝ)
  let s := Complex.exp ((theta:ℂ)*I)
  have jp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have sn : s^j = -1 := by
    dsimp [s]
    rw [←Complex.exp_nat_mul]
    convert Complex.exp_pi_mul_I using 2
    dsimp [theta]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast jp.ne' : (j:ℂ)≠0)
  have sr : 0≤s.re := by
    dsimp [s]
    rw [Complex.exp_re]
    simp only [Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,one_mul,Complex.mul_I_im,Complex.ofReal_re]
    apply Real.cos_nonneg_of_mem_Icc
    have j2 : (2:ℝ)≤j := by exact_mod_cast hj
    dsimp [theta]
    exact ⟨by linarith [Real.pi_pos,div_pos Real.pi_pos jp],div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) j2⟩
  have identity (t : ℝ) : ∑ r : Fin j, s^(r:ℕ)*(oscillatingSection j r t:ℂ)=Complex.exp (s*(t:ℂ)) := by
    rw [←regroup_exponential (by omega : 1≤j),mul_pow,sn,neg_one_mul]
    apply Finset.sum_congr rfl
    intro i _
    unfold oscillatingSection
    push_cast
    have rr := real_section j i (-(t^j):ℝ)
    push_cast at rr
    rw [mul_pow,rr]
    ring
  have vanish : Tendsto (fun t : ℝ ↦ ∑ r : Fin j,s^(r:ℕ)*(oscillatingSection j r t:ℂ)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun (r : Fin j) _ ↦
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (allLim r)).const_mul (s^(r:ℕ)))
  have small := (vanish.norm.eventually_lt_const (show ‖(0:ℂ)‖<(1:ℝ) by simp)).and (eventually_ge_atTop (0:ℝ))
  obtain ⟨t,sm,large⟩ := small.exists
  rw [identity,Complex.norm_exp] at sm
  have pos : 0≤(s*(t:ℂ)).re := by simpa [Complex.mul_re] using mul_nonneg sr large
  exact (not_lt_of_ge (Real.one_le_exp pos)) sm

#print axioms next_section_deriv
#print axioms initial_section_deriv
#print axioms oscillator_not_all_decay
end OrderedPartitions.ReciprocalEdge
