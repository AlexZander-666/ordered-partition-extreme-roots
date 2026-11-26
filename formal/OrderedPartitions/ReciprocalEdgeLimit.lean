import OrderedPartitions.ReciprocalEdgeKernel

noncomputable section
open PowerSeries Finset Filter
open scoped Topology
namespace OrderedPartitions.ReciprocalEdge

theorem choose_limit (k : ℕ) :
    Tendsto (fun d : ℕ ↦ (d.choose k:ℝ)/(d:ℝ)^k) atTop (𝓝 (1/(k.factorial:ℝ))) := by
  have identity (d : ℕ) : (d.descFactorial k:ℝ)=(k.factorial:ℝ)*(d.choose k:ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose d k
  apply ((descending_limit k).div_const (k.factorial:ℝ)).congr'
  apply Eventually.of_forall
  intro d
  dsimp only
  rw [identity]
  field_simp

private theorem choose_lower {i m : ℕ} (lt : i < m) :
    Tendsto (fun d : ℕ ↦ (d.choose i:ℝ)/(d:ℝ)^m) atTop (𝓝 0) := by
  have k0 : m-i≠0 := by omega
  have decay := Kernel.inv_power_limit tendsto_id (m-i)
  have lim := (choose_limit i).mul decay
  simp only [zero_pow k0,mul_zero] at lim
  apply lim.congr' (Eventually.of_forall (fun d ↦ ?_))
  rw [show m=i+(m-i) by omega,pow_add]
  simp [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

theorem fixed_coefficient_limit (V L : PowerSeries ℝ) (m : ℕ) :
    Tendsto (fun d : ℕ ↦ coeff m (V*(1+X*L)^d)/(d:ℝ)^m) atTop
      (𝓝 (constantCoeff V * (constantCoeff L)^m / m.factorial)) := by
  simp only [fixed_coeff]
  simp_rw [Finset.sum_div,Finset.sum_range_succ]
  have low := tendsto_finsetSum (range m) (fun i h ↦
    (choose_lower (mem_range.mp h)).mul_const (coeff (m-i) (V*L^i)))
  have top := (choose_limit m).mul_const (coeff 0 (V*L^m))
  simp only [zero_mul,sum_const_zero] at low
  have lim := low.add top
  simpa [Nat.sub_self,coeff_zero_eq_constantCoeff,div_eq_mul_inv,mul_assoc,mul_left_comm,
    mul_comm] using lim

#print axioms choose_limit
#print axioms fixed_coefficient_limit
end OrderedPartitions.ReciprocalEdge
