import OrderedPartitions.HardRodScaling
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open PowerSeries Finset Filter
open scoped Topology
namespace OrderedPartitions.ReciprocalEdge

/-- Coefficients at a fixed distance above the minimal degree, as a polynomial
in the number of free factors in the binomial basis. -/
theorem fixed_coeff (V L : PowerSeries ℝ) (d m : ℕ) :
    coeff m (V*(1+X*L)^d) =
      ∑ i ∈ range (m+1), (d.choose i:ℝ) * coeff (m-i) (V*L^i) := by
  rw [add_comm (1 : PowerSeries ℝ),add_pow,mul_sum,map_sum]
  have term (i : ℕ) : coeff m (V*((X*L)^i*1^(d-i)*(d.choose i : PowerSeries ℝ))) =
      if i≤m then (d.choose i:ℝ)*coeff (m-i) (V*L^i) else 0 := by
    rw [one_pow,mul_one,mul_pow]
    have reorder : V*(X^i*L^i*(d.choose i : PowerSeries ℝ)) =
        C (d.choose i : ℝ)*((V*L^i)*X^i) := by simp;ring
    rw [reorder,coeff_C_mul,coeff_mul_X_pow']
    split_ifs <;> simp_all
  simp_rw [term]
  let f := fun i : ℕ ↦ (d.choose i:ℝ)*coeff (m-i) (V*L^i)
  change (∑ i ∈ range (d+1), if i≤m then f i else 0) = ∑ i ∈ range (m+1), f i
  rw [← sum_filter]
  have eq : (range (d+1)).filter (fun i ↦ i≤m) ⊆ range (m+1) := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2)
  apply sum_subset eq
  intro i hi outside
  have im := Nat.le_of_lt_succ (mem_range.mp hi)
  have di : d < i := by
    by_contra! le
    exact outside (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le le),im⟩)
  simp [f,Nat.choose_eq_zero_of_lt di]

theorem descending_limit (k : ℕ) :
    Tendsto (fun d : ℕ ↦ (d.descFactorial k : ℝ)/(d:ℝ)^k) atTop (𝓝 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have half : Tendsto (fun d : ℕ ↦ 1-(k:ℝ)*(d:ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub
        ((Kernel.cutoff_inv_limit tendsto_id).const_mul (k:ℝ))
    apply ((ih.mul half).congr' ?_) |> (by simpa using ·)
    filter_upwards [eventually_ge_atTop (k+1)] with d hd
    have ne : (d:ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
    rw [Nat.cast_sub (by omega : k≤d),pow_succ]
    field_simp


#print axioms fixed_coeff
#print axioms descending_limit
end OrderedPartitions.ReciprocalEdge
