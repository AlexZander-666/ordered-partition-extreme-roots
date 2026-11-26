import OrderedPartitions.ReciprocalEdgeUpperExclusion
import OrderedPartitions.ReciprocalEdgeLimit
import OrderedPartitions.ReciprocalEdgeSectors

/-! Binomial approximations to all residues at once, with a summable factorial majorant. -/
noncomputable section
namespace OrderedPartitions.ReciprocalEdge
open Filter Finset Complex
open scoped Topology

/-- The sections of (1+t/N)^N converge pointwise in the complex plane to
the same functions obtained from the original ordered-partition polynomials. -/
theorem euler_sections_limit {j : ℕ} (hj : 1≤j) (r : ℕ) (w : ℂ) :
    Tendsto (fun N : ℕ ↦ ∑ h ∈ range (N+1),
      (N.choose (j*h+r):ℂ)*((1/(N:ℝ):ℝ):ℂ)^(j*h+r)*w^h) atTop (𝓝 (reciprocalLimit j r w)) := by
  let f (N h : ℕ) := ((N.choose (j*h+r):ℂ)/(N:ℂ)^(j*h+r))*w^h
  let g (h : ℕ) := (1/((j*h+r).factorial:ℂ))*w^h
  have point h : Tendsto (fun N ↦ f N h) atTop (𝓝 (g h)) := by
    have lim := (Complex.continuous_ofReal.continuousAt.tendsto.comp (choose_limit (j*h+r))).mul_const (w^h)
    simpa [f,g,Function.comp_def] using lim
  have dom : ∀ᶠ N : ℕ in atTop, ∀ h, ‖f N h‖ ≤ ‖w‖^h/(h.factorial:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hn h
    let k := j*h+r
    have hp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
    have hk : h≤k := by have he:=Nat.mul_le_mul_right h hj;dsimp [k];simpa using he.trans (Nat.le_add_right _ _)
    have normalized : (N.choose k:ℝ)/(N:ℝ)^k ≤ 1/(k.factorial:ℝ) := by
      rw [div_le_iff₀ (pow_pos hp k)]
      simpa [div_eq_mul_inv,mul_comm] using Nat.choose_le_pow_div (α:=ℝ) k N
    change ‖(N.choose k:ℂ)/(N:ℂ)^k*w^h‖ ≤ _
    simp only [norm_mul,norm_div,norm_pow,Complex.norm_natCast]
    calc
      _ ≤ (1/(k.factorial:ℝ))*‖w‖^h := mul_le_mul_of_nonneg_right normalized (by positivity)
      _ ≤ (1/(h.factorial:ℝ))*‖w‖^h := by
        gcongr
      _ = _ := by ring
  have sum := tendsto_tsum_of_dominated_convergence (Real.summable_pow_div_factorial ‖w‖) point dom
  have gf : ∑' h,g h=reciprocalLimit j r w := by
    unfold reciprocalLimit
    apply tsum_congr
    intro n
    simp [g,Nat.add_comm]
  rw [gf] at sum
  apply sum.congr'
  filter_upwards with N
  rw [tsum_eq_sum (s:=range (N+1)) (by
    intro h nh
    have lo : N<h := by simpa using nh
    have k : h≤j*h+r := by
      have m := Nat.mul_le_mul_right h hj
      simpa using m.trans (Nat.le_add_right _ _)
    simp [f,Nat.choose_eq_zero_of_lt (lo.trans_le k)])]
  exact sum_congr rfl (fun h _ ↦ by simp [f,div_eq_mul_inv])

/-- The two determinant inequalities are closed under pointwise convergence of the entries. -/
theorem limit_sectors {j : ℕ} (hj : 1≤j) {w : ℂ} (i k : Fin j)
    (chain : ∀ᶠ N : ℕ in atTop, ReciprocalSector.Sector w
      (∑ h ∈ range (N+1), (N.choose (j*h+i.val):ℂ)*((1/(N:ℝ):ℝ):ℂ)^(j*h+i.val)*w^h)
      (∑ h ∈ range (N+1), (N.choose (j*h+k.val):ℂ)*((1/(N:ℝ):ℝ):ℂ)^(j*h+k.val)*w^h)) :
    ReciprocalSector.Sector w (reciprocalLimit j i w) (reciprocalLimit j k w) := by
  have A := euler_sections_limit hj i w
  have B := euler_sections_limit hj k w
  refine ⟨ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp (A.mul B.star)) (chain.mono fun _ h ↦ h.1),
    ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp ((B.const_mul w).mul A.star)) (chain.mono fun _ h ↦ h.2)⟩

#print axioms euler_sections_limit
#print axioms limit_sectors
end OrderedPartitions.ReciprocalEdge
