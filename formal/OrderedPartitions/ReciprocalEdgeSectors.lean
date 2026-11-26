import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Positivity of the two determinants for cyclic sections of a positive linear product. -/
noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex
open scoped ComplexConjugate

/-- The two oriented areas for an ordered pair of sections at a fixed argument. -/
def Sector (z a b : ℂ) : Prop :=
  0 ≤ (a * conj b).im ∧ 0 ≤ (z * b * conj a).im

theorem sector_self {z : ℂ} (up : 0 ≤ z.im) (a : ℂ) : Sector z a a := by
  unfold Sector
  constructor
  · simp [Complex.mul_conj]
  · rw [mul_assoc, Complex.mul_conj]
    simpa using mul_nonneg up (Complex.normSq_nonneg a)

theorem sector_wrap {z a b : ℂ} (h : Sector z a b) : Sector z (z*b) a := by
  constructor
  · exact h.2
  · have id : z * a * conj (z*b) = (Complex.normSq z : ℂ) * (a*conj b) := by
      rw [← Complex.mul_conj]
      simp only [map_mul]
      ring
    rw [id]
    simpa using mul_nonneg (Complex.normSq_nonneg z) h.1

private theorem add_left {z a b c : ℂ} (h : Sector z a c) (h' : Sector z b c) :
    Sector z (a+b) c := by
  constructor <;> simp only [map_add, add_mul, mul_add, add_im]
  · exact add_nonneg h.1 h'.1
  · exact add_nonneg h.2 h'.2

private theorem add_right {z a b c : ℂ} (h : Sector z a b) (h' : Sector z a c) :
    Sector z a (b+c) := by
  constructor <;> simp only [map_add, add_mul, mul_add, add_im]
  · exact add_nonneg h.1 h'.1
  · exact add_nonneg h.2 h'.2

private theorem scale_left {z a b : ℂ} {c : ℝ} (hc : 0 ≤ c) (h : Sector z a b) :
    Sector z (c*a) b := by
  constructor
  · rw [mul_assoc]
    simpa using mul_nonneg hc h.1
  · have id : z*b*conj ((c:ℂ)*a) = c*(z*b*conj a) := by
      simp only [map_mul, conj_ofReal]
      ring
    rw [id]
    simpa using mul_nonneg hc h.2

private theorem scale_right {z a b : ℂ} {c : ℝ} (hc : 0 ≤ c) (h : Sector z a b) :
    Sector z a (c*b) := by
  constructor
  · have id : a*conj ((c:ℂ)*b) = c*(a*conj b) := by
      simp only [map_mul, conj_ofReal]
      ring
    rw [id]
    simpa using mul_nonneg hc h.1
  · have id : z*((c:ℂ)*b)*conj a = c*(z*b*conj a) := by ring
    rw [id]
    simpa using mul_nonneg hc h.2

theorem sector_mix {z a b u v : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (ab : Sector z a b) (av : Sector z a v) (ub : Sector z u b) (uv : Sector z u v) :
    Sector z (a+c*u) (b+c*v) :=
  add_left (add_right ab (scale_right hc av))
    (scale_left hc (add_right ub (scale_right hc uv)))

def AreaChain {d : ℕ} (z : ℂ) (V : Fin (d+1) → ℂ) : Prop :=
  ∀ i k, i ≤ k → Sector z (V i) (V k)

/-- The residue classes of the exponents after multiplying by a linear factor. -/
def step {d : ℕ} (z : ℂ) (c : ℝ) (V : Fin (d+1) → ℂ) : Fin (d+1) → ℂ :=
  Fin.cases (V 0+c*(z*V (Fin.last d))) (fun i ↦ V i.succ+c*V i.castSucc)

theorem step_preserves {d : ℕ} {z : ℂ} (up : 0 ≤ z.im) {c : ℝ} (hc : 0 ≤ c)
    {V : Fin (d+1) → ℂ} (old : AreaChain z V) : AreaChain z (step z c V) := by
  intro i k ik
  obtain eq | lt := eq_or_lt_of_le ik
  · subst k
    exact sector_self up _
  induction i using Fin.cases with
  | zero =>
    induction k using Fin.cases with
    | zero => exact (lt_irrefl _ lt).elim
    | succ k =>
      simp only [step, Fin.cases_zero, Fin.cases_succ]
      exact sector_mix hc (old _ _ (Fin.zero_le _)) (old _ _ (Fin.zero_le _))
        (sector_wrap (old _ _ (Fin.le_last _))) (sector_wrap (old _ _ (Fin.le_last _)))
  | succ i =>
    induction k using Fin.cases with
    | zero => exact (not_lt_of_ge (Fin.zero_le _) lt).elim
    | succ k =>
      simp only [step, Fin.cases_succ]
      have strong : i.val < k.val := by simpa using lt
      apply sector_mix hc
      all_goals
        apply old
        simp only [Fin.le_def, Fin.val_castSucc,
        Fin.val_succ]
        omega

#print axioms sector_wrap
#print axioms step_preserves
end OrderedPartitions.ReciprocalSector
