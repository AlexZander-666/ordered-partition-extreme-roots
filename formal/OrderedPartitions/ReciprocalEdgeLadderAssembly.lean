import OrderedPartitions.ReciprocalEdgeLadder
import OrderedPartitions.ReciprocalEdgeActualZeros

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex OrderedPartitions.ReciprocalEdge

/-- A complete simple-zero ladder. The natural index starts at the first zero;
each entry gives its positive distance from zero. -/
structure ZeroLadder (j : ℕ) (L : Fin j → ℕ → ℝ) : Prop where
  positive : ∀ r n, 0<L r n
  increasing : ∀ r, StrictMono (L r)
  across : ∀ n, StrictMono (fun r ↦ L r n)
  next_level : ∀ n r s, L r n < L s (n+1)
  roots : ∀ (r : Fin j) (w : ℂ), reciprocalLimit j r w=0 ↔ ∃ n, w = -(L r n:ℂ)
  simple : ∀ (r : Fin j) n, deriv (reciprocalLimit j r) (-(L r n:ℂ)) ≠ 0

/-- The enumeration, all shifts and wraparound hold once the zeros of each
actual section are known to be unbounded to the left. -/
theorem ladder_of_unbounded {j : ℕ} (hj : 2≤j)
    (unbounded : ∀ (r : Fin j) (b : ℝ), ∃ a, a<b ∧ reciprocalLimit j r a=0) :
    ∃ L, ZeroLadder j L := by
  classical
  cases j with
  | zero => omega
  | succ d =>
    have jp : 1≤d+1 := by omega
    choose z arr using fun r : Fin (d+1) ↦ section_listing jp r (unbounded r)
    let L (r : Fin (d+1)) (n : ℕ) := -z r n
    have edge {i k : Fin (d+1)} (ik : i<k)
        (separate : ∀ x : ℝ, x<0 → sectionR (d+1) k x=0 → sectionR (d+1) i x≠0)
        (n : ℕ) : L i n<L k n ∧ L k n<L i (n+1) := by
      obtain ⟨one,two⟩ := pair_ladder jp i k ik (arr i) (arr k) (unbounded k) separate n
      exact ⟨neg_lt_neg one,neg_lt_neg two⟩
    have ascent (n : ℕ) : StrictMono (fun r ↦ L r n) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      apply (edge (i:=i.castSucc) (k:=i.succ) Fin.castSucc_lt_succ _ n).1
      intro x hx zero
      exact mt zero_cast.mp (no_adjacent_zero i.succ.isLt hx (zero_cast.mp zero))
    let last := Fin.last d
    have first_last : (0:Fin (d+1))<last := by change 0<d; omega
    have next (n : ℕ) : L last n<L 0 (n+1) := by
      apply (edge first_last _ n).2
      intro x hx pole hz
      exact (no_wrap_zero jp hx (zero_cast.mp hz)) (by simpa [last] using zero_cast.mp pole)
    refine ⟨L,fun r n ↦ neg_pos.mpr ((arr r).negative n),?_,ascent,?_,?_,?_⟩
    · intro r a b ab; exact neg_lt_neg ((arr r).decreasing ab)
    · intro n r s
      exact ((ascent n).monotone (Fin.le_last r)).trans_lt
        ((next n).trans_le ((ascent (n+1)).monotone (Fin.zero_le s)))
    · intro r w
      constructor
      · intro zero
        obtain ⟨real,neg⟩ := all_section_zeros_negative hj r zero
        have rc : (w.re:ℂ)=w := Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr real)
        obtain ⟨n,hn⟩ := (arr r).complete neg (zero_cast.mpr (rc ▸ zero))
        exact ⟨n,by simp [L,hn,rc]⟩
      · rintro ⟨n,rfl⟩
        simpa [L] using zero_cast.mp ((arr r).vanishes n)
    · intro r n
      simpa [L] using section_simple jp r ((arr r).negative n) (zero_cast.mp ((arr r).vanishes n))

#print axioms ladder_of_unbounded
end OrderedPartitions.ReciprocalSector
