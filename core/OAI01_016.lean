    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hp i j k)
  simp only [gcdBlock]
  rw [Finset.sum_comm]
  simp_rw [hi]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => quadraticRow (cols j) (primaryGenerator (rows i)) * a j)

theorem energy_le_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      ∑ D ∈ gcdPool cols, ‖gcdBlock D rows cols a‖ := by
  have he := congrArg norm (energy_eq_gcd_blocks rows cols a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_large_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (G : ℝ) (hG : 0 < G)
    (hS : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ‖gcdBlock D rows cols a‖) ≤
      highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hfac : 0 ≤ supportConstant ε hε * N ^ ε :=
    mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)
  have hB : 0 ≤ highKernelNorm M (N / G) K := highKernelNorm_nonneg _ _ _
  have hb (D : Ideal O) (hD : D ∈ S) : ‖gcdBlock D rows cols a‖ ≤
      highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
    have hn : 0 < (Ideal.absNorm D : ℝ) := hG.trans_le (hS D hD)
    have hD0 : D ≠ 0 := by intro hz; simp [hz] at hn
    have hmono := highKernelNorm_mono (M := M) (K := K) (M' := M) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (by linarith : 0 ≤ N) hG (hS D hD)) le_rfl
    exact (highKernel_gcdBlock_bound ε hε D hD0 rows cols hr hc M N K hN hrows hcols a).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hfac) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ D ∈ S, ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (divisor_mask_energy_small_power ε hε S cols (fun j => (hcols j).1.1) N (fun j => (hcols j).2) a)
        (mul_nonneg hB hfac)
    _ = _ := by ring

theorem highKernel_energy_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      (∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖gcdBlock D rows cols a‖) +
      highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := energy_le_gcd_blocks rows cols a
  rw [← Finset.sum_filter_add_sum_filter_not (gcdPool cols) (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_gcd_blocks ε hε _ G hG
    (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    rows cols hr hc M N K hN hrows hcols a))

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

def sectorCoefficient {n r : Type*} [DecidableEq r] (σ : n → r) (c : r) (a : n → ℂ) (j : n) : ℂ :=
  if σ j = c then a j else 0

theorem sectorCoefficient_energy {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (σ : n → r) (a : n → ℂ) :
    (∑ c, ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) = ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (σ j)]
  · simp [sectorCoefficient]
  · intro c hc hne
    simp [sectorCoefficient, Ne.symm hne]
  · simp

private theorem norm_sum_square_card {r : Type*} [Fintype r] (f : r → ℂ) :
    ‖∑ c, f c‖ ^ 2 ≤ (Fintype.card r : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : r => (1 : ℝ)) (fun c => ‖f c‖)
  have hh : ‖∑ c, f c‖ ^ 2 ≤ (∑ c, ‖f c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  exact hh.trans (by simpa using h)

theorem sector_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) :
    (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : (∑ j, A i j * a j) = ∑ c, ∑ j, A i j * sectorCoefficient σ c a j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, Finset.sum_eq_single (σ j)]
    · simp [sectorCoefficient]
    · intro c hc hne
      simp [sectorCoefficient, Ne.symm hne]
    · simp
  calc
    _ ≤ ∑ i, (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [hi]
      exact norm_sum_square_card _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
open FiniteSieveRestriction

def columnRay (I : Ideal O) : EisensteinEPrimaryPhase.Coord := ActualEisensteinCoordinates.residue (primaryGenerator I)

def rayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  gcdBlock D rows cols (sectorCoefficient (fun j => columnRay (cols j)) c a)

theorem rayGcdBlock_eq {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    rayGcdBlock D c rows cols a = ∑ i, ∑ j, ∑ k,
      if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
        star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
          (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0 := by
  unfold rayGcdBlock gcdBlock gcdTerm sectorCoefficient
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : gcd (cols j) (cols k) = D <;>
    by_cases hj : columnRay (cols j) = c <;> by_cases hk : columnRay (cols k) = c <;>
      simp only [hg, hj, hk, ↓reduceIte, true_and, false_and, and_false,
        mul_zero, zero_mul, star_zero]

theorem highKernel_energy_ray_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖rayGcdBlock D c rows cols a‖) +
        highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → EisensteinEPrimaryPhase.Coord := fun j => columnRay (cols j)
  let C := highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2
  have hs := sector_energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) σ a
  have hcard : Fintype.card EisensteinEPrimaryPhase.Coord = 16 := by decide
  rw [hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
        ((∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖rayGcdBlock D c rows cols a‖) + C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_energy_gcd_reduction ε hε G hG rows cols hr hc M N K hN hrows hcols
        (sectorCoefficient σ c a)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end CanonicalQuadraticSieve

namespace FiniteSieveOperator

theorem quadratic_form_bound {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (a : n → ℂ) :
    ‖∑ j, ∑ k, star (a j) * H j k * a k‖ ≤ ‖operator H‖ * ∑ j, ‖a j‖ ^ 2 := by
  let u : EuclideanSpace ℂ n := WithLp.toLp 2 a
  have he : inner ℂ u (operator H u) = ∑ j, ∑ k, star (a j) * H j k * a k := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ j, (∑ k, H j k * a k) * star (a j)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← he]
  calc
    _ ≤ ‖u‖ * ‖operator H u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖operator H‖ * ‖u‖) := mul_le_mul_of_nonneg_left ((operator H).le_opNorm u) (norm_nonneg _)
    _ = ‖operator H‖ * ‖u‖ ^ 2 := by ring
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]
end FiniteSieveOperator

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy

def rayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) : Matrix n n ℂ :=
  fun j k => ∑ i, if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
    star (quadraticRow (cols j) (primaryGenerator (rows i))) *
      quadraticRow (cols k) (primaryGenerator (rows i)) else 0

theorem rayGcdBlock_eq_quadraticForm {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    rayGcdBlock D c rows cols a =
      ∑ j, ∑ k, star (a j) * rayGramMatrix D c rows cols j k * a k := by
  rw [rayGcdBlock_eq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [rayGramMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c
  · simp only [ite_eq_left h, star_mul]
    ring
  · simp only [ite_eq_right h, mul_zero, zero_mul]

theorem rayGcdBlock_norm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    ‖rayGcdBlock D c rows cols a‖ ≤ ‖operator (rayGramMatrix D c rows cols)‖ * ∑ j, ‖a j‖ ^ 2 := by
  rw [rayGcdBlock_eq_quadraticForm]
  exact quadratic_form_bound _ _

def rayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ /
      (∑ J, ‖a J‖ ^ 2)))

def thirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, rayThirdNorm M N K D c

theorem rayThirdNorm_bddAbove (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    BddAbove (Set.range (fun a : idealRange N → ℂ =>
      ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ /
        (∑ J, ‖a J‖ ^ 2))) := by
  refine ⟨‖operator (rayGramMatrix D c (fun I : highKernelRange M K => I.val)
    (fun J : idealRange N => J.val))‖, ?_⟩
  rintro x ⟨a, rfl⟩
  dsimp only
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · rw [← he, div_zero]
    exact norm_nonneg _
  · exact (div_le_iff₀ he).mpr (rayGcdBlock_norm_le D c _ _ a)

theorem rayThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    0 ≤ rayThirdNorm M N K D c := by
  unfold rayThirdNorm
  apply le_csSup (rayThirdNorm_bddAbove M N K D c)
  refine ⟨(fun _ => 0), ?_⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, div_zero]

theorem thirdNorm_nonneg (M N K : ℝ) (D : Ideal O) : 0 ≤ thirdNorm M N K D :=
  Finset.sum_nonneg (fun c _ => rayThirdNorm_nonneg M N K D c)

theorem rayThirdNorm_bound (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ ≤
      rayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · have hb := rayGcdBlock_norm_le D c (fun I : highKernelRange M K => I.val)
      (fun J : idealRange N => J.val) a
    simpa only [← he, mul_zero] using hb
  · exact (div_le_iff₀ he).mp (le_csSup (rayThirdNorm_bddAbove M N K D c)
      (Set.mem_range_self a))

theorem highKernelNorm_le_thirdNorm (M N K G : ℝ) (hN : 1 ≤ N) (hG : 0 < G)
    (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 *
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          thirdNorm M N K D) +
        highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply squared_norm_le_of_energy _ _
  · have hb := highKernelNorm_nonneg M (N / G) K
    have hs := (supportConstant_pos ε hε).le
    have hd := (divisorConstant_pos ε hε).le
    have ht : 0 ≤ ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        thirdNorm M N K D := Finset.sum_nonneg (fun D _ => thirdNorm_nonneg M N K D)
    positivity
  · intro a
    have h := highKernel_energy_ray_gcd_reduction ε hε G hG
      (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val)
      Subtype.val_injective Subtype.val_injective M N K hN (fun I => I.property)
      (fun J => mem_idealRange.mp J.property) a
    apply h.trans
    have hsum : (∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖) ≤
        (∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          thirdNorm M N K D) * ∑ J, ‖a J‖ ^ 2 := by
      calc
        _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
            ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
              rayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum (fun D _ => rayThirdNorm_bound M N K D c a)
        _ = _ := by rw [Finset.sum_comm]; simp only [thirdNorm, Finset.sum_mul]
    nlinarith

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def weightedGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (w : m → ℂ) (a : n → ℂ) : ℂ :=
  ∑ i, w i * ∑ j, ∑ k, gcdTerm D rows cols a i j k

theorem highKernel_weightedGcdBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    ‖weightedGcdBlock D rows cols w a‖ ≤ W * highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K *
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
  let v : m → ℂ := fun i => w i *
    (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i)))
  have hv (i : m) : ‖v i‖ ≤ W := by
    dsimp only [v]
    simp only [norm_mul, norm_star]
    calc
      _ ≤ W * (1 * 1) := by
        apply mul_le_mul (hw i)
        · exact mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one D _) (norm_nonneg _) (by norm_num)
        · positivity
        · exact hW
      _ = W := by ring
  have he : weightedGcdBlock D rows cols w a = ∑ i, v i * ∑ j, ∑ k,
      if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0 := by
    unfold weightedGcdBlock
    simp_rw [gcdTerm_eq_quotient D hD rows cols (fun j => (hcols j).1) a]
    simp only [v, ← Finset.mul_sum, mul_assoc]
  rw [he]
  have hb := ideal_coprime_gram_operator_bound ε hε (fun j => totalQuotient D (cols j))
    (fun j => totalQuotient_ne_zero D _ (hcols j).1) N (by linarith)
    (fun j => totalQuotient_norm_le D _ (hcols j).1 N hN (hcols j).2)
    (quotientMatrix D rows cols) (fun j => if D ∣ cols j then a j else 0) v W hW hv
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (highKernel_quotientMatrix_squared_norm_le D hD rows cols hr hc M N K hrows hcols) hW)
      (mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem highKernel_large_weighted_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (G : ℝ) (hG : 0 < G)
    (hS : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) (a : n → ℂ) :
    (∑ D ∈ S, ‖weightedGcdBlock D rows cols w a‖) ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hfac : 0 ≤ supportConstant ε hε * N ^ ε :=
    mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)
  have hB : 0 ≤ highKernelNorm M (N / G) K := highKernelNorm_nonneg _ _ _
  have hb (D : Ideal O) (hD : D ∈ S) : ‖weightedGcdBlock D rows cols w a‖ ≤
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
    have hn : 0 < (Ideal.absNorm D : ℝ) := hG.trans_le (hS D hD)
    have hD0 : D ≠ 0 := by intro hz; simp [hz] at hn
    have hmono := highKernelNorm_mono (M := M) (K := K) (M' := M) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (by linarith : 0 ≤ N) hG (hS D hD)) le_rfl
    exact (highKernel_weightedGcdBlock_bound ε hε D hD0 rows cols hr hc M N K hN hrows hcols w W hW hw a).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hW) hfac) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ∑ D ∈ S, ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ W * highKernelNorm M (N / G) K * (supportConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (divisor_mask_energy_small_power ε hε S cols (fun j => (hcols j).1.1) N (fun j => (hcols j).2) a)
        (mul_nonneg (mul_nonneg hW hB) hfac)
    _ = _ := by ring

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction

theorem sector_weighted_energy_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (A : Matrix m n ℂ) (σ : n → r) (a : n → ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (∑ i, v i * ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, v i * ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hi (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤
      (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
    simpa only [Fintype.sum_unique] using sector_energy_bound (fun _ : Unit => A i) σ a
  calc
    _ ≤ ∑ i, v i * ((Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hv i))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

theorem weighted_energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) :
    ((∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a := by
  have hi (i : m) : ((‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k := by
    simpa only [gcdBlock, Fintype.sum_unique, gcdTerm] using energy_eq_gcd_blocks (fun _ : Unit => rows i) cols a
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hi, Finset.mul_sum, weightedGcdBlock]
  rw [Finset.sum_comm]

theorem weighted_energy_le_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      ∑ D ∈ gcdPool cols, ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖ := by
  have he := congrArg norm (weighted_energy_eq_gcd_blocks rows cols v a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _)))] at he
  rw [he]
  exact norm_sum_le _ _

theorem highKernel_weighted_energy_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      (∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        ‖weightedGcdBlock D rows cols (fun i => (v i : ℂ)) a‖) +
      W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
        (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := weighted_energy_le_gcd_blocks rows cols v (fun i => (hv i).1) a
  rw [← Finset.sum_filter_add_sum_filter_not (gcdPool cols) (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_weighted_gcd_blocks ε hε _ G hG
    (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    rows cols hr hc M N K hN hrows hcols (fun i => (v i : ℂ)) W hW
    (fun i => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv i).1] using (hv i).2) a))

def weightedRayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) : ℂ :=
  weightedGcdBlock D rows cols (fun i => (v i : ℂ))
    (sectorCoefficient (fun j => columnRay (cols j)) c a)

theorem highKernel_weighted_energy_ray_gcd_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (G : ℝ) (hG : 0 < G)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (v : m → ℝ) (W : ℝ) (hW : 0 ≤ W) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ W) (a : n → ℂ) :
    (∑ i, v i * ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G), ‖weightedRayGcdBlock D c rows cols v a‖) +
        W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2) := by
  let σ : n → EisensteinEPrimaryPhase.Coord := fun j => columnRay (cols j)
  let C := W * highKernelNorm M (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2
  have hs := sector_weighted_energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) σ a v (fun i => (hv i).1)
  have hcard : Fintype.card EisensteinEPrimaryPhase.Coord = 16 := by decide
  rw [hcard] at hs
  norm_num only [Nat.cast_ofNat] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
        ((∑ D ∈ (gcdPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖weightedRayGcdBlock D c rows cols v a‖) + C * ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact highKernel_weighted_energy_gcd_reduction ε hε G hG rows cols hr hc M N K hN hrows hcols v W hW hv
        (sectorCoefficient σ c a)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, sectorCoefficient_energy]

end

open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def smoothHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.sieveBump ((Ideal.absNorm I : ℝ) / M)

def smoothHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, smoothHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2

theorem highKernel_energy_le_smooth (M N K : ℝ) (hM : 0 < M) (a : idealRange N → ℂ) :
    (∑ I : highKernelRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      smoothHighEnergy M N K a := by
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hsub : highKernelRange M K ⊆ highKernelRange (2 * M) K := by
    intro I hI
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp hI
    exact mem_highKernelRange.mpr ⟨hs, by linarith, hk⟩
  have hv (I : Ideal O) (hI : I ∈ highKernelRange M K) : smoothHighWeight M I = 1 := by
    apply QuadraticInitialBound.sieveBump_eq_one (div_nonneg (Nat.cast_nonneg _) hM.le)
    exact (div_le_one hM).mpr (mem_highKernelRange.mp hI).2.1
  change (∑ I : highKernelRange M K, E I.val) ≤
    ∑ I : highKernelRange (2 * M) K, smoothHighWeight M I.val * E I.val
  rw [Finset.sum_coe_sort (highKernelRange M K) E,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => smoothHighWeight M I * E I)]
  calc
    _ = ∑ I ∈ highKernelRange M K, smoothHighWeight M I * E I :=
      Finset.sum_congr rfl (fun I hI => by rw [hv I hI, one_mul])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _))

def smoothRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val) a

theorem highKernel_energy_smooth_gcd_reduction (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) (a : idealRange N → ℂ) :
    (∑ I : highKernelRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖smoothRayGcdBlock M N K D c a‖) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ J, ‖a J‖ ^ 2) := by
  apply (highKernel_energy_le_smooth M N K hM a).trans
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε G hG
    (fun I : highKernelRange (2 * M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2 * M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => smoothHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.sieveBump.nonneg, QuadraticInitialBound.sieveBump.le_one⟩) a
  simpa only [smoothHighEnergy, smoothRayGcdBlock, one_mul] using h

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0129

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion
Source SHA256: 6e09a66a8f79fcd654bd40e49bb288b739e70d1ed2e4fb294543ef45de71ebd1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0130


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

def weightedRayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O)
    (v : m → ℝ) : Matrix n n ℂ :=
  fun j k => ∑ i, (v i : ℂ) *
    (if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
      star (quadraticRow (cols j) (primaryGenerator (rows i))) *
        quadraticRow (cols k) (primaryGenerator (rows i)) else 0)

theorem weightedRayGcdBlock_eq_quadraticForm {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O)
    (v : m → ℝ) (a : n → ℂ) :
    weightedRayGcdBlock D c rows cols v a =
      ∑ j, ∑ k, star (a j) * weightedRayGramMatrix D c rows cols v j k * a k := by
  unfold weightedRayGcdBlock weightedGcdBlock
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [weightedRayGramMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  unfold gcdTerm sectorCoefficient
  by_cases hg : gcd (cols j) (cols k) = D <;>
    by_cases hj : columnRay (cols j) = c <;> by_cases hk : columnRay (cols k) = c <;>
      simp only [hg, hj, hk, ↓reduceIte, true_and, false_and, and_false,
        mul_zero, zero_mul, star_zero, star_mul] ; ring

theorem smoothRayGcdBlock_norm_le (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖smoothRayGcdBlock M N K D c a‖ ≤
      ‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
        (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val))‖ * ∑ J, ‖a J‖ ^ 2 := by
  unfold smoothRayGcdBlock
  rw [weightedRayGcdBlock_eq_quadraticForm]
  exact quadratic_form_bound _ _

def smoothRayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖smoothRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2)))

def smoothThirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, smoothRayThirdNorm M N K D c

theorem smoothRayThirdNorm_bddAbove (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    BddAbove (Set.range (fun a : idealRange N → ℂ =>
      ‖smoothRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2))) := by
  refine ⟨‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val))‖, ?_⟩
  rintro x ⟨a, rfl⟩
  dsimp only
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · rw [← he, div_zero]
    exact norm_nonneg _
  · exact (div_le_iff₀ he).mpr (smoothRayGcdBlock_norm_le M N K D c a)

theorem smoothRayThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    0 ≤ smoothRayThirdNorm M N K D c := by
  unfold smoothRayThirdNorm
  apply le_csSup (smoothRayThirdNorm_bddAbove M N K D c)
  refine ⟨(fun _ => 0), ?_⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, div_zero]

theorem smoothThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) : 0 ≤ smoothThirdNorm M N K D :=
  Finset.sum_nonneg (fun c _ => smoothRayThirdNorm_nonneg M N K D c)

theorem smoothRayThirdNorm_bound (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖smoothRayGcdBlock M N K D c a‖ ≤ smoothRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · have hb := smoothRayGcdBlock_norm_le M N K D c a
    simpa only [← he, mul_zero] using hb
  · exact (div_le_iff₀ he).mp (le_csSup (smoothRayThirdNorm_bddAbove M N K D c) (Set.mem_range_self a))

theorem highKernelNorm_le_smoothThirdNorm (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 *
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          smoothThirdNorm M N K D) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply squared_norm_le_of_energy _ _
  · have hb := highKernelNorm_nonneg (2 * M) (N / G) K
    have hs := (supportConstant_pos ε hε).le
    have hd := (divisorConstant_pos ε hε).le
    have ht : 0 ≤ ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        smoothThirdNorm M N K D := Finset.sum_nonneg (fun D _ => smoothThirdNorm_nonneg M N K D)
    positivity
  · intro a
    have h := highKernel_energy_smooth_gcd_reduction M N K G hM hN hG ε hε a
    apply h.trans
    have hsum : (∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖smoothRayGcdBlock M N K D c a‖) ≤
        (∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          smoothThirdNorm M N K D) * ∑ J, ‖a J‖ ^ 2 := by
      calc
        _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
            ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
              smoothRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum (fun D _ => smoothRayThirdNorm_bound M N K D c a)
        _ = _ := by rw [Finset.sum_comm]; simp only [smoothThirdNorm, Finset.sum_mul]
    nlinarith

end

section
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

def rayPairValue (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) : ℂ :=
  ∑ J : idealRange N, ∑ lengthScale : idealRange N,
    gcdTerm D (fun _ : Unit => I) (fun J : idealRange N => J.val)
      (sectorCoefficient (fun J : idealRange N => columnRay J.val) c a) () J lengthScale

theorem rayPairValue_eq (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) :
    rayPairValue N D c a I = ∑ J : idealRange N, ∑ lengthScale : idealRange N,
      if gcd J.val lengthScale.val = D ∧ columnRay J.val = c ∧ columnRay lengthScale.val = c then
        star (quadraticRow J.val (primaryGenerator I) * a J) *
          (quadraticRow lengthScale.val (primaryGenerator I) * a lengthScale) else 0 := by
  simpa only [rayPairValue, rayGcdBlock, gcdBlock, Fintype.sum_unique, gcdTerm] using
    rayGcdBlock_eq D c (fun _ : Unit => I) (fun J : idealRange N => J.val) a

theorem smoothHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2 * M ≤ (Ideal.absNorm I : ℝ)) : smoothHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ) / M := (le_div_iff₀ hM).mpr (by linarith)
  have hnonneg : 0 ≤ (Ideal.absNorm I : ℝ) / M := div_nonneg (Nat.cast_nonneg _) hM.le
  by_contra hn
  have hm : (Ideal.absNorm I : ℝ) / M ∈ Function.support QuadraticInitialBound.sieveBump := hn
  rw [QuadraticInitialBound.sieveBump.support_eq] at hm
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hm
  change (Ideal.absNorm I : ℝ) / M < 2 at hm
  linarith

theorem smoothRayGcdBlock_eq_finite (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    smoothRayGcdBlock M N K D c a =
      ∑ I : highKernelRange (2 * M) K, (smoothHighWeight M I.val : ℂ) * rayPairValue N D c a I.val := by
  rfl

theorem smoothRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    smoothRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.sieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by
  rw [smoothRayGcdBlock_eq_finite,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => (smoothHighWeight M I : ℂ) * rayPairValue N D c a I)]
  symm
  rw [tsum_eq_sum (s := highKernelRange (2 * M) K) (fun I hI => ?_)]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
      have h := mem_highKernelRange.mp hI
      exact ⟨h.1, h.2.2⟩
    rw [ite_eq_left hp, QuadraticInitialBound.sieveCutoff_apply]
    rfl
  · by_cases hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ)
    · have hn : 2 * M < (Ideal.absNorm I : ℝ) := by
        by_contra hh
        exact hI (mem_highKernelRange.mpr ⟨hp.1, le_of_not_gt hh, hp.2⟩)
      rw [ite_eq_left hp, QuadraticInitialBound.sieveCutoff_apply]
      change (smoothHighWeight M I : ℂ) * _ = 0
      rw [smoothHighWeight_eq_zero M hM I hn.le]
      simp
    · exact ite_eq_right hp

end

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

def highKernelShellRange (M K : ℝ) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => M / 2 < (Ideal.absNorm I : ℝ))

theorem mem_highKernelShellRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelShellRange M K ↔ I ∈ highKernelRange M K ∧ M / 2 < (Ideal.absNorm I : ℝ) :=
  Finset.mem_filter

def highKernelShellMatrix (M N K : ℝ) : Matrix (highKernelShellRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def highKernelShellNorm (M N K : ℝ) : ℝ := ‖operator (highKernelShellMatrix M N K)‖ ^ 2

theorem highKernelShellNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelShellNorm M N K := sq_nonneg _

theorem exists_dyadic_shell (n lengthScale : ℕ) (hn : 1 ≤ n) (hL : (n : ℝ) ≤ (2 : ℝ) ^ lengthScale) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ (2 : ℝ) ^ j := by
  have hex : ∃ j : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ j := ⟨lengthScale, hL⟩
  let j := Nat.find hex
  have hj : (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ lengthScale := Nat.find_min' hex hL
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, hj⟩
  have hjfind : j = Nat.find hex := rfl
  rcases j with _ | j
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · have hprev : ¬ (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_min hex (by omega)
    have hp := lt_of_not_ge hprev
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp

theorem highKernel_dyadic_cover (M K : ℝ) (lengthScale : ℕ) (hML : M ≤ (2 : ℝ) ^ lengthScale)
    (I : Ideal O) (hI : I ∈ highKernelRange M K) :
    ∃ j ∈ Finset.range (lengthScale + 1), I ∈ highKernelShellRange ((2 : ℝ) ^ j) K := by
  obtain ⟨hs, hN, hk⟩ := mem_highKernelRange.mp hI
  have hn : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hs.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨j, hj, hlo, hhi⟩ := exists_dyadic_shell (Ideal.absNorm I) lengthScale hn (hN.trans hML)
  exact ⟨j, hj, mem_highKernelShellRange.mpr ⟨mem_highKernelRange.mpr ⟨hs, hhi, hk⟩, hlo⟩⟩

theorem highKernelNorm_le_dyadic_shells (M N K : ℝ) (lengthScale : ℕ) (hML : M ≤ (2 : ℝ) ^ lengthScale) :
    highKernelNorm M N K ≤ ∑ j ∈ Finset.range (lengthScale + 1), highKernelShellNorm ((2 : ℝ) ^ j) N K := by
  apply squared_norm_le_of_energy _ _ (Finset.sum_nonneg (fun j _ => highKernelShellNorm_nonneg _ _ _))
  intro a
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hE (I : Ideal O) : 0 ≤ E I := sq_nonneg _
  change (∑ I : highKernelRange M K, E I.val) ≤ _
  rw [Finset.sum_coe_sort (highKernelRange M K) E]
  calc
    _ ≤ ∑ I ∈ highKernelRange M K, ∑ j ∈ Finset.range (lengthScale + 1),
        if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨j, hj, hIj⟩ := highKernel_dyadic_cover M K lengthScale hML I hI
      have h := Finset.single_le_sum (s := Finset.range (lengthScale + 1))
        (f := fun j => if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0)
        (fun _ _ => by split_ifs <;> positivity) hj
      simpa only [ite_eq_left hIj] using h
    _ = ∑ j ∈ Finset.range (lengthScale + 1), ∑ I ∈ highKernelRange M K,
        if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0 := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (lengthScale + 1), ∑ I ∈ highKernelShellRange ((2 : ℝ) ^ j) K, E I := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro I hI
        exact (Finset.mem_filter.mp hI).2
      · intro I hI hnot
        exact hE I
    _ ≤ ∑ j ∈ Finset.range (lengthScale + 1), highKernelShellNorm ((2 : ℝ) ^ j) N K * ∑ J, ‖a J‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_coe_sort (highKernelShellRange ((2 : ℝ) ^ j) K) E]
      exact FiniteSieveOperator.energy_bound (highKernelShellMatrix ((2 : ℝ) ^ j) N K) a
    _ = _ := (Finset.sum_mul ..).symm

end CanonicalQuadraticSieve

open scoped SchwartzMap ContDiff
namespace QuadraticInitialBound

def annularSieveBump : ContDiffBump (3 / 4 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def annularSieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    annularSieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annularSieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem annularSieveCutoff_apply (t : ℝ) : annularSieveCutoff t = (annularSieveBump t : ℂ) := rfl

theorem annularSieveBump_eq_one {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) : annularSieveBump t = 1 := by
  apply annularSieveBump.one_of_mem_closedBall
  change dist t (3 / 4) ≤ 1 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

theorem annularSieveBump_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem annularSieveBump_zero_of_ge {t : ℝ} (ht : 5 / 4 ≤ t) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

@[simp] theorem annularSieveCutoff_zero : annularSieveCutoff 0 = 0 := by
  rw [annularSieveCutoff_apply, annularSieveBump_zero_of_le (by norm_num), Complex.ofReal_zero]

end QuadraticInitialBound

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def annularHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.annularSieveBump ((Ideal.absNorm I : ℝ) / M)

def annularHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2

theorem highKernelShell_energy_le_annular (M N K : ℝ) (hM : 0 < M) (a : idealRange N → ℂ) :
    (∑ I : highKernelShellRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      annularHighEnergy M N K a := by
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hsub : highKernelShellRange M K ⊆ highKernelRange (2 * M) K := by
    intro I hI
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp (mem_highKernelShellRange.mp hI).1
    exact mem_highKernelRange.mpr ⟨hs, by linarith, hk⟩
  have hv (I : Ideal O) (hI : I ∈ highKernelShellRange M K) : annularHighWeight M I = 1 := by
    apply QuadraticInitialBound.annularSieveBump_eq_one
    · apply (le_div_iff₀ hM).mpr
      have h := (mem_highKernelShellRange.mp hI).2
      linarith
    · exact (div_le_one hM).mpr (mem_highKernelRange.mp (mem_highKernelShellRange.mp hI).1).2.1
  change (∑ I : highKernelShellRange M K, E I.val) ≤
    ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val * E I.val
  rw [Finset.sum_coe_sort (highKernelShellRange M K) E,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => annularHighWeight M I * E I)]
  calc
    _ = ∑ I ∈ highKernelShellRange M K, annularHighWeight M I * E I :=
      Finset.sum_congr rfl (fun I hI => by rw [hv I hI, one_mul])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (sq_nonneg _))

def annularRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val) a

theorem highKernelShell_energy_annular_gcd_reduction (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) (a : idealRange N → ℂ) :
    (∑ I : highKernelShellRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖annularRayGcdBlock M N K D c a‖) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ J, ‖a J‖ ^ 2) := by
  apply (highKernelShell_energy_le_annular M N K hM a).trans
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε G hG
    (fun I : highKernelRange (2 * M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2 * M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.annularSieveBump.nonneg, QuadraticInitialBound.annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy, annularRayGcdBlock, one_mul] using h

end

section
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

theorem annularRayGcdBlock_norm_le (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖annularRayGcdBlock M N K D c a‖ ≤
      ‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
        (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val))‖ * ∑ J, ‖a J‖ ^ 2 := by
  unfold annularRayGcdBlock
  rw [weightedRayGcdBlock_eq_quadraticForm]
  exact quadratic_form_bound _ _

def annularRayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖annularRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2)))

def annularThirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, annularRayThirdNorm M N K D c

theorem annularRayThirdNorm_bddAbove (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    BddAbove (Set.range (fun a : idealRange N → ℂ =>
      ‖annularRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2))) := by
  refine ⟨‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val))‖, ?_⟩
  rintro x ⟨a, rfl⟩
  dsimp only
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · rw [← he, div_zero]
    exact norm_nonneg _
  · exact (div_le_iff₀ he).mpr (annularRayGcdBlock_norm_le M N K D c a)

theorem annularRayThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    0 ≤ annularRayThirdNorm M N K D c := by
  unfold annularRayThirdNorm
  apply le_csSup (annularRayThirdNorm_bddAbove M N K D c)
  refine ⟨(fun _ => 0), ?_⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, div_zero]

theorem annularThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) : 0 ≤ annularThirdNorm M N K D :=
  Finset.sum_nonneg (fun c _ => annularRayThirdNorm_nonneg M N K D c)

theorem annularRayThirdNorm_bound (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖annularRayGcdBlock M N K D c a‖ ≤ annularRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · have hb := annularRayGcdBlock_norm_le M N K D c a
    simpa only [← he, mul_zero] using hb
  · exact (div_le_iff₀ he).mp (le_csSup (annularRayThirdNorm_bddAbove M N K D c) (Set.mem_range_self a))

theorem highKernelShellNorm_le_annularThirdNorm (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelShellNorm M N K ≤ 16 *
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm M N K D) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply squared_norm_le_of_energy _ _
  · have hb := highKernelNorm_nonneg (2 * M) (N / G) K
    have hs := (supportConstant_pos ε hε).le
    have hd := (divisorConstant_pos ε hε).le
    have ht : 0 ≤ ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        annularThirdNorm M N K D := Finset.sum_nonneg (fun D _ => annularThirdNorm_nonneg M N K D)
    positivity
  · intro a
    have h := highKernelShell_energy_annular_gcd_reduction M N K G hM hN hG ε hε a
    apply h.trans
    have hsum : (∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖annularRayGcdBlock M N K D c a‖) ≤
        (∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm M N K D) * ∑ J, ‖a J‖ ^ 2 := by
      calc
        _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
            ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
              annularRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum (fun D _ => annularRayThirdNorm_bound M N K D c a)
        _ = _ := by rw [Finset.sum_comm]; simp only [annularThirdNorm, Finset.sum_mul]
    nlinarith

end

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

theorem annularHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2 * M ≤ (Ideal.absNorm I : ℝ)) : annularHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ) / M := (le_div_iff₀ hM).mpr (by linarith)
  exact QuadraticInitialBound.annularSieveBump_zero_of_ge (by linarith)

theorem annularRayGcdBlock_eq_finite (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : highKernelRange (2 * M) K, (annularHighWeight M I.val : ℂ) * rayPairValue N D c a I.val := by
  rfl

theorem annularRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.annularSieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by
  rw [annularRayGcdBlock_eq_finite,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => (annularHighWeight M I : ℂ) * rayPairValue N D c a I)]
  symm
  rw [tsum_eq_sum (s := highKernelRange (2 * M) K) (fun I hI => ?_)]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
      have h := mem_highKernelRange.mp hI
      exact ⟨h.1, h.2.2⟩
    rw [ite_eq_left hp, QuadraticInitialBound.annularSieveCutoff_apply]
    rfl
  · by_cases hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ)
    · have hn : 2 * M < (Ideal.absNorm I : ℝ) := by
        by_contra hh
        exact hI (mem_highKernelRange.mpr ⟨hp.1, le_of_not_gt hh, hp.2⟩)
      rw [ite_eq_left hp, QuadraticInitialBound.annularSieveCutoff_apply]
      change (annularHighWeight M I : ℂ) * _ = 0
      rw [annularHighWeight_eq_zero M hM I hn.le]
      simp
    · exact ite_eq_right hp

end CanonicalQuadraticSieve

namespace FiniteSieveOperator

theorem bounded_entry_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖operator A‖ ^ 2 ≤ (Fintype.card m : ℝ) * Fintype.card n := by
  apply squared_norm_le_of_energy _ _ (by positivity)
  intro a
  have hi (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤ (Fintype.card n : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
    have hs : ‖∑ j, A i j * a j‖ ≤ ∑ j, ‖a j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hA i j)
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : n => (1 : ℝ)) (fun j => ‖a j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans (by simpa using hc)
  calc
    _ ≤ ∑ i : m, (Fintype.card n : ℝ) * ∑ j, ‖a j‖ ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end FiniteSieveOperator

namespace CanonicalQuadraticSieve

section
open FiniteSieveOperator

theorem highKernelNorm_trivial (M N K : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    highKernelNorm M N K ≤ 128 ^ 2 * M * N := by
  have hr := DescentFiberCost.finite_ideal_count_real (highKernelRange M K) M hM
    (fun I hI => (mem_highKernelRange.mp hI).1.1)
    (fun I hI => (mem_highKernelRange.mp hI).2.1)
  have hc := DescentFiberCost.finite_ideal_count_real (idealRange N) N hN
    (fun I hI => (mem_idealRange.mp hI).1.1)
    (fun I hI => (mem_idealRange.mp hI).2)
  have hb := bounded_entry_squared_norm_le (highKernelMatrix M N K)
    (fun I J => quadraticRow_norm_le_one J.val _)
  change highKernelNorm M N K ≤ _ at hb
  apply hb.trans
  simp only [Fintype.card_coe]
  calc
    _ ≤ (128 * M) * (128 * N) := mul_le_mul hr hc (by positivity) (by positivity)
    _ = _ := by ring

theorem highKernelNorm_short_columns (M N K : ℝ) (hM : 1 ≤ M) (hN : N ≤ 1) :
    highKernelNorm M N K ≤ 128 ^ 2 * M := by
  exact (highKernelNorm_mono (M := M) (K := K) le_rfl hN le_rfl).trans
    (by simpa only [mul_one] using highKernelNorm_trivial M 1 K hM le_rfl)

end

open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem highKernelNorm_le_annular_recursion (M N K G : ℝ) (lengthScale : ℕ)
    (hML : M ≤ (2 : ℝ) ^ lengthScale) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 * ∑ j ∈ Finset.range (lengthScale + 1),
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm ((2 : ℝ) ^ j) N K D) +
        highKernelNorm (2 * (2 : ℝ) ^ j) (N / G) K *
          (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply (highKernelNorm_le_dyadic_shells M N K lengthScale hML).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j hj => highKernelShellNorm_le_annularThirdNorm
    ((2 : ℝ) ^ j) N K G (by positivity) hN hG ε hε)

theorem sieveNorm_le_annular_recursion (M N K G : ℝ) (lengthScale : ℕ)
    (hML : M ≤ (2 : ℝ) ^ lengthScale) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    sieveNorm M N ≤ sieveNorm K N + 16 * ∑ j ∈ Finset.range (lengthScale + 1),
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm ((2 : ℝ) ^ j) N K D) +
        highKernelNorm (2 * (2 : ℝ) ^ j) (N / G) K *
          (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  exact (sieveNorm_le_low_add_high M N K).trans
    (add_le_add le_rfl (highKernelNorm_le_annular_recursion M N K G lengthScale hML hN hG ε hε))

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0130

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
Source SHA256: 626604988296f8e449a2d6d35853bc30bf2e12a1c11993daa272bf19f4d45666
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0131



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

instance canonicalPoolMaximal (F : Finset (Ideal O)) (i : primePool F) : i.val.IsMaximal := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem poolGood (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ i.val := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).1

theorem poolOdd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    ringChar (O ⧸ i.val) ≠ 2 := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).2

def poolPrimary (F : Finset (Ideal O)) (i : primePool F) : O := primaryPrime i.val

theorem poolPrimary_ne_zero (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : poolPrimary F i ≠ 0 := primaryPrime_ne_zero i.val (poolGood F hF i)

theorem poolPrimary_span (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : Ideal.span {poolPrimary F i} = i.val :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.1

theorem primaryPrime_eq_primaryGenerator (P : Ideal O) [P.IsMaximal] :
    primaryPrime P = primaryGenerator P := by
  have hp : Prime P := Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  rw [primaryGenerator, ite_eq_right hp.ne_zero, UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
    normalize_eq]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

theorem primaryGenerator_eq_poolProduct (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) :
    primaryGenerator I = ∏ i ∈ idealSupport F I, poolPrimary F i := by
  calc
    _ = primaryGenerator (∏ i ∈ idealSupport F I, i.val) :=
      congrArg primaryGenerator (idealSupport_product_eq F hIF (hF I hIF).2.1).symm
    _ = ∏ i ∈ idealSupport F I, primaryGenerator i.val := by
      change primaryGeneratorHom (∏ i ∈ idealSupport F I, i.val) =
        ∏ i ∈ idealSupport F I, primaryGeneratorHom i.val
      rw [map_prod]
    _ = _ := Finset.prod_congr rfl (fun i hi => (primaryPrime_eq_primaryGenerator i.val).symm)

theorem quadraticRow_eq_pool (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    quadraticRow I z = QuadraticInitialBound.quadraticRow
      (fun i : primePool F => i.val) (poolGood F hF) (idealSupport F I) z := by
  rw [quadraticRow_eq F hF I hIF z]
  rfl

theorem poolPrimary_coprime (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) :
    Pairwise (Function.onFun IsCoprime (fun i : primePool F => Ideal.span {poolPrimary F i})) := by
  intro i j hij
  change IsCoprime (Ideal.span {poolPrimary F i}) (Ideal.span {poolPrimary F j})
  rw [poolPrimary_span F hF i, poolPrimary_span F hF j]
  exact Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))

theorem poolPrimary_good (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ Ideal.span {poolPrimary F i} := by rw [poolPrimary_span F hF i]; exact poolGood F hF i

theorem poolPrimary_odd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    ringChar (O ⧸ Ideal.span {poolPrimary F i}) ≠ 2 := by rw [poolPrimary_span F hF i]; exact poolOdd F hF i

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates

theorem quadraticRow_eq_primaryPool (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    quadraticRow I z = QuadraticInitialBound.quadraticRow
      (fun i : primePool F => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF) (idealSupport F I) z := by
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) = (fun i : primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  simpa only [he] using quadraticRow_eq_pool F hF I hIF z

theorem quadraticRow_eq_primeSubset (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    quadraticRow I z = finiteSexticRow
      (fun i : idealSupport F I => i.val.val) (fun i => poolGood F hF i.val) (fun _ => 3) z := by
  rw [quadraticRow_eq_pool F hF I hIF z, QuadraticInitialBound.quadraticRow_eq_canonical]

theorem idealSupport_disjoint_of_coprime (F : Finset (Ideal O)) (I J : Ideal O)
    (hIJ : IsCoprime I J) : Disjoint (idealSupport F I) (idealSupport F J) := by
  apply Finset.disjoint_left.mpr
  intro P hPI hPJ
  have hi := (mem_idealSupport_iff F I P).mp hPI
  have hj := (mem_idealSupport_iff F J P).mp hPJ
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hi
  exact hp.not_isUnit (hIJ.isRelPrime
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hi)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hj))

theorem primaryGenerator_unit_mod_four (I : Ideal O) (hI : Admissible I) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I)) := by
  let F : Finset (Ideal O) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have hJI : J = I := Finset.mem_singleton.mp hJ
    simpa only [hJI] using hI
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [primaryGenerator_eq_poolProduct F hF I (Finset.mem_singleton_self I)]
  exact RayFourExpansion.prime_product_unit_mod_four (poolPrimary F) (poolPrimary_odd F hF) _

theorem columnRay_idealQuotient_eq (D I J : Ideal O) (hI : Admissible I) (_hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : columnRay I = columnRay J) :
    columnRay (idealQuotient D I) = columnRay (idealQuotient D J) := by
  have hD : Admissible D := admissible_of_dvd hI hDI
  have hu := primaryGenerator_unit_mod_four D hD
  obtain ⟨u, hu⟩ := hu
  have hray : residue (primaryGenerator I) = residue (primaryGenerator J) := hIJ
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq hray
  have hquot : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator J) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨z, hz⟩
  have hprodI : primaryGenerator I = primaryGenerator D * primaryGenerator (idealQuotient D I) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDI]
  have hprodJ : primaryGenerator J = primaryGenerator D * primaryGenerator (idealQuotient D J) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDJ]
  rw [hprodI, hprodJ, map_mul, map_mul, ← hu] at hquot
  have heq := (Units.mul_right_inj u).mp hquot
  exact QuadraticGaussRay.residue_eq_of_quotient_four_eq _ _ heq

end
section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem quadraticRow_eq_primarySubset (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    quadraticRow I z = finiteSexticRow
      (fun i : idealSupport F I => Ideal.span {poolPrimary F i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) z := by
  have he : (fun i : idealSupport F I => Ideal.span {poolPrimary F i.val}) =
      (fun i : idealSupport F I => i.val.val) := funext (fun i => poolPrimary_span F hF i.val)
  simpa only [he] using quadraticRow_eq_primeSubset F hF I hIF z

end

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem quadraticRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    quadraticRow I 0 = 0 := by
  let F : Finset (Ideal O) := {I}
  have hIF : I ∈ F := Finset.mem_singleton_self I
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have hJI := Finset.mem_singleton.mp hJ
    simpa only [hJI] using hI
  have hS : (idealSupport F I).Nonempty := by
    by_contra hn
    have he : idealSupport F I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp := idealSupport_product_eq F hIF hI.2.1
    rw [he, Finset.prod_empty] at hp
    exact hI1 hp.symm
  let : Nonempty (idealSupport F I) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  rw [quadraticRow_eq_primeSubset F hF I hIF]
  exact finiteSexticRow_zero _ _ _

theorem quadratic_pair_zero_of_nontrivial (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (h : I ≠ 1 ∨ J ≠ 1) : quadraticRow I 0 * quadraticRow J 0 = 0 := by
  rcases h with h | h
  · rw [quadraticRow_zero_of_ne_one I hI h, zero_mul]
  · rw [quadraticRow_zero_of_ne_one J hJ h, mul_zero]

theorem quadratic_pair_tsum_remove_zero (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (h : I ≠ 1 ∨ J ≠ 1) (f : O → ℂ) :
    (∑' z : O, quadraticRow I z * quadraticRow J z * f z) =
      ∑' z : O, if z = 0 then 0 else quadraticRow I z * quadraticRow J z * f z := by
  apply tsum_congr
  intro z
  by_cases hz : z = 0
  · subst z
    rw [quadratic_pair_zero_of_nontrivial I J hI hJ h, zero_mul, ite_eq_left rfl]
  · rw [ite_eq_right hz]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def radialPairKernel (e k : O) (W : 𝓢(ℝ, ℂ))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (S T : Finset ι) : ℂ :=
  star (normalizedColumn p (fun U => V₁ (columnLog p X₁ U)) S) *
    normalizedColumn p (fun U => V₂ (columnLog p X₂ U)) T *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p S * primeProductNorm p T))

theorem actualSecondKernel_eq_coupled
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) :
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (radialPairKernel p e k W V₁ V₂ X₁ X₂ Y) := by
  simp only [actualSecondKernel, secondKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, radialPairKernel, normalizedColumn,
      FirstPassCubeLabels.primeProductNorm_union p S T hd, Finset.prod_union hd,
      map_mul, norm_mul, Complex.ofReal_mul,  Complex.star_def,
      Complex.conj_ofReal, div_eq_mul_inv, mul_inv_rev, map_inv₀]
    ring_nf
  · simp [hd]

theorem secondChildKernelPair_fixed_pool
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
        star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M * K (V∪N) (V∪M) := by
  have hzero (N : Finset ι) (hNF : N ∈ F.powerset)
      (hNV : N ∉ (F \ V).powerset) : ¬ Disjoint V N := by
    intro hd
    apply hNV
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hNF) hi,
      fun hiv => Finset.disjoint_left.mp hd hiv hi⟩
  unfold secondChildKernelPair
  calc
    _ = ∑ N ∈ (F \ V).powerset, ∑ M ∈ F.powerset,
        star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M * K (V∪N) (V∪M) := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro M hMF hMV
      rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₂ (m*r) c e
        (d*e*k₂) (fun _ => 1) V M (hzero M hMF hMV), mul_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro N hNF hNV
      rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₁ (m*r) c e
        (d*e*k₁) (fun _ => 1) V N (hzero N hNF hNV), star_zero]
      simp only [zero_mul, Finset.sum_const_zero]

theorem actualSecondKernel_eq_coupled_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) :
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) (radialPairKernel p e k W V₁ V₂ X₁ X₂ Y) := by
  rw [actualSecondKernel_eq_coupled,
    secondKernelPair_eq_children p hp hcop hg hinj hc hpr]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

def elementNorm (a : O) : ℝ := ‖eisEmbedding a‖ ^ 2

lemma elementNorm_pos (a : O) (ha : a ≠ 0) : 0 < elementNorm a := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))

lemma elementNorm_mul (a b : O) : elementNorm (a*b) = elementNorm a * elementNorm b := by
  simp only [elementNorm, map_mul, norm_mul, mul_pow]

theorem seven_radial_ratio (d e v n₁ n₂ k D E V X K Y : ℝ)
    (hd : 0 < d) (he : 0 < e) (hv : 0 < v) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hk : 0 < k) (hD : 0 < D) (hE : 0 < E) (hV : 0 < V) (hX : 0 < X) (hK : 0 < K) :
    Y * k / (e * v ^ 2 * n₁ * n₂) =
      (Y * K / (D * E ^ 2 * V ^ 2 * X ^ 2)) * Real.exp
        (Real.log (d*e*k/K) - Real.log (d/D) - 2*Real.log (e/E) -
          2*Real.log (v/V) - Real.log (n₁/X) - Real.log (n₂/X)) := by
  rw [show 2 * Real.log (e/E) = Real.log (e/E) + Real.log (e/E) by ring,
    show 2 * Real.log (v/V) = Real.log (v/V) + Real.log (v/V) by ring]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hd hD),
    Real.exp_log (div_pos he hE), Real.exp_log (div_pos hv hV),
    Real.exp_log (div_pos hn₁ hX), Real.exp_log (div_pos hn₂ hX),
    Real.exp_log (div_pos (mul_pos (mul_pos hd he) hk) hK)]
  field_simp

theorem second_radial_dyadic_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N M : Finset ι)
    (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX₀ : 0 < X₀) (hK : 0 < K) :
    Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (V∪N) * primeProductNorm p (V∪M)) =
      (Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
        (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
          2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
          columnLog p X₀ N - columnLog p X₀ M) := by
  rw [primeProductNorm_union p V N hVN, primeProductNorm_union p V M hVM]
  simp only [elementNorm_mul, columnLog]
  have h := seven_radial_ratio (elementNorm d) (elementNorm e) (primeProductNorm p V)
    (primeProductNorm p N) (primeProductNorm p M) (elementNorm k) D E V₀ X₀ K Y
    (elementNorm_pos d hd) (elementNorm_pos e he) (primeProductNorm_pos p hp V)
    (primeProductNorm_pos p hp N) (primeProductNorm_pos p hp M) (elementNorm_pos k hk)
    hD hE hV₀ hX₀ hK
  convert h using 1 ; unfold elementNorm ; ring

def conjugateProfile (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap g

@[simp] lemma conjugateProfile_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    conjugateProfile g s = star (g s) := rfl

theorem normalizedColumn_pair_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N M : Finset ι)
    (hVN : Disjoint V N) (hVM : Disjoint V M)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun S => g₁ (columnLog p X S)) (V∪N)) *
      normalizedColumn p (fun S => g₂ (columnLog p X S)) (V∪M) =
    (X : ℂ)⁻¹ *
      conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) := by
  rw [normalizedColumn_union_test p hp V N hVN X X₀ hX hX₀ U hUc hUs g₁ hU₁,
    normalizedColumn_union_test p hp V M hVM X X₀ hX hX₀ U hUc hUs g₂ hU₂]
  simp only [conjugateProfile_apply, star_div₀, Complex.star_def, Complex.conj_ofReal]
  have hs : (Real.sqrt X : ℂ) * (Real.sqrt X : ℂ) = (X : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hX.le]
  simp only [div_eq_mul_inv]
  calc
    _ = ((Real.sqrt X : ℂ) * (Real.sqrt X : ℂ))⁻¹ *
        star (halfNormalizationCLM U g₁
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N)) *
        halfNormalizationCLM U g₂
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) := by
      rw [mul_inv_rev]
      simp only [Complex.star_def, div_eq_mul_inv]
      ring
    _ = _ := by rw [hs]; simp only [Complex.star_def, div_eq_mul_inv]

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

private theorem active_row_norm_le_one (S T : Finset ι) (a : O) :
    ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
    (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

def secondPairRadialMode (S T : Finset ι) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport T S, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
    activeGaussRowFactor p hp hinj hg T S e k

theorem secondPairRadialMode_summable (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => secondPairRadialMode p hp hg hinj S T e k W Y) := by
  let n := ∏ i : activeSupport T S, p i.val
  let G := FiniteGaussPhase.canonicalProductGauss (fun i : activeSupport T S => p i.val)
    (fun i => hp i.val) (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj T S)
    (fun i => hg i.val) (activeExponent T S)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hK : 0 < Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) :=
    div_pos hY (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hs := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W _ hK
  have hgk (k : O) : ‖activeGaussRowFactor p hp hinj hg T S e k‖ ≤ ‖G‖ := by
    simp only [activeGaussRowFactor, norm_mul, norm_star]
    change ‖G‖ * (_ * _) ≤ ‖G‖
    have hb : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) e‖ *
        ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) k‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (active_row_norm_le_one p hg T S e)
        (active_row_norm_le_one p hg T S k) (norm_nonneg _) zero_le_one
    exact mul_le_of_le_one_right (norm_nonneg _) hb
  have harg (k : O) : Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) =
      (Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) * ‖eisEmbedding k‖ ^ 2 := by ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((hs.mul_left ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖).mul_right ‖G‖)
  intro k
  simp only [secondPairRadialMode, norm_mul]
  rw [show (∏ i : activeSupport T S, p i.val) = n from rfl, harg]
  exact mul_le_mul_of_nonneg_left (hgk k) (by positivity)

theorem maskedSecondDual_eq_modes (G S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    maskedSecondDual p hg hp hinj G S T W Y =
      ∑ E ∈ G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, secondPairRadialMode p hp hg hinj S T
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y := by
  simp only [maskedSecondDual, secondPairRadialMode, mul_assoc, tsum_mul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  ring

def residualSecondMode (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
    if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y
    else 0

theorem residualSecondMode_summable (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) := by
  apply summable_sum
  intro S hS
  apply summable_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd]
    exact (secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).mul_left _
  · simp only [ite_eq_right hd]
    exact summable_zero

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondFrequencyKernel (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T
  else 0

theorem residualSecondMode_tsum (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' k : O, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) =
      ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑' k : O, if Disjoint S T then
          star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
          (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
          secondPairRadialMode p hp hg hinj S T e k W Y
        else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : O => if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd]
      exact (secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).mul_left _
    · simp only [ite_eq_right hd]
      exact summable_zero
  unfold residualSecondMode
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  exact Summable.tsum_finsetSum (fun T _ => hs S T)

def secondOverlapBlock (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset, if Disjoint S T then
    overlapPairWeight p hg Ψ m c d H G S T * maskedSecondDual p hg hp hinj G S T W Y
  else 0

theorem secondOverlapBlock_eq_modes (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y =
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E ∈ G.powerset,
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
            (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
          ∑' k : O, residualSecondMode p hp hg hinj F G Ψ Ψ m c d
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y := by
  let a := (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ)
  let w := fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)
  let f := fun (E S T : Finset ι) (k : O) => if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S *
      secondInputCoefficient p hg Ψ m c d (fun U => H (G ∪ U)) S) *
    (supportMobius (fun i => Ideal.span {p i}) T *
      secondInputCoefficient p hg Ψ m c d (fun U => H (G ∪ U)) T) *
    secondPairRadialMode p hp hg hinj S T (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y
    else 0
  have hterm (S T : Finset ι) :
      (if Disjoint S T then overlapPairWeight p hg Ψ m c d H G S T *
        maskedSecondDual p hg hp hinj G S T W Y else 0) =
      a * ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd, maskedSecondDual_eq_modes p hp hg hinj,
        overlapPairWeight, f, Finset.mul_sum, tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      dsimp only [a, w]
      ring
    · simp [hd, f]
  calc
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
      simp only [secondOverlapBlock, hterm, Finset.mul_sum]
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ E ∈ G.powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_comm]
    _ = a * ∑ E ∈ G.powerset, ∑ S ∈ (F \ G).powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro E hE
      rw [residualSecondMode_tsum p hp hg hinj F G Ψ Ψ m c d
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E)
        (primeSubsetGenerator_ne_zero _ E) W Y hY]
      simp only [Finset.mul_sum]
      rfl

theorem residualSecondMode_eq_frequencyKernel (F G E : Finset ι) (hEG : E ⊆ G)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
    (k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y =
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m (secondMaskQuotient p E G hEG) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k H₁ H₂ W Y := by
  unfold residualSecondMode
  rw [input_pair_fixed_pool p hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂]
  unfold secondFrequencyKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [ite_eq_left hd, ite_eq_left hd]
    have hn : (∏ i : activeSupport T S, p i.val) = ∏ i ∈ S ∪ T, p i := by
      rw [Finset.prod_coe_sort]
      simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
        Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.union_comm T S]
    simp only [secondPairRadialMode, secondGaussTerm, hn, primeProductNorm,
      ← secondMaskQuotient_spec p E G hEG]
    ring
  · simp [hd]

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0131

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
Source SHA256: 4b680ac9cc31fb2907426952ce570ab1c0be87ed83548242d03a302468380b8e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0132


namespace OAI

noncomputable section

namespace SecondPassArithmetic

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem inputConjugateRow_smoothed_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
    ∑ G ∈ F.powerset,
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
      ∑ E : G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
        ∑' k : O,
          secondFrequencyKernel p hp hg hinj F Ψ Ψ m
            (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  change secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y = _
  rw [secondOverlapBlock_eq_modes p hp hg hinj F G Ψ m c d H W Y hY]
  congr 1
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  congr 1
  apply tsum_congr
  intro k
  exact residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d
    (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) k W Y

theorem firstCoreInputRow_finite_le_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    let Ψ' := firstCoreTwist negative χ Ψ r
    let m' := m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂
    let c' := c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂
    let H' := firstCoreTest H V y negative t D
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset,
        (↑(‖secondInputCoefficient p hg Ψ' m' c' d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E : G.powerset,
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
            (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
          ∑' k : O,
            secondFrequencyKernel p hp hg hinj (F \ D) Ψ' Ψ' m'
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c' d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H' (G ∪ U)) (fun U => H' (G ∪ U)) rowMajorant Y).re := by
  dsimp only
  have h := finite_row_energy_le_rowMajorant
    (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) T Y hY hT
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t rowMajorant Y,
    inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc] at h
  · exact h
  · exact hY

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma finiteSquarefreeRow_zero_of_nonempty (S : Finset ι) (hS : S.Nonempty) :
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 0 = 0 := by
  obtain ⟨i, hi⟩ := hS
  apply FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S 0
  have h : ∃ j ∈ S, (0 : O) ∈ Ideal.span {p j} := ⟨i, hi, Ideal.zero_mem _⟩
  simp only [rowCoprimeMask, ite_eq_left h]

theorem inputConjugateRow_zero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : inputConjugateRow p hg F Ψ m c d H 0 = H ∅ := by
  unfold inputConjugateRow supportConjugateSum
  rw [Finset.sum_eq_single ∅]
  · have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
      simp only [supportMobius, Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one]
    rw [hm]
    simp [secondInputCoefficient, rowCoprimeMask, finiteSquarefreeRow]
  · intro S hS hne
    rw [finiteSquarefreeRow_zero_of_nonempty p hg S (Finset.nonempty_iff_ne_empty.mpr hne),
      star_zero, mul_zero]
  · simp

theorem firstCoreInputRow_zero
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t 0 =
      firstCoreTest H V y negative t D ∅ := by
  unfold firstCoreInputRow
  simp only [neg_zero, ite_self, inputConjugateRow_zero]

end

def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)

lemma nonzeroRowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => if z = 0 then 0 else
      rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz]
  simp

theorem nonzeroRowMajorantSum_eq_sub (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum P Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) -
        (↑(‖P 0‖ ^ 2) : ℂ) := by
  have h := (rowMajorant_summable P Y hY).tsum_eq_add_tsum_ite 0
  have h0 : rowMajorant (0 : ℝ) = 1 := rowMajorant_one 0 (by norm_num)
  simp only [map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, h0, one_mul] at h
  change _ = _ + nonzeroRowMajorantSum P Y at h
  rw [h]
  ring

theorem finite_nonzero_row_energy_le_majorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤ (nonzeroRowMajorantSum P Y).re := by
  have hs := nonzeroRowMajorant_summable P Y hY
  unfold nonzeroRowMajorantSum
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (if z = 0 then (0 : ℂ) else
        rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [ite_eq_right (hT0 z hz), rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      split_ifs
      · norm_num
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem inputConjugateRow_nonzero_correction (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum (inputConjugateRow p hg F Ψ m c d H) Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) - (↑(‖H ∅‖ ^ 2) : ℂ) := by
  rw [nonzeroRowMajorantSum_eq_sub _ Y hY, inputConjugateRow_zero]

theorem firstCoreInputRow_nonzero_correction
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) -
          (↑(‖firstCoreTest H V y negative t D ∅‖ ^ 2) : ℂ) := by
  rw [nonzeroRowMajorantSum_eq_sub _ Y hY, firstCoreInputRow_zero]

theorem firstCoreInputRow_finite_le_corrected_source
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re -
          ‖firstCoreTest H V y negative t D ∅‖ ^ 2 := by
  have h := finite_nonzero_row_energy_le_majorant
    (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) T Y hY hT hT0
  rw [firstCoreInputRow_nonzero_correction p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t Y hY,
    Complex.sub_re, Complex.ofReal_re] at h
  exact h

end

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

lemma firstCoreTest_empty_mass {ι : Type*} [DecidableEq ι]
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D : Finset ι) :
    ‖firstCoreTest H V y negative t D ∅‖ ^ 2 = ‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2 := by
  cases negative <;> simp only [firstCoreTest, Finset.union_empty, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star, FourierBridge.logPhase_norm, mul_one, mul_pow]

theorem firstCoreInputRow_integrated_le_corrected_source
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    {k : ℝ → ℝ} (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
    (∫ t : ℝ, k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re) -
      (‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2) * ∫ t : ℝ, k t := by
  let mass := ‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2
  let source := fun t : ℝ =>
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re
  have isource : Integrable (fun t : ℝ => k t * source t) volume :=
    firstCoreInputRow_majorant_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r Y hY hk
  have icorr : Integrable (fun t : ℝ => k t * (source t - mass)) volume := by
    simp only [mul_sub]
    exact isource.sub (hk.mul_const mass)
  have hpoint (t : ℝ) : k t * (∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      k t * (source t - mass) := by
    have h := firstCoreInputRow_finite_le_corrected_source p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t T Y hY hT hT0
    rw [firstCoreTest_empty_mass] at h
    exact mul_le_mul_of_nonneg_left h (hk0 t)
  calc
    _ ≤ ∫ t : ℝ, k t * (source t - mass) := by
      apply integral_mono _ icorr hpoint
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ (fun z hz =>
        firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk)
    _ = _ := by
      simp only [mul_sub]
      rw [integral_sub isource (hk.mul_const mass), integral_mul_const]
      dsimp only [source, mass]
      ring

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma aLabel_dvd_primeProduct (B : Finset ι) (v : ι → ℕ) (ε : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : aLabel p B ε ∣ primeProduct p B v := by
  unfold aLabel primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  cases h : ε i <;> simp only [bit, h, Bool.false_eq_true, ite_false, ite_true]
  · exact Nat.zero_le _
  · exact hv i hi

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

def actualSecondTuple (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (k : O) : SecondPassFiber.OldTuple where
  core := ![Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂},
    ∏ i ∈ C, Ideal.span {p i}, ∏ i ∈ E, Ideal.span {p i},
    Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)},
    Ideal.span {primeProduct p B v₁}, Ideal.span {aLabel p B ε₁},
    Ideal.span {aLabel p B ε₂}, ∏ i ∈ D, Ideal.span {p i}]
  v := ∏ i ∈ V, Ideal.span {p i}
  j2 := Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  row := k

def actualSecondLabel (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Ideal O :=
  Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂} *
    (∏ i ∈ C, Ideal.span {p i}) * (∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i})

def actualSecondRow (D E : Finset ι) (k : O) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) D *
    primeSubsetGenerator (fun i => Ideal.span {p i}) E * k

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_valid
    (B C D E V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C ∪ B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (k : O) :
    SecondPassFiber.Valid (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k)
      (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (actualSecondRow p D E k) := by
  have hJ := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2 p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
  have hb := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.cube_product_decomposition p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [primeProduct_add] at hb
  have hA₁ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₁ hv)
  have hA₂ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₂ hv)
  rw [primeProduct_add, ← Ideal.span_singleton_mul_span_singleton] at hA₁ hA₂
  have hrad := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [← Ideal.span_singleton_mul_span_singleton] at hrad
  have hD' : (∏ i ∈ D, Ideal.span {p i}) ∣
      (∏ i ∈ C, Ideal.span {p i}) * Ideal.span {cubeRadical p B} := by
    have hh := Finset.prod_dvd_prod_of_subset D (C ∪ B) (fun i => (Ideal.span {p i} : Ideal O)) hD
    rw [Finset.prod_union hCB] at hh
    simpa only [cubeRadical, FiniteGaussPhase.span_finset_prod] using hh
  have hD'' := hD'.trans (mul_dvd_mul_left (∏ i ∈ C, (Ideal.span {p i} : Ideal O)) hrad)
  constructor
  · rfl
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} =
          Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
    simpa only [← Ideal.span_singleton_mul_span_singleton] using hJ.symm
  · change Ideal.span {primeProduct p B v₁} * Ideal.span {primeProduct p B v₂} =
        Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)}
    simpa only [pow_two, ← Ideal.span_singleton_mul_span_singleton] using hb
  · exact hA₁
  · exact hA₂
  · apply hD''.trans
    refine ⟨(∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i}), ?_⟩
    simp only [actualSecondLabel]
    ring
  · rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_newLabel
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newLabel (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_newRow
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newRow (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondRow p D E k := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondLabel_span
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
      primeSubsetGenerator (fun i => Ideal.span {p i}) E * (∏ i ∈ V, p i)} =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := by
  simp only [actualSecondLabel, ← Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
    FiniteGaussPhase.span_finset_prod]
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)

@[ext] structure SecondSupportData (ι : Type*) where
  common : Finset ι
  firstDivisor : Finset ι
  secondDivisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

instance {ι : Type*} : Inhabited (SecondSupportData ι) := ⟨⟨∅, ∅, ∅, ∅, 0⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSupportTuple (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p B x.common x.firstDivisor x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency

def secondSupportLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
    jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor * (∏ i ∈ x.overlap, p i)

def secondSupportNewLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : Ideal O :=
  actualSecondLabel p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂

def secondSupportRow (x : SecondSupportData ι) : O :=
  actualSecondRow p x.firstDivisor x.secondDivisor x.frequency

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondSupportTuple_newLabel
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    SecondPassFiber.newLabel (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x) =
      secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondSupportTuple_newRow
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    SecondPassFiber.newRow (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x) = secondSupportRow p x := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportLabel_span
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    Ideal.span {secondSupportLabel p B v₁ v₂ ε₁ ε₂ x} = secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x :=
  actualSecondLabel_span p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂

theorem secondSupportTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Function.Injective (secondSupportTuple p B v₁ v₂ ε₁ ε₂) := by
  intro x y h
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  apply SecondSupportData.ext
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hC
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hD
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hE
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hV
  · exact hk

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportTuple_valid
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (x : SecondSupportData ι)
    (hCB : Disjoint x.common B) (hD : x.firstDivisor ⊆ x.common ∪ B) :
    SecondPassFiber.Valid (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x)
      (SecondPassFiber.newLabel (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x))
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (SecondPassFiber.newRow (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x)) :=
  actualSecondTuple_valid p B x.common x.firstDivisor x.secondDivisor x.overlap hCB hD
    v₁ v₂ ε₁ ε₂ hv x.frequency

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sector_b0_ne_bot (hp : ∀ i, p i ≠ 0)
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} : Ideal O) ≠ ⊥ := by
  apply Ideal.span_singleton_eq_bot.not.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp i))

def secondSectorZ (X X₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap * X₀ / X)

def secondSectorUd (D : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖ ^ 2 / D)

def secondSectorUe (E : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)‖ ^ 2 / E)

def secondSectorUv (V₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap / V₀)

def secondSectorKap (K : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (secondSupportRow p x)‖ ^ 2 / K)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ X X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))

theorem actual_second_sector_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
          Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
            FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow windows
          (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x) (secondSectorUe p E₀ x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
          A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X X₀ K Y hD₀ hE₀ hV₀ hX hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb, hbound⟩ := htrans _ hR
  refine ⟨b, hb, ?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m hv hCB hD hBnd hL hmap hT0 hnorm hw
  let encode := secondSupportTuple p B v₁ v₂ ε₁ ε₂
  have hi : Function.Injective encode := secondSupportTuple_injective p hinj B v₁ v₂ ε₁ ε₂
  let decode := Function.invFun encode
  have hdec (x : SecondSupportData ι) : decode (encode x) = x := Function.leftInverse_invFun hi x
  let s' := s.image encode
  let w' := fun x => w (decode x)
  let label' := fun x => secondSupportLabel p B v₁ v₂ ε₁ ε₂ (decode x)
  let z' := fun x => secondSectorZ p X X₀ (decode x)
  let ud' := fun x => secondSectorUd p D₀ (decode x)
  let ue' := fun x => secondSectorUe p E₀ (decode x)
  let uv' := fun x => secondSectorUv p V₀ (decode x)
  let kap' := fun x => secondSectorKap p K (decode x)
  have hsvalid : ∀ x ∈ s', SecondPassFiber.Valid x (SecondPassFiber.newLabel x)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}) (SecondPassFiber.newRow x) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact secondSupportTuple_valid p B v₁ v₂ ε₁ ε₂ hv a (hCB a ha) (hD a ha)
  have hsmap : ∀ x ∈ s', (SecondPassFiber.newLabel x, SecondPassFiber.newRow x) ∈ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hmap a ha
  have hsw : ∀ x ∈ s', ‖w' x‖ * ‖outerWindow windows (z' x) (ud' x) (ue' x) (uv' x) (kap' x)‖ ≤ Bnd := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [w', z', ud', ue', uv', kap']
    rw [hdec]
    exact hw a ha
  have hslabel : ∀ x ∈ s', Ideal.span {label' x} = SecondPassFiber.newLabel x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [label']
    rw [hdec]
    exact secondSupportLabel_span p B v₁ v₂ ε₁ ε₂ a
  have hout := hbound s' T (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
    w' Bnd lengthScale label' F Ψ₁ Ψ₂ m z' ud' ue' uv' kap' X₀ X₀
    (sector_b0_ne_bot p hp B v₁ v₂ ε₁ ε₂) hBnd hL hsvalid hsmap hT0 hnorm hsw hslabel
  have hsource : tupleSourceSum p hp hcop hg s' w' label' F Ψ₁ Ψ₂ m
      A₁ A₂ W windows z' ud' ue' uv' kap' X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2)) =
      actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y := by
    unfold tupleSourceSum actualSecondSectorSource
    rw [Finset.sum_image (fun a ha c hc h => hi h)]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [w', label', z', ud', ue', uv', kap']
    rw [hdec]
    rfl
  rw [hsource] at hout
  exact hout

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0132

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.FixedProfiles
Source SHA256: fb3ce03c60bdca7b5688ed2a6993de7f3ba7fb4225db5451a48dd91ecdbc7ddb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0133



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondGaussTerm_test_factors (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T =
      star (H₁ S) * H₂ T *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
  simp only [secondGaussTerm, secondInputCoefficient, star_mul, mul_one]
  ring

theorem secondFrequencyKernel_log_tests (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (W : 𝓢(ℝ, ℂ)) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (fun S => V₁ (columnLog p X₁ S)) (fun T => V₂ (columnLog p X₂ T)) W Y =
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y := by
  unfold secondFrequencyKernel actualSecondKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd]
    rw [secondGaussTerm_test_factors]
    ring
  · simp [hd]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration

section
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem radialPairKernel_dyadic_normalization
    (V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M) =
      (X : ℂ)⁻¹ *
      (conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) *
      EisensteinSchwartzPoisson.paperRadialFourier W
        ((Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
          (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
            2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
            columnLog p X₀ N - columnLog p X₀ M))) := by
  unfold radialPairKernel
  rw [normalizedColumn_pair_union p hp V N M hVN hVM X X₀ hX hX₀ U hUc hUs g₁ g₂ hU₁ hU₂,
    second_radial_dyadic_argument p hp V N M hVN hVM d e k hd he hk D E V₀ X₀ K Y hD hE hV₀ hX₀ hK]
  ring

variable [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildKernelPair_eq_postCommon
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) (windows : Fin 7 → ℝ → ℂ) :
    let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
    let A₂ := halfNormalizationCLM U g₂
    let z := Real.log (primeProductNorm p V * X₀ / X)
    let ud := Real.log (elementNorm d / D)
    let ue := Real.log (elementNorm e / E)
    let uv := Real.log (primeProductNorm p V / V₀)
    let kap := Real.log (elementNorm (d*e*k) / K)
    outerWindow windows z ud ue uv kap = 1 →
    (∀ a : ℝ, A₁ (z+a) ≠ 0 → windows 5 a = 1) →
    (∀ a : ℝ, A₂ (z+a) ≠ 0 → windows 6 a = 1) →
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
      (radialPairKernel p e k W g₁ g₂ X X Y) =
      (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
        (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
        z ud ue uv kap X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  dsimp only
  intro houter hcut₁ hcut₂
  rw [secondChildKernelPair_fixed_pool]
  simp only [postCommonSmoothPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hVN : Disjoint V N
  · by_cases hVM : Disjoint V M
    · rw [radialPairKernel_dyadic_normalization p hp V N M hVN hVM d e k hd he hk
        D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂, houter]
      by_cases h₁ : conjugateProfile (halfNormalizationCLM U g₁)
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) = 0
      · rw [h₁]; ring
      · by_cases h₂ : halfNormalizationCLM U g₂
            (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) = 0
        · rw [h₂]; ring
        · rw [hcut₁ _ h₁, hcut₂ _ h₂]; ring
    · rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₂ (m*r) c e
        (d*e*(-k)) (fun _ => 1) V M hVM]
      ring
  · rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₁ (m*r) c e
      (d*e*k) (fun _ => 1) V N hVN, star_zero]
    ring

end

section
open JointLogSeparation

theorem halfNormalization_support_bound (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (A : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) :
    ∀ s, halfNormalizationCLM U g s ≠ 0 → |s| ≤ A := by
  intro s hs
  apply hg s
  intro hzero
  apply hs
  rw [halfNormalizationCLM_apply U hUc hUs, hzero, mul_zero]

lemma translated_support_bound (g : ℝ → ℂ) (A B z x : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) (hz : |z| ≤ B) (hx : g (z+x) ≠ 0) :
    |x| ≤ A+B := by
  have ht := hg (z+x) hx
  have ha : |x| ≤ |z+x| + |z| := by
    calc
      |x| = |(z+x)-z| := by congr 1; ring
      _ ≤ |z+x| + |z| := abs_sub _ _
  linarith

theorem exists_fixed_sector_windows (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ windows : Fin 7 → ℝ → ℂ,
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      (∀ z ud ue uv kap : ℝ,
        |z| ≤ B → |ud| ≤ B → |ue| ≤ B → |uv| ≤ B → |kap| ≤ B →
        outerWindow windows z ud ue uv kap = 1) ∧
      (∀ (g : ℝ → ℂ) (z : ℝ), (∀ s, g s ≠ 0 → |s| ≤ A) → |z| ≤ B →
        ∀ j x, g (z+x) ≠ 0 → windows j x = 1) := by
  obtain ⟨w, hwc, hws, hweq, hwsupp, hwzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (A+B) (add_nonneg hA hB)
  refine ⟨fun _ => w, fun _ => hwc, fun _ => hws, ?_, ?_, ?_⟩
  · intro j s hs
    have hh := hwsupp (subset_closure hs)
    exact abs_le.mpr hh
  · intro z ud ue uv kap hz hd he hv hk
    have heq (s : ℝ) (hs : |s| ≤ B) : w s = 1 := hweq s (by linarith)
    simp only [outerWindow, heq z hz, heq ud hd, heq ue he, heq uv hv, heq kap hk,
      one_mul]
  · intro g z hg hz j x hx
    exact hweq x (translated_support_bound g A B z x hg hz hx)

end

open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem exists_fixed_normalized_child_tests {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W g₁ g₂ X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  apply secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondRawSector
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (X Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x *
    secondChildKernelPair p hp hcop hg F x.overlap Ψ₁ Ψ₂ m r
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
        jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
      x.frequency (-x.frequency)
      (radialPairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
        x.frequency W g₁ g₂ X X Y)

theorem actualSecondRawSector_fixed_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O),
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p X X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y =
          (X : ℂ)⁻¹ * actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ (m*r)
            A₁ A₂ W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r hk hz hud hue huv hkap
  simp only [actualSecondRawSector, actualSecondSectorSource, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor) x.frequency
    (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) (hk x hx)
    (hz x hx) (hud x hx) (hue x hx) (huv x hx) (hkap x hx)
  rw [heq]
  simp only [secondSupportLabel, secondSupportRow, actualSecondRow,
    secondSectorZ, secondSectorUd, secondSectorUe, secondSectorUv, secondSectorKap,
    elementNorm, mul_neg]
  ring

end

open ActualEisensteinCubic
open FiniteGaussPhase (canonicalProductGauss_cross_factors)
open FirstCauchyArithmetic (activeGaussRowFactor supportMobius)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_zero_of_ne (S T : Finset ι) (hne : S ≠ T) (e : O) :
    activeGaussRowFactor p hp hinj hg S T e 0 = 0 := by
  have hs : (activeSupport S T).Nonempty := by
    by_contra hn
    apply hne
    have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
    exact Finset.Subset.antisymm he.1 he.2
  let : Nonempty (activeSupport S T) := hs.to_subtype
  unfold activeGaussRowFactor
  simp only [finiteSexticRow_zero, star_zero, mul_zero]

theorem activeGaussRowFactor_empty (e k : O) :
    activeGaussRowFactor p hp hinj hg ∅ ∅ e k = 1 := by
  have hempty : activeSupport (∅ : Finset ι) ∅ = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport (∅ : Finset ι) ∅) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [activeGaussRowFactor, finiteSexticRow, star_one, mul_one,
    canonicalProductGauss_cross_factors, Fintype.prod_empty]

theorem secondGaussTerm_empty (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ ∅ ∅ =
      star (H₁ ∅) * H₂ ∅ := by
  have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
    change (UniqueFactorizationMonoid.moebius (1 : Ideal O) : ℂ) = 1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [secondGaussTerm, hm, one_mul, secondInputCoefficient, Finset.prod_empty,
    map_one, activeGaussRowFactor_empty, mul_one]
  simp [rowCoprimeMask, finiteSquarefreeRow]

theorem secondFrequencyKernel_zero (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ W Y =
      (Y : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier W 0 * star (H₁ ∅) * H₂ ∅ := by
  have hz (S T : Finset ι) (hne : S ≠ T) :
      secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ S T = 0 := by
    unfold secondGaussTerm
    rw [activeGaussRowFactor_zero_of_ne p hp hg hinj T S (Ne.symm hne) e, mul_zero]
  unfold secondFrequencyKernel
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [secondGaussTerm_empty, mul_assoc]
    · intro T hT hne
      rw [hz ∅ T (Ne.symm hne)]
      simp
    · simp
  · intro S hS hne
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hd : Disjoint S T
    · have hneq : S ≠ T := by
        intro heq
        subst T
        exact hne ((show S = ∅ by simpa using Finset.disjoint_iff_inter_eq_empty.mp hd))
      rw [hz S T hneq]
      simp
    · simp [hd]
  · simp

end SecondPassArithmetic

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma symbol_cube_numerator (a d : O) (hd : denominatorCondition (a^3) d) :
    symbol (a^3) d=1 := by
  have hprimary : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd.2
  rw [symbol_pow_numerator a d hprimary 3]
  apply symbol_cube_of_isCoprime a d hprimary
  exact hd.1.of_isCoprime_of_dvd_left ⟨a^2,by ring⟩

theorem arithmeticResidueSum_cube (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3)=(Nat.card (AdmissibleResidue (a^3)):ℂ) := by
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Fintype (AdmissibleResidue (a^3)) := Fintype.ofFinite _
  rw [arithmeticResidueSum,tsum_fintype]
  have hterm (r : AdmissibleResidue (a^3)) :
      eisEmbedding (symbol (a^3) (denominatorRep (a^3) r.1))*
        ShortDraftTrace.breveE (cuspFrequency 0*eisEmbedding (denominatorRep (a^3) r.1)/
          eisEmbedding (a^3))=1 := by
    rw [symbol_cube_numerator a _ r.2,map_one]
    simp [cuspFrequency]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]

lemma admissibleResidue_nonempty (c : O) (hc : c ≠ 0) : Nonempty (AdmissibleResidue c) := by
  let d : AdmissibleDenominator c := ⟨1,isCoprime_one_right,by simp⟩
  exact ⟨((residueDenominatorEquiv c hc).symm d).1⟩

theorem arithmeticResidueSum_cube_ne_zero (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3) ≠ 0 := by
  rw [arithmeticResidueSum_cube a ha]
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Nonempty (AdmissibleResidue (a^3)) := admissibleResidue_nonempty _ (pow_ne_zero 3 ha)
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := AdmissibleResidue (a^3))).ne'

lemma denominatorCondition_congr (c d e : O) (h : 3*c ∣ d-e) :
    denominatorCondition c d ↔ denominatorCondition c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact denominatorCondition_shift c e n

lemma denominatorCondition_mul (c d t : O) (hd : denominatorCondition c d)
    (ht : denominatorCondition c t) : denominatorCondition c (d*t) := by
  refine ⟨hd.1.mul_right ht.1,?_⟩
  convert dvd_add (hd.2.mul_right t) ht.2 using 1 ; ring

lemma row_symbol_congr_modulus (c d e : O) (hlevel : (3:O) ∣ c)
    (he : (3:O) ∣ e-1) (h : 3*c ∣ d-e) : symbol c d=symbol c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact row_symbol_shift c e n hlevel he

lemma denominatorRep_product_congr (c t : O) (r : DenominatorResidue c) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r)-t*denominatorRep c r := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [denominatorRep_spec,map_mul,denominatorRep_spec]

def residueMultiplication (c t : O) (ht : denominatorCondition c t)
    (r : AdmissibleResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1,
    (denominatorCondition_congr c _ _ (denominatorRep_product_congr c t r.1)).2
      (denominatorCondition_mul c t _ ht r.2)⟩

lemma denominatorCondition_coprime_modulus (c t : O) (ht : denominatorCondition c t) :
    IsCoprime (3*c) t := by
  obtain ⟨n,hn⟩ := ht.2
  have h3 : IsCoprime (3:O) t := ⟨-n,1,by linear_combination hn⟩
  exact h3.mul_left ht.1

lemma residueMultiplication_injective (c t : O) (ht : denominatorCondition c t) :
    Function.Injective (residueMultiplication c t ht) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {3*c}) t) := by
    have hh := (denominatorCondition_coprime_modulus c t ht).map
      (Ideal.Quotient.mk (Ideal.span {3*c}))
    have hz : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [hz,isCoprime_zero_left] using hh
  intro r q heq
  apply Subtype.ext
  exact hunit.mul_left_cancel (congrArg Subtype.val heq)

def residueMultiplicationEquiv (c : O) (hc : c ≠ 0) (t : O)
    (ht : denominatorCondition c t) : AdmissibleResidue c ≃ AdmissibleResidue c := by
  letI : Finite (AdmissibleResidue c) := finite_admissibleResidue c hc
  exact Equiv.ofBijective (residueMultiplication c t ht)
    ⟨residueMultiplication_injective c t ht,
      Finite.surjective_of_injective (residueMultiplication_injective c t ht)⟩

lemma residueMultiplication_phase (c : O) (hlevel : (3:O) ∣ c) (t : O)
    (ht : denominatorCondition c t) (r : AdmissibleResidue c) :
    symbol c (denominatorRep c (residueMultiplication c t ht r).1)=
      symbol c t*symbol c (denominatorRep c r.1) := by
  change symbol c (denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1))=
    symbol c t*symbol c (denominatorRep c r.1)
  rw [row_symbol_congr_modulus c _ (t*denominatorRep c r.1) hlevel
    (denominatorCondition_mul c t _ ht r.2).2 (denominatorRep_product_congr c t r.1)]
  exact symbol_mul_denominator c t (denominatorRep c r.1)

lemma arithmeticResidueSum_zero (c : O) :
    arithmeticResidueSum 0 c=∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1)) := by
  simp only [arithmeticResidueSum,cuspFrequency,map_zero,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]

theorem arithmeticResidueSum_constant_eigen (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (t : O) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum 0 c=arithmeticResidueSum 0 c := by
  rw [arithmeticResidueSum_zero]
  have heq := (residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c => eisEmbedding (symbol c (denominatorRep c r.1)))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t*symbol c (denominatorRep c r.1)) := by
      simp only [map_mul,tsum_mul_left]
    _ = _ := by
      convert heq using 1
      apply tsum_congr
      intro r
      exact congrArg eisEmbedding (residueMultiplication_phase c hlevel t ht r).symm

theorem arithmeticResidueSum_ne_zero_forces_trivial (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∀ t : O, denominatorCondition c t → symbol c t=1 := by
  intro t ht
  apply eisEmbedding_injective
  rw [map_one]
  apply (mul_right_cancel₀ hA)
  rw [arithmeticResidueSum_constant_eigen c hc hlevel t ht,one_mul]

end CubicEisenstein

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma coprime_of_dvd_sub_one (a b : O) (h : a ∣ b-1) : IsCoprime a b := by
  obtain ⟨r,hr⟩ := h
  exact ⟨-r,1,by linear_combination hr⟩

lemma primary_coprime_three (p : O) (hp : lambda^2 ∣ p-1) : IsCoprime p (3:O) :=
  (coprime_of_dvd_sub_one 3 p (three_dvd_primary_sub_one p hp)).symm

lemma exists_one_mod_and_prescribed (p m x : O) (hpm : IsCoprime p m) :
    ∃ t : O, m ∣ t-1 ∧ p ∣ t-x := by
  obtain ⟨r,u,hu⟩ := hpm
  refine ⟨1+m*u*(x-1),⟨u*(x-1),by ring⟩,⟨-r*(x-1),?_⟩⟩
  linear_combination (x-1)*hu

theorem constant_coefficient_primary_prime_exponent (c p b : O) (n : ℕ)
    (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hp : Prime p) (hprimary : lambda^2 ∣ p-1)
    (hpb : ¬p ∣ b) (hfactor : c=p^n*b) (hA : arithmeticResidueSum 0 c ≠ 0) :
    3 ∣ n := by
  by_contra hn
  let P : Ideal O := Ideal.span {p}
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ P := primary_maximal_divisor_good p hprimary P (Ideal.subset_span (by simp []))
  have hchar : (cubicChar P hg)^n ≠ 1 := by
    intro heq
    have hd := orderOf_dvd_of_pow_eq_one heq
    rw [cubicChar_order P hg] at hd
    exact hn hd
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hchar
  rw [MulChar.pow_apply_coe] at hu
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ P)
  have hp9 : IsCoprime p (9:O) := by
    simpa only [show (3:O)^2=9 by norm_num] using (primary_coprime_three p hprimary).pow_right (n := 2)
  have hpm : IsCoprime p (9*b) := hp9.mul_right (hp.coprime_iff_not_dvd.mpr hpb)
  obtain ⟨t,htm,htp⟩ := exists_one_mod_and_prescribed p (9*b) x hpm
  have h9 : (9:O) ∣ t-1 := (dvd_mul_right 9 b).trans htm
  have hb : b ∣ t-1 := (dvd_mul_left b 9).trans htm
  have h3 : (3:O) ∣ t-1 := (show (3:O) ∣ 9 from ⟨3,by norm_num⟩).trans h9
  have htprimary : lambda^2 ∣ t-1 := lambda_sq_dvd_three.trans h3
  have htu : Ideal.Quotient.mk P t=(u : O ⧸ P) := by
    rw [← hx]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr htp)
  have hpt : IsCoprime p t := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have hz : Ideal.Quotient.mk P t=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    rw [htu] at hz
    exact Units.ne_zero u hz)
  have hbt : IsCoprime b t := coprime_of_dvd_sub_one b t hb
  have hct : IsCoprime c t := by
    rw [hfactor]
    exact hpt.pow_left.mul_left hbt
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t ⟨hct,h3⟩
  have hbsym : symbol b t=1 := by
    have hh := symbol_denominator_congr b t 1 htprimary (by simp) h9 hb
    simpa only [symbol_one] using hh
  have hpsym : symbol p t=cubicChar P hg (u : O ⧸ P) := by
    rw [symbol_reciprocity p t hp.ne_zero (primary_ne_zero t htprimary) hprimary htprimary]
    change idealSymbol P t=_
    rw [idealSymbol_prime P hg,htu]
  rw [hfactor,symbol_mul_numerator _ _ t htprimary,symbol_pow_numerator p t htprimary,
    hbsym,mul_one,hpsym] at htriv
  exact hu htriv

end CubicEisenstein

end

end OAI
end OAIOriginalModule0133

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
Source SHA256: b9de3765135208bb0288fe4c6265e718e516585f9e259fe09110fd09f14ed5d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0134


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace CubicEisenstein
open MeasureTheory Set Filter
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid

lemma multiset_cube_remainder {α : Type*} [DecidableEq α] (s : Multiset α) (p : α)
    (hdiv : ∀ q, q ≠ p → 3 ∣ s.count q) :
    ∃ t : Multiset α, s=(s.count p % 3) • {p} + 3 • t := by
  let t := Finsupp.toMultiset (s.toFinsupp.mapRange (fun n : ℕ => n/3) (by decide))
  refine ⟨t,?_⟩
  apply Multiset.ext.mpr
  intro q
  simp only [Multiset.count_add,Multiset.count_nsmul,Multiset.count_singleton,
    t,Finsupp.count_toMultiset,Finsupp.mapRange_apply,Multiset.toFinsupp_apply]
  by_cases hq : q=p
  · subst q
    simp only [ite_true,mul_one]
    omega
  · simp only [hq,ite_false,mul_zero,zero_add]
    exact (Nat.mul_div_cancel' (hdiv q hq)).symm

lemma residue_lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

lemma constant_coefficient_unramified_count [NormalizationMonoid O]
    (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0)
    (q : O) (hq : q ≠ normalize lambda) : 3 ∣ (normalizedFactors c).count q := by
  by_cases hmem : q ∈ normalizedFactors c
  · have hprime := prime_of_normalized_factor q hmem
    let P : Ideal O := Ideal.span {q}
    let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
    have hg : lambda ∉ P := by
      intro hl
      have ha : Associated q lambda :=
        hprime.associated_of_dvd residue_lambda_prime (Ideal.mem_span_singleton.mp hl)
      apply hq
      exact (normalize_normalized_factor q hmem).symm.trans
        (normalize_eq_normalize_iff_associated.mpr ha)
    obtain ⟨p,hP,hprimary,-⟩ := cubicJacobi_exists_primary_generator P hg
    have hqp : Associated q p := Ideal.span_singleton_eq_span_singleton.mp hP
    have hp : Prime p := hqp.prime_iff.mp hprime
    obtain ⟨b,hfactor,hpb⟩ := (FiniteMultiplicity.of_prime_left hp hc).exists_eq_pow_mul_and_not_dvd
    have hd := constant_coefficient_primary_prime_exponent c p b (multiplicity p c)
      hc hlevel hp hprimary hpb hfactor hA
    have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hc
    rw [normalize_normalized_factor q hmem] at hcount
    rw [← hcount,← multiplicity_eq_of_associated_left hqp]
    exact hd
  · rw [Multiset.count_eq_zero.mpr hmem]
    exact dvd_zero _

theorem constant_coefficient_cube_reduction (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∃ (u : Oˣ) (r : ℕ) (a : O), r < 3 ∧ c=(u:O)*lambda^r*a^3 := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := normalizedFactors c
  obtain ⟨t,ht⟩ := multiset_cube_remainder s (normalize lambda)
    (constant_coefficient_unramified_count c hc hlevel hA)
  let r := s.count (normalize lambda) % 3
  have hprod : s.prod=(normalize lambda)^r*t.prod^3 := by
    rw [ht,Multiset.prod_add,Multiset.prod_nsmul,Multiset.prod_singleton,Multiset.prod_nsmul]
  have hassoc : Associated (lambda^r*t.prod^3) c := by
    have hnorm : Associated ((normalize lambda)^r*t.prod^3) (lambda^r*t.prod^3) :=
      (normalize_associated lambda).pow_pow.mul_right _
    apply hnorm.symm.trans
    rw [← hprod]
    exact prod_normalizedFactors hc
  obtain ⟨u,hu⟩ := hassoc
  refine ⟨u,r,t.prod,Nat.mod_lt _ (by decide),?_⟩
  rw [← hu]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified

lemma constant_coefficient_ramified_equation (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (hA : arithmeticResidueSum 0 c ≠ 0) (u : Oˣ) (r : ℕ) (a : O) (ha : a ≠ 0)
    (hfactor : c=(u:O)*lambda^r*a^3) (A B : ℤ) :
    symbol (u:O) (primaryCoord A B)*(cubicExp A)^r=1 := by
  let t0 := primaryCoord A B
  have ht0 : lambda^2 ∣ t0-1 := primaryCoord_primary A B
  obtain ⟨w,hw⟩ := exists_coprime_three_shift t0 3 a ht0 (primary_coprime_three t0 ht0) ha
  let t := t0+3*w*3
  have ht : lambda^2 ∣ t-1 := primary_add_multiple_three t0 3 w ht0
  have h9 : (9:O) ∣ t-t0 := ⟨w,by dsimp [t]; ring⟩
  have hat : IsCoprime a t := hw.symm
  have hlt : IsCoprime lambda t :=
    coprime_of_dvd_sub_one lambda t ((show lambda ∣ lambda^2 from ⟨lambda,by ring⟩).trans ht)
  have hct : IsCoprime c t := by
    rw [hfactor,show (u:O)*lambda^r*a^3=(u:O)*(lambda^r*a^3) by ring]
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    exact hlt.pow_left.mul_left hat.pow_left
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t
    ⟨hct,three_dvd_primary_sub_one t ht⟩
  have hacube : symbol (a^3) t=1 := by
    rw [symbol_pow_numerator a t ht 3]
    exact symbol_cube_of_isCoprime a t ht hat
  rw [hfactor,symbol_mul_numerator _ _ t ht,symbol_mul_numerator _ _ t ht,
    symbol_pow_numerator lambda t ht r,hacube,mul_one,
    symbol_unit_congr_mod_nine (u:O) t t0 u.isUnit ht ht0 h9,
    symbol_lambda_congr_mod_nine t t0 ht ht0 h9,
    symbol_lambda_eq_linearRay t0 ht0] at htriv
  simpa only [t0,linearRay_primaryCoord,one_mul,zero_mul,add_zero] using htriv

lemma unit_eq_sign_of_symbol_class (u : Oˣ)
    (hu : symbol (u:O) (primaryCoord 0 1)=1) : (u:O)=1 ∨ (u:O)=-1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega (primaryCoord 0 1)=omega^2 := by
    rw [symbol_omega_eq_linearRay _ (primaryCoord_primary 0 1),linearRay_primaryCoord]
    norm_num [cubicExp]
  have hω2 : symbol (omega^2) (primaryCoord 0 1)=omega^4 := by
    rw [symbol_pow_numerator omega _ (primaryCoord_primary 0 1) 2,hω,← pow_mul]
  have hn2 : omega^2 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 2).not.mpr (by decide)
  have hn4 : omega^4 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 4).not.mpr (by decide)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · exact Or.inl (by rw [h,Units.val_one])
  · exact Or.inr (by rw [h,Units.val_neg,Units.val_one])
  · exact False.elim (hn2 (by simpa only [h,hη,hω] using hu))
  · exact False.elim (hn2 (by simpa only [h,Units.val_neg,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_pow_eq_pow_val,hη,hω2] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω2] using hu))

theorem arithmeticResidueSum_ne_zero_implies_cube (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) : ∃ a : O,c=a^3 := by
  obtain ⟨u,r,a,hr,hfactor⟩ := constant_coefficient_cube_reduction c hc hlevel hA
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : (3:ℕ) ≠ 0),mul_zero] at hfactor
    exact hc hfactor
  have h01 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 0 1
  have husign := unit_eq_sign_of_symbol_class u (by
    simpa only [cubicExp_zero,one_pow,mul_one] using h01)
  have h10 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 1 0
  have hωr : omega^r=1 := by
    rcases husign with hu | hu
    · simpa only [hu,symbol_one_numerator _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
    · simpa only [hu,symbol_neg_one _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
  have hdiv : 3 ∣ r := (omega_primitive.pow_eq_one_iff_dvd r).mp hωr
  have hr0 : r=0 := by omega
  rw [hr0,pow_zero,mul_one] at hfactor
  rcases husign with hu | hu
  · refine ⟨a,?_⟩
    simpa only [hu,one_mul] using hfactor
  · refine ⟨-a,?_⟩
    rw [hfactor,hu]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

theorem arithmeticResidueSum_ne_zero_iff_cube (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c ≠ 0 ↔ ∃ a : O,c=a^3 := by
  constructor
  · exact arithmeticResidueSum_ne_zero_implies_cube c hc hlevel
  · rintro ⟨a,rfl⟩
    have ha : a ≠ 0 := fun h => hc (by rw [h]; norm_num)
    exact arithmeticResidueSum_cube_ne_zero a ha

theorem arithmeticResidueSum_constant_formula (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c=
      if ∃ a : O,c=a^3 then (Nat.card (AdmissibleResidue c):ℂ) else 0 := by
  split_ifs with hcube
  · obtain ⟨a,rfl⟩ := hcube
    exact arithmeticResidueSum_cube a (fun h => hc (by rw [h]; norm_num))
  · exact not_ne_iff.mp (fun hA => hcube (arithmeticResidueSum_ne_zero_implies_cube c hc hlevel hA))

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

def idealZeroMask (D : Ideal O) (z : O) : ℂ :=
  if ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P then 0 else 1

theorem idealSupport_singleton_univ (D : Ideal O) :
    idealSupport {D} D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro P
  apply (mem_idealSupport_iff {D} D P).mpr
  obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
  have hID : I = D := Finset.mem_singleton.mp hI
  simpa only [hID] using hP

theorem singleton_rowCoprimeMask_eq_idealZeroMask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : primePool {D} => P.val) Finset.univ z = idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (primePool {D})), z ∈ P.val) ↔
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
      have hID : I = D := Finset.mem_singleton.mp hI
      exact ⟨P.val, hID ▸ hP, hz⟩
    · rintro ⟨P, hP, hz⟩
      have hp : P ∈ primePool {D} := mem_primePool_iff.mpr ⟨D, Finset.mem_singleton_self D, hP⟩
      exact ⟨⟨P, hp⟩, Finset.mem_univ _, hz⟩
  simp only [rowCoprimeMask, idealZeroMask, he]

theorem canonical_quadraticRow_star (D : Ideal O) (hD : Admissible D) (z : O) :
    star (quadraticRow D z) = quadraticRow D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticInitialBound.quadraticRow_star _ _ _ _

theorem canonical_quadraticRow_squared (D : Ideal O) (hD : Admissible D) (z : O) :
    quadraticRow D z * quadraticRow D z = idealZeroMask D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  rw [← QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ z z, ← pow_two,
    QuadraticSquarefreeKernel.quadraticRow_square, idealSupport_singleton_univ]
  exact singleton_rowCoprimeMask_eq_idealZeroMask D z

def gcdMaskPrimes (D : Ideal O) : Finset (Ideal O) :=
  {Ideal.span {lambda}, Ideal.span {(2 : O)}} ∪
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset

instance gcdMaskPrimes_maximal (D : Ideal O) (P : gcdMaskPrimes D) : P.val.IsMaximal := by
  rcases Finset.mem_union.mp P.property with hp | hp
  · rcases Finset.mem_insert.mp hp with hp | hp
    · rw [hp]
      exact lambdaIdeal_maximal
    · rw [Finset.mem_singleton.mp hp]
      exact twoIdeal_maximal
  · have h := UniqueFactorizationMonoid.prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp hp)
    exact (Ideal.isPrime_of_prime h).isMaximal h.ne_zero

theorem gcdMaskPrimes_mask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z =
      rowCoprimeMask badPrime Finset.univ z * idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val) ↔
      (lambda ∣ z ∨ (2 : O) ∣ z) ∨
        ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      rcases Finset.mem_union.mp P.property with hp | hp
      · rcases Finset.mem_insert.mp hp with hp | hp
        · exact Or.inl (Or.inl (Ideal.mem_span_singleton.mp (hp ▸ hz)))
        · exact Or.inl (Or.inr (Ideal.mem_span_singleton.mp ((Finset.mem_singleton.mp hp) ▸ hz)))
      · exact Or.inr ⟨P.val, Multiset.mem_toFinset.mp hp, hz⟩
    · rintro ((hz | hz) | ⟨P, hP, hz⟩)
      · exact ⟨⟨Ideal.span {lambda}, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨Ideal.span {(2 : O)}, Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨P, Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hP)⟩, Finset.mem_univ _, hz⟩
  change (if ∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val then (0 : ℂ) else 1) = _
  simp only [he]
  rw [badPrime_mask, supported_span_iff]
  unfold idealZeroMask
  by_cases hl : lambda ∣ z <;> by_cases ht : (2 : O) ∣ z <;>
    by_cases hd : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P <;> simp [hl, ht, hd]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance

theorem canonical_same_ray_pair_poisson
    {α : Type*} [DecidableEq α]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hd : Disjoint A B := idealSupport_disjoint_of_coprime F I J hcop
  have hpgI : primaryGenerator I = ∏ i ∈ A, p i := primaryGenerator_eq_poolProduct F hF I hIF
  have hpgJ : primaryGenerator J = ∏ i ∈ B, p i := primaryGenerator_eq_poolProduct F hF J hJF
  have hr : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i) := by
    rw [← hpgI, ← hpgJ]
    exact hray
  have hn : (∏ i ∈ A ∪ B, p i) = primaryGenerator I * primaryGenerator J := by
    rw [Finset.prod_union hd, ← hpgI, ← hpgJ]
  have hrowI (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) A z = quadraticRow I z :=
    (quadraticRow_eq_primaryPool F hF I hIF z).symm
  have hrowJ (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) B z = quadraticRow J z :=
    (quadraticRow_eq_primaryPool F hF J hJF z).symm
  have ht := same_ray_quadratic_pair_poisson R hinj S p (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    A B hd hr W M hM
  simpa only [hn, hrowI, hrowJ] using ht

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance PrimaryIdealUnitReindex

theorem canonical_pair_unit_invariant (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (u : Oˣ) (z : O) :
    quadraticRow I (u.val * z) * quadraticRow J (u.val * z) =
      quadraticRow I z * quadraticRow J z := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hcA : Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hcB : Pairwise (Function.onFun IsCoprime (fun i : B => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hr : residue (∏ i : A, p i.val) = residue (∏ i : B, p i.val) := by
    rw [Finset.prod_coe_sort, Finset.prod_coe_sort,
      ← primaryGenerator_eq_poolProduct F hF I hIF, ← primaryGenerator_eq_poolProduct F hF J hJF]
    exact hray
  have h := quadratic_pair_unit_invariant
    (fun i : A => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcA
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i : B => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcB
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val) hr u z
  have hrowI (w : O) : finiteSexticRow (fun i : A => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow I w :=
    (quadraticRow_eq_primarySubset F hF I hIF w).symm
  have hrowJ (w : O) : finiteSexticRow (fun i : B => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow J w :=
    (quadraticRow_eq_primarySubset F hF J hJF w).symm
  simpa only [hrowI, hrowJ] using h

theorem canonical_masked_pair_summable {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact quadraticRow_norm_le_one I z
      · exact quadraticRow_norm_le_one J z
    _ = _ := by ring

theorem canonical_pair_lattice_eq_primary_ideal_sum
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' lengthScale : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
      (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
      W ((Ideal.absNorm lengthScale.val : ℝ) / M) := by
  have hs := canonical_masked_pair_summable R S I J W M hM
  have hu (u : Oˣ) (lengthScale : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator lengthScale.val) *
        (quadraticRow I (u.val * primaryGenerator lengthScale.val) * quadraticRow J (u.val * primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (u.val * primaryGenerator lengthScale.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
        (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (primaryGenerator lengthScale.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, canonical_pair_unit_invariant I J hI hJ hray,
      norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  change (∑' z : O, if lambda ∣ z then (0 : ℂ) else _) = _ at ht
  have hn (lengthScale : GoodIdeal) := primaryGenerator_norm_sq lengthScale.val lengthScale.property
  simpa only [hn] using ht

theorem canonical_mask_lattice_eq_six_all_ideals
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (hmask : ∀ z : O, lambda ∣ z → rowCoprimeMask R S z = 0)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O,
      rowCoprimeMask R S (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) := by
  have ht := canonical_pair_lattice_eq_primary_ideal_sum R S I J hI hJ hray W M hM
  rw [card_units_eq_six] at ht
  have hl : (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M) := by
    apply tsum_congr
    intro z
    by_cases hz : lambda ∣ z
    · simp [hz, hmask z hz]
    · rw [ite_eq_right hz]
  rw [hl] at ht
  rw [ht]
  congr 1
  let f : Ideal O → ℂ := fun lengthScale => rowCoprimeMask R S (primaryGenerator lengthScale) *
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
    W ((Ideal.absNorm lengthScale : ℝ) / M)
  change (∑' lengthScale : GoodIdeal, f lengthScale.val) = ∑' lengthScale : Ideal O, f lengthScale
  have hsub : (∑' lengthScale : GoodIdeal, f lengthScale.val) =
      ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | primaryGenerator lengthScale ≠ 0} : Set (Ideal O)).indicator f lengthScale :=
    tsum_subtype _ f
  rw [hsub]
  apply tsum_congr
  intro lengthScale
  by_cases hg : primaryGenerator lengthScale ≠ 0
  · exact Set.indicator_of_mem hg f
  · rw [Set.indicator_of_notMem hg]
    have hz : primaryGenerator lengthScale = 0 := not_not.mp hg
    dsimp only [f]
    rw [hz, hmask 0 (dvd_zero _)]
    simp only [zero_mul]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

theorem supported_primaryGenerator_ne_zero (lengthScale : Ideal O) (hL : Supported lengthScale) :
    primaryGenerator lengthScale ≠ 0 :=
  primaryGenerator_ne_zero_of_good_factors lengthScale hL.1 (fun P hP => (hL.2 P hP).1)

theorem supported_span_primaryGenerator_iff (lengthScale : Ideal O) :
    Supported (Ideal.span {primaryGenerator lengthScale}) ↔ Supported lengthScale := by
  constructor
  · intro h
    have hn : primaryGenerator lengthScale ≠ 0 := by
      intro hz
      apply h.1
      simp [hz]
    rwa [(primaryGenerator_spec lengthScale hn).1] at h
  · intro h
    rw [(primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale h)).1]
    exact h

theorem badPrime_mask_primaryGenerator (lengthScale : Ideal O) :
    rowCoprimeMask badPrime Finset.univ (primaryGenerator lengthScale) = if Supported lengthScale then 1 else 0 := by
  rw [badPrime_mask, supported_span_primaryGenerator_iff]

theorem canonical_supported_lattice_eq_six_ideals
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask badPrime Finset.univ z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O, if Supported lengthScale then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask badPrime Finset.univ z = 0 := by
    rw [badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => ((supported_span_iff z).mp h).1 hz
    exact ite_eq_right hns
  rw [canonical_mask_lattice_eq_six_all_ideals badPrime Finset.univ hm I J hI hJ hray W M hM]
  congr 1
  apply tsum_congr
  intro lengthScale
  rw [badPrime_mask_primaryGenerator]
  by_cases hL : Supported lengthScale <;> simp [hL]

theorem canonical_supported_pair_poisson
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' lengthScale : Ideal O, if Supported lengthScale then χ (primaryGenerator lengthScale) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset Bool).powerset,
          let d := primeSubsetGenerator badPrime E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, badPrime i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hlat := canonical_same_ray_pair_poisson badPrime badPrime_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_supported_lattice_eq_six_ideals I J hI hJ hray W M hM
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0134

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
Source SHA256: c2b08f430b19873829799dc24def35482a4ee9c82b3c28f18636246960440381
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0135



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem supported_mul_iff (A B : Ideal O) : Supported (A * B) ↔ Supported A ∧ Supported B := by
  constructor
  · intro h
    have hA : A ≠ 0 := left_ne_zero_of_mul h.1
    have hB : B ≠ 0 := right_ne_zero_of_mul h.1
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inl hP)
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inr hP)
  · rintro ⟨hA, hB⟩
