      split_ifs <;> simp
    rw [hz]
    ring
  rw [heq]
  calc
    _ ≤ ∑ D ∈ B.powerset, ‖(-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ B.powerset,
        W * ‖operator A‖ ^ 2 * ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro D _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact weighted_energy_bound A (fun j => if D ⊆ support j then a j else 0) w W hW hw
    _ = _ := by
      rw [← Finset.mul_sum, masked_coefficient_energy B support hs a]

end CoprimeSieveOperator

namespace IdealCoprimeSieveOperator
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid

theorem primeSupport_disjoint_iff {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Disjoint (primeSupport I) (primeSupport J) ↔ IsCoprime I J := by
  constructor
  · intro h
    have hr : IsRelPrime I J := (isRelPrime_iff_no_prime_factors hI).mpr (by
      intro P hPI hPJ hP
      apply Finset.disjoint_left.mp h
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hI).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPI⟩
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hJ).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    exact associated_iff_eq.mp (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hr))
  · intro h
    exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors h.isRelPrime)

def supportConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose

theorem supportConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < supportConstant ε hε :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose_spec.1

theorem support_card_bound (ε : ℝ) (hε : 0 < ε) (I : Ideal O) (hI : I ≠ 0) :
    (2 : ℝ) ^ (primeSupport I).card ≤ supportConstant ε hε * (Ideal.absNorm I : ℝ) ^ ε :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose_spec.2 I hI

theorem ideal_coprime_gram_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (_hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if IsCoprime (column j) (column k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  let B : Finset (Ideal O) := Finset.univ.biUnion (fun j => primeSupport (column j))
  have hs (j : n) : primeSupport (column j) ⊆ B := by
    intro P hP
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩
  have h := coprime_gram_operator_bound B (fun j => primeSupport (column j)) hs A a w W hW hw
  simp_rw [primeSupport_disjoint_iff (hcol _) (hcol _)] at h
  apply h.trans
  have hmass : (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (support_card_bound ε hε (column j) (hcol j)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
        (supportConstant_pos ε hε).le)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hW (sq_nonneg ‖operator A‖))

open ConcretePrimeRowBridge

theorem actual_quadratic_coprime_gram_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ normalizedFactors I, goodLambda ∉ P)
    (r : m → O) (N : ℝ) (hN : 0 ≤ N)
    (hnorm : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ N)
    (a : F → ℂ) (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3
    ‖∑ i, w i * (∑ J : F, ∑ columnTwo : F,
      if IsCoprime J.val columnTwo.val then star (A i J * a J) * (A i columnTwo * a columnTwo) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ J : F, ‖a J‖ ^ 2 := by
  dsimp only
  exact ideal_coprime_gram_operator_bound ε hε (fun J : F => J.val)
    (fun J => hFpos J.val J.property) N hN (fun J => hnorm J.val J.property)
    (fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3) a w W hW hw

end IdealCoprimeSieveOperator

open scoped BigOperators Classical
namespace QuadraticMainOperatorBound
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary IdealCoprimeSieveOperator FiniteSieveOperator

def mainWeight (K : ℝ) (H D E : Ideal O) : ℂ :=
  (cutoffDifference K H D : ℂ) / (Real.sqrt (Ideal.absNorm (H * D * E) : ℝ) : ℂ)

theorem mainWeight_eq_zero_of_row_gt (K : ℝ) (H D E : Ideal O) (hD : D ≠ 0)
    (hH : K < (Ideal.absNorm H : ℝ)) : mainWeight K H D E = 0 := by
  have hc : cutoffDifference K H D = 0 := by
    by_contra h
    exact (not_le.mpr hH) ((cutoffDifference_nonzero_iff K H D hD).mp h).1
  simp [mainWeight, hc]

theorem mainWeight_norm_le (K : ℝ) (hK : 0 < K) (H D E : Ideal O)
    (hD : D ≠ 0) (hE : E ≠ 0) : ‖mainWeight K H D E‖ ≤ 1 / Real.sqrt K := by
  by_cases hc : cutoffDifference K H D = 0
  · simp [mainWeight, hc]
  have hn : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    exact lt_of_not_ge (fun h => hc (cutoffDifference_eq_zero_of_product_le K hD hE h))
  have hsq : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hle := Real.sqrt_le_sqrt hn.le
  rw [mainWeight, cutoffDifference_eq_neg_one_of_nonzero K H D hD hc]
  simp only [norm_div, Complex.ofReal_neg, Complex.ofReal_one, norm_neg, norm_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le hsq hle

theorem main_difference_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O)
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ)
    (r : Ideal O → Ideal O → n → ℂ) (hr : ∀ D E j, ‖r D E j‖ ≤ 1) :
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ j, ‖a j‖ ^ 2) := by
  let B := (1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
    ∑ j, ‖a j‖ ^ 2
  have hB : 0 ≤ B := by
    have hC := (supportConstant_pos ε hε).le
    dsimp [B]
    positivity
  have hterm (D : Ideal O) (hD : D ∈ idealDivisors G)
      (E : Ideal O) (hE : E ∈ idealDivisors G) :
      ‖(UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤ B := by
    have hD0 := IdealDivisorBound.divisor_ne_zero hG hD
    have hE0 := IdealDivisorBound.divisor_ne_zero hG hE
    have he := ideal_coprime_gram_operator_bound ε hε column hcol N hN hnorm A
      (fun j => a j * r D E j) (fun i => mainWeight K (H i) D E) (1 / Real.sqrt K)
      (by positivity) (fun i => mainWeight_norm_le K hK (H i) D E hD0 hE0)
    have hm : (∑ j, ‖a j * r D E j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hr D E j)
    have heB : ‖∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0)‖ ≤ B := by
      apply he.trans
      exact mul_le_mul_of_nonneg_left hm (by
        have hC := (supportConstant_pos ε hε).le
        positivity)
    have hmu : ‖(UniqueFactorizationMonoid.moebius E : ℂ)‖ ≤ 1 := by
      unfold UniqueFactorizationMonoid.moebius
      split_ifs <;> simp
    rw [norm_mul]
    calc
      _ ≤ 1 * B := mul_le_mul hmu heB (norm_nonneg _) (by norm_num)
      _ = B := one_mul B
  calc
    _ ≤ ∑ D ∈ idealDivisors G, ‖∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, B := by
      apply Finset.sum_le_sum
      intro D hD
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun E hE => hterm D hD E hE))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, B]; ring

open ConcretePrimeRowBridge ActualEisensteinCubic

theorem ideal_quadraticRow_norm_le_one (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (J : Ideal O) (z : O) : ‖(idealSexticRow F hFpos hFgood J z) ^ 3‖ ≤ 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  exact finiteSquarefreeRow_norm_le_one (fun i : primePool F => i.val)
    (primePool_good F hFgood) (idealSupport F J) z

theorem actual_quadratic_main_difference_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O) (g : Ideal O → O)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ J ∈ F, (Ideal.absNorm J : ℝ) ≤ N)
    (a : F → ℂ) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (g (H i))) ^ 3
    let r : Ideal O → Ideal O → F → ℂ := fun D E J =>
      (idealSexticRow F hFpos hFgood J.val (g D * g E)) ^ 3
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ J : F, ∑ columnTwo : F, if IsCoprime J.val columnTwo.val then
          star (A i J * (a J * r D E J)) * (A i columnTwo * (a columnTwo * r D E columnTwo)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ J : F, ‖a J‖ ^ 2) := by
  dsimp only
  apply main_difference_operator_bound ε hε K hK G hG H (fun J : F => J.val)
    (fun J => hFpos J.val J.property) N hN (fun J => hnorm J.val J.property)
  intro D E J
  exact ideal_quadraticRow_norm_le_one F hFpos hFgood J.val (g D * g E)

end QuadraticMainOperatorBound

end

end OAI
end OAIOriginalModule0105

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
Source SHA256: f2002647b815900d6d4bbae396d57735c5fcf3e933eb12e842e90519f42facfe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0106


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def blockRow {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) : ℂ :=
  finiteSexticRow (fun i : S => Ideal.span {p i.val}) (fun i => hg i.val) (fun i => e i.val) u

theorem blockRow_eq_product {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) :
    blockRow p hg S e u = ∏ i ∈ S,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u) :=
  Finset.prod_coe_sort S (fun i =>
    (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u))

theorem blockRow_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) (u : O) :
    blockRow p hg (S ∪ T) e u = blockRow p hg S e u * blockRow p hg T e u := by
  simp only [blockRow_eq_product, Finset.prod_union hd]

theorem blockRow_congr {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (hef : ∀ i ∈ S, e i = f i) (u : O) : blockRow p hg S e u = blockRow p hg S f u := by
  simp only [blockRow_eq_product]
  exact Finset.prod_congr rfl (fun i hi => by rw [hef i hi])

theorem blockRow_one {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 1) u = finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
  simp only [blockRow_eq_product, pow_one, finiteSquarefreeRow]

theorem blockRow_five {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 5) u = star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u) := by
  simp only [blockRow_eq_product, finiteSquarefreeRow, star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), canonicalSextic_conj_as_row_label]
  ring

theorem threeBlockRow_factor {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (u : O) :
    blockRow p hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) u =
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N u) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P u *
      blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
        (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) u := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  have hN : ∀ i ∈ N, threeBlockExponent N P v ε₁ ε₂ i = 5 := by
    intro i hi; simp [threeBlockExponent, hi]
  have hP : ∀ i ∈ P, threeBlockExponent N P v ε₁ ε₂ i = 1 := by
    intro i hi
    simp [threeBlockExponent, hi, show i ∉ N from fun hn => Finset.disjoint_left.mp hNP hn hi]
  have hC : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, threeBlockExponent N P v ε₁ ε₂ i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    simp [threeBlockExponent,
      show i ∉ N from fun hn => Finset.disjoint_left.mp hNC hn hi,
      show i ∉ P from fun hp => Finset.disjoint_left.mp hPC hp hi]
  rw [blockRow_union p hg (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    blockRow_union p hg N P hNP, blockRow_congr p hg N _ _ hN,
    blockRow_congr p hg P _ _ hP, blockRow_congr p hg _ _ _ hC,
    blockRow_five, blockRow_one]

theorem masked_block_radial_poisson_product {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
      W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) * canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) /
        (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, star (blockRow p hg S e h) * paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) := by
  let Q := fun i : S => Ideal.span {p i.val}
  let q := fun i : S => p i.val
  let hQ := columnPrimeCoprime p hcop S
  let j := fun i : S => e i.val
  have h := canonical_masked_radial_poisson_collected (fun i => Ideal.span {p i}) hinj M
    Q hQ (fun i => hg i.val) (fun i => hc i.val) j
    (fun i => he i.val i.property) (fun i => he6 i.val i.property) W lengthScale hL
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
    rw [GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q, Finset.prod_coe_sort]
  dsimp only at h
  rw [hn] at h
  have hrow : finiteSexticRow Q (fun i => hg i.val) j = blockRow p hg S e := rfl
  rw [hrow] at h
  rw [h]
  let a := fun E : Finset ι =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F := fun E : Finset ι => fun t : ℝ =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (lengthScale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2))
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset a F
  rw [hrow] at ht
  change ((lengthScale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hg i.val) j /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) * _ = _
  calc
    _ = ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
        ∑ E ∈ M.powerset, a E * ∑' h : O, star (blockRow p hg S e h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring

def cubeBaseFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) : ℂ :=
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
  gaussBlock p hp hg C e * blockRow p hg C e d * star (blockRow p hg C e h)

def threeGaussRowFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
    (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) *
    (blockRow p hg S e d * star (blockRow p hg S e h))

def cubeTransformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
    quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
    quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
    star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
      FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (d * crtLabel p B v ε₁ ε₂ true) N *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
    (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
      FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (d * crtLabel p B v ε₁ ε₂ false) P *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h))

theorem threeGaussRowFactor_eq_transformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  unfold threeGaussRowFactor
  dsimp only
  rw [a_weighted_three_cube_gauss p hp hcop hg hc hpr N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB]
  simp only [cubeTransformedPair, cubeBaseFactor,
    FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    finiteSquarefreeRow_mul, star_mul, star_star]
  ring

theorem a_weighted_three_block_radial_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (M N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
    let e := threeBlockExponent N P v ε₁ ε₂
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
        W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) *
              cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  dsimp only
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, ite_eq_right hn, ite_eq_right hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i < 6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W lengthScale hL]
  simp_rw [← threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  simp only [Finset.mul_sum, ← tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  unfold threeGaussRowFactor
  dsimp only
  ring

end FirstPassCubeLabels

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace LocalLogFourier

theorem coupled_positive_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let C : ℝ := B / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    simpa [C, B, P, b, K, Lwin, m] using hbound

end LocalLogFourier

namespace EisensteinSchwartzPoisson

theorem paperRadialFourier_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_schwartz V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end EisensteinSchwartzPoisson
end

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

section
abbrev O := ActualEisensteinCubic.O

variable {F : Type*} [Field F] [Fintype F]

def rootCard (F : Type*) [Fintype F] : ℝ := Real.sqrt (Fintype.card F)

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

def tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  (rootCard F : ℂ)⁻¹ * gaussSum (χ ^ j) ψ

def bracket (χ : MulChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  if j = 4 then
    (rootCard F : ℂ)⁻¹ * (-1 + (Fintype.card F : ℂ) * if x = 0 then 1 else 0)
  else if j = 0 then (rootCard F : ℂ)⁻¹ * (χ ^ 2)⁻¹ x
  else (χ ^ (j + 2))⁻¹ x

def phase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (ε : Fˣ) : ℂ :=
  if j = 4 then tau χ (ψ.mulShift (-1)) 4
  else if j = 0 then -tau χ ψ 2 * (χ ^ 2)⁻¹ ε
  else tau χ (ψ.mulShift (-1)) j * tau χ ψ (j + 2) * (χ ^ (j + 2))⁻¹ ε

theorem norm_tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχ : χ ^ j ≠ 1) (hψ : ψ.IsPrimitive) : ‖tau χ ψ j‖ = 1 :=
  ShortDraftGauss.norm_normalized_gaussSum (χ ^ j) ψ hχ hψ

theorem bracket_four_split (χ : MulChar F ℂ) (x : F) :
    bracket χ 4 x = -(rootCard F : ℂ)⁻¹ + (rootCard F : ℂ) * if x = 0 then 1 else 0 := by
  have hr : (rootCard F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard F : ℂ) ^ 2 = (Fintype.card F : ℂ) := by exact_mod_cast (rootCard_sq (F := F))
  simp only [bracket, ↓reduceIte]
  rw [← hsq]
  field_simp

theorem bracket_four_cube_split (χ : MulChar F ℂ) (n b : F) :
    bracket χ 4 (n * b ^ 3) = -(rootCard F : ℂ)⁻¹ +
      (rootCard F : ℂ) * (if n = 0 then 1 else 0) +
      (rootCard F : ℂ) * (if n ≠ 0 ∧ b = 0 then 1 else 0) := by
  rw [bracket_four_split]
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [hn, hb]

theorem bracket_zero_mask (χ : MulChar F ℂ) (j : ℕ) (hj : j ≠ 4) :
    bracket χ j 0 = 0 := by simp [bracket, hj]

theorem norm_bracket_nonexceptional (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) :
    ‖bracket χ j x‖ = if x = 0 then 0 else 1 := by
  simp only [bracket, ite_eq_right hj4, ite_eq_right hj0]
  by_cases hx : x = 0
  · simp [hx]
  · rw [ite_eq_right hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ (j + 2))⁻¹) (Units.mk0 x hx)

theorem norm_bracket_zero (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ = (rootCard F)⁻¹ * if x = 0 then 0 else 1 := by
  simp only [bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · rw [ite_eq_right hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ 2)⁻¹) (Units.mk0 x hx)

theorem norm_bracket_four_nonzero (χ : MulChar F ℂ) (x : F) (hx : x ≠ 0) :
    ‖bracket χ 4 x‖ = (rootCard F)⁻¹ := by
  rw [bracket_four_split]
  simp [hx, Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]

theorem norm_bracket_four_zero (χ : MulChar F ℂ) :
    ‖bracket χ 4 (0 : F)‖ = ((Fintype.card F : ℝ) - 1) / rootCard F := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  simp only [bracket, ↓reduceIte, mul_one, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg rootCard_pos.le]
  have heq : (-1 + (Fintype.card F : ℂ)) = (((Fintype.card F : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hq)]
  ring

end

section
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem shifted_power_nontrivial (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4) : χ ^ (j + 2) ≠ 1 := by
  by_cases hj : j = 5
  · subst j
    have heq : χ ^ (5 + 2) = χ ^ 1 := by
      rw [show (5 + 2 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul]
    rw [heq]
    exact hn 1 (by decide) (by decide)
  · exact hn (j + 2) (by omega) (by omega)

theorem phase_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ ^ 6 = 1) (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj6 : j < 6) (ε : Fˣ) :
    ‖phase χ ψ j ε‖ = 1 := by
  have hψminus : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (a := (-1 : F)) (by simp))
  by_cases hj4 : j = 4
  · subst j
    simp only [phase, ↓reduceIte]
    exact norm_tau χ _ 4 (hn 4 (by decide) (by decide)) hψminus
  by_cases hj0 : j = 0
  · subst j
    simp only [phase, ite_eq_right hj4, ↓reduceIte, norm_mul, norm_neg]
    rw [norm_tau χ ψ 2 (hn 2 (by decide) (by decide)) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num
  · simp only [phase, ite_eq_right hj4, ite_eq_right hj0, norm_mul]
    rw [norm_tau χ _ j (hn j hj0 hj6) hψminus,
      norm_tau χ ψ (j + 2) (shifted_power_nontrivial χ h6 hn j hj0 hj6 hj4) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num

end

open ActualEisensteinCubic

noncomputable local instance quotientField (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance quotientFintype (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_phase_norm (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (ε : (O ⧸ P)ˣ) :
    ‖phase (canonicalSextic P hgood) ψ j ε‖ = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact phase_norm (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (fun k hk0 hk6 => canonicalSextic_pow_ne_one P hgood hchar hk0 hk6) hψ j hj6 ε

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

variable {F : Type*} [Field F] [Fintype F]

def activeRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ *
    ∑ h : Fˣ, (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
      (((χ⁻¹) ^ 2) (σ * h)) * ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

open ActualEisensteinCubic
noncomputable local instance quotientFieldNormalized (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeNormalized (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_A5_normalized (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    activeRow (canonicalSextic P hgood) ψ j σ ε x =
      (((canonicalSextic P hgood)⁻¹) ^ 2) σ *
        phase (canonicalSextic P hgood) ψ j ε * bracket (canonicalSextic P hgood) j x := by
  let χ := canonicalSextic P hgood
  have hψne : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hr : (rootCard (O ⧸ P) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard (O ⧸ P) : ℂ) ^ 2 = (Fintype.card (O ⧸ P) : ℂ) := by
    exact_mod_cast (rootCard_sq (F := O ⧸ P))
  by_cases hj0 : j = 0
  · subst j
    have hh := canonical_A5_jzero_active P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte]
    rw [← hsq]
    field_simp
  by_cases hj4 : j = 4
  · subst j
    have hh := canonical_A5_jfour P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    have hqNat : 1 ≤ Fintype.card (O ⧸ P) := Fintype.card_pos_iff.mpr ⟨0⟩
    have hcardunits : (Fintype.card (O ⧸ P)ˣ : ℂ) = (Fintype.card (O ⧸ P) : ℂ) - 1 := by
      rw [Fintype.card_units, Nat.cast_sub hqNat, Nat.cast_one]
    have hsum : (if (ε : O ⧸ P) * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1) =
        -1 + (Fintype.card (O ⧸ P) : ℂ) * if x = 0 then 1 else 0 := by
      by_cases hx : x = 0
      · simp [hx, hcardunits]
        ring
      · simp [hx, mul_ne_zero (Units.ne_zero ε) hx]
    rw [hsum]
    simp only [phase, bracket, tau,  ↓reduceIte]
    rw [← hsq]
    field_simp
  · have hh := canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, ite_eq_right hj4, ite_eq_right hj0]
    rw [← hsq]
    field_simp

theorem canonical_A5_norm_eq_bracket (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      ‖bracket (canonicalSextic P hgood) j x‖ := by
  rw [canonical_A5_normalized P hgood hchar ψ hψ j hj6 σ ε x,
    norm_mul, norm_mul, canonical_phase_norm P hgood hchar ψ hψ j hj6 ε,
    FiniteRayExpansion.norm_char_unit, one_mul, one_mul]

theorem canonical_bracket_four_cube_split (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (n b : O) :
    bracket (canonicalSextic P hgood) 4 (Ideal.Quotient.mk P (n * b ^ 3)) =
      -(rootCard (O ⧸ P) : ℂ)⁻¹ + (rootCard (O ⧸ P) : ℂ) * (if n ∈ P then 1 else 0) +
      (rootCard (O ⧸ P) : ℂ) * (if n ∉ P ∧ b ∈ P then 1 else 0) := by
  rw [map_mul, map_pow, bracket_four_cube_split]
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

end LocalReflectionBrackets

end

end OAI
end OAIOriginalModule0106

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
Source SHA256: c5596f4c56825b5318dfc1c3edd3f6c5a24860b789ee448e64278ebfa0fda6e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0107


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

open scoped BigOperators Classical
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport firstPassColumnMinus firstPassColumnPlus)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)

def fixedRayExpansion {ι : Type*} (p : ι → O) (F S : Finset ι) : ℂ :=
  ∑ χ : RayCharacter, ∑ η : RayCharacter,
    crossCoeff χ η * supportRay p χ S * supportRay p η F

theorem fixedRayExpansion_eq_cross {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F S : Finset ι) (hd : Disjoint S F) :
    fixedRayExpansion p F S = quadraticCrossPhase p hg S F :=
  (RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc S F hd).symm

def cubeMinusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
    firstPassColumnMinus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ true) S

def cubePlusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
    firstPassColumnPlus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ false) S

def idealPairReindex {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (R : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ R.powerset,
      (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
      star (conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => star (supportRay p r.1 (recoveredSupport P (R \ D) I)) *
          C₁ (D ∪ recoveredSupport P (R \ D) I)) h) *
      conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => supportRay p r.2 (recoveredSupport P (R \ D) I) *
          C₂ (D ∪ recoveredSupport P (R \ D) I)) h

theorem threeGaussRowFactor_eq_ray_columns {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
        star (supportMobius (fun i => Ideal.span {p i}) N *
          cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d N *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
        (supportMobius (fun i => Ideal.span {p i}) P *
          cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d P *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) := by
  rw [threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  unfold cubeTransformedPair cubeMinusCoefficient cubePlusCoefficient
  rw [fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) N
      (hNB.mono_right (Finset.filter_subset _ _)),
    fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) P
      (hPB.mono_right (Finset.filter_subset _ _))]
  simp only [star_mul, star_star]
  ring

theorem sum_threeGaussRowFactor_eq_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (R B : Finset ι) (hRB : Disjoint R B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg R
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d) h := by
  let A := cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d
  let C := cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d
  have hsum :
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        quadraticCrossPhase p hg N P *
          star (supportMobius (fun i => Ideal.span {p i}) N * A N *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
          (supportMobius (fun i => Ideal.span {p i}) P * C P *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N hN
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hd : Disjoint N P
    · rw [ite_eq_left hd, ite_eq_left hd,
        threeGaussRowFactor_eq_ray_columns p hp hcop hg hc hpr N P B hd
          (hRB.mono_left (Finset.mem_powerset.mp hN))
          (hRB.mono_left (Finset.mem_powerset.mp hP))]
      dsimp only [A, C]
      ring
    · simp [hd]
  rw [hsum]
  congr 1
  exact FirstCauchyArithmetic.quadratic_phase_reindex_to_ideal_rows p hp hinj hg hc R A C h

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FourierBridge (logPhase logPhase_norm logPhase_continuous_left)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem two_variable_radial_separation (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
        ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K := by
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let M : Bool → ℝ := fun j => if j then M₂ else M₁
  have hM : ∀ j, 0 ≤ M j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j := by
    intro j; cases j
    · exact hV₁
    · exact hV₂
  obtain ⟨K, hK, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_schwartz
    W V (fun _ => -1) M hM hV A J
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hbound⟩ := hsep R hR
  refine ⟨b, ?_, hi, hbound⟩
  intro x y
  have hs := hb (fun j => if j then y else x)
  simpa only [V, Fintype.prod_bool, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    neg_one_mul, mul_neg_one, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hs

def logTwistMinus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * star (V (y S) * logPhase t (-(y S)))

def logTwistPlus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * (V (y S) * logPhase t (-(y S)))

theorem threeGaussRowFactor_log_twist {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (t : ℝ) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h =
    (V₁ (y₁ N) * logPhase t (-(y₁ N))) * (V₂ (y₂ P) * logPhase t (-(y₂ P))) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor, logTwistMinus, logTwistPlus, star_mul, star_star]
  ring

theorem integrable_log_pair (b : 𝓢(ℝ, ℂ)) (x y : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => b t * (logPhase t x * logPhase t y * c)) volume := by
  apply b.integrable.mul_bdd (c := ‖c‖)
  · exact (((logPhase_continuous_left x).mul (logPhase_continuous_left y)).mul_const c).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp only [norm_mul, logPhase_norm, one_mul, le_refl])

theorem smooth_cube_pairs_to_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
      Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N) - y₂ P))) *
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_separation W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hsep, hbint, hbnd⟩ := hs R hR
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, ite_eq_left hd]
      have hi := integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h)
      convert hi using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  refine ⟨b, hbint, hbnd, ?_, ?_⟩
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N) - y₂ P))) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, ite_eq_left hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

def primeProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) : ℝ :=
  ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

def columnLog {ι : Type*} (p : ι → O) (X : ℝ) (S : Finset ι) : ℝ :=
  Real.log (primeProductNorm p S / X)

def firstDualScale {ι : Type*} (p : ι → O) (C : Finset ι)
    (lengthScale X₁ X₂ : ℝ) (d h : O) : ℝ :=
  lengthScale * ‖eisEmbedding h‖ ^ 2 /
    (‖eisEmbedding d‖ ^ 2 * primeProductNorm p C * X₁ * X₂)

theorem actual_radial_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (N P C : Finset ι)
    (hNP : Disjoint N P) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (lengthScale X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (d h : O) :
    firstDualScale p C lengthScale X₁ X₂ d h * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) =
      lengthScale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ C)) := by
  rw [primeProductNorm_union p (N ∪ P) C (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    primeProductNorm_union p N P hNP]
  simp only [columnLog, sub_eq_add_neg, Real.exp_add, Real.exp_neg]
  rw [Real.exp_log (div_pos (primeProductNorm_pos p hp N) hX₁),
    Real.exp_log (div_pos (primeProductNorm_pos p hp P) hX₂)]
  simp only [firstDualScale, div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp [ne_of_gt hX₁, ne_of_gt hX₂]

def normalizedColumn {ι : Type*} (p : ι → O) (C : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  C S / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)

theorem threeGaussRowFactor_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (normalizedColumn p C₁) (normalizedColumn p C₂) d h =
    ((‖eisEmbedding (∏ i ∈ N, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ P, p i)‖ : ℂ)⁻¹) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hs (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  have hsi (x : ℝ) : star ((x : ℂ)⁻¹) = (x : ℂ)⁻¹ := by simp
  simp only [threeGaussRowFactor, normalizedColumn, div_eq_mul_inv, star_mul, hsi]
  ring

theorem actual_pair_prefactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (lengthScale : ℝ) (d h : O) :
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
        (normalizedColumn p C₁) (normalizedColumn p C₂) d h := by
  rw [threeGaussRowFactor_normalized]
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩), Finset.prod_union hNP]
  simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cube_integral_of_radial_separation {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (R : ℝ)
    (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * FourierBridge.logPhase t (-x)) *
        (V₂ y * FourierBridge.logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, ite_eq_left hd]
      convert integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  constructor
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, ite_eq_left hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t

theorem actual_first_kernel_to_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
        Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          idealPairReindex p hg F
            (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h) volume ∧
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
          ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
        ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          idealPairReindex p hg F
            (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_separation W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  let R := firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h
  have hR : 0 < R := by
    unfold R firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hb, hi, hbound⟩ := hs R hR
  have hpair := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂ (columnLog p X₁) (columnLog p X₂) R b hb
  refine ⟨b, hi, hbound, hpair.1, ?_⟩
  rw [← hpair.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [ite_eq_left hNP, ite_eq_left hNP]
    have hNB : Disjoint N B := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB : Disjoint P B := hFB.mono_left (Finset.mem_powerset.mp hP)
    have harg := actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _)) (hPB.mono_right (Finset.filter_subset _ _))
      lengthScale X₁ X₂ hX₁ hX₂ d h
    change R * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) = _ at harg
    rw [harg]
    have hpre := actual_pair_prefactor p hp hcop hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]

end FirstPassCubeLabels

open scoped BigOperators Classical
namespace QuadraticDivisorSplit
abbrev O := ActualEisensteinCubic.O

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm

open IdealMobiusDivisorSum

theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he

theorem residual_norm_le (D I : Ideal O) (hD : D ≠ 0) (N : ℝ)
    (hN : (Ideal.absNorm (D * I) : ℝ) ≤ N) :
    (Ideal.absNorm I : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hpos : (0 : ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (le_div_iff₀ hpos).mpr
  simpa only [map_mul, Nat.cast_mul, mul_comm] using hN

end QuadraticDivisorSplit

end

end OAI
end OAIOriginalModule0107

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
Source SHA256: d151b5efbcd982f613a10187cebc7105d0a7c2cb8559991e3ff178c31e49d2c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0108


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

namespace LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar

section
variable {F : Type*} [Field F] [Fintype F]

theorem bracket_eq_zero_iff (χ : MulChar F ℂ) (j : ℕ) (hj4 : j ≠ 4) (x : F) :
    bracket χ j x = 0 ↔ x = 0 := by
  have hr : (rootCard F : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos))
  by_cases hj0 : j = 0
  · simp only [bracket, ite_eq_right hj4, ite_eq_left hj0, mul_eq_zero, hr, false_or,
      MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not]
  · simp only [bracket, ite_eq_right hj4, ite_eq_right hj0, MulChar.apply_eq_zero_iff,
      isUnit_iff_ne_zero, not_not]

theorem norm_bracket_nonexceptional_le_one (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) : ‖bracket χ j x‖ ≤ 1 := by
  rw [norm_bracket_nonexceptional χ j hj4 hj0]
  split_ifs <;> norm_num

theorem norm_bracket_zero_le (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ ≤ (rootCard F)⁻¹ := by
  rw [norm_bracket_zero]
  split_ifs <;> simp only [mul_zero, mul_one, le_refl]
  exact inv_nonneg.mpr rootCard_pos.le

open ActualEisensteinCubic
noncomputable local instance quotientFieldBounds (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeBounds (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_A5_norm_cases (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      if j = 4 then
        (if x = 0 then ((Fintype.card (O ⧸ P) : ℝ) - 1) / rootCard (O ⧸ P)
         else (rootCard (O ⧸ P))⁻¹)
      else if j = 0 then (rootCard (O ⧸ P))⁻¹ * (if x = 0 then 0 else 1)
      else if x = 0 then 0 else 1 := by
  rw [canonical_A5_norm_eq_bracket P hgood hchar ψ hψ j hj6 σ ε x]
  by_cases hj4 : j = 4
  · subst j
    simp only [↓reduceIte]
    by_cases hx : x = 0
    · subst x
      simp only [↓reduceIte]
      exact norm_bracket_four_zero _
    · rw [ite_eq_right hx]
      exact norm_bracket_four_nonzero _ x hx
  · rw [ite_eq_right hj4]
    by_cases hj0 : j = 0
    · subst j
      simp only [↓reduceIte]
      exact norm_bracket_zero _ x
    · rw [ite_eq_right hj0]
      exact norm_bracket_nonexceptional _ j hj4 hj0 x

theorem actual_trace_A5_normalized (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ Ideal.span {p})ˣ) (x : O ⧸ Ideal.span {p}) :
    let χ := canonicalSextic (Ideal.span {p}) hgood
    let ψ := ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    activeRow χ ψ j σ ε x = ((χ⁻¹) ^ 2) σ * phase χ ψ j ε * bracket χ j x := by
  exact canonical_A5_normalized (Ideal.span {p}) hgood hchar _
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp) j hj6 σ ε x

theorem actual_bracket_four_divisibility_split (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (n b : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) 4 (Ideal.Quotient.mk (Ideal.span {p}) (n * b ^ 3)) =
      -(rootCard (O ⧸ Ideal.span {p}) : ℂ)⁻¹ +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if p ∣ n then 1 else 0) +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if ¬p ∣ n ∧ p ∣ b then 1 else 0) := by
  simpa only [Ideal.mem_span_singleton] using canonical_bracket_four_cube_split (Ideal.span {p}) hgood n b

theorem actual_bracket_zero_iff (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (j : ℕ) (hj4 : j ≠ 4) (n : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) j (Ideal.Quotient.mk (Ideal.span {p}) n) = 0 ↔ p ∣ n := by
  rw [bracket_eq_zero_iff _ j hj4, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem rootCard_span (p : O) [(Ideal.span {p}).IsMaximal] :
    rootCard (O ⧸ Ideal.span {p}) = ‖ConcreteTraceCRT.eisEmbedding p‖ := by
  rw [rootCard, ← Nat.card_eq_fintype_card]
  change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

end

variable {F : Type*} [Field F] [Fintype F]

def zeroFourierCoefficient (χ : MulChar F ℂ) (j : ℕ) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ t : F, (χ ^ j) t

theorem zeroFourierCoefficient_zero (χ : MulChar F ℂ) :
    zeroFourierCoefficient χ 0 = 1 - (Fintype.card F : ℂ)⁻¹ := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  rw [zeroFourierCoefficient, pow_zero, MulChar.sum_one_eq_card_units, Fintype.card_units,
    Nat.cast_sub hq, Nat.cast_one]
  field_simp

theorem zeroFourierCoefficient_nontrivial (χ : MulChar F ℂ) (j : ℕ) (hj : χ ^ j ≠ 1) :
    zeroFourierCoefficient χ j = 0 := by
  rw [zeroFourierCoefficient, MulChar.sum_eq_zero_of_ne_one hj, mul_zero]

theorem zeroFourierCoefficient_zero_norm_le_one (χ : MulChar F ℂ) :
    ‖zeroFourierCoefficient χ 0‖ ≤ 1 := by
  rw [zeroFourierCoefficient_zero]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hqpos : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le zero_lt_one hq
  have hinv : (Fintype.card F : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hqpos).mpr
    exact hq
  have hnonneg : 0 ≤ 1 - (Fintype.card F : ℝ)⁻¹ := sub_nonneg.mpr hinv
  have heq : (1 : ℂ) - (Fintype.card F : ℂ)⁻¹ = ((1 - (Fintype.card F : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  exact sub_le_self _ (inv_nonneg.mpr hqpos.le)

open ActualEisensteinCubic
noncomputable local instance quotientFieldInactive (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeInactive (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_zeroFourierCoefficient (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) (j : ℕ) (hj6 : j < 6) :
    zeroFourierCoefficient (canonicalSextic P hgood) j =
      if j = 0 then 1 - (Fintype.card (O ⧸ P) : ℂ)⁻¹ else 0 := by
  by_cases hj : j = 0
  · subst j
    simpa using zeroFourierCoefficient_zero (canonicalSextic P hgood)
  · rw [ite_eq_right hj]
    exact zeroFourierCoefficient_nontrivial _ j (canonicalSextic_pow_ne_one P hgood hchar hj hj6)

theorem finite_active_scalar_norm_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ ε : ∀ i, (O ⧸ P i)ˣ) :
    ‖∏ i, (((canonicalSextic (P i) (hgood i))⁻¹) ^ 2) (σ i) *
      phase (canonicalSextic (P i) (hgood i)) (ψ i) (j i) (ε i)‖ = 1 := by
  rw [norm_prod]
  have hlocal (i : ι) :
      ‖(((canonicalSextic (P i) (hgood i))⁻¹) ^ 2) (σ i) *
        phase (canonicalSextic (P i) (hgood i)) (ψ i) (j i) (ε i)‖ = 1 := by
    rw [norm_mul, FiniteRayExpansion.norm_char_unit,
      canonical_phase_norm (P i) (hgood i) (hchar i) (ψ i) (hψ i) (j i) (hj6 i) (ε i), one_mul]
  simp only [hlocal, Finset.prod_const_one]

end LocalReflectionBrackets

namespace EisensteinSchwartzPoisson
open MeasureTheory MeasureTheory.Measure Set Real
open scoped SchwartzMap FourierTransform

theorem complex_radial_norm_sq_integral (F : ℝ → ℂ) :
    (∫ z : ℂ, F (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by
  have hsub : (∫ r : ℝ in Ioi 0, (2 * r) • F (r ^ 2)) = ∫ t : ℝ in Ioi 0, F t := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
      using (integral_comp_rpow_Ioi_of_pos (g := F) (by norm_num : (0 : ℝ) < 2))
  have hsub' : (2 : ℂ) * (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) =
      ∫ t : ℝ in Ioi 0, F t := by
    simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_assoc, integral_const_mul] using hsub
  calc
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * F (p.1 ^ 2) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp only [Complex.norm_polarCoord_symm, sq_abs, Complex.real_smul]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) *
        ∫ _θ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp only [mul_one]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) * (2 * Real.pi : ℂ) := by
      congr 1
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter, volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]),
        sub_neg_eq_add, Complex.real_smul, mul_one]
      push_cast
      ring
    _ = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by rw [← hsub']; ring

theorem paperRadialFourier_zero_eq_halfline (F : ℝ → ℂ) :
    paperRadialFourier F 0 = (2 * Real.pi / Real.sqrt 3 : ℂ) *
      ∫ t : ℝ in Ioi 0, F t := by
  have he : paperE 0 = 1 := by simp [paperE_eq_exp]
  simp only [paperRadialFourier, paperFourier, Real.sqrt_zero, Complex.ofReal_zero,
    mul_zero, neg_zero, he, one_mul]
  rw [complex_radial_norm_sq_integral]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem quadratic_principal_zero_modes_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (fun t : ℝ => paperRadialFourier W (t ^ 2)) 0 =
      paperRadialFourier (fun t : ℝ => W (t ^ 2)) 0 := by
  rw [paperRadialFourier_zero_eq_halfline, paperRadialFourier_zero_eq_halfline,
    paperRadialFourier_halfline_integral]

def quadraticSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  horizontalSlice (radialTest W) 0

@[simp] theorem quadraticSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSquareProfile W x = W (x ^ 2) := by
  simp [quadraticSquareProfile, horizontalSlice_apply, complexPoint_eq,
    radialTest_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def quadraticTransformedSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))
      (horizontalSlice (𝓕 (radialTest W)) 0)

@[simp] theorem quadraticTransformedSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticTransformedSquareProfile W x = paperRadialFourier W (x ^ 2) := by
  simp only [quadraticTransformedSquareProfile, _root_.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, horizontalSlice_apply]
  rw [paperRadialFourier_square]
  simp only [complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero,
    SchwartzMap.fourier_coe, mul_comm x (2 / Real.sqrt 3)]
  rfl

theorem quadraticSquareProfile_principal_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (quadraticTransformedSquareProfile W) 0 =
      paperRadialFourier (quadraticSquareProfile W) 0 := by
  have h1 : (quadraticTransformedSquareProfile W : ℝ → ℂ) =
      fun x => paperRadialFourier W (x ^ 2) := by funext x; exact quadraticTransformedSquareProfile_apply W x
  have h2 : (quadraticSquareProfile W : ℝ → ℂ) = fun x => W (x ^ 2) := by
    funext x; exact quadraticSquareProfile_apply W x
  rw [h1, h2, quadratic_principal_zero_modes_equal]

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

theorem masked_principal_radial_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * ∑ E ∈ S.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
        ∑' h : O, paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
  let Q : Empty → Ideal O := Empty.elim
  let : ∀ i, (Q i).IsMaximal := fun i => nomatch i
  have hcop : Pairwise (Function.onFun IsCoprime Q) := by intro i; cases i
  have hg : ∀ i, lambda ∉ Q i := fun i => nomatch i
  have hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2 := fun i => nomatch i
  have hj0 : ∀ i : Empty, (1 : ℕ) ≠ 0 := fun i => nomatch i
  have hj6 : ∀ i : Empty, (1 : ℕ) < 6 := fun i => nomatch i
  have hp := canonical_masked_radial_poisson_collected P hinj S Q hcop hg hc
    (fun _ => 1) hj0 hj6 V M hM
  simpa only [finiteSexticRow_of_isEmpty, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    star_one, one_mul, one_pow, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast] using hp

def maskedPrincipalRemainder {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (V : ℝ → ℂ) (M : ℝ) : ℂ :=
  (M : ℂ) * ∑ E ∈ S.powerset,
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier V
      (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))

theorem masked_principal_radial_poisson_zero_split {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * paperRadialFourier V 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) +
        maskedPrincipalRemainder P S V M := by
  have hp (E : Finset ι) : 0 < (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hs (E : Finset ι) :
      (∑' h : O, paperRadialFourier V
        (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))) =
      paperRadialFourier V 0 +
        ∑' h : O, if h = 0 then 0 else paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
    have hsum := (paperRadialFourier_lattice_summable_norm V
      (M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) (div_pos hM (hp E))).of_norm
    have heq (h : O) : M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) * ‖eisEmbedding h‖ ^ 2 =
        M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by ring
    simp_rw [heq] at hsum
    simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      using hsum.tsum_eq_add_tsum_ite 0
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  rw [masked_principal_radial_poisson P hinj S V M hM]
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  rw [primeSubset_moebius_norm_sum P hprime hinj S]
  unfold maskedPrincipalRemainder
  ring

theorem quadratic_square_poisson_main_cancel {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z *
      paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) =
      maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M -
      maskedPrincipalRemainder P S (quadraticSquareProfile W) M := by
  have h1 := masked_principal_radial_poisson_zero_split P hinj S
    (quadraticTransformedSquareProfile W) M hM
  have h2 := masked_principal_radial_poisson_zero_split P hinj S (quadraticSquareProfile W) M hM
  simp only [quadraticTransformedSquareProfile_apply] at h1
  simp only [quadraticSquareProfile_apply] at h2
  rw [h1, h2, quadraticSquareProfile_principal_equal]
  ring

end ActualEisensteinCubic

open scoped BigOperators Classical
namespace PrimaryIdealUnitReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

abbrev GoodIdeal := {I : Ideal O // primaryGenerator I ≠ 0}
abbrev GoodElement := {z : O // primaryGenerator (Ideal.span {z}) ≠ 0}

theorem finite_units : Finite Oˣ := by
  let f : Oˣ → {z : O // z ∈ rowNormDisk 1} := fun u => ⟨u.val, by
    rw [mem_rowNormDisk]
    rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
    norm_num⟩
  exact Finite.of_injective f (fun u v h => Units.ext (congrArg Subtype.val h))

theorem span_unit_primary (u : Oˣ) (I : GoodIdeal) :
    Ideal.span {(u : O) * primaryGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact (primaryGenerator_spec I.val I.property).1

def unitIdealToElement (p : Oˣ × GoodIdeal) : GoodElement :=
  ⟨p.1.val * primaryGenerator p.2.val, by rw [span_unit_primary]; exact p.2.property⟩

theorem unitIdealToElement_injective : Function.Injective unitIdealToElement := by
  intro p q hpq
  have he : p.1.val * primaryGenerator p.2.val = q.1.val * primaryGenerator q.2.val :=
    congrArg Subtype.val hpq
  have hI : p.2 = q.2 := by
    apply Subtype.ext
    simpa only [span_unit_primary] using congrArg (fun z : O => Ideal.span {z}) he
  have hu : p.1 = q.1 := by
    apply Units.ext
    rw [hI] at he
    exact mul_right_cancel₀ q.2.property he
  exact Prod.ext hu hI

theorem unitIdealToElement_surjective : Function.Surjective unitIdealToElement := by
  intro z
  let I : GoodIdeal := ⟨Ideal.span {z.val}, z.property⟩
  have ha : Associated (primaryGenerator I.val) z.val :=
    Ideal.span_singleton_eq_span_singleton.mp (primaryGenerator_spec I.val I.property).1
  obtain ⟨u, hu⟩ := ha
  refine ⟨(u, I), Subtype.ext ?_⟩
  change u.val * primaryGenerator I.val = z.val
  simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × GoodIdeal ≃ GoodElement :=
  Equiv.ofBijective unitIdealToElement ⟨unitIdealToElement_injective, unitIdealToElement_surjective⟩

theorem tsum_good_elements_product (f : O → ℂ) :
    (∑' z : GoodElement, f z.val) =
      ∑' p : Oˣ × GoodIdeal, f (p.1.val * primaryGenerator p.2.val) := by
  exact (unitIdealEquiv.tsum_eq (fun z : GoodElement => f z.val)).symm

theorem tsum_good_elements_unit_invariant (f : O → ℂ)
    (hf : Summable (fun z : GoodElement => f z.val))
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : GoodElement, f z.val) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have hp : Summable (fun p : Oˣ × GoodIdeal => f (p.1.val * primaryGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr hf
  rw [tsum_good_elements_product, hp.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

theorem lambda_prime_actual : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K).zeta_sub_one_prime'

theorem primaryGenerator_ne_zero_of_good_factors (I : Ideal O) (hI : I ≠ 0)
    (hg : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, lambda ∉ P) :
    primaryGenerator I ≠ 0 := by
  rw [primaryGenerator, ite_eq_right hI]
  apply Multiset.prod_ne_zero
  intro hz
  obtain ⟨P, hP, hzero⟩ := Multiset.mem_map.mp hz
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  exact primaryPrime_ne_zero P (hg P hP) hzero

theorem primaryGenerator_span_ne_zero_iff (z : O) :
    primaryGenerator (Ideal.span {z}) ≠ 0 ↔ ¬ lambda ∣ z := by
  constructor
  · intro hg hdiv
    have hs := primaryGenerator_spec (Ideal.span {z}) hg
    have hzgen : z ∣ primaryGenerator (Ideal.span {z}) := by
      apply Ideal.mem_span_singleton.mp
      exact hs.1.le (Ideal.subset_span (by simp))
    have hgen := hdiv.trans hzgen
    have hminus : lambda ∣ primaryGenerator (Ideal.span {z}) - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hs.2
    have hone : lambda ∣ (1 : O) := by
      convert dvd_sub hgen hminus using 1 ; ring
    exact lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  · intro hdiv
    have hz : z ≠ 0 := by intro h; subst z; exact hdiv (dvd_zero _)
    have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
    apply primaryGenerator_ne_zero_of_good_factors _ hI
    intro P hP hlam
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzin : z ∈ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
      (Ideal.subset_span (by simp))
    have hcop : IsCoprime lambda z := lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hdiv
    obtain ⟨a, b, hab⟩ := hcop
    have hone : (1 : O) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left a hlam) (P.mul_mem_left b hzin)
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).mpr hone)

theorem tsum_ramified_mask (f : O → ℂ) :
    (∑' z : O, if lambda ∣ z then 0 else f z) = ∑' z : GoodElement, f z.val := by
  calc
    _ = ∑' z : O, ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O).indicator f z := by
      apply tsum_congr
      intro z
      simp only [Set.indicator, Set.mem_ofPred_eq, primaryGenerator_span_ne_zero_iff]
      split_ifs <;> rfl
    _ = _ := (tsum_subtype ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O) f).symm

theorem tsum_ramified_mask_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : O, if lambda ∣ z then 0 else f z) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  rw [tsum_ramified_mask]
  exact tsum_good_elements_unit_invariant f (hf.subtype _) hu

end PrimaryIdealUnitReindex

open scoped BigOperators Classical
namespace QuadraticUnitInvariance
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay

theorem principalNormalizedGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) :
    principalNormalizedGauss P hcop hg (fun _ => 3) c hc hc0 = quadraticGammaO c hc0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let e := (Ideal.quotEquivOfEq hc).trans (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (P i) (hg i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ P i) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hchar

theorem principalNormalizedGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) :
    principalNormalizedGauss P hcop hg (fun _ => 3) c hc hc0 = quadraticRayValue (residue c) := by
  rw [principalNormalizedGauss_three_eq_quadraticGamma P hcop hg hchar c hc hc0,
    quadraticGammaO_eq_rayValue]

theorem quadratic_unit_phase
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val *
      quadraticRayValue (residue (∏ i, p i)) =
        quadraticRayValue (residue (u.val * ∏ i, p i)) := by
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hn : Ideal.span {∏ i, p i} = ∏ i, Ideal.span {p i} := span_finset_prod _ _
  have hc : Ideal.span {u.val * ∏ i, p i} = ∏ i, Ideal.span {p i} := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hn]
  have h := principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hg (fun _ => 3)
    (u.val * ∏ i, p i) (∏ i, p i) hc hn (mul_ne_zero u.ne_zero hn0) hn0 u rfl
  rw [principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar,
    principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar] at h
  exact h.symm

theorem finiteSexticRow_three_star
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (z : O) :
    star (finiteSexticRow P hg (fun _ => 3) z) = finiteSexticRow P hg (fun _ => 3) z := by
  simp only [finiteSexticRow, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [canonicalSextic_pow_three_quadratic]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, star_intCast]

theorem quadratic_unit_value_eq_of_same_ray
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val =
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val := by
  have hne : quadraticRayValue (residue (∏ i, p i)) ≠ 0 := by
    rw [← canonicalProductGauss_three_eq_rayValue p hp hcop hg hchar]
    exact norm_ne_zero_iff.mp (by rw [norm_canonicalProductGauss p hp hcop hg hchar
      (fun _ => 3) (fun _ => by decide) (fun _ => by decide)]; norm_num)
  apply mul_right_cancel₀ hne
  rw [quadratic_unit_phase p hp hcop hg hchar, hray,
    quadratic_unit_phase q hq hcopq hgq hcharq, residue_mul, residue_mul, hray]

theorem quadratic_pair_unit_invariant
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) (z : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * z) *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * z) =
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z := by
  have hu := quadratic_unit_value_eq_of_same_ray p hp hcop hg hchar q hq hcopq hgq hcharq hray u
  have hs := finiteSexticRow_unit_mul_star (fun i => Ideal.span {q i}) hgq (fun _ => 3) u
  rw [finiteSexticRow_three_star] at hs
  rw [finiteSexticRow_mul, finiteSexticRow_mul, hu]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) := by ring
    _ = _ := by rw [hs, one_mul]

end QuadraticUnitInvariance

end

end OAI
end OAIOriginalModule0108

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound
Source SHA256: ec14257256dc7e0441b2fb52d435bde1627fa0c3a18523da27367d2de60029e2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0109


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

open scoped BigOperators Classical
namespace CoprimeBilinearSieve
open FiniteSieveOperator CoprimeSieveOperator CoprimeMobiusExtension

theorem disjoint_bilinear_expansion {ι n p : Type*} [DecidableEq ι]
    [Fintype n] [Fintype p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (z : n → ℂ) (v : p → ℂ) :
    (∑ j, ∑ k, if Disjoint (left j) (right k) then star (z j) * v k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (star (∑ j, if D ⊆ left j then z j else 0) *
          (∑ k, if D ⊆ right k then v k else 0)) := by
  have hp (j : n) (k : p) :
      (if Disjoint (left j) (right k) then star (z j) * v k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) := by
    calc
      _ = (if Disjoint (left j) (right k) then (1 : ℂ) else 0) *
          (star (z j) * v k) := by split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hl j) (hr k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      simp only [star_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ left j <;> by_cases hk : D ⊆ right k <;> simp [hj, hk]

theorem coprime_bilinear_operator_bound {ι m n p : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2) := by
  let X (D : Finset ι) (i : m) : ℂ := ∑ j, A i j * (if D ⊆ left j then a j else 0)
  let Y (D : Finset ι) (i : m) : ℂ := ∑ k, C i k * (if D ⊆ right k then b k else 0)
  have heq (i : m) :
      (∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card * (star (X D i) * Y D i) := by
    simpa only [X, Y, mul_ite, mul_zero] using
      disjoint_bilinear_expansion B left right hl hr (fun j => A i j * a j)
        (fun k => C i k * b k)
  have hnorm :
      (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0‖) ≤
        ∑ D ∈ B.powerset, ∑ i, ‖X D i‖ * ‖Y D i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D _
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_star]
    exact le_rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (B.powerset ×ˢ (Finset.univ : Finset m))
    (fun di => ‖X di.1 di.2‖) (fun di => ‖Y di.1 di.2‖)
  simp only [Finset.sum_product] at hCS
  have hX : (∑ D ∈ B.powerset, ∑ i, ‖X D i‖ ^ 2) ≤
      ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator A‖ ^ 2 *
          ∑ j, ‖if D ⊆ left j then a j else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound A _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B left hl a]
  have hY : (∑ D ∈ B.powerset, ∑ i, ‖Y D i‖ ^ 2) ≤
      ‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator C‖ ^ 2 *
          ∑ k, ‖if D ⊆ right k then b k else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound C _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B right hr b]
  exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2).trans
    (hCS.trans (mul_le_mul hX hY (by positivity) (by positivity)))

end CoprimeBilinearSieve

namespace IdealCoprimeBilinearSieve
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum IdealCoprimeSieveOperator FiniteSieveOperator

theorem support_weighted_energy_bound {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (support_card_bound ε hε (column j) (hcol j)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
      (supportConstant_pos ε hε).le)

theorem ideal_coprime_bilinear_operator_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε)
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (_hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let B : Finset (Ideal O) :=
    (Finset.univ.biUnion (fun j => primeSupport (left j))) ∪
      (Finset.univ.biUnion (fun k => primeSupport (right k)))
  have hl (j : n) : primeSupport (left j) ⊆ B := by
    intro P hP
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩))
  have hr (k : p) : primeSupport (right k) ⊆ B := by
    intro P hP
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hP⟩))
  have h := CoprimeBilinearSieve.coprime_bilinear_operator_bound B
    (fun j => primeSupport (left j)) (fun k => primeSupport (right k)) hl hr A C a b
  simp_rw [primeSupport_disjoint_iff (hl0 _) (hr0 _)] at h
  apply h.trans
  apply mul_le_mul
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (support_weighted_energy_bound ε hε left hl0 N₁ hlN a) (sq_nonneg ‖operator A‖)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (support_weighted_energy_bound ε hε right hr0 N₂ hrN b) (sq_nonneg ‖operator C‖)
  · positivity
  · have hpos := (supportConstant_pos ε hε).le
    positivity

end IdealCoprimeBilinearSieve

namespace DivisorBlockCauchy
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum FiniteSieveOperator IdealCoprimeSieveOperator

theorem divisor_mask_energy {n : Type*} [Fintype n]
    (S : Finset (Ideal O)) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      ∑ j, ((idealDivisors (column j)).card : ℝ) * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  have hsub : S.filter (fun D => D ∣ column j) ⊆ idealDivisors (column j) := by
    intro D hD
    exact (mem_idealDivisors (hcol j)).mpr (Finset.mem_filter.mp hD).2
  have hite (D : Ideal O) : ‖if D ∣ column j then a j else 0‖ ^ 2 =
      if D ∣ column j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

def divisorConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose

theorem divisorConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < divisorConstant ε hε :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.1

theorem divisor_mask_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O))
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  apply (divisor_mask_energy S column hcol a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2
    (column j) (hcol j)).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le) (divisorConstant_pos ε hε).le

theorem rectangular_cauchy {α β : Type*} (S : Finset α) (T : Finset β)
    (H : α → β → ℝ) (E : α → ℝ) (F : β → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hH : ∀ d ∈ S, ∀ e ∈ T, (H d e) ^ 2 ≤ C * E d * F e) :
    (∑ d ∈ S, ∑ e ∈ T, H d e) ^ 2 ≤
      (S.card : ℝ) * T.card * C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ T)
    (fun _ => (1 : ℝ)) (fun x => H x.1 x.2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hCS
  have hsum : (∑ d ∈ S, ∑ e ∈ T, (H d e) ^ 2) ≤
      C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
    calc
      _ ≤ ∑ d ∈ S, ∑ e ∈ T, C * E d * F e := by
        apply Finset.sum_le_sum
        intro d hd
        exact Finset.sum_le_sum (fun e he => hH d hd e he)
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  apply hCS.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ (S.card : ℝ) * T.card by positivity)

end DivisorBlockCauchy

namespace IdealDivisorBilinearBlocks
abbrev O := ActualEisensteinCubic.O
open FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def blockValue {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  ∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
    star (A D i j * (if D ∣ left j then a j else 0)) *
      (B E i k * (if E ∣ right k then b k else 0)) else 0‖

theorem blockValue_nonneg {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    0 ≤ blockValue left right A B a b D E :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ D ∈ S, ‖operator (A D)‖ ^ 2 ≤ UA)
    (hB : ∀ E ∈ T, ‖operator (B E)‖ ^ 2 ≤ UB) :
    (∑ D ∈ S, ∑ E ∈ T, blockValue left right A B a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card *
        (UA * UB * (supportConstant ε hε * N₁ ^ ε) *
          (supportConstant ε hε * N₂ ^ ε)) *
        ((divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let EL (D : Ideal O) : ℝ := ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2
  let ER (E : Ideal O) : ℝ := ∑ k, ‖if E ∣ right k then b k else 0‖ ^ 2
  let C : ℝ := UA * UB * (supportConstant ε hε * N₁ ^ ε) *
    (supportConstant ε hε * N₂ ^ ε)
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hEL (D) : 0 ≤ EL D := by dsimp [EL]; positivity
  have hER (E) : 0 ≤ ER E := by dsimp [ER]; positivity
  have hp (D : Ideal O) (hD : D ∈ S) (E : Ideal O) (hE : E ∈ T) :
      (blockValue left right A B a b D E) ^ 2 ≤ C * EL D * ER E := by
    have hh := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound
      ε hε left right hl0 hr0 N₁ N₂ hN₁ hN₂ hlN hrN (A D) (B E)
      (fun j => if D ∣ left j then a j else 0)
      (fun k => if E ∣ right k then b k else 0)
    change (blockValue left right A B a b D E) ^ 2 ≤
      (‖operator (A D)‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * EL D) *
      (‖operator (B E)‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ER E) at hh
    apply hh.trans
    calc
      _ ≤ (UA * (supportConstant ε hε * N₁ ^ ε) * EL D) *
          (UB * (supportConstant ε hε * N₂ ^ ε) * ER E) := by
        gcongr
        · exact hA D hD
        · exact hB E hE
      _ = _ := by dsimp [C]; ring
  have hc := rectangular_cauchy S T (blockValue left right A B a b) EL ER C hC hp
  have he1 := divisor_mask_energy_small_power ε hε S left hl0 N₁ hlN a
  have he2 := divisor_mask_energy_small_power ε hε T right hr0 N₂ hrN b
  apply hc.trans
  change (S.card : ℝ) * T.card * C * (∑ D ∈ S, EL D) * (∑ E ∈ T, ER E) ≤ _
  change (∑ D ∈ S, EL D) ≤ _ at he1
  change (∑ E ∈ T, ER E) ≤ _ at he2
  dsimp only [C]
  gcongr

end IdealDivisorBilinearBlocks

namespace FiniteSieveRestriction
open FiniteSieveOperator

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

def extendByZero (S : Finset n) (f : n → p) (u : n → ℂ) (k : p) : ℂ :=
  ∑ j ∈ S, if f j = k then u j else 0

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_apply_image (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) (j : n) (hj : j ∈ S) : extendByZero S f u (f j) = u j := by
  unfold extendByZero
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp only [ite_eq_right (fun h => hkj (hf hk hj h))]
  · exact fun h => (h hj).elim

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_zero (S : Finset n) (f : n → p) (u : n → ℂ)
    (k : p) (hk : k ∉ S.image f) : extendByZero S f u k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact ite_eq_right (fun h => hk (Finset.mem_image.mpr ⟨j, hj, h⟩))

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_energy (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) :
    (∑ k, ‖extendByZero S f u k‖ ^ 2) = ∑ j ∈ S, ‖u j‖ ^ 2 := by
  calc
    _ = ∑ k ∈ S.image f, ‖extendByZero S f u k‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [extendByZero_zero S f u k hk]
    _ = ∑ j ∈ S, ‖extendByZero S f u (f j)‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun j hj k hk h => hf hj hk h
    _ = _ := Finset.sum_congr rfl (fun j hj => by rw [extendByZero_apply_image S f u hf j hj])

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_matrix {m : Type*} (S : Finset n) (f : n → p)
    (u : n → ℂ) (A : Matrix m p ℂ) (i : m) :
    (∑ k, A i k * extendByZero S f u k) = ∑ j ∈ S, A i (f j) * u j := by
  simp only [extendByZero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (f j)]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

theorem masked_column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (S : Finset n) (f : n → p) (hf : Set.InjOn f S) (A : Matrix m p ℂ) :
    ‖operator (fun i j => if j ∈ S then A i (f j) else 0)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  let v : EuclideanSpace ℂ p := WithLp.toLp 2 (extendByZero S f u)
  have hv : ‖v‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖extendByZero S f u k‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2
    rw [extendByZero_energy S f u hf]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖u j‖)
  have heq : operator (fun i j => if j ∈ S then A i (f j) else 0) u = operator A v := by
    ext i
    change (∑ j, (if j ∈ S then A i (f j) else 0) * u j) =
      ∑ k, A i k * extendByZero S f u k
    rw [extendByZero_matrix]
    simp only [ite_mul, zero_mul, ← Finset.sum_filter]
    simp
  rw [heq]
  exact ((operator A).le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))

theorem column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix m p ℂ) :
    ‖operator (fun i j => A i (f j))‖ ≤ ‖operator A‖ := by
  simpa only [Finset.mem_univ, ite_true] using
    masked_column_restriction_norm_le Finset.univ f hf.injOn A

theorem row_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix p m ℂ) :
    ‖operator (fun i j => A (f i) j)‖ ≤ ‖operator A‖ := by
  let B : Matrix n m ℂ := fun i j => A (f i) j
  have h := column_restriction_norm_le f hf A.conjTranspose
  change ‖operator B.conjTranspose‖ ≤ ‖operator A.conjTranspose‖ at h
  rw [operator_conjTranspose_norm B, operator_conjTranspose_norm A] at h
  exact h

theorem submatrix_norm_le {m q : Type*} [Fintype m] [Fintype q]
    [DecidableEq m] [DecidableEq q]
    (r : m → q) (hr : Function.Injective r) (c : n → p) (hc : Function.Injective c)
    (A : Matrix q p ℂ) :
    ‖operator (fun i j => A (r i) (c j))‖ ≤ ‖operator A‖ :=
  (row_restriction_norm_le r hr (fun i j => A i (c j))).trans
    (column_restriction_norm_le c hc A)

end FiniteSieveRestriction

open scoped BigOperators
namespace FiniteSieveOperator

theorem squared_norm_le_of_energy {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a : n → ℂ, (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤ C * ∑ j, ‖a j‖ ^ 2) :
    ‖operator A‖ ^ 2 ≤ C := by
  have hop : ‖operator A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro a
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg a))).mp
    simpa only [mul_pow, Real.sq_sqrt hC, EuclideanSpace.norm_sq_eq, operator_apply] using h a
  simpa only [Real.sq_sqrt hC] using pow_le_pow_left₀ (norm_nonneg _) hop 2

end FiniteSieveOperator

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
abbrev O := ActualEisensteinCubic.O
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss

theorem idealSexticRow_ambient
    (F G : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥) (hGp : ∀ I ∈ G, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hGg : ∀ I ∈ G, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hIF : I ∈ F) (hIG : I ∈ G) (z : O) :
    idealSexticRow F hFp hFg I z = idealSexticRow G hGp hGg I z := by
  let idx (i : primePool F) (hi : i ∈ idealSupport F I) : primePool G :=
    ⟨i.val, mem_primePool_iff.mpr ⟨I, hIG, (mem_idealSupport_iff F I i).mp hi⟩⟩
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff G I (idx i hi)).mpr ((mem_idealSupport_iff F I i).mp hi)
  · intro i hi j hj hij
    exact Subtype.ext (congrArg (fun k : primePool G => k.val) hij)
  · intro j hj
    let i : primePool F := ⟨j.val, mem_primePool_iff.mpr
      ⟨I, hIF, (mem_idealSupport_iff G I j).mp hj⟩⟩
    have hi : i ∈ idealSupport F I :=
      (mem_idealSupport_iff F I i).mpr ((mem_idealSupport_iff G I j).mp hj)
    exact ⟨i, hi, Subtype.ext rfl⟩
  · intro i hi
    rfl

def Admissible (I : Ideal O) : Prop :=
  I ≠ 0 ∧ Squarefree I ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2

theorem singletonPositive (I : Ideal O) (h : Admissible I) : ∀ J ∈ ({I} : Finset (Ideal O)), J ≠ ⊥ := by
  intro J hJ
  rcases Finset.mem_singleton.mp hJ with rfl
  exact h.1

theorem singletonGood (I : Ideal O) (h : Admissible I) :
    ∀ J ∈ ({I} : Finset (Ideal O)), ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors J,
      goodLambda ∉ P := by
  intro J hJ P hP
  rcases Finset.mem_singleton.mp hJ with rfl
  exact (h.2.2 P hP).1

def quadraticRow (I : Ideal O) (z : O) : ℂ :=
  if h : Admissible I then
    (idealSexticRow {I} (singletonPositive I h) (singletonGood I h) I z) ^ 3
  else 0

theorem quadraticRow_eq (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hI : I ∈ F) (z : O) :
    quadraticRow I z =
      (idealSexticRow F (fun J hJ => (hF J hJ).1)
        (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I z) ^ 3 := by
  rw [quadraticRow, dite_eq_left (hF I hI)]
  congr 1
  exact idealSexticRow_ambient {I} F (singletonPositive I (hF I hI))
    (fun J hJ => (hF J hJ).1) (singletonGood I (hF I hI))
    (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I (Finset.mem_singleton_self I) hI z

def idealRange (X : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊X⌋₊).filter Admissible

theorem mem_idealRange {X : ℝ} {I : Ideal O} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem idealRange_mono {X Y : ℝ} (h : X ≤ Y) : idealRange X ⊆ idealRange Y := by
  intro I hI
  rcases mem_idealRange.mp hI with ⟨ha, hN⟩
  exact mem_idealRange.mpr ⟨ha, hN.trans h⟩

def matrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def sieveNorm (M N : ℝ) : ℝ := ‖FiniteSieveOperator.operator (matrix M N)‖ ^ 2

theorem sieveNorm_nonneg (M N : ℝ) : 0 ≤ sieveNorm M N := sq_nonneg _

def rangeInclusion {X Y : ℝ} (h : X ≤ Y) (I : idealRange X) : idealRange Y :=
  ⟨I.val, idealRange_mono h I.property⟩

theorem rangeInclusion_injective {X Y : ℝ} (h : X ≤ Y) :
    Function.Injective (rangeInclusion h) := by
  intro I J heq
  exact Subtype.ext (congrArg (fun x : idealRange Y => x.val) heq)

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  have h := FiniteSieveRestriction.submatrix_norm_le
    (rangeInclusion hM) (rangeInclusion_injective hM)
    (rangeInclusion hN) (rangeInclusion_injective hN) (matrix M' N')
  change ‖FiniteSieveOperator.operator (matrix M N)‖ ≤
    ‖FiniteSieveOperator.operator (matrix M' N')‖ at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (matrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem energy_bound (M N : ℝ) (a : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      sieveNorm M N * ∑ J, ‖a J‖ ^ 2 :=
  FiniteSieveOperator.energy_bound (matrix M N) a

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0109

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients
Source SHA256: f7f5d5b4e8d5ef142c0370928e926f16413cd76c852272d016080373a051c820
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0110




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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem primaryGenerator_admissible (I : Ideal O) (hI : Admissible I) : primaryGenerator I ≠ 0 :=
  PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors I hI.1
    (fun P hP => (hI.2.2 P hP).1)

theorem primaryGenerator_inj_on_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J) (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I (primaryGenerator_admissible I hI)).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J (primaryGenerator_admissible J hJ)).1

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => (hF I hI).1
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (hF I hI).2.2 P hP |>.1
  have hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2 := by
    intro i
    obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp i.property
    exact (hF I hI).2.2 i.val hP |>.2
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I (primaryGenerator_admissible I (mem_idealRange.mp hI).1)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3) =
        ∑ J : F, quadraticRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [quadraticRow_eq F hF J.val J.property z]
    simp only [aext, dite_eq_left J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 3 =
      (idealSexticRow F hFp hFg J.val z) ^ 3 * a J
    exact mul_comm _ _
  have he := QuadraticInitialBound.ideal_initial_quadratic_sieve F hFp hFg
    (fun I hI => (hF I hI).2.1) hchar ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dite_eq_left J.property]
    rfl
  rw [heR, hea] at he
  exact he

end

open ActualEisensteinCubic CompletedGauss

def idealQuotient (D I : Ideal O) : Ideal O := if h : D ∣ I then h.choose else 0

theorem idealQuotient_mul {D I : Ideal O} (h : D ∣ I) : D * idealQuotient D I = I := by
  rw [idealQuotient, dite_eq_left h]
  exact h.choose_spec.symm

theorem idealQuotient_dvd {D I : Ideal O} (h : D ∣ I) : idealQuotient D I ∣ I := by
  refine ⟨D, ?_⟩
  rw [mul_comm, idealQuotient_mul h]

theorem idealQuotient_injective_on (D : Ideal O) :
    Set.InjOn (idealQuotient D) {I | D ∣ I} := by
  intro I hI J hJ heq
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hI).symm
    _ = D * idealQuotient D J := by rw [heq]
    _ = J := idealQuotient_mul hJ

theorem admissible_of_dvd {I J : Ideal O} (hI : Admissible I) (hJI : J ∣ I) : Admissible J := by
  have hJ : J ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hJI
  refine ⟨hJ, hI.2.1.squarefree_of_dvd hJI, ?_⟩
  intro P hP
  have hfac := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hJ hI.1).mp hJI
  exact hI.2.2 P (Multiset.mem_of_le hfac hP)

theorem admissible_idealQuotient {D I : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) := admissible_of_dvd hI (idealQuotient_dvd hD)

theorem idealQuotient_norm_le {D I : Ideal O} (hD0 : D ≠ 0) (hD : D ∣ I)
    (N : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hp : (0 : ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD0 (Ideal.absNorm_eq_zero_iff.mp h))
  apply (le_div_iff₀ hp).mpr
  calc
    _ = (Ideal.absNorm (D * idealQuotient D I) : ℝ) := by
      rw [map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm I : ℝ) := by rw [idealQuotient_mul hD]
    _ ≤ N := hN

theorem quotient_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hdiv : ∀ j, D ∣ cols j) (M N : ℝ)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
  apply family_squared_norm_le rows (fun j => idealQuotient D (cols j)) hr
  · intro j k heq
    exact hc (idealQuotient_injective_on D (hdiv j) (hdiv k) heq)
  · exact hrows
  · intro j
    exact ⟨admissible_idealQuotient (hcols j).1 (hdiv j),
      idealQuotient_norm_le hD (hdiv j) N (hcols j).2⟩

def quotientMatrix {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) :
    Matrix m n ℂ := fun i j => if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0

theorem quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols) (M N : ℝ)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
  let S : Finset n := Finset.univ.filter (fun j => D ∣ cols j)
  let A : Matrix m S ℂ := fun i j =>
    quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i))
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
    apply quotient_family_squared_norm_le D hD rows (fun j : S => cols j.val) hr
      (hc.comp Subtype.val_injective)
    · intro j
      exact (Finset.mem_filter.mp j.property).2
    · exact hrows
    · intro j
      exact hcols j.val
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (sieveNorm_nonneg _ _)
  intro a
  have hinner (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, A i j * a j.val := by
    change (∑ j, (if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0) * a j) =
      ∑ j : S, quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i)) * a j.val
    rw [Finset.sum_coe_sort S (fun j : n =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) * a j)]
    simp only [S, Finset.sum_filter, ite_mul, zero_mul]
  simp_rw [hinner]
  have henergy := FiniteSieveOperator.energy_bound A (fun j : S => a j.val)
  apply henergy.trans
  calc
    _ ≤ sieveNorm M (N / (Ideal.absNorm D : ℝ)) * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sieveNorm_nonneg _ _)
      rw [Finset.sum_coe_sort S (fun j : n => ‖a j‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

end CanonicalQuadraticSieve

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace FourierBridge

def fourierSeminormBound (k : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ k * (k + 1) *
    (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C

def fourierPointBound (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ k * (fourierSeminormBound 0 C + fourierSeminormBound k C)

theorem fourierPointBound_nonneg (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ fourierPointBound k C := by unfold fourierPointBound fourierSeminormBound; positivity

theorem uniform_fourier_pointwise (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C)
    (t : ℝ) :
    S * (1 + ‖t‖) ^ k * ‖(𝓕 g) t‖ ≤ fourierPointBound k C := by
  have h0 : S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) ≤ fourierSeminormBound 0 C :=
    uniform_fourier_seminorm_transfer g 0 S C hS hC
      (fun i hi => hsource i (hi.trans (Nat.zero_le k)))
  have hk : S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤ fourierSeminormBound k C :=
    uniform_fourier_seminorm_transfer g k S C hS hC hsource
  have hpow : (1 + ‖t‖) ^ k ≤ (2 : ℝ) ^ k * (1 + ‖t‖ ^ k) := by
    have h := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) k
    have he : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    simp only [one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have hn0 := SchwartzMap.norm_le_seminorm ℝ (𝓕 g) t
  have hnk := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 g) k t
  calc
    _ ≤ S * ((2 : ℝ) ^ k * (1 + ‖t‖ ^ k)) * ‖(𝓕 g) t‖ := by gcongr
    _ = (2 : ℝ) ^ k * (S * ‖(𝓕 g) t‖ + S * (‖t‖ ^ k * ‖(𝓕 g) t‖)) := by ring
    _ ≤ (2 : ℝ) ^ k * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g)) := by gcongr
    _ ≤ fourierPointBound k C := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0 hk) (by positivity)

end FourierBridge

namespace LocalLogFourier

theorem coupled_positive_log_separation_envelope
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  let C : ℝ := (B + Bpoint) / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hBpoint : 0 ≤ Bpoint := FourierBridge.fourierPointBound_nonneg J P hP
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    have hb : (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ B / m ^ A := by
      simpa [B, P, b, K, Lwin, m] using hbound
    exact hb.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hBpoint) (by positivity))
  · intro t
    let g := positiveLogProfile V F R hVc hVs hFpos hR
    have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource (n : ℕ) (hn : n ≤ J) :
        (m ^ A * (1 + R) ^ A) *
          ((SchwartzMap.seminorm ℝ 0 n) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P := by
      apply positive_log_source_pair V F R m Lwin CW CF P A K n
        hVc hVs hFpos hR hm hm1 hL hCW hCF
      · dsimp [K]; omega
      · exact hVderiv
      · exact hwindow'
      · exact hEuler
      · intro i hi
        exact momentConstant_dominates K i Lwin CW CF hL hCW hCF hi
    have hpoint := FourierBridge.uniform_fourier_pointwise g J
      (m ^ A * (1 + R) ^ A) P (by positivity) hP hsource t
    have hb : (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ Bpoint / m ^ A := by
      apply (le_div_iff₀ (pow_pos hm A)).mpr
      simpa only [g, b, Bpoint, mul_assoc, mul_left_comm, mul_comm] using hpoint
    exact hb.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hB) (by positivity))

end LocalLogFourier

namespace EisensteinSchwartzPoisson

theorem paperRadialFourier_log_separation_envelope
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_envelope V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end EisensteinSchwartzPoisson
end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

def rayIdealRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  conjugateIdealRowSum (supportIdealFamily P (F \ D))
    (supportIdealFamily_pos P (F \ D)) (supportIdealFamily_good P hg (F \ D))
    (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
      else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C (D ∪ recoveredSupport P (F \ D) I)) h

def rayPairWeight {ι : Type*} (p : ι → O)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  crossCoeff r.1 r.2 * (supportMobius (fun i => Ideal.span {p i}) D *
    rowCoprimeMask (fun i => Ideal.span {p i}) D h * supportRay p r.1 D * supportRay p r.2 D)

def rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ *
      ‖rayIdealRow p hg F C negative (if negative then r.1 else r.2) D h‖ ^ 2

theorem rayIdealEnergy_nonneg {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) :
    0 ≤ rayIdealEnergy p hg F C negative h := by
  unfold rayIdealEnergy
  positivity

theorem idealPairReindex_eq_ray_rows {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    idealPairReindex p hg F C₁ C₂ h =
    ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      rayPairWeight p r D h * rayIdealRow p hg F C₂ false r.2 D h *
        star (rayIdealRow p hg F C₁ true r.1 D h) := by
  simp only [idealPairReindex, rayPairWeight, rayIdealRow, Bool.false_eq_true,
    ite_false, ite_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_congr rfl (fun D hD => by ring)

theorem idealPairReindex_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    ‖idealPairReindex p hg F C₁ C₂ h‖ ≤
      Real.sqrt (rayIdealEnergy p hg F C₁ true h) *
        Real.sqrt (rayIdealEnergy p hg F C₂ false h) := by
  rw [idealPairReindex_eq_ray_rows]
  have hc := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)
    (fun z => rayPairWeight p z.1 z.2 h)
    (fun z => rayIdealRow p hg F C₂ false z.1.2 z.2 h)
    (fun z => rayIdealRow p hg F C₁ true z.1.1 z.2 h)
  simp only [Finset.sum_product] at hc
  change ‖∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      rayPairWeight p r D h * rayIdealRow p hg F C₂ false r.2 D h *
        star (rayIdealRow p hg F C₁ true r.1 D h)‖ ≤
    Real.sqrt (rayIdealEnergy p hg F C₂ false h) *
      Real.sqrt (rayIdealEnergy p hg F C₁ true h) at hc
  exact hc.trans_eq (mul_comm _ _)

theorem norm_rayPairWeight {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) :
    ‖rayPairWeight p r D h‖ = ‖crossCoeff r.1 r.2‖ *
      ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ := by
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) D‖ = 1 := by
    have hh := FirstCauchyArithmetic.supportMobius_sq (fun i => Ideal.span {p i})
      (fun i => Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance) hinj D
    have hh' := congrArg norm hh
    simp only [norm_mul, norm_one] at hh'
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) D)]
  have hr (χ : RayCharacter) : ‖supportRay p χ D‖ = 1 := by
    obtain ⟨u, hu⟩ := RayFourExpansion.prime_product_unit_mod_four p hc D
    change ‖χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i))‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit χ u
  simp only [rayPairWeight, norm_mul, hmu, hr, one_mul, mul_one]

def cubeLogCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : O) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C V y t) d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C V y t) d

theorem cubeLogCoefficient_continuous {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (d : O) (S : Finset ι) :
    Continuous (fun t : ℝ => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t d S) := by
  cases negative <;>
    simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true,
      cubeMinusCoefficient, cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus]
  all_goals
    have hp := FourierBridge.logPhase_continuous_left (-(y S))
    fun_prop

theorem norm_cubeLogCoefficient_eq_zero {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : O) (S : Finset ι) :
    ‖cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t d S‖ =
    ‖cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y 0 d S‖ := by
  cases negative <;>
    simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true,
      cubeMinusCoefficient, cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus,
      norm_mul, norm_star, FourierBridge.logPhase_norm]

private theorem rayIdealRow_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    Continuous (fun t => rayIdealRow p hg F (C t) negative χ D h) := by
  simp only [rayIdealRow, ConcretePrimeRowBridge.conjugateIdealRowSum,
    ConcretePrimeRowBridge.mobiusIdealColumn]
  fun_prop

private theorem rayIdealRow_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖rayIdealRow p hg F (C t) negative χ D h‖ ≤ M := by
  let P := fun i => Ideal.span {p i}
  let s := supportIdealFamily P (F \ D)
  let T := fun (t : ℝ) (I : Ideal O) =>
    ConcretePrimeRowBridge.mobiusIdealColumn
      (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
        else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C t (D ∪ recoveredSupport P (F \ D) I)) I *
      star (ConcretePrimeRowBridge.idealSexticRow s (supportIdealFamily_pos P (F \ D))
        (supportIdealFamily_good P hg (F \ D)) I h)
  refine ⟨∑ I ∈ s, ‖T 0 I‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  change ‖∑ I ∈ s, T t I‖ ≤ _
  apply (norm_sum_le s (T t)).trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  simp only [T, ConcretePrimeRowBridge.mobiusIdealColumn, norm_mul, hC]

private theorem rayIdealEnergy_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => rayIdealEnergy p hg F (C t) negative h) := by
  unfold rayIdealEnergy
  apply continuous_finsetSum _
  intro r hr
  apply continuous_finsetSum _
  intro D hD
  exact continuous_const.mul ((rayIdealRow_continuous p hg F C hC negative _ D h).norm.pow 2)

private theorem rayIdealEnergy_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, rayIdealEnergy p hg F (C t) negative h ≤ M := by
  choose M hM hbound using fun (r : RayCharacter × RayCharacter) (D : Finset ι) =>
    rayIdealRow_uniform_bound p hg F C hC negative (if negative then r.1 else r.2) D h
  refine ⟨∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ * (M r D)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound r D t) 2)
    (norm_nonneg _)

private theorem integrable_rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => ‖b t‖ * rayIdealEnergy p hg F (C t) negative h) volume := by
  obtain ⟨M, hM, hb⟩ := rayIdealEnergy_uniform_bound p hg F C hn negative h
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (rayIdealEnergy_continuous p hg F C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (rayIdealEnergy_nonneg p hg F (C t) negative h)]
      exact hb t)

theorem cube_integral_norm_le_energy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : 𝓢(ℝ, ℂ)) (a : ℂ) :
    ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by
  let E₁ := fun t => rayIdealEnergy p hg F (C₁ t) true h
  let E₂ := fun t => rayIdealEnergy p hg F (C₂ t) false h
  let w := fun t : ℝ => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => rayIdealEnergy_nonneg p hg F (C₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => rayIdealEnergy_nonneg p hg F (C₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume := by
    convert (integrable_rayIdealEnergy p hg F C₁ hc₁ hn₁ true h b).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₁]
    ring
  have i₂ : Integrable (fun t => w t * E₂ t) volume := by
    convert (integrable_rayIdealEnergy p hg F C₂ hc₂ hn₂ false h b).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₂]
    ring
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (((b.continuous.norm.mul_const ‖a‖).mul
      (rayIdealEnergy_continuous p hg F C₁ hc₁ true h)))
  have hg' : Continuous g :=
    Real.continuous_sqrt.comp (((b.continuous.norm.mul_const ‖a‖).mul
      (rayIdealEnergy_continuous p hg F C₂ hc₂ false h)))
  have hfsq (t : ℝ) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : ℝ) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : ℝ) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (idealPairReindex_norm_le p hg F (C₁ t) (C₂ t) h) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, w t * E₁ t) * Real.sqrt (∫ t : ℝ, w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal

end FirstPassCubeLabels

end

end OAI
end OAIOriginalModule0110

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
Source SHA256: afb947f47c6a955e08508cf05a6d04b5382b7ecc6a0989c244d182dbde98ff26
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0111


namespace OAI

noncomputable section

namespace FirstPassCubeLabels

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def actualFirstKernel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ lengthScale : ℝ) (d h : O) : ℂ :=
  ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
    (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
    paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
      (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0

def firstColumnEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
    rayIdealEnergy p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (normalizedColumn p C) V (columnLog p X) t d) negative h

theorem firstColumnEnergy_nonneg {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) :
    0 ≤ firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative C V X d h b := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (rayIdealEnergy_nonneg _ _ _ _ _ _)

theorem actual_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_to_ideal_rows p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  obtain ⟨b, hi, hb, _, he⟩ := hs lengthScale hL d h hd hh
  refine ⟨b, hi, hb, ?_⟩
  let D₁ := fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
    (normalizedColumn p C₁) V₁ (columnLog p X₁) t d
  let D₂ := fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
    (normalizedColumn p C₂) V₂ (columnLog p X₂) t d
  have hiE := cube_integral_norm_le_energy p hg F D₁ D₂
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  change actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h = _ at he
  rw [he, norm_mul]
  have hn : ‖(lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)‖ =
      lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
      abs_of_nonneg (norm_nonneg _)]
  rw [hn, mul_assoc]
  exact mul_le_mul_of_nonneg_left hiE (div_nonneg hL.le (norm_nonneg _))

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

omit [DecidableEq ι] in
theorem row_four_star (S : Finset ι) (f h : O) :
    finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h) =
      star (finiteSquarefreeRow P hg S (h * f ^ 2)) := by
  have hf : star (finiteSquarefreeRow P hg S (f ^ 2)) =
      finiteSquarefreeRow P hg S f ^ 4 := by
    rw [row_pow, star_pow, finiteSquarefreeRow_conj_as_row_label]
    calc
      _ = finiteSquarefreeRow P hg S f ^ 4 * finiteSquarefreeRow P hg S f ^ 6 := by ring
      _ = _ := by
        rw [row_sixth]
        simpa only [pow_one] using row_power_mul_mask_power P hg S f 4 1 (by decide)
  rw [finiteSquarefreeRow_mul, star_mul, hf]

def beforeDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d *
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
    finiteSquarefreeRow P hg S f ^ 4

def afterDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S (c * jLabel p B v ε₁ ε₂) ^ 4 *
    finiteSquarefreeRow P hg S d * rowCoprimeMask P S (b0Label p B v ε₁ ε₂)

theorem beforeDilationLabel_union {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O)
    (S T : Finset ι) (hd : Disjoint S T) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f (S ∪ T) =
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f T := by
  simp only [beforeDilationLabel, row_union P hg S T hd, mask_union P hg S T hd, mul_pow]
  ring

omit [DecidableEq ι] in
theorem beforeDilationLabel_norm_le_one {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) :
    ‖beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S‖ ≤ 1 := by
  have hm : ‖rowCoprimeMask P S (cubeRadical p B)‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [beforeDilationLabel, norm_mul, norm_pow]
  calc
    _ ≤ (1:ℝ)^4 * 1 * (1 * 1^4 * 1) * 1^4 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one P hg S _
    _ = 1 := by norm_num

omit [DecidableEq ι] in
theorem beforeDilationLabel_star_row {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (side : Bool) (c d f h : O) (S : Finset ι) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      star (finiteSquarefreeRow P hg S h) =
    afterDilationLabel P hg p B v ε₁ ε₂ c d S *
      star (finiteSquarefreeRow P hg S (h * f^2 * dilationLabel p B v ε₁ ε₂)) := by
  unfold beforeDilationLabel afterDilationLabel
  calc
    _ = (finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d) *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        (finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h))) := by ring
    _ = _ := by
      rw [row_four_star, first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side]
      simp only [finiteSquarefreeRow_mul, mul_pow]
      ring
end Local

theorem rayIdealRow_eq_supportRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter) (h : O) :
    rayIdealRow p hg F C negative χ D h =
    supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
      (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) h := by
  symm
  exact FirstCauchyArithmetic.supportConjugateSum_eq_conjugateIdealRowSum
    (fun i => Ideal.span {p i}) hinj hg (F \ D) _ h

def dilatedRayColumn {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d y : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
    (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) *
      C (D ∪ U) * afterDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ c d U) y

theorem rayIdealRow_beforeDilation {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    rayIdealRow p hg F
      (fun S => C S * beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f S)
      negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      dilatedRayColumn p hg F D C negative χ q B v ε₁ ε₂ c d
        (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by
  rw [rayIdealRow_eq_supportRow p hinj]
  unfold dilatedRayColumn supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := by
    exact Finset.disjoint_left.mpr (fun i hiD hiU =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hiU)).2 hiD)
  dsimp only
  rw [beforeDilationLabel_union _ hg q B v ε₁ ε₂ side c d f D U hd]
  calc
    _ = beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f U *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) := by ring
    _ = _ := by
      rw [beforeDilationLabel_star_row _ hg q B v ε₁ ε₂ hv side c d f h U]
      ring

def originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) (S : Finset ι) : ℂ :=
  C S * rowCoprimeMask (fun i => Ideal.span {p i}) S (cubeRadical p B) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S
      (aLabel p B (if negative then ε₂ else ε₁) * c) ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4

def cubeCoreCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  if negative then
    star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      star (V (y S) * FourierBridge.logPhase t (-(y S)))
  else
    fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      (V (y S) * FourierBridge.logPhase t (-(y S)))

theorem cubeLogCoefficient_originalLabel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (c d f : O) (S : Finset ι) :
    cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d S =
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
  cases negative <;>
    simp only [cubeLogCoefficient, cubeCoreCoefficient, cubeMinusCoefficient,
      cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus,
      originalLabelColumn, beforeDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      finiteSquarefreeRow_mul, mul_pow] <;> ring

theorem rayIdealRow_cube_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
        negative χ p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
    fun S => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hp hcop hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact rayIdealRow_beforeDilation p hinj hg F D _ negative χ p B v ε₁ ε₂ hv negative c d f h

theorem first_cube_energy_small_power (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
      (y : Finset ι → ℝ) (t : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∑ x ∈ s, ‖w x‖ * ‖rayIdealRow p hg F
        (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1))
            V y t d) negative χ D x.2‖ ^ 2) ≤
      M * K * Y ^ deltaLoss * ∑ z ∈ T,
        ‖dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
          negative χ p B v ε₁ ε₂ c d z‖ ^ 2 := by
  obtain ⟨K, hK, hpush⟩ := SquarefreeDivisorBound.first_element_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C V y t c d s T w M Y hM hY hs hmap hT hnorm hw
  apply le_trans _ (hpush s T (dilationLabel p B v ε₁ ε₂) w
    (dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
      negative χ p B v ε₁ ε₂ c d) M Y hM hY hs hmap hT hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ C V y t c d,
    norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (beforeDilationLabel_norm_le_one _ hg p B v ε₁ ε₂ negative c d
      (ConcretePrimeRowBridge.idealGenerator x.1) D)

theorem normalized_originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) :
    normalizedColumn p (originalLabelColumn p hg B ε₁ ε₂ negative C c f) =
      originalLabelColumn p hg B ε₁ ε₂ negative (normalizedColumn p C) c f := by
  funext S
  simp only [normalizedColumn, originalLabelColumn, div_eq_mul_inv]
  ring

theorem firstColumnEnergy_original_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
