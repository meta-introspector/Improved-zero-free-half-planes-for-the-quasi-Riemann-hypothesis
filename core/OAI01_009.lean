          _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
              ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
                star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
                  canonicalProductG p hp hcop hgood) := by ring
          _ = _ := by rw [hα, one_mul]
  rw [hA]
  field_simp

end FiniteGaussPhase

end

end OAI
end OAIOriginalModule0087

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.ActiveConductor
Source SHA256: c7bef7d846cb76f5cc7fee07191f35e9ac89c6f9ee79877705c94e8872249ce2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0088



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

namespace ActualEisensteinCubic

section

 theorem activeSupport_nonempty_of_ne {α : Type*} [DecidableEq α]
    {S T : Finset α} (h : S ≠ T) : (activeSupport S T).Nonempty := by
  by_contra hn
  apply h
  have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  ext i
  simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
  exact ⟨fun hi => he.1 hi, fun hi => he.2 hi⟩

 theorem activeRow_zero_of_ne {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) {S T : Finset α} (h : S ≠ T) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) 0 = 0 := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne h).to_subtype
  exact finiteSexticRow_zero _ _ _

open ConcreteTraceCRT EisensteinSchwartzPoisson

 theorem finiteSexticRow_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 1 := by
  simp [finiteSexticRow]

 theorem finitePrimeModulus_norm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) : ‖eisEmbedding (finitePrimeModulus P)‖ = 1 := by
  have h := finitePrimeModulus_norm_sq P
  simp only [Finset.univ_eq_empty, Finset.prod_empty, map_one, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (finitePrimeModulus P))]

 theorem canonicalGaussSum_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalGaussSum P hcop hgood j = 1 := by
  let c := finitePrimeModulus P
  have hc : Ideal.span {c} = ⊤ := by
    simpa only [c, Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top] using
      span_finitePrimeModulus P
  have hzero (r : O ⧸ Ideal.span {c}) : r = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hc]; trivial)
  let : Subsingleton (O ⧸ Ideal.span {c}) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  unfold canonicalGaussSum
  change (∑ r : O ⧸ Ideal.span {c}, _ ) = 1
  rw [Fintype.sum_subsingleton _ 0]
  simp [principalSexticRow, finiteSexticQuotientRow]

 theorem canonicalNormalizedGauss_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j = 1 := by
  rw [canonicalNormalizedGauss, canonicalGaussSum_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, div_one]

noncomputable def squarefreePairPoissonZeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        (star (row 0) * paperRadialFourier W 0)

 theorem squarefreePairPoissonZeroMode_eq_zero_of_ne
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    {S T : Finset ι} (hST : S ≠ T) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S T W scale = 0 := by
  simp only [squarefreePairPoissonZeroMode, activeRow_zero_of_ne P hgood hST,
    star_zero, zero_mul, mul_zero, Finset.sum_const_zero]

 theorem squarefreePairPoissonZeroMode_diag
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ) := by
  have hempty : activeSupport S S = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport S S) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [squarefreePairPoissonZeroMode, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    Finset.inter_self, finiteSexticRow_of_isEmpty, star_one, one_mul]
  rw [← Finset.sum_mul]
  have hn (E : Finset ι) : ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
      (ConcretePrimeRowBridge.span_idealGenerator _)
  simp_rw [hn, Complex.ofReal_natCast]
  ring

end

open EisensteinSchwartzPoisson

theorem primeSubset_moebius_norm_sum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  simp only [Finset.prod_const_one, mul_one,  map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

theorem primeDensity_nonneg_le_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    0 ≤ (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ∧
      (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ≤ 1 := by
  have hfactor (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (P i) ∧
      1 - (1 : ℝ) / Ideal.absNorm (P i) ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Ideal.absNorm (P i) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (P i)))
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hnorm)
    · have : 0 ≤ (1 : ℝ) / Ideal.absNorm (P i) := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i _ => (hfactor i).1),
    Finset.prod_le_one₀ (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)⟩

theorem squarefreePairPoissonZeroMode_diag_product
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonZeroMode P hinj hgood S S W scale =
      (scale : ℂ) * paperRadialFourier W 0 *
        ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [squarefreePairPoissonZeroMode_diag, primeSubset_moebius_norm_sum P hprime hinj]

theorem norm_squarefreePairPoissonZeroMode_diag_le
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖squarefreePairPoissonZeroMode P hinj hgood S S W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ := by
  rw [squarefreePairPoissonZeroMode_diag_product P hprime]
  have hp : (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) =
      ((∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) : ℝ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hp, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeDensity_nonneg_le_one P S).1]
  exact mul_le_of_le_one_right (by positivity) (primeDensity_nonneg_le_one P S).2

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

noncomputable def idealPairPoissonZeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonZeroMode (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem weighted_idealPairPoissonZeroMode_eq_zero_of_ne
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F I ≠ idealSupport F J := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hI hJ hsI hsJ h)
      let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood I J W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.1)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsJ]
  · simp [baseChangeWeight_eq_zero_of_not_squarefree χ hsI]

theorem idealRowSum_zeroMode_diagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
      idealPairPoissonZeroMode F hFpos hFgood I I W scale := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  · intro J hJ hJI
    exact weighted_idealPairPoissonZeroMode_eq_zero_of_ne F hFpos hFgood
      χ A hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem norm_idealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2 := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨I, hI, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have hb : ‖idealPairPoissonZeroMode F hFpos hFgood I I W scale‖ ≤
      |scale| * ‖paperRadialFourier W 0‖ :=
    norm_squarefreePairPoissonZeroMode_diag_le (fun i : primePool F => i.val)
      hprime Subtype.val_injective (primePool_good F hFgood) (idealSupport F I) W scale
  nlinarith [mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖baseChangeWeight χ I * A (Ideal.absNorm I)‖)]

end ConcretePrimeRowBridge

open scoped BigOperators Classical SchwartzMap ContDiff
namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem activeRow_norm_le_one
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι) (h : O) :
    ‖finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) h‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (finiteSquarefreeRow_norm_le_one P hgood (S \ T) h)
      (finiteSquarefreeRow_norm_le_one P hgood (T \ S) h) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem activeRow_paperFourier_summable
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun h : O => star (finiteSexticRow (activePrimes P S T)
      (fun i => hgood i.val) (activeExponent S T) h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W scale hscale)
  intro h
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (activeRow_norm_le_one P hgood S T h)

theorem activeRow_paperFourier_zero_split
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) (den : ℝ) (hden : 0 < den) :
    let row := finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T)
    (∑' h : O, star (row h) * paperRadialFourier W
      (scale * ‖eisEmbedding h‖ ^ 2 / den)) =
      star (row 0) * paperRadialFourier W 0 +
        ∑' h : O, if h = 0 then 0 else star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / den) := by
  dsimp only
  have hs := activeRow_paperFourier_summable P hgood S T W
    (scale / den) (div_pos hscale hden)
  have heq (h : O) : scale / den * ‖eisEmbedding h‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 / den := by ring
  simp_rw [heq] at hs
  simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_div] using hs.tsum_eq_add_tsum_ite 0

noncomputable def squarefreePairPoissonNonzeroMode
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, if h = 0 then 0 else star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem squarefreePairPoissonKernel_zero_split
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    squarefreePairPoissonKernel P hinj hgood S T W scale =
      squarefreePairPoissonZeroMode P hinj hgood S T W scale +
        squarefreePairPoissonNonzeroMode P hinj hgood S T W scale := by
  unfold squarefreePairPoissonKernel squarefreePairPoissonZeroMode
    squarefreePairPoissonNonzeroMode
  dsimp only
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  have hden : 0 < ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
      ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr
      (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))
      (sq_pos_of_pos (norm_pos_iff.mpr
        (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero (activePrimes P S T)))))
  rw [activeRow_paperFourier_zero_split P hgood S T W scale hscale _ hden, mul_add]

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def idealPrimeDensity (F : Finset (Ideal O)) (I : Ideal O) : ℝ :=
  ∏ i ∈ idealSupport F I, (1 - (1 : ℝ) / Ideal.absNorm i.val)

theorem idealPrimeDensity_mem_Icc
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥) (I : Ideal O) :
    idealPrimeDensity F I ∈ Set.Icc (0 : ℝ) 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact primeDensity_nonneg_le_one (fun i : primePool F => i.val) (idealSupport F I)

theorem idealPairPoissonZeroMode_diag
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    idealPairPoissonZeroMode F hFpos hFgood I I W scale =
      (scale : ℂ) * paperRadialFourier W 0 * idealPrimeDensity F I := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.val := by
    obtain ⟨J, hJ, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  have heq := squarefreePairPoissonZeroMode_diag_product
    (fun i : primePool F => i.val) hprime Subtype.val_injective
    (primePool_good F hFgood) (idealSupport F I) W scale
  simpa only [idealPairPoissonZeroMode, idealPrimeDensity, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast] using heq

theorem idealRowSum_zeroMode_formula
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I := by
  rw [idealRowSum_zeroMode_diagonal F hFpos hFgood χ A W scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealPairPoissonZeroMode_diag]
  ring

noncomputable def idealPairPoissonNonzeroMode
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonNonzeroMode (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale

theorem idealPairPoissonKernel_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    idealPairPoissonKernel F hFpos hFgood I J W scale =
      idealPairPoissonZeroMode F hFpos hFgood I J W scale +
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonKernel_zero_split (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale hscale

theorem idealRowSum_smoothed_poisson_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, W (‖eisEmbedding u‖ ^ 2 / scale) *
      (↑(‖idealRowSum F hFpos hFgood χ A u‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖baseChangeWeight χ I * A (Ideal.absNorm I)‖ ^ 2) : ℂ) *
        idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
          (baseChangeWeight χ J * A (Ideal.absNorm J))) *
        idealPairPoissonNonzeroMode F hFpos hFgood I J W scale := by
  rw [idealRowSum_smoothed_poisson F hFpos hFgood hchar χ A W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [idealRowSum_zeroMode_formula F hFpos hFgood χ A W scale]

end ConcretePrimeRowBridge

namespace ShortDraftHeckeBridge

theorem norm_baseChangeWeight_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  by_cases hI : Squarefree I
  · simp only [baseChangeWeight, hI.moebius_eq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact χ.norm_le_one _
  · rw [ConcretePrimeRowBridge.baseChangeWeight_eq_zero_of_not_squarefree χ hI, norm_zero]
    exact zero_le_one

end ShortDraftHeckeBridge

namespace ConcretePrimeRowBridge

section
open ActualEisensteinCubic ShortDraftHeckeBridge EisensteinSchwartzPoisson

theorem norm_idealRowSum_zeroMode_le_test_mass
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (A : ℕ → ℂ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (baseChangeWeight χ I * A (Ideal.absNorm I)) *
        (baseChangeWeight χ J * A (Ideal.absNorm J))) *
      idealPairPoissonZeroMode F hFpos hFgood I J W scale‖ ≤
    (|scale| * ‖paperRadialFourier W 0‖) *
      ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  refine (norm_idealRowSum_zeroMode_le F hFpos hFgood χ A W scale).trans ?_
  gcongr with I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_baseChangeWeight_le_one χ I)

end

open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_image_eq_factors
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) :
    (idealSupport F I).image Subtype.val =
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
  ext P
  simp only [Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_idealSupport_iff F I p).mp hp
  · intro hP
    let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
    exact ⟨p, (mem_idealSupport_iff F I p).mpr hP, rfl⟩

theorem idealSupport_product_eq
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) (hsI : Squarefree I) :
    (∏ i ∈ idealSupport F I, i.val) = I := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    hsI.ne_zero).mp hsI
  calc
    _ = ∏ P ∈ (idealSupport F I).image Subtype.val, P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P := by
      rw [idealSupport_image_eq_factors F hI]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod = _
      rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hsI.ne_zero

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem activeSupport_product_mul_common_sq
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (P : ι → M) (S T : Finset ι) :
    (∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i) ^ 2 =
      (∏ i ∈ S, P i) * (∏ i ∈ T, P i) := by
  have hset : activeSupport S T = (S ∪ T) \ (S ∩ T) := by
    ext i
    simp only [activeSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsub : S ∩ T ⊆ S ∪ T := Finset.inter_subset_left.trans Finset.subset_union_left
  calc
    _ = ((∏ i ∈ activeSupport S T, P i) * (∏ i ∈ S ∩ T, P i)) *
      (∏ i ∈ S ∩ T, P i) := by rw [pow_two, mul_assoc]
    _ = (∏ i ∈ S ∪ T, P i) * (∏ i ∈ S ∩ T, P i) := by
      rw [hset, Finset.prod_sdiff hsub]
    _ = _ := Finset.prod_union_inter

theorem activePrimeModulus_norm_sq
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S T : Finset ι) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ activeSupport S T, P i) : ℝ) := by
  rw [finitePrimeModulus_norm_sq]
  congr 2
  exact Finset.prod_coe_sort (activeSupport S T) P

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_active_conductor_mul_common_sq
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J) :
    (∏ i ∈ activeSupport (idealSupport F I) (idealSupport F J), i.val) *
      (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) ^ 2 = I * J := by
  rw [primeSubsetProduct, activeSupport_product_mul_common_sq,
    idealSupport_product_eq F hI hsI, idealSupport_product_eq F hJ hsJ]

theorem idealPairPoisson_conductor_norm_sq
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [activePrimeModulus_norm_sq]
  have hn := congrArg (fun K : Ideal O => (Ideal.absNorm K : ℝ))
    (idealSupport_active_conductor_mul_common_sq F hI hJ hsI hsJ)
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using hn

theorem idealPairPoisson_conductor_norm_sq_of_weight_ne_zero
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hwI : baseChangeWeight χ I ≠ 0) (hwJ : baseChangeWeight χ J ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (finitePrimeModulus
      (activePrimes (fun i : primePool F => i.val) (idealSupport F I) (idealSupport F J)))‖ ^ 2 *
      (Ideal.absNorm (primeSubsetProduct F (idealSupport F I ∩ idealSupport F J)) : ℝ) ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  have hsI : Squarefree I := by
    by_contra h
    exact hwI (baseChangeWeight_eq_zero_of_not_squarefree χ h)
  have hsJ : Squarefree J := by
    by_contra h
    exact hwJ (baseChangeWeight_eq_zero_of_not_squarefree χ h)
  exact idealPairPoisson_conductor_norm_sq F hI hJ hsI hsJ

end ConcretePrimeRowBridge

end

end OAI
end OAIOriginalModule0088

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
Source SHA256: cb21f0e22054cbc24ce4cb9d0ba7cd69297c10482ad2418e5f4431eeb13cd13e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0089


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

namespace ActualEisensteinCubic

theorem cubicChar_reduce_ne_one (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q) :
    (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q) ≠ 1 := by
  intro hred
  apply cubicChar_ne_one P hPgood
  apply MulChar.ext
  intro u
  apply cubic_roots_reduce_injective Q hQgood
  · rw [← (cubicChar P hPgood).pow_apply_coe, cubicChar_pow_three]
    exact MulChar.one_apply_coe u
  · simp
  · have h := congrArg (fun χ : MulChar (O ⧸ P) (O ⧸ Q) => χ (u : O ⧸ P)) hred
    simpa only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one] using h

theorem cubicGauss_cube_of_nontrivial {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (hξ : (cubicChar P hgood).ringHomComp ι ≠ 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hξ3 : ξ ^ 3 = 1 := by
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
  have hξ2 : ξ * ξ ≠ 1 := by
    intro h2
    apply hξ
    calc
      ξ = ξ * (ξ * ξ) := by rw [h2, mul_one]
      _ = ξ ^ 3 := by rw [pow_succ, pow_two]; ac_rfl
      _ = 1 := hξ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hξ3
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hξneg : ξ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hξ3
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξ hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary, map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

theorem cubicGauss_cube_reduce {E : Type*} [Field E]
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (η : (O ⧸ Q) →+* E) (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hPgood).ringHomComp (η.comp (Ideal.Quotient.mk Q))) ψ ^ 3 =
      -(η (Ideal.Quotient.mk Q p)) * (Nat.card (O ⧸ P) : E) := by
  apply cubicGauss_cube_of_nontrivial _ P hPgood p hP hprimary _ ψ hψ
  have h := (MulChar.ringHomComp_ne_one_iff η.injective).mpr
    (cubicChar_reduce_ne_one P Q hPgood hQgood)
  exact h

end ActualEisensteinCubic

namespace CubicFrobenius

theorem card_cast_ne_zero (F F' : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] (hchar : ringChar F' ≠ ringChar F) :
    (Fintype.card F : F') ≠ 0 := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [hcard, Nat.cast_pow]
  apply pow_ne_zero
  intro hz
  have hd := (CharP.cast_eq_zero_iff F' (ringChar F') (ringChar F)).mp hz
  exact hchar ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F' _) hp).mp hd)

theorem gaussSum_pow_card (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (χ : MulChar F F') (ψ : AddChar F E) :
    gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' E))
        (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F' (ringChar F')
  have hchar := Algebra.ringChar_eq F' E
  have hpE : (ringChar E).Prime := hchar ▸ hp
  let : Fact (ringChar E).Prime := ⟨hpE⟩
  have hcardE : Fintype.card F' = ringChar E ^ (n : ℕ) := by simpa only [hchar] using hcard
  unfold gaussSum
  rw [hcardE, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← hcardE]
  change (algebraMap F' E (χ x)) ^ Fintype.card F' * ψ x ^ Fintype.card F' = _
  rw [← map_pow, FiniteField.pow_card, ← AddChar.mulShift_spec']
  rfl

theorem gauss_cube_residue_relation (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (hchar : ringChar F' ≠ ringChar F)
    (χ : MulChar F F') (hχ : χ ≠ 1) (ψ : AddChar F E) (hψ : ψ.IsPrimitive)
    (a : F') (m : ℕ) (hm : Fintype.card F' = 3 * m + 1)
    (hcube : gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ 3 = algebraMap F' E a) :
    χ (Fintype.card F' : F) * a ^ m = 1 := by
  let ξ := χ.ringHomComp (algebraMap F' E)
  have hξ : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (algebraMap F' E).injective).mpr hχ
  have hcard : (Fintype.card F : E) ≠ 0 := by
    rw [← map_natCast (algebraMap F' E)]
    exact (map_ne_zero (algebraMap F' E)).mpr (card_cast_ne_zero F F' hchar)
  have hg : gaussSum ξ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hξ hψ
  have hq : (Fintype.card F' : F) ≠ 0 := card_cast_ne_zero F' F hchar.symm
  let u : Fˣ := (isUnit_iff_ne_zero.mpr hq).unit
  have hu : (u : F) = Fintype.card F' := (isUnit_iff_ne_zero.mpr hq).unit_spec
  have hshift := gaussSum_mulShift ξ ψ u
  rw [hu, ← gaussSum_pow_card F F' E χ ψ] at hshift
  have hp : gaussSum ξ ψ ^ Fintype.card F' =
      algebraMap F' E (a ^ m) * gaussSum ξ ψ := by
    rw [hm, pow_succ, pow_mul, hcube, map_pow]
  rw [hp] at hshift
  have hone : ξ (Fintype.card F' : F) * algebraMap F' E (a ^ m) = 1 := by
    apply mul_right_cancel₀ hg
    simpa only [mul_assoc, one_mul] using hshift
  apply (algebraMap F' E).injective
  simpa only [ξ, map_mul, map_one, MulChar.ringHomComp_apply] using hone

end CubicFrobenius

namespace ActualEisensteinCubic

theorem cubic_primary_frobenius_relation (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O))) = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Field (O ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fintype (O ⧸ Q) := Fintype.ofFinite _
  let ψ := AddChar.FiniteField.primitiveChar (O ⧸ P) (O ⧸ Q) hchar
  let E := CyclotomicField ψ.n (O ⧸ Q)
  let η : (O ⧸ Q) →+* E := algebraMap (O ⧸ Q) E
  let χ := (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q)
  let a : O ⧸ Q := -(Ideal.Quotient.mk Q p) * (Fintype.card (O ⧸ P) : O ⧸ Q)
  let m := (Fintype.card (O ⧸ Q) - 1) / 3
  have hqdiv : 3 ∣ Fintype.card (O ⧸ Q) - 1 := by
    simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three Q hQgood
  have hqpos : 0 < Fintype.card (O ⧸ Q) := Fintype.card_pos
  have hm : Fintype.card (O ⧸ Q) = 3 * m + 1 := by
    dsimp [m]
    omega
  have hcube : gaussSum (χ.ringHomComp η) ψ.char ^ 3 = η a := by
    have hc := cubicGauss_cube_reduce P Q hPgood hQgood p hP hprimary η ψ.char ψ.prim
    convert hc using 1
    · rfl
    · simp only [a, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card]
  have hrel := CubicFrobenius.gauss_cube_residue_relation (O ⧸ P) (O ⧸ Q) E
    hchar χ (cubicChar_reduce_ne_one P Q hPgood hQgood) ψ.char ψ.prim a m hm hcube
  have heuler := cubicChar_reduce Q hQgood
    (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))
  have heuler' : Ideal.Quotient.mk Q
      (cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = a ^ m := by
    simpa only [a, m, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card] using heuler
  rw [← heuler'] at hrel
  change Ideal.Quotient.mk Q (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) *
    Ideal.Quotient.mk Q (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = 1 at hrel
  have hx : (Fintype.card (O ⧸ Q) : O ⧸ P) ≠ 0 :=
    CubicFrobenius.card_cast_ne_zero (O ⧸ Q) (O ⧸ P) hchar.symm
  have hy : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) ≠ 0 := by
    intro hz
    rw [hz, MulChar.map_zero, map_zero, mul_zero] at hrel
    exact zero_ne_one hrel
  have hxcube : (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  have hycube : (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)
  have hprod : cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O))) = 1 := by
    apply cubic_roots_reduce_injective Q hQgood
    · rw [mul_pow, hxcube, hycube, mul_one]
    · simp
    · simpa only [map_mul, map_one] using hrel
  have hminus : cubicChar Q hQgood (-1 : O ⧸ Q) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (cubicChar_pow_three Q hQgood)
  have hneg : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) =
      (-1) * Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O)) := by
    simp only [map_mul, map_neg, map_natCast]
    ring
  rw [hneg, map_mul, hminus, one_mul] at hprod
  simpa only [Nat.card_eq_fintype_card] using hprod

theorem cubic_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  have hPQ := cubic_primary_frobenius_relation P Q hPgood hQgood hchar p hP hpprimary
  have hQP := cubic_primary_frobenius_relation Q P hQgood hPgood hchar.symm q hQ hqprimary
  simp only [map_mul, map_natCast] at hPQ hQP
  let U := cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P)
  let V := cubicChar Q hQgood (Nat.card (O ⧸ P) : O ⧸ Q)
  have hB : cubicChar Q hQgood (Ideal.Quotient.mk Q p) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hPQ
  have hA : cubicChar P hPgood (Ideal.Quotient.mk P q) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hQP
  have hUV : U * V ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hA
    exact zero_ne_one hA
  exact mul_right_cancel₀ hUV (hA.trans hB.symm)

theorem canonicalSextic_sq_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
    p q hP hQ hpprimary hqprimary]

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem norm_eisEmbedding_unit (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

@[simp] theorem norm_eisEmbedding_unit_mul (u : Oˣ) (a : O) :
    ‖eisEmbedding ((u : O) * a)‖ = ‖eisEmbedding a‖ := by
  rw [map_mul, norm_mul, norm_eisEmbedding_unit, one_mul]

theorem finiteSexticRow_unit_mul_star {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (u : Oˣ) :
    finiteSexticRow P hgood j (u : O) * star (finiteSexticRow P hgood j (u : O)) = 1 := by
  unfold finiteSexticRow
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk (P i)))

def principalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) /
      (‖eisEmbedding c‖ : ℂ)

theorem canonicalNormalizedGauss_eq_principal {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j =
      principalNormalizedGauss P hcop hgood j (finitePrimeModulus P)
        (span_finitePrimeModulus P) (finitePrimeModulus_ne_zero P) := rfl

theorem principal_gauss_sum_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n)
    [Fintype (O ⧸ Ideal.span {c})] [Fintype (O ⧸ Ideal.span {n})] :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) =
      finiteSexticRow P hgood j (u : O) *
        ∑ r : O ⧸ Ideal.span {n}, principalSexticRow P hcop hgood j n hn r *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0 r := by
  let e₀ := Ideal.quotEquivOfEq (hn.trans hc.symm)
  let ū : (O ⧸ Ideal.span {n})ˣ := Units.map (Ideal.Quotient.mk (Ideal.span {n})).toMonoidHom u
  let e : (O ⧸ Ideal.span {n}) ≃ (O ⧸ Ideal.span {c}) := ū.mulLeft.trans e₀.toEquiv
  have he (a : O) : e (Ideal.Quotient.mk (Ideal.span {n}) a) =
      Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a) := by
    change e₀ (Ideal.Quotient.mk (Ideal.span {n}) (u : O) *
      Ideal.Quotient.mk (Ideal.span {n}) a) = _
    rw [← map_mul, Ideal.quotEquivOfEq_mk]
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he, principalSexticRow_mk, principalSexticRow_mk, finiteSexticRow_mul]
  have hphase : eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
      (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a)) =
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0
        (Ideal.Quotient.mk (Ideal.span {n}) a) := by
    rw [eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE, hcn, map_mul, map_mul]
    congr 1
    field_simp [eisEmbedding_ne_zero u.ne_zero]
  rw [hphase]
  ring

theorem principalNormalizedGauss_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n) :
    principalNormalizedGauss P hcop hgood j c hc hc0 =
      finiteSexticRow P hgood j (u : O) *
        principalNormalizedGauss P hcop hgood j n hn hn0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hn0
  let : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  unfold principalNormalizedGauss
  rw [principal_gauss_sum_unit_change P hcop hgood j c n hc hn hc0 hn0 u hcn]
  rw [hcn, norm_eisEmbedding_unit_mul]
  ring

theorem principalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    principalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j (∏ i, p i)
      (span_finset_prod Finset.univ p) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) =
      canonicalProductGauss p hp hcop hgood j := rfl

theorem exists_modulus_unit {ι : Type*} [Fintype ι] (p : ι → O) :
    ∃ u : Oˣ, finitePrimeModulus (fun i => Ideal.span {p i}) = (u : O) * ∏ i, p i := by
  have hs : Ideal.span {∏ i, p i} =
      Ideal.span {finitePrimeModulus (fun i => Ideal.span {p i})} := by
    rw [span_finitePrimeModulus, span_finset_prod]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def modulusUnit {ι : Type*} [Fintype ι] (p : ι → O) : Oˣ :=
  Classical.choose (exists_modulus_unit p)

theorem modulusUnit_spec {ι : Type*} [Fintype ι] (p : ι → O) :
    finitePrimeModulus (fun i => Ideal.span {p i}) = (modulusUnit p : O) * ∏ i, p i :=
  Classical.choose_spec (exists_modulus_unit p)

theorem canonicalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j =
      finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
        canonicalProductGauss p hp hcop hgood j := by
  rw [canonicalNormalizedGauss_eq_principal,
    principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hgood j
      (finitePrimeModulus (fun i => Ideal.span {p i})) (∏ i, p i)
      (span_finitePrimeModulus _) (span_finset_prod Finset.univ p)
      (finitePrimeModulus_ne_zero _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (modulusUnit p) (modulusUnit_spec p), principalNormalizedGauss_eq_product]

theorem canonicalNormalizedGauss_frequency_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (h : O) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j ((modulusUnit p : O) * h)) =
      canonicalProductGauss p hp hcop hgood j *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood j,
    finiteSexticRow_mul, star_mul]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O))) *
        (canonicalProductGauss p hp hcop hgood j *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h)) := by ring
    _ = _ := by rw [finiteSexticRow_unit_mul_star, one_mul]

theorem gauss_weighted_radial_sum_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
        F (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F (‖eisEmbedding h‖ ^ 2)) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  calc
    _ = ∑' h : O, canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        (star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j
          ((modulusUnit p : O) * h)) * F (‖eisEmbedding ((modulusUnit p : O) * h)‖ ^ 2)) :=
      ((modulusUnit p).mulLeft.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [norm_eisEmbedding_unit_mul, ← mul_assoc,
        canonicalNormalizedGauss_frequency_transport p hp hcop hgood j, mul_assoc]

theorem gauss_weighted_finite_radial_sum_transport {ι κ : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (D : Finset κ) (a : κ → ℂ) (F : κ → ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑ k ∈ D, a k * ∑' h : O,
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑ k ∈ D, a k * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            F k (‖eisEmbedding h‖ ^ 2)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a k * (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [gauss_weighted_radial_sum_transport p hp hcop hgood j]; ring

theorem finitePrimeModulus_norm_eq_product {ι : Type*} [Fintype ι] (p : ι → O) :
    ‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖ =
      ‖eisEmbedding (∏ i, p i)‖ := by
  rw [modulusUnit_spec p, norm_eisEmbedding_unit_mul]

theorem canonical_radial_poisson_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow (fun i => Ideal.span {p i}) hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalProductGauss p hp hcop hgood j /
        (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2) := by
  have h := canonical_radial_poisson_normalized (fun i => Ideal.span {p i})
    hcop hgood hchar j hj0 hj6 W scale hscale
  dsimp only at h
  rw [finitePrimeModulus_norm_eq_product p] at h
  rw [h]
  have ht := gauss_weighted_radial_sum_transport p hp hcop hgood j
    (fun t => paperRadialFourier W (scale * t / ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
          ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            paperRadialFourier W
              (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring

theorem moebius_star_canonicalNormalizedGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1)) =
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood (fun _ => 1), star_mul]
  calc
    _ = star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1))) := by ring
    _ = _ := by rw [moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary]

theorem moebius_gauss_frequency_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (h : O) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1) *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1)
          ((modulusUnit p : O) * h))) =
      (star (canonicalProductG p hp hcop hgood))⁻¹ *
        star (canonicalProductCoefficient p hp hcop hgood) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) h) := by
  rw [canonicalNormalizedGauss_frequency_transport p hp hcop hgood (fun _ => 1)]
  have hc := congrArg (fun z : ℂ => star z)
    (moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary)
  simp only [star_mul, star_star, star_inv₀, star_intCast] at hc
  calc
    _ = (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
        (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)) *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) h) := by ring
    _ = _ := by rw [hc]; ring

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

def squarefreePairProductPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i, q i
  ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
      (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem squarefreePairPoissonKernel_eq_product
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let hg : ∀ i : activeSupport S T, lambda ∉ Q i := fun i => hgood i.val
  let j := activeExponent S T
  let row := finiteSexticRow Q hg j
  let n := ∏ i, q i
  let a : Finset ι → ℂ := fun E =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F : Finset ι → ℝ → ℂ := fun E t =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (scale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hc : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    finitePrimeModulus_norm_eq_product q
  unfold squarefreePairPoissonKernel squarefreePairProductPoissonKernel
  dsimp only
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j /
      (‖eisEmbedding (finitePrimeModulus Q)‖ : ℂ)) * _ = _
  rw [hc]
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2)) =
    ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ hg j /
      (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))
  have ht := gauss_weighted_finite_radial_sum_transport q (fun i => hp i.val)
    hQ hg j (S ∩ T).powerset a F
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ hg j *
          (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))) := by ring
    _ = _ := by rw [ht]; ring

theorem finiteSquarefreeRow_pair_radial_poisson_product
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood S z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood T z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  rw [finiteSquarefreeRow_pair_radial_poisson (fun i => Ideal.span {p i}) hinj hgood hchar
    S T W scale hscale, squarefreePairPoissonKernel_eq_product p hp hinj hgood]

end GaussGeneratorTransport

end

end OAI
end OAIOriginalModule0089

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.MixedConversion
Source SHA256: 7a7d7459142cb9f2462fd41c7d59b28ab4c5a55e725a6cf2336f1083dca84df8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0090



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

open scoped BigOperators Classical

namespace MixedGaussConversion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase

def localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (canonicalSextic (Ideal.span {p}) hg ^ j)

def localCoefficient (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  star (angularFactor p) * localGauss p hp hg 2

def localG (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  breveLocalG (Ideal.span {p}) hg p rfl hp

theorem norm_localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) : ‖localGauss p hp hg j‖ = 1 := by
  let q : Unit → O := fun _ => p
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})) := by
    intro i k hik
    exact (hik (Subsingleton.elim i k)).elim
  have h := norm_canonicalProductGauss q (fun _ => hp) hcop (fun _ => hg)
    (fun _ => hchar) (fun _ => j) (fun _ => hj0) (fun _ => hj6)
  rw [canonicalProductGauss_constant_power q (fun _ => hp) hcop (fun _ => hg) j hj0] at h
  simpa only [q, Fintype.prod_unique, Finset.univ_unique, Finset.erase_singleton,
    Finset.prod_empty, Finset.prod_singleton, one_pow, one_mul, localGauss] using h

theorem canonicalSextic_fifth_eq_inverse (p : O) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    canonicalSextic (Ideal.span {p}) hg ^ 5 = (canonicalSextic (Ideal.span {p}) hg)⁻¹ := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), ← MulChar.star_apply',
    canonicalSextic_conj_as_row_label]
  ring

theorem localGauss_five_eq (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    localGauss p hp hg 5 = breveGammaMinus1 (Ideal.span {p}) hg p rfl hp := by
  rw [localGauss, canonicalSextic_fifth_eq_inverse]
  rfl

theorem local_sign_conversion (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (-localGauss p hp hg 1) * star (localG p hp hg) = star (localCoefficient p hp hg) ∧
    (-localGauss p hp hg 5) * localG p hp hg =
      canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
        localCoefficient p hp hg := by
  have h := first_poisson_prime_sign_pairing (Ideal.span {p}) hg hchar p rfl hp hprimary 1
  dsimp only at h
  simp only [map_one, mul_one, inv_one] at h
  constructor
  · simpa only [localGauss, localG, localCoefficient, angularFactor, pow_one,
      ConcreteBreveE.normalizedTraceGauss, breveGamma1, breveGamma2, star_mul, star_star,
      mul_comm] using h.2.2.1
  · rw [localGauss_five_eq]
    exact h.2.1

theorem norm_localG (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) : ‖localG p hp hg‖ = 1 := by
  have h := congrArg norm (local_sign_conversion p hp hg hchar hprimary).1
  simp only [norm_mul, norm_neg, norm_star, localCoefficient] at h
  rw [norm_localGauss p hp hg hchar 1 (by decide) (by decide), one_mul,
    norm_angularFactor p hp,
    norm_localGauss p hp hg hchar 2 (by decide) (by decide), one_mul] at h
  exact h

def convertedLocal (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (inverse : Bool) : ℂ :=
  if inverse then
    (canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
      localCoefficient p hp hg) / localG p hp hg
  else star (localCoefficient p hp hg) / star (localG p hp hg)

theorem neg_localGauss_eq_converted (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) (inverse : Bool) :
    -localGauss p hp hg (if inverse then 5 else 1) = convertedLocal p hp hg inverse := by
  have hG : localG p hp hg ≠ 0 := by
    intro hz
    have hn := norm_localG p hp hg hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  cases inverse
  · exact (eq_div_iff (star_ne_zero.mpr hG)).mpr
      (local_sign_conversion p hp hg hchar hprimary).1
  · exact (eq_div_iff hG).mpr (local_sign_conversion p hp hg hchar hprimary).2

theorem moebius_mixed_gauss_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (inverse : ι → Bool) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      canonicalProductGauss p hp hcop hgood (fun i => if inverse i then 5 else 1) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
  rw [product_moebius_eq_sign p hcop, canonicalProductGauss_cross_factors]
  have hprod : (-1 : ℂ) ^ Fintype.card ι *
      (∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) =
      ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
    rw [← Finset.card_univ, ← Finset.prod_neg]
    apply Finset.prod_congr rfl
    intro i _
    exact neg_localGauss_eq_converted (p i) (hp i) (hgood i) (hchar i) (hprimary i) (inverse i)
  calc
    _ = (∏ i, ∏ k ∈ Finset.univ.erase i,
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
            (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ((-1 : ℂ) ^ Fintype.card ι *
          ∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) := by
      unfold localGauss
      ring
    _ = _ := by rw [hprod]

end MixedGaussConversion

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion

theorem pair_moebius_eq_active
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (S T : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ) =
      (UniqueFactorizationMonoid.moebius
        (Ideal.span {∏ i : activeSupport S T, p i.val}) : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hcop := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  rw [prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj T,
    product_moebius_eq_sign (fun i : activeSupport S T => p i.val) hcop, ← pow_add]
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have ha : Fintype.card (activeSupport S T) = (S \ T).card + (T \ S).card := by
    rw [Fintype.card_coe, activeSupport, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter S T
  have ht := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at ht
  have hcard : S.card + T.card = Fintype.card (activeSupport S T) + 2 * (S ∩ T).card := by omega
  rw [hcard, pow_add, pow_mul]
  norm_num

def activeConvertedGauss
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  (∏ i : activeSupport S T,
    ∏ k ∈ @Finset.erase (activeSupport S T)
      (fun a b => Classical.propDecidable (a = b)) Finset.univ i,
    (canonicalSextic (Ideal.span {p i.val}) (hgood i.val) ^ activeExponent S T i)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) *
    ∏ i : activeSupport S T,
      convertedLocal (p i.val) (hp i.val) (hgood i.val) (decide (i.val ∈ S \ T))

def activePairDualSeries
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let row := finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
    (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i : activeSupport S T, p i.val
  ∑ E ∈ (S ∩ T).powerset,
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, star (row h) * paperRadialFourier W
        (scale * ‖eisEmbedding h‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

def convertedPairPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  ((scale : ℂ) / (‖eisEmbedding (∏ i : activeSupport S T, p i.val)‖ : ℂ)) *
    activeConvertedGauss p hp hgood S T * activePairDualSeries p hgood S T W scale

theorem moebius_squarefreePairPoissonKernel_conversion
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have hg : (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
        (activeExponent S T) = activeConvertedGauss p hp hgood S T := by
    have he : activeExponent S T =
        (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
      funext i
      simp only [activeExponent, decide_eq_true_eq]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hQ (fun i => hgood i.val)
      (fun i => hchar i.val) (fun i => hprimary i.val) (fun i => decide (i.val ∈ S \ T))
  rw [pair_moebius_eq_active p hinj S T, squarefreePairPoissonKernel_eq_product p hp hinj hgood]
  change (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
      (((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
        (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
          activePairDualSeries p hgood S T W scale) = _
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, q i}) : ℂ) *
          canonicalProductGauss q (fun i => hp i.val) hQ (fun i => hgood i.val)
            (activeExponent S T)) * activePairDualSeries p hgood S T W scale := by ring
    _ = _ := by rw [hg]; rfl

theorem moebius_pair_radial_poisson_converted
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ)) *
      (∑' z : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood S z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hgood T z) *
          W (‖eisEmbedding z‖ ^ 2 / scale)) =
      convertedPairPoissonKernel p hp hgood S T W scale := by
  rw [finiteSquarefreeRow_pair_radial_poisson (fun i => Ideal.span {p i}) hinj hgood hchar
    S T W scale hscale]
  exact moebius_squarefreePairPoissonKernel_conversion p hp hinj hgood hchar hprimary S T W scale

theorem moebius_pair_kernel_conversion_of_generators
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (p : ι → O) (hP : ∀ i, P i = Ideal.span {p i}) (hp : ∀ i, p i ≠ 0)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    letI : ∀ i, (Ideal.span {p i}).IsMaximal := fun i =>
      (hP i) ▸ (inferInstance : (P i).IsMaximal)
    let hg : ∀ i, lambda ∉ Ideal.span {p i} := fun i => (hP i) ▸ hgood i
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, P i) : ℂ)) *
      squarefreePairPoissonKernel P hinj hgood S T W scale =
      convertedPairPoissonKernel p hp hg S T W scale := by
  have hPeq : P = fun i => Ideal.span {p i} := funext hP
  subst P
  exact moebius_squarefreePairPoissonKernel_conversion p hp hinj hgood hchar hprimary S T W scale

end GaussGeneratorTransport

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def mobiusIdealColumn (C : Ideal O → ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * C I

noncomputable def conjugateIdealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) : ℂ :=
  ∑ I ∈ F, mobiusIdealColumn C I * star (idealSexticRow F hFpos hFgood I y)

theorem conjugateIdealRowSum_eq_star
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) :
    conjugateIdealRowSum F hFpos hFgood C y =
      star (∑ I ∈ F, star (mobiusIdealColumn C I) * idealSexticRow F hFpos hFgood I y) := by
  simp only [conjugateIdealRowSum, star_sum, star_mul, star_star, mul_comm]

theorem conjugateIdealRowSum_smoothed_summable
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun y : O => W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow_smoothed_mean_square_summable
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale

theorem conjugateIdealRowSum_smoothed_poisson
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonKernel F hFpos hFgood J I W scale := by
  simp_rw [conjugateIdealRowSum_eq_star, norm_star]
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  change (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
    (↑(‖∑ I ∈ F, star (mobiusIdealColumn C I) *
      finiteSquarefreeRow (fun i : primePool F => i.val) (primePool_good F hFgood)
        (idealSupport F I) y‖ ^ 2) : ℂ)) = _
  rw [finiteSquarefreeRow_smoothed_mean_square_expand
    (fun i : primePool F => i.val) (primePool_good F hFgood)
    F (idealSupport F) (fun I => star (mobiusIdealColumn C I)) W scale hscale,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteSquarefreeRow_pair_radial_poisson
    (fun i : primePool F => i.val) Subtype.val_injective (primePool_good F hFgood)
    hchar (idealSupport F J) (idealSupport F I) W scale hscale, star_star]
  rw [mul_comm (mobiusIdealColumn C J)]
  rfl

theorem mobiusIdealColumn_eq_zero_of_not_squarefree
    (C : Ideal O → ℂ) {I : Ideal O} (hI : ¬ Squarefree I) :
    mobiusIdealColumn C I = 0 := by
  simp only [mobiusIdealColumn, UniqueFactorizationMonoid.moebius_of_not_squarefree hI,
    Int.cast_zero, zero_mul]

theorem conjugateIdealRowSum_zeroMode_offDiagonal
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F) (hIJ : I ≠ J)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
      idealPairPoissonZeroMode F hFpos hFgood J I W scale = 0 := by
  by_cases hsI : Squarefree I
  · by_cases hsJ : Squarefree J
    · have hsupport : idealSupport F J ≠ idealSupport F I := fun h =>
        hIJ (idealSupport_injective_on_squarefree F hJ hI hsJ hsI h).symm
      let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
      have hz : idealPairPoissonZeroMode F hFpos hFgood J I W scale = 0 :=
        squarefreePairPoissonZeroMode_eq_zero_of_ne (fun i : primePool F => i.val)
          Subtype.val_injective (primePool_good F hFgood) hsupport W scale
      rw [hz, mul_zero]
    · simp [mobiusIdealColumn_eq_zero_of_not_squarefree C hsJ]
  · simp [mobiusIdealColumn_eq_zero_of_not_squarefree C hsI]

theorem conjugateIdealRowSum_zeroMode_formula
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    (∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale) =
    (scale : ℂ) * paperRadialFourier W 0 *
      ∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.sum_eq_single I]
  · rw [idealPairPoissonZeroMode_diag, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    change (star _ * _) * _ = _ * ((star _ * _) * _)
    ring
  · intro J hJ hJI
    exact conjugateIdealRowSum_zeroMode_offDiagonal F hFpos hFgood C hI hJ hJI.symm W scale
  · exact fun h => (h hI).elim

theorem conjugateIdealRowSum_smoothed_poisson_zero_split
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' y : O, W (‖eisEmbedding y‖ ^ 2 / scale) *
      (↑(‖conjugateIdealRowSum F hFpos hFgood C y‖ ^ 2) : ℂ)) =
    (scale : ℂ) * paperRadialFourier W 0 *
      (∑ I ∈ F, (↑(‖mobiusIdealColumn C I‖ ^ 2) : ℂ) * idealPrimeDensity F I) +
      ∑ I ∈ F, ∑ J ∈ F,
        (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
          idealPairPoissonNonzeroMode F hFpos hFgood J I W scale := by
  rw [conjugateIdealRowSum_smoothed_poisson F hFpos hFgood hchar C W scale hscale]
  simp_rw [idealPairPoissonKernel_zero_split F hFpos hFgood _ _ W scale hscale,
    mul_add, Finset.sum_add_distrib]
  rw [conjugateIdealRowSum_zeroMode_formula F hFpos hFgood C W scale]

theorem norm_mobiusIdealColumn_le (C : Ideal O → ℂ) (I : Ideal O) :
    ‖mobiusIdealColumn C I‖ ≤ ‖C I‖ := by
  by_cases hI : Squarefree I
  · simp only [mobiusIdealColumn, hI.moebius_eq, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_refl]
  · rw [mobiusIdealColumn_eq_zero_of_not_squarefree C hI, norm_zero]
    exact norm_nonneg _

theorem norm_conjugateIdealRowSum_zeroMode_le
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖C I‖ ^ 2 := by
  rw [conjugateIdealRowSum_zeroMode_formula F hFpos hFgood C W scale,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I hI => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (idealPrimeDensity_mem_Icc F hFpos I).1]
  calc
    _ ≤ ‖mobiusIdealColumn C I‖ ^ 2 := mul_le_of_le_one_right
      (sq_nonneg _) (idealPrimeDensity_mem_Icc F hFpos I).2
    _ ≤ ‖C I‖ ^ 2 := by gcongr; exact norm_mobiusIdealColumn_le C I

theorem norm_secondPoisson_zeroMode_fixed_factors
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (ξ ρ : Ideal O → ℂ) (A : ℕ → ℂ)
    (hξ : ∀ I ∈ F, ‖ξ I‖ ≤ 1) (hρ : ∀ I ∈ F, ‖ρ I‖ ≤ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    let C : Ideal O → ℂ := fun I => ξ I * ρ I * A (Ideal.absNorm I)
    ‖∑ I ∈ F, ∑ J ∈ F,
      (star (mobiusIdealColumn C I) * mobiusIdealColumn C J) *
        idealPairPoissonZeroMode F hFpos hFgood J I W scale‖ ≤
      (|scale| * ‖paperRadialFourier W 0‖) * ∑ I ∈ F, ‖A (Ideal.absNorm I)‖ ^ 2 := by
  dsimp only
  refine (norm_conjugateIdealRowSum_zeroMode_le F hFpos hFgood
    (fun I => ξ I * ρ I * A (Ideal.absNorm I)) W scale).trans ?_
  gcongr with I hI
  simp only [norm_mul]
  calc
    ‖ξ I‖ * ‖ρ I‖ * ‖A (Ideal.absNorm I)‖ ≤
        1 * 1 * ‖A (Ideal.absNorm I)‖ := by gcongr; exact hξ I hI; exact hρ I hI
    _ = _ := by ring

end ConcretePrimeRowBridge

open MeasureTheory Set
open scoped BigOperators

namespace EisensteinSchwartzPoisson

theorem scaled_cauchy_antitone (b : ℝ) :
    AntitoneOn (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg b, sq_nonneg (y - x),
    mul_nonneg (sq_nonneg b) (show 0 ≤ y ^ 2 - x ^ 2 by nlinarith)]

theorem scaled_cauchy_nat_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / (2 * b) := by
  have hi := (integrable_inv_one_add_mul_sq hb.ne').integrableOn (s := Ioi 0)
  have ht := (scaled_cauchy_antitone b).tsum_le_integral hi
    (fun t ht => by positivity)
  have he : (∫ x : ℝ in Ioi 0, (1 + (b * x) ^ 2)⁻¹) = Real.pi / (2 * b) := by
    rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
      smul_eq_mul]
    ring
  simpa [he] using ht

theorem summable_scaled_cauchy_nat (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℕ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  exact (scaled_cauchy_antitone b).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_mul_sq hb.ne').integrableOn (fun _ _ => by positivity)

theorem summable_scaled_cauchy_int (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_scaled_cauchy_nat b hb
  · simpa [mul_neg] using summable_scaled_cauchy_nat b hb

theorem scaled_cauchy_int_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / b := by
  have hs := summable_scaled_cauchy_nat b hb
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      (1 + (b * ((-(n + 1) : ℤ) : ℝ)) ^ 2)⁻¹) := by
    convert hs1 using 1
    ext n
    push_cast
    congr 1
    ring
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹)
    (by simpa only [Int.cast_natCast] using hs) hneg]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, mul_neg,
    neg_sq]
  have hz := hs.tsum_eq_zero_add
  have he : (∑' n : ℕ, (1 + (b * (↑n + 1)) ^ 2)⁻¹) =
      (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hz.symm
  rw [he]
  have := scaled_cauchy_nat_bound b hb
  have hh : Real.pi / (2 * b) = (Real.pi / b) / 2 := by ring
  rw [hh] at this
  linarith

open ConcreteTraceCRT ActualEisensteinCubic

theorem scaled_eisenstein_cauchy_summable (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hp.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (b * (p.1 : ℝ)) (b * (p.2 : ℝ))
    (K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (by positivity)
  change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
    K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]

theorem scaled_eisenstein_cauchy_bound (K : ℝ) (hK : 0 < K) :
    (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi / Real.sqrt K) ^ 2 := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have he : (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) =
      ∑' p : ℤ × ℤ, ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹ :=
    (latticeCoordEquiv.symm.tsum_eq _).symm
  rw [he]
  calc
    _ ≤ ∑' p : ℤ × ℤ, 4 * ((1 + (b * (p.1 : ℝ)) ^ 2)⁻¹ *
          (1 + (b * (p.2 : ℝ)) ^ 2)⁻¹) := by
      apply ((latticeCoordEquiv.symm.summable_iff).mpr
        (scaled_eisenstein_cauchy_summable K hK)).tsum_le_tsum _ (hp.mul_left 4)
      intro p
      apply inverse_square_le_cauchy_product _ _ _ (by positivity)
      change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
        K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
      rw [eisEmbedding_eval_norm_sq]
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
    _ = 4 * (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ^ 2 := by
      rw [tsum_mul_left, ← hs.tsum_mul_tsum hs hp, pow_two]
    _ ≤ 4 * (1 + Real.pi / b) ^ 2 := by
      gcongr
      exact scaled_cauchy_int_bound b hb

theorem scaled_eisenstein_cauchy_small (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    K * (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi) ^ 2 := by
  have hs := scaled_eisenstein_cauchy_bound K hK
  have hb : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hb1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
  have hsq := Real.sq_sqrt hK.le
  calc
    _ ≤ K * (4 * (1 + Real.pi / Real.sqrt K) ^ 2) :=
      mul_le_mul_of_nonneg_left hs hK.le
    _ = 4 * (Real.sqrt K + Real.pi) ^ 2 := by
      nth_rw 1 [← hsq]
      field_simp
    _ ≤ _ := by gcongr

theorem one_le_eisenstein_norm_sq (h : O) (hh : h ≠ 0) :
    1 ≤ ‖eisEmbedding h‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {h}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hh)

theorem cauchy_large_scale_pointwise (K q : ℝ) (hK : 1 ≤ K) (hq : 1 ≤ q) :
    K * ((1 + K * q) ^ 2)⁻¹ ≤ 4 * ((1 + q) ^ 2)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have h1 : K * (1 + q) ≤ 2 * (1 + K * q) := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ K * (1 + q)) h1 2
  have h3 : K * (1 + q) ^ 2 ≤ K ^ 2 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (1 + q)]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + K * q) ^ 2)
    (by positivity : 0 < (1 + q) ^ 2)).mpr
  nlinarith

theorem lattice_profile_nonzero_scaled_bound
    (F : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * ‖F t‖ ≤ B)
    (K : ℝ) (hK : 0 < K) :
    K * (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * B := by
  have hm (h : O) : ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      B * ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hF (K * ‖eisEmbedding h‖ ^ 2) (by positivity)
  have hs := scaled_eisenstein_cauchy_summable K hK
  have hf : Summable (fun h : O => ‖F (K * ‖eisEmbedding h‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hm (hs.mul_left B)
  have hsub := hf.subtype (fun h : O => h ≠ 0)
  have hc := eisenstein_cauchy_summable.subtype (fun h : O => h ≠ 0)
  by_cases hK1 : K ≤ 1
  · have htotal : (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        ∑' h : O, ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ :=
      hsub.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf
    have hbound := hf.tsum_le_tsum hm (hs.mul_left B)
    rw [tsum_mul_left] at hbound
    calc
      _ ≤ K * (B * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (htotal.trans hbound) hK.le
      _ = B * (K * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by ring
      _ ≤ B * (4 * (1 + Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_eisenstein_cauchy_small K hK hK1) hB
      _ ≤ _ := by nlinarith [eisensteinCauchyMass_nonneg]
  · have hp (h : {h : O // h ≠ 0}) :
        K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
      calc
        _ ≤ K * (B * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hm h.val) hK.le
        _ = B * (K * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
        _ ≤ B * (4 * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (cauchy_large_scale_pointwise K _
            (le_of_not_ge hK1) (one_le_eisenstein_norm_sq h.val h.property)) hB
        _ = _ := by ring
    calc
      _ = ∑' h : {h : O // h ≠ 0}, K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left.symm
      _ ≤ ∑' h : {h : O // h ≠ 0}, (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
        (hsub.mul_left K).tsum_le_tsum hp (hc.mul_left (4 * B))
      _ = (4 * B) * ∑' h : {h : O // h ≠ 0}, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (4 * B) * eisensteinCauchyMass := mul_le_mul_of_nonneg_left
        (eisensteinCauchyMass_subtype (fun h : O => h ≠ 0)) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (1 + Real.pi)]

theorem paperRadialFourier_nonzero_lattice_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (K : ℝ), 0 < K →
        K * (∑' h : {h : O // h ≠ 0},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨s, (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * C, ?_, ?_⟩
  · have := eisensteinCauchyMass_nonneg
    have := Real.pi_pos
    positivity
  · intro W K hK
    simpa only [mul_assoc] using lattice_profile_nonzero_scaled_bound
      (paperRadialFourier W) (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
        (by positivity) (hb W) K hK

end EisensteinSchwartzPoisson

end

end OAI
end OAIOriginalModule0090

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
Source SHA256: 72607eef57bb692a8f488250c84294fd058057bd9c56235116afe799acb4c74c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0091



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

namespace ActualEisensteinCubic

theorem primary_associated_eq (x y : O) (hxy : Associated x y)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) : x = y := by
  obtain ⟨u, hu⟩ := hxy
  have huprimary : lambda ^ 2 ∣ (u : O) - 1 := by
    have heq : (u : O) - 1 = (y - 1) - (x - 1) * (u : O) := by
      rw [← hu]
      ring
    rw [heq]
    exact dvd_sub hy (dvd_mul_of_dvd_left hx _)
  have huone : (u : O) = 1 := A3_primary_unit_eq_one _ u.isUnit huprimary
  simpa only [huone, mul_one] using hu

theorem primary_multiset_prod (s : Multiset O)
    (hs : ∀ x ∈ s, lambda ^ 2 ∣ x - 1) : lambda ^ 2 ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hb := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons]
    have heq : a * s.prod - 1 = (a - 1) * s.prod + (s.prod - 1) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

theorem primary_maximal_divisor_good (t : O) (ht : lambda ^ 2 ∣ t - 1)
    (P : Ideal O) [P.IsMaximal] (htP : t ∈ P) : lambda ∉ P := by
  intro hlam
  have hlam2 : lambda ^ 2 ∈ P := by
    simpa only [pow_two] using P.mul_mem_left lambda hlam
  have hsub : t - 1 ∈ P := Ideal.mem_of_dvd P ht hlam2
  have hone : (1 : O) ∈ P := by simpa using P.sub_mem htP hsub
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
    ((Ideal.eq_top_iff_one _).mpr hone)

theorem exists_primary_prime_factorization (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  classical
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      obtain ⟨r, hrspan, hrprimary, _⟩ := cubicJacobi_exists_primary_generator
        (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hrspan
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hrprimary⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht

theorem residue_char_mem (P : Ideal O) :
    (ringChar (O ⧸ P) : O) ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast]
  exact CharP.cast_eq_zero (O ⧸ P) (ringChar (O ⧸ P))

theorem maximal_eq_or_eq_of_same_residue_char
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (hRP : ringChar (O ⧸ R) = ringChar (O ⧸ P)) : R = P ∨ R = Q := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨a, b, _, _, _, _, hcover⟩ := rational_prime_ideal_cover
    (ringChar (O ⧸ P)) (CharP.char_is_prime (O ⧸ P) _)
  have hp := hcover P inferInstance (residue_char_mem P)
  have hq := hcover Q inferInstance (by rw [← hPQ]; exact residue_char_mem Q)
  have hr := hcover R inferInstance (by rw [← hRP]; exact residue_char_mem R)
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    rcases hr with hr | hr <;> simp_all

theorem prime_divisor_residue_char_ne
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (t : O) (htP : t ∉ P) (htQ : t ∉ Q) (htR : t ∈ R) :
    ringChar (O ⧸ R) ≠ ringChar (O ⧸ P) := by
  intro hRP
  rcases maximal_eq_or_eq_of_same_residue_char P Q R hne hPQ hRP with rfl | rfl
  · exact htP htR
  · exact htQ htR

theorem lambda_sq_dvd_three : lambda ^ 2 ∣ (3 : O) := by
  have hlam : lambda ^ 2 = -3 * omega := by
    change (omega - 1) ^ 2 = -3 * omega
    linear_combination omega_sq_for_norm
  refine ⟨-omega ^ 2, ?_⟩
  rw [hlam]
  calc
    (3 : O) = 3 * omega ^ 3 := by rw [omega_primitive.pow_eq_one]; ring
    _ = -3 * omega * -omega ^ 2 := by ring

theorem neg_two_primary : lambda ^ 2 ∣ (-2 : O) - 1 := by
  convert dvd_neg.mpr lambda_sq_dvd_three using 1 ; ring

theorem neg_add_primary (p q : O)
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1) :
    lambda ^ 2 ∣ -(p + q) - 1 := by
  have hd := dvd_neg.mpr (dvd_add (dvd_add hp hq) lambda_sq_dvd_three)
  convert hd using 1 ; ring

theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

theorem cubic_reciprocity_equal_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      A3_cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, A3_cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, A3_cubicChar_neg_one, one_mul] at htval
  exact htval

theorem cubic_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  by_cases hPQ : P = Q
  · have hqP : q ∈ P := by rw [hPQ, hQ]; exact Ideal.subset_span (by simp)
    have hpQ : p ∈ Q := by rw [← hPQ, hP]; exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqP,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpQ, MulChar.map_zero, MulChar.map_zero]
  · by_cases hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P)
    · exact cubic_reciprocity_equal_residue_char P Q hPgood hQgood hPQ hchar
        p q hP hQ hpprimary hqprimary
    · exact cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
        p q hP hQ hpprimary hqprimary

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

def cubicTwoIdeal : Ideal O := Ideal.span {(-2 : O)}

instance cubicTwoIdeal_isMaximal : cubicTwoIdeal.IsMaximal := by
  rcases rational_prime_factor_cases 2 Nat.prime_two with hm |
      ⟨a, b, _, _, _, ha, _, _, _⟩
  · simpa only [cubicTwoIdeal, Ideal.span_singleton_neg, Nat.cast_ofNat] using hm
  · have hin : (Ideal.span {a} : Ideal O) ∈ {I : Ideal O | Ideal.absNorm I = 2} := by
      change Ideal.absNorm (Ideal.span {a}) = 2
      rwa [← qNat_eq_absNorm_span]
    rw [ShortDraftHeckeBridge.norm_p_fiber_inert Nat.prime_two (by decide)] at hin
    exact False.elim hin

theorem cubicTwoIdeal_good : lambda ∉ cubicTwoIdeal := by
  apply primary_maximal_divisor_good (-2 : O) neg_two_primary
  exact Ideal.subset_span (by simp)

theorem cubicTwoIdeal_residue_char : ringChar (O ⧸ cubicTwoIdeal) = 2 := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  have hmem : (2 : O) ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.subset_span (by simp)
  have hz : (2 : O ⧸ cubicTwoIdeal) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ cubicTwoIdeal) _)
    Nat.prime_two).mp ((ringChar.spec (O ⧸ cubicTwoIdeal) 2).mp hz)

theorem canonicalSextic_four_eq_fixed_two
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)) =
      ConcreteTraceCRT.eisEmbedding
        (cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal p)) := by
  have hfour : Ideal.Quotient.mk P (4 : O) = (Ideal.Quotient.mk P (-2 : O)) ^ 2 := by
    simp only [map_ofNat, map_neg]
    ring
  rw [hfour, map_pow, ← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
    canonicalSextic_pow_two]
  change ConcreteTraceCRT.eisEmbedding (cubicChar P hgood (Ideal.Quotient.mk P (-2 : O))) = _
  congr 1
  exact cubic_reciprocity_primary P cubicTwoIdeal hgood cubicTwoIdeal_good
    p (-2) hP rfl hprimary neg_two_primary

theorem canonicalSextic_four_prod_eq_fixed_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) =
      ConcreteTraceCRT.eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
        (Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i))) := by
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_four_eq_fixed_two (P i) (hgood i) (p i) (hP i hi) (hprimary i hi)

theorem canonicalSextic_four_prod_eq_one_of_mod_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hmod : (2 : O) ∣ (∏ i ∈ s, p i) - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) = 1 := by
  have hmem : (∏ i ∈ s, p i) - 1 ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.mem_span_singleton.mpr hmod
  have heq : Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i) = 1 := by
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  rw [canonicalSextic_four_prod_eq_fixed_two s P hgood p hP hprimary, heq, map_one, map_one]

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem sum_square_phase_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) :
    (∑ x : T, ψ (x ^ 2)) =
      ∏ i, ∑ y : R i, coordinateAddChar R e ψ i (y ^ 2) := by
  calc
    _ = ∑ x : T, ∏ i, coordinateAddChar R e ψ i ((e x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (x ^ 2)]
      simp only [map_pow, Pi.pow_apply]
    _ = ∑ x : ∀ i, R i, ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2) :=
      Equiv.sum_comp e.toEquiv
        (fun x : ∀ i, R i => ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2))
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => coordinateAddChar R e ψ i (x ^ 2))).symm

theorem quadratic_gauss_finite_crt_eq_square_sum {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ)
    (hψ : ψ.IsPrimitive) (hchar : ∀ i, ringChar (R i) ≠ 2) :
    (∑ x : T, (∏ i, ((quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : T, ψ (x ^ 2) := by
  rw [gauss_sum_finite_crt R e
    (fun i => (quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) ψ,
    sum_square_phase_finite_crt R e ψ]
  apply Finset.prod_congr rfl
  intro i _
  have hp := coordinateAddChar_isPrimitive R e ψ hψ i
  have hn : coordinateAddChar R e ψ i ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase _ (hchar i) hn

end IdealGaussCRT

namespace QuadraticGaussRay

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem canonicalProductGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticGammaO (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ Ideal.span {p i}) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) hchar

theorem I_zpow_eq_of_mod_four {a b : ℤ} (h : (a : ZMod 4) = b) :
    Complex.I ^ a = Complex.I ^ b := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a 4).mp h.symm
  have ha : a = b + 4 * k := by omega
  rw [ha, zpow_add₀ Complex.I_ne_zero, zpow_mul]
  norm_num

theorem fourTerms_eq_of_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    breveGaussianFourTerms a b = breveGaussianFourTerms c d := by
  have hn : ((-b : ℤ) : ZMod 4) = (-d : ℤ) := by simpa using congrArg Neg.neg hb
  have hs : ((b-a : ℤ) : ZMod 4) = (d-c : ℤ) := by
    push_cast
    rw [ha, hb]
  rw [breveGaussianFourTerms_formula, breveGaussianFourTerms_formula,
    I_zpow_eq_of_mod_four ha, I_zpow_eq_of_mod_four hn, I_zpow_eq_of_mod_four hs]

def quadraticRayValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  breveGaussianFourTerms (r.1.val : ℤ) (r.2.val : ℤ)

theorem quadraticGammaO_eq_rayValue (c : O) (hc : c ≠ 0) :
    quadraticGammaO c hc = quadraticRayValue (residue c) := by
  have h := quadraticGammaO_eq_fourTerms (coords c).1 (coords c).2 (by rwa [eval_coords])
  have h' : quadraticGammaO c hc = breveGaussianFourTerms (coords c).1 (coords c).2 := by
    simpa only [eval_coords] using h
  rw [h']
  unfold quadraticRayValue residue
  exact fourTerms_eq_of_mod_four (by simp) (by simp)

theorem quadraticGammaO_eq_of_residue_eq (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : residue c = residue d) : quadraticGammaO c hc = quadraticGammaO d hd := by
  rw [quadraticGammaO_eq_rayValue, quadraticGammaO_eq_rayValue, h]

theorem canonicalProductGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticRayValue (residue (∏ i, p i)) := by
  rw [canonicalProductGauss_three_eq_quadraticGamma p hp hcop hgood hchar,
    quadraticGammaO_eq_rayValue]

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem fixed_two_mk_eq_residue_lift (c : O) :
    Ideal.Quotient.mk cubicTwoIdeal c =
      Ideal.Quotient.mk cubicTwoIdeal (lift (residue c)) := by
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq (residue_lift (residue c)).symm
  apply Ideal.Quotient.eq.mpr
  rw [cubicTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨(-2 : O) * z, ?_⟩
  calc
    c - lift (residue c) = 4 * z := hz
    _ = (-2 : O) * (-2 * z) := by ring

def fixedGValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (Ideal.Quotient.mk cubicTwoIdeal (lift r))))⁻¹ * quadraticRayValue r

theorem residue_eq_of_four_dvd_sub (c d : O) (h : (4 : O) ∣ c - d) :
    residue c = residue d := by
  obtain ⟨z, hz⟩ := h
  have he : c = eval ((coords d).1 + 4 * (coords z).1)
      ((coords d).2 + 4 * (coords z).2) := by
    calc
      c = d + 4 * z := by linear_combination hz
      _ = eval (coords d).1 (coords d).2 + 4 * eval (coords z).1 (coords z).2 := by
        rw [eval_coords, eval_coords]
      _ = _ := by simp only [eval]; push_cast; ring
  rw [he, residue_eval]
  simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

theorem residue_eq_of_quotient_four_eq (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) : residue c = residue d :=
  residue_eq_of_four_dvd_sub c d (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

def residueQuotientFour : (O ⧸ Ideal.span {(4 : O)}) → EisensteinEPrimaryPhase.Coord :=
  Quotient.lift residue (fun c d h => residue_eq_of_quotient_four_eq c d (Quotient.sound h))

@[simp] theorem residueQuotientFour_mk (c : O) :
    residueQuotientFour (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = residue c := rfl

def fixedGQuotientValue (r : O ⧸ Ideal.span {(4 : O)}) : ℂ :=
  fixedGValue (residueQuotientFour r)

theorem canonicalProductG_eq_fixedGValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood = fixedGValue (residue (∏ i, p i)) := by
  rw [canonicalProductG,
    canonicalSextic_four_prod_eq_fixed_two Finset.univ (fun i => Ideal.span {p i}) hgood p
      (fun i _ => rfl) (fun i _ => hprimary i),
    canonicalProductGauss_three_eq_rayValue p hp hcop hgood hchar,
    fixed_two_mk_eq_residue_lift]
  rfl

theorem canonicalProductG_eq_of_residue_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (kcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (kgood : ∀ i, lambda ∉ Ideal.span {q i})
    (kchar : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (kprimary : ∀ i, lambda ^ 2 ∣ q i - 1)
    (hres : residue (∏ i, p i) = residue (∏ i, q i)) :
    canonicalProductG p hp hcop hgood = canonicalProductG q hq kcop kgood := by
  rw [canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary,
    canonicalProductG_eq_fixedGValue q hq kcop kgood kchar kprimary, hres]

theorem canonicalProductG_eq_fixed_quotient
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i, p i)) :=
  canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary

end QuadraticGaussRay

end

end OAI
end OAIOriginalModule0091

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation
Source SHA256: b76feecf4a3bb5055eae0d2eab5d0010ea881623d77cdf36ba2b66042b2a2ab9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0092



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

namespace MixedCrossSeparation

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

private theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5 * x k i) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ A.erase i, x i k ^ 5) * (∏ k ∈ B, x i k ^ 5) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ B.erase i, x i k) * (∏ k ∈ A, x i k) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
    simp only [pow_one]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

def crossSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) : ℂ :=
  canonicalSextic (Ideal.span {p i}) (hg i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (p k))

theorem mixed_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι)
    (hpi : lambda ^ 2 ∣ p i - 1) (hpk : lambda ^ 2 ∣ p k - 1) :
    crossSymbol p hg i k ^ 5 * crossSymbol p hg k i =
      crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 := by
  have hs : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary
      (Ideal.span {p i}) (Ideal.span {p k}) (hg i) (hg k)
      (p i) (p k) rfl rfl hpi hpk
  calc
    _ = crossSymbol p hg i k ^ 3 * crossSymbol p hg i k ^ 2 * crossSymbol p hg k i := by ring
    _ = _ := by rw [hs]; ring

def convertedColumnBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (inverse : Bool) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if inverse then 5 else 1)) *
    convertedLocal (p i) (hp i) (hg i) inverse

def quadraticCrossPhase {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3

theorem mixed_converted_gauss_separation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (inverse : ι → Bool)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (∏ i, ∏ k ∈ Finset.univ.erase i,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
      (∏ i, convertedLocal (p i) (hp i) (hg i) (inverse i)) =
    convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = true) true *
      convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = false) false *
      quadraticCrossPhase p hg (Finset.univ.filter fun i => inverse i = true)
        (Finset.univ.filter fun i => inverse i = false) := by
  let A := Finset.univ.filter (fun i => inverse i = true)
  let B := Finset.univ.filter (fun i => inverse i = false)
  have hA (i : ι) : i ∈ A ↔ inverse i = true := by simp [A]
  have hB (i : ι) : i ∈ B ↔ inverse i = false := by simp [B]
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have ht := (hA i).mp hi
    have hf := (hB i).mp hj
    rw [ht] at hf
    contradiction
  have hu : A ∪ B = Finset.univ := by
    ext i
    simp only [Finset.mem_union, hA, hB, Finset.mem_univ, iff_true]
    cases inverse i <;> simp
  have hpow (i k : ι) :
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k)) =
      crossSymbol p hg i k ^ (if i ∈ A then 5 else 1) := by
    rw [MulChar.pow_apply' _ (by cases inverse i <;> decide)]
    simp only [hA,  crossSymbol]
  simp_rw [hpow]
  rw [← Finset.prod_mul_distrib,
    ordered_cross_partition (crossSymbol p hg)
      (fun i => convertedLocal (p i) (hp i) (hg i) (inverse i)) A B hd hu]
  have hn : (∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 5) *
      convertedLocal (p i) (hp i) (hg i) (inverse i)) = convertedColumnBlock p hp hg A true := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [(hA i).mp hi,   ↓reduceIte]
  have hp' : (∏ i ∈ B, (∏ k ∈ B.erase i, crossSymbol p hg i k) *
      convertedLocal (p i) (hp i) (hg i) (inverse i)) = convertedColumnBlock p hp hg B false := by
    unfold convertedColumnBlock
    simp only [Bool.false_eq_true, ↓reduceIte, pow_one]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(hB i).mp hi]
  have hc : (∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 5 * crossSymbol p hg k i) =
      quadraticCrossPhase p hg A B := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    exact mixed_cross_eq_quadratic p hg i k (hprimary i) (hprimary k)
  rw [hn, hp', hc]

theorem quadraticCrossPhase_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B ^ 2 = 1 := by
  have hpow (i k : ι) (hik : i ≠ k) : crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [crossSymbol, map_pow, ite_eq_right (prime_generator_not_mem_other p hcop i k hik)]
      using canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  unfold quadraticCrossPhase
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hik : i ≠ k := by
    intro h
    subst k
    exact Finset.disjoint_left.mp hd hi hk
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, hpow i k hik, hpow k i hik.symm, one_mul]

theorem quadraticCrossPhase_eq_one_or_neg_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B = 1 ∨ quadraticCrossPhase p hg A B = -1 := by
  exact sq_eq_one_iff.mp (quadraticCrossPhase_sq p hcop hg A B hd)

theorem activeConvertedGauss_separated
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    let q : activeSupport S T → O := fun i => p i.val
    let hq : ∀ i, q i ≠ 0 := fun i => hp i.val
    let hgood : ∀ i, lambda ∉ Ideal.span {q i} := fun i => hg i.val
    let A : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∈ S \ T
    let B : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∉ S \ T
    GaussGeneratorTransport.activeConvertedGauss p hp hg S T =
      convertedColumnBlock q hq hgood A true * convertedColumnBlock q hq hgood B false *
        quadraticCrossPhase q hgood A B := by
  dsimp only
  have h := mixed_converted_gauss_separation (fun i : activeSupport S T => p i.val)
    (fun i => hp i.val) (fun i => hg i.val) (fun i => decide (i.val ∈ S \ T))
    (fun i => hprimary i.val)
  simp only [GaussGeneratorTransport.activeConvertedGauss, activeExponent,
    decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  convert h using 1 ; congr 2
  funext i
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk; rfl

theorem active_dual_row_factorization
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset ι) (d h : O) :
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
      (activeExponent S T)
    row d * star (row h) =
      star (finiteSquarefreeRow P hg (S \ T) d *
        star (finiteSquarefreeRow P hg (S \ T) h)) *
      (finiteSquarefreeRow P hg (T \ S) d *
        star (finiteSquarefreeRow P hg (T \ S) h)) := by
  dsimp only
  rw [finiteSexticRow_activeSupport, finiteSexticRow_activeSupport]
  simp only [star_mul, star_star]
  ring

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates

private theorem prod_subtype_erase {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (A : Finset ι) (i : A) (f : ι → M) :
    (∏ k ∈ (Finset.univ : Finset A).erase i, f k.val) = ∏ k ∈ A.erase i.val, f k := by
  apply Finset.prod_bij (fun k _ => k.val)
  · intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨?_, k.property⟩
    exact fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h)
  · intro a ha b hb h
    exact Subtype.ext h
  · intro k hk
    refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
    apply Finset.mem_erase.mpr
    exact ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a ha
    rfl

private theorem restricted_prime_coprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) := by
  intro i k hik
  exact hcop (fun h => hik (Subtype.ext h))

def quadraticBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) : ℂ :=
  ∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 3) *
    localGauss (p i) (hp i) (hg i) 3

theorem quadraticBlock_eq_productGauss
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) :
    quadraticBlock p hp hg A =
      canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
        (restricted_prime_coprime p hcop A) (fun i => hg i.val)
        (fun _ => 3) := by
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  unfold quadraticBlock
  rw [← Finset.prod_coe_sort A]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [← prod_subtype_erase A i (fun k => crossSymbol p hg i.val k ^ 3)]
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk
    exact (MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0) _).symm

theorem quadraticBlock_eq_rayValue
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : Finset ι) :
    quadraticBlock p hp hg A = quadraticRayValue (residue (∏ i ∈ A, p i)) := by
  rw [quadraticBlock_eq_productGauss p hp hcop hg A,
    canonicalProductGauss_three_eq_rayValue (fun i : A => p i.val) (fun i => hp i.val)
      (restricted_prime_coprime p hcop A) (fun i => hg i.val)
      (fun i => hchar i.val), Finset.prod_coe_sort]

theorem quadraticBlock_union
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticBlock p hp hg (A ∪ B) = quadraticBlock p hp hg A *
      quadraticBlock p hp hg B * quadraticCrossPhase p hg A B := by
  let x := crossSymbol p hg
  let l := fun i => localGauss (p i) (hp i) (hg i) 3
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ A.erase i, x i k ^ 3) * (∏ k ∈ B, x i k ^ 3) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : (A ∪ B).erase i = A.erase i ∪ B := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ B.erase i, x i k ^ 3) * (∏ k ∈ A, x i k ^ 3) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : (A ∪ B).erase i = B.erase i ∪ A := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  change (∏ i ∈ A ∪ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) = _
  rw [Finset.prod_union hd, hpA, hpB, Finset.prod_comm (s := B) (t := A)]
  unfold quadraticBlock quadraticCrossPhase
  simp only [Finset.prod_mul_distrib]
  dsimp only [x, l]
  ring

theorem norm_quadraticBlock
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : Finset ι) :
    ‖quadraticBlock p hp hg A‖ = 1 := by
  rw [quadraticBlock_eq_productGauss p hp hcop hg A]
  exact norm_canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
    (restricted_prime_coprime p hcop A) (fun i => hg i.val)
    (fun i => hchar i.val) (fun _ => 3) (fun _ => by decide) (fun _ => by decide)

def quadraticRayPair (a b : EisensteinEPrimaryPhase.Coord) : ℂ :=
  quadraticRayValue (EisensteinEPrimaryPhase.mul a b) /
    (quadraticRayValue a * quadraticRayValue b)

theorem quadraticCrossPhase_eq_rayPair
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) := by
  have hA0 : quadraticBlock p hp hg A ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar A
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hB0 : quadraticBlock p hp hg B ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar B
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have h := quadraticBlock_union p hp hg A B hd
  have hdiv : quadraticCrossPhase p hg A B = quadraticBlock p hp hg (A ∪ B) /
      (quadraticBlock p hp hg A * quadraticBlock p hp hg B) := by
    apply (eq_div_iff (mul_ne_zero hA0 hB0)).mpr
    rw [h]
    ring
  rw [hdiv, quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B),
    quadraticBlock_eq_rayValue p hp hcop hg hchar A,
    quadraticBlock_eq_rayValue p hp hcop hg hchar B, Finset.prod_union hd,
    residue_mul]
  rfl

theorem mixed_converted_gauss_separation_mod_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (inverse : ι → Bool) (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (∏ i, ∏ k ∈ Finset.univ.erase i,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
      (∏ i, convertedLocal (p i) (hp i) (hg i) (inverse i)) =
    convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = true) true *
      convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = false) false *
      quadraticRayPair
        (residue (∏ i ∈ Finset.univ.filter (fun i => inverse i = true), p i))
        (residue (∏ i ∈ Finset.univ.filter (fun i => inverse i = false), p i)) := by
  rw [mixed_converted_gauss_separation p hp hg inverse hprimary]
  congr 1
  apply quadraticCrossPhase_eq_rayPair p hp hcop hg hchar
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have ht := (Finset.mem_filter.mp hi).2
  have hf := (Finset.mem_filter.mp hj).2
  rw [ht] at hf
  contradiction

end MixedCrossSeparation

open scoped BigOperators Classical

namespace CoprimeMobiusExtension
abbrev O := ActualEisensteinCubic.O

theorem sum_subset_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

theorem disjoint_indicator_expansion {ι : Type*} [DecidableEq ι]
    (B S T : Finset ι) (hS : S ⊆ B) (_hT : T ⊆ B) :
    (if Disjoint S T then (1 : ℂ) else 0) =
      ∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
  have hsub : (S ∩ T).powerset ⊆ B.powerset :=
    Finset.powerset_mono.mpr (Finset.inter_subset_left.trans hS)
  have heq : (∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) =
      ∑ D ∈ (S ∩ T).powerset, (-1 : ℂ) ^ D.card := by
    calc
      _ = ∑ D ∈ (S ∩ T).powerset,
            if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
        symm
        apply Finset.sum_subset hsub
        intro D hD hnot
        have hn : ¬(D ⊆ S ∧ D ⊆ T) := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hnot
        simp [hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        have hh : D ⊆ S ∧ D ⊆ T := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hD
        simp [hh]
  rw [heq, sum_subset_sign]
  simp only [Finset.disjoint_iff_inter_eq_empty]

theorem double_sum_disjoint_expansion {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
  have hp (S T : Finset ι) (hS : S ∈ B.powerset) (hT : T ∈ B.powerset) :
      (if Disjoint S T then Z S T else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
    calc
      _ = (if Disjoint S T then (1 : ℂ) else 0) * Z S T := by split_ifs <;> simp
      _ = (∑ D ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) * Z S T := by
        rw [disjoint_indicator_expansion B S T (Finset.mem_powerset.mp hS)
          (Finset.mem_powerset.mp hT)]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D hD
        split_ifs <;> simp
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, ∑ D ∈ B.powerset,
        (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => hp S T hS hT)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ D ∈ B.powerset, ∑ T ∈ B.powerset,
            (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem sum_supersets {ι : Type*} [DecidableEq ι]
    (B D : Finset ι) (hD : D ⊆ B) (f : Finset ι → ℂ) :
    (∑ S ∈ B.powerset, if D ⊆ S then f S else 0) =
      ∑ U ∈ (B \ D).powerset, f (D ∪ U) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun S _ => S \ D) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl _)
  · intro S hS T hT heq
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS hT
    have he := congrArg (fun U => D ∪ U) heq
    simpa [Finset.union_sdiff_of_subset hS.2, Finset.union_sdiff_of_subset hT.2] using he
  · intro U hU
    have hUB : U ⊆ B \ D := Finset.mem_powerset.mp hU
    refine ⟨D ∪ U, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hD (hUB.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · apply Finset.union_sdiff_cancel_left
      exact (Finset.disjoint_of_subset_right hUB disjoint_sdiff_self_right)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.union_sdiff_of_subset hS.2]

theorem double_sum_disjoint_reindexed {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset, Z (D ∪ U) (D ∪ V) := by
  rw [double_sum_disjoint_expansion]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hDB := Finset.mem_powerset.mp hD
  calc
    _ = ∑ S ∈ B.powerset, if D ⊆ S then
          (∑ T ∈ B.powerset, if D ⊆ T then Z S T else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hh : D ⊆ S <;> simp [hh]
    _ = _ := by
      rw [sum_supersets B D hDB]
      apply Finset.sum_congr rfl
      intro U hU
      exact sum_supersets B D hDB (Z (D ∪ U))

open ActualEisensteinCubic

theorem ideal_mobius_coprime_reindex
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (B : Finset ι) (Z : Ideal O → Ideal O → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then Z (∏ i ∈ S, P i) (∏ i ∈ T, P i) else 0) =
      ∑ D ∈ B.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ D, P i) : ℂ) *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          Z ((∏ i ∈ D, P i) * ∏ i ∈ U, P i) ((∏ i ∈ D, P i) * ∏ i ∈ V, P i) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [prime_product_moebius P hprime hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  rw [Finset.prod_union (Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right)]
  rw [Finset.prod_union (Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right)]

end CoprimeMobiusExtension

end

end OAI
end OAIOriginalModule0092

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
Source SHA256: dd0ae071b0bdb5746fa6362de83aa86a4ee4462810a7fdbc72f0af95b5887675
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0093


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

namespace IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

def idealDivisors (I : Ideal O) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_idealDivisors {I J : Ideal O} (hI : I ≠ ⊥) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

def primeSupport (I : Ideal O) : Finset (Ideal O) := (normalizedFactors I).toFinset

theorem support_prime {I : Ideal O} {P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal O} (hI : I ≠ ⊥) {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal O}
    {S T : Finset (Ideal O)} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal O} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal O} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal O) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := by
      apply Multiset.toFinset_eq_empty.mp
      exact h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_moebius_divisors (I : Ideal O) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card := by
      exact Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    rw [heq, CoprimeMobiusExtension.sum_subset_sign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

end IdealMobiusDivisorSum

open scoped BigOperators Classical

namespace CompletedGauss

section

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def primaryPrime (P : Ideal O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    (cubicJacobi_exists_primary_generator P h.2).choose
  else 0

theorem primaryPrime_spec (P : Ideal O) (h : primaryPrime P ≠ 0) :
    P.IsMaximal ∧ lambda ∉ P ∧
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
  classical
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    have hs := (cubicJacobi_exists_primary_generator P hg.2).choose_spec
    simpa only [primaryPrime, dite_eq_left hg] using ⟨hg.1, hg.2, hs.1.symm, hs.2.1⟩
  · simp only [primaryPrime, dite_eq_right hg, ne_eq, not_true_eq_false] at h

theorem primaryPrime_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) :
    primaryPrime P ≠ 0 := by
  classical
  have hs := (cubicJacobi_exists_primary_generator P hg).choose_spec
  have htest : P.IsMaximal ∧ lambda ∉ P := ⟨inferInstance, hg⟩
  intro hz
  have hp0 : (cubicJacobi_exists_primary_generator P hg).choose = 0 := by
    simpa only [primaryPrime, dite_eq_left htest] using hz
  rw [hp0] at hs
  exact (NeZero.ne P) (by simpa using hs.1)

def primaryGenerator (I : Ideal O) : O :=
  if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod

@[simp] theorem primaryGenerator_zero : primaryGenerator 0 = 0 := by rw [primaryGenerator, ite_eq_left rfl]

@[simp] theorem primaryGenerator_bot : primaryGenerator ⊥ = 0 := primaryGenerator_zero

@[simp] theorem primaryGenerator_one : primaryGenerator 1 = 1 := by
  rw [primaryGenerator, ite_eq_right one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl

theorem primaryGenerator_mul (I J : Ideal O) :
    primaryGenerator (I * J) = primaryGenerator I * primaryGenerator J := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [primaryGenerator, ite_eq_right hI, ite_eq_right hJ, ite_eq_right (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

def primaryGeneratorHom : Ideal O →*₀ O where
  toFun := primaryGenerator
  map_zero' := primaryGenerator_zero
  map_one' := primaryGenerator_one
  map_mul' := primaryGenerator_mul

theorem primaryGenerator_ne_zero_ideal (I : Ideal O) (h : primaryGenerator I ≠ 0) : I ≠ 0 := by
  intro hI
  exact h (by simp [hI])

theorem primaryPrime_factor_ne_zero (I P : Ideal O) (hI : primaryGenerator I ≠ 0)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : primaryPrime P ≠ 0 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hprod : ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod ≠ 0 := by
    simpa only [primaryGenerator, ite_eq_right hI0] using hI
  intro hz
  exact hprod (Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨P, hP, hz⟩))

theorem span_multiset_prod (s : Multiset O) :
    Ideal.span {s.prod} = (s.map (fun x => Ideal.span {x})).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem primaryGenerator_spec (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    Ideal.span {primaryGenerator I} = I ∧ lambda ^ 2 ∣ primaryGenerator I - 1 := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I h
  have hprime : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P h hP)).2.2
  rw [primaryGenerator, ite_eq_right hI0]
  constructor
  · rw [span_multiset_prod, Multiset.map_map]
    have hm : (UniqueFactorizationMonoid.normalizedFactors I).map
        ((fun x => Ideal.span {x}) ∘ primaryPrime) =
        UniqueFactorizationMonoid.normalizedFactors I := by
      calc
        _ = (UniqueFactorizationMonoid.normalizedFactors I).map id :=
          Multiset.map_congr rfl (fun P hP => (hprime P hP).1)
        _ = _ := Multiset.map_id' _
    rw [hm]
    exact Ideal.prod_normalizedFactors_eq_self hI0
  · apply primary_multiset_prod
    intro r hr
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hr
    exact (hprime P hP).2

theorem primaryGenerator_span (n : O) (hn : n ≠ 0)
    (hprimary : lambda ^ 2 ∣ n - 1) : primaryGenerator (Ideal.span {n}) = n := by
  classical
  have hI0 : (Ideal.span {n} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  have hgen : primaryGenerator (Ideal.span {n}) ≠ 0 := by
    rw [primaryGenerator, ite_eq_right hI0]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨P, hP, hz⟩ := Multiset.mem_map.mp hzero
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
    have hnP : n ∈ P := hle (Ideal.subset_span (by simp))
    exact primaryPrime_ne_zero P (primary_maximal_divisor_good n hprimary P hnP) hz
  have hspec := primaryGenerator_spec (Ideal.span {n}) hgen
  exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1)
    hspec.2 hprimary

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

theorem compact_window_bound (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ y, W y ≠ 0 → y ≤ B := by
  obtain ⟨B, hB⟩ := hW.bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact (hB (subset_tsupport W hy)).trans (le_max_left _ _)

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_scale_bounds (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b ^ 3 * c ^ 3 ∧ b ≤ a * b ^ 3 * c ^ 3 ∧ c ≤ a * b ^ 3 * c ^ 3 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  constructor
  · calc a = a * 1 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  constructor
  · calc b ≤ b ^ 3 := le_self_pow₀ hb (by decide)
         _ = 1 * b ^ 3 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  · calc c ≤ c ^ 3 := le_self_pow₀ hc (by decide)
         _ = 1 * 1 * c ^ 3 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr

theorem finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * X)
  let S := {I : Ideal O | Ideal.absNorm I ≤ M}
  have hS : S.Finite := Ideal.finite_setOfPred_absNorm_le M
  apply (hS.prod (hS.prod hS)).subset
  rintro ⟨I, J, H⟩ hF
  have hF0 : F (I, J, H) ≠ 0 := hF
  have hI : I ≠ 0 := fun h => hF0 (hzero I J H (Or.inl h))
  have hJ : J ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inl h)))
  have hH : H ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inr h)))
  have hw : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
      (Ideal.absNorm H : ℝ) ^ 3 / X) ≠ 0 := fun h => hF0 (hwindow I J H h)
  have hsize := (div_le_iff₀ hX).mp (hbound _ hw)
  have hb := triple_scale_bounds _ _ _ (norm_at_least_one I hI)
    (norm_at_least_one J hJ) (norm_at_least_one H hH)
  have hIM : Ideal.absNorm I ≤ M := by exact_mod_cast (hb.1.trans hsize).trans hM.le
  have hJM : Ideal.absNorm J ≤ M := by exact_mod_cast (hb.2.1.trans hsize).trans hM.le
  have hHM : Ideal.absNorm H ≤ M := by exact_mod_cast (hb.2.2.trans hsize).trans hM.le
  exact ⟨hIM, hJM, hHM⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT

def primeSupport (I : Ideal O) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

abbrev PrimeIndex (I : Ideal O) := {P : Ideal O // P ∈ primeSupport I}

instance primeIndexMaximal (I : Ideal O) (P : PrimeIndex I) : P.val.IsMaximal := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp P.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primeIndex_good (I : Ideal O) (hI : primaryGenerator I ≠ 0) (P : PrimeIndex I) :
    lambda ∉ P.val :=
  (primaryPrime_spec P.val (primaryPrime_factor_ne_zero I P.val hI
    (Multiset.mem_toFinset.mp P.property))).2.1

theorem primeIndex_le (I : Ideal O) (hI : I ≠ 0) (P : PrimeIndex I) : I ≤ P.val :=
  ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp P.property)).2

def cubicRow (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O ⧸ I) : ℂ :=
  ∏ P : PrimeIndex I,
    (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
      (Ideal.Quotient.factor (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI) P) x)

def gaussTwo (I : Ideal O) (hI : primaryGenerator I ≠ 0) : ℂ := by
  let n := primaryGenerator I
  letI : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hI
  letI : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  exact (∑ x : O ⧸ Ideal.span {n}, cubicRow I hI (e x) * ψ x) / (‖eisEmbedding n‖ : ℂ)

def squarefreeGaussCoefficient (I : Ideal O) : ℂ :=
  if h : Squarefree I ∧ primaryGenerator I ≠ 0 then
    star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I h.2
  else 0

@[simp] theorem squarefreeGaussCoefficient_zero : squarefreeGaussCoefficient 0 = 0 := by
  simp [squarefreeGaussCoefficient]

@[simp] theorem squarefreeGaussCoefficient_bot : squarefreeGaussCoefficient ⊥ = 0 :=
  squarefreeGaussCoefficient_zero

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dite_eq_left ⟨hs, hI⟩]

theorem angularFactor_mul (a b : O) :
    FiniteGaussPhase.angularFactor (a * b) =
      FiniteGaussPhase.angularFactor a * FiniteGaussPhase.angularFactor b := by
  simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul]
  ring

def cubeWeight (Ψ : O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (FiniteGaussPhase.angularFactor (primaryGenerator I)) ^ 3 *
    Ψ (primaryGenerator I) ^ 3 / (Ideal.absNorm I : ℂ)
  map_one' := by
    simp only [primaryGenerator_one, FiniteGaussPhase.angularFactor, map_one,
      norm_one, Complex.ofReal_one, div_one, star_one, one_pow, one_mul, Nat.cast_one]
  map_mul' I J := by
    simp only [primaryGenerator_mul, angularFactor_mul, map_mul, star_mul, mul_pow, Nat.cast_mul]
    ring

@[simp] theorem cubeWeight_zero (Ψ : O →* ℂ) : cubeWeight Ψ 0 = 0 := by
  simp [cubeWeight, FiniteGaussPhase.angularFactor]

@[simp] theorem cubeWeight_bot (Ψ : O →* ℂ) : cubeWeight Ψ ⊥ = 0 := cubeWeight_zero Ψ

def columnWeight (Ψ : O →* ℂ) (I : Ideal O) : ℂ :=
  squarefreeGaussCoefficient I * Ψ (primaryGenerator I)

@[simp] theorem columnWeight_zero (Ψ : O →* ℂ) : columnWeight Ψ 0 = 0 := by
  simp [columnWeight]

@[simp] theorem columnWeight_bot (Ψ : O →* ℂ) : columnWeight Ψ ⊥ = 0 := columnWeight_zero Ψ

def Vstar (W : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * W y

def summand (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) * cubeWeight Ψ J *
    Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)

def completedT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, summand Ψ W X I J

theorem summand_zero_left (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (J : Ideal O) :
    summand Ψ W X 0 J = 0 := by simp [summand]

theorem summand_zero_right (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I : Ideal O) :
    summand Ψ W X I 0 = 0 := by simp [summand]

theorem summand_zero_window (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O)
    (h : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X) = 0) :
    summand Ψ W X I J = 0 := by simp [summand, Vstar, h]

theorem cubicRow_mk (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) =
      ∏ P : PrimeIndex I, (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
        (Ideal.Quotient.mk P.val a) := by
  simp only [cubicRow, Ideal.Quotient.factor_mk]

theorem cubicRow_zero_iff (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) = 0 ↔
      ∃ P ∈ primeSupport I, a ∈ P := by
  rw [cubicRow_mk, Finset.prod_eq_zero_iff]
  have hlocal (P : PrimeIndex I) :
      (canonicalSextic P.val (primeIndex_good I hI P) ^ 2) (Ideal.Quotient.mk P.val a) = 0 ↔ a ∈ P.val := by
    let : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
    rw [MulChar.apply_eq_zero_iff]
    simp only [isUnit_iff_ne_zero, not_not, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨P, _, hP⟩
    exact ⟨P.val, P.property, (hlocal P).mp hP⟩
  · rintro ⟨P, hP, ha⟩
    exact ⟨⟨P, hP⟩, Finset.mem_univ _, (hlocal ⟨P, hP⟩).mpr ha⟩

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem cubeWeight_span (Ψ : O →* ℂ) (n : O) (hn : n ≠ 0)
    (hp : lambda ^ 2 ∣ n - 1) :
    cubeWeight Ψ (Ideal.span {n}) =
      star (FiniteGaussPhase.angularFactor n) ^ 3 * Ψ n ^ 3 /
        (ShortDraftLatticeCount.qNat n : ℂ) := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator (Ideal.span {n}))) ^ 3 *
    Ψ (primaryGenerator (Ideal.span {n})) ^ 3 / (Ideal.absNorm (Ideal.span {n}) : ℂ) = _
  rw [primaryGenerator_span n hn hp, qNat_eq_absNorm_span]

theorem columnWeight_eq (Ψ : O →* ℂ) (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    columnWeight Ψ I = star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
      gaussTwo I hI * Ψ (primaryGenerator I) := by
  rw [columnWeight, squarefreeGaussCoefficient_eq I hs hI]

theorem columnWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : columnWeight Ψ I = 0 := by
  simp only [columnWeight, h, mul_zero]

theorem cubeWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : cubeWeight Ψ I = 0 := by
  change _ * Ψ (primaryGenerator I) ^ 3 / _ = 0
  rw [h, zero_pow (by decide), mul_zero, zero_div]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

def MulFiber (B : Ideal O) := {p : Ideal O × Ideal O // p.1 * p.2 = B}

def mulFiberDivisorEquiv (B : Ideal O) (hB : B ≠ 0) :
    MulFiber B ≃ {D : Ideal O // D ∈ idealDivisors B} := by
  let f : MulFiber B → {D : Ideal O // D ∈ idealDivisors B} :=
    fun p => ⟨p.val.1, (mem_idealDivisors hB).mpr ⟨p.val.2, p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz, zero_mul] at he
      exact hB he.symm
    apply mul_left_cancel₀ hn
    rw [p.property, hfst, q.property]
  · intro D
    obtain ⟨J, hJ⟩ := (mem_idealDivisors hB).mp D.property
    exact ⟨⟨(D.val, J), hJ.symm⟩, rfl⟩

theorem mulFiber_moebius_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) =
      if B = 1 then 1 else 0 := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B},
        (UniqueFactorizationMonoid.moebius D.val : ℂ) := by
      exact e.tsum_eq (fun D => (UniqueFactorizationMonoid.moebius D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (UniqueFactorizationMonoid.moebius D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun D => Iff.rfl)
        (fun D => (UniqueFactorizationMonoid.moebius D : ℂ))).symm
    _ = if B = 1 then 1 else 0 := by
      simpa only [Ideal.one_eq_top] using sum_moebius_divisors B hB

theorem ideal_cube_convolution (c : Ideal O →* ℂ) (hc0 : c 0 = 0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2))).Finite) :
    (∑' H : Ideal O, ∑' J : Ideal O,
      (UniqueFactorizationMonoid.moebius H : ℂ) * c (H * J) * f (H * J)) = f 1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2)
  have hF : Summable F := summable_of_hasFiniteSupport hfinite
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      if B = 1 then f 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have heach : ∀ p : MulFiber 0, F p.val = 0 := by
        intro p
        dsimp [F]
        rw [p.property, hc0, mul_zero, zero_mul]
      simp only [heach, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = ∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) * (c B * f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property, mul_assoc]
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) * (c B * f B) := by
          rw [tsum_mul_right]
        _ = if B = 1 then f 1 else 0 := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with h
          · subst B; simp only [map_one, one_mul]
          · simp
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) (∑' p, F p) at hs
  simp_rw [hfiber] at hs
  have hsum : (∑' p, F p) = f 1 := by
    have he := hs.tsum_eq.symm
    simpa only [tsum_ite_eq, one_ne_zero] using he
  rw [← hF.tsum_prod]
  exact hsum

end CompletedGauss

end

end OAI
end OAIOriginalModule0093

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
Source SHA256: 01569023b64065bc867e0a0ce170bc71a006758313b4b05b886b4af7a0b7ee94
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0094


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
