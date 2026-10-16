  ring

lemma eigenfunction_summand_eq_actual_series (s : ℂ) (r : CuspCosets)
    (x y v : ℝ) (hv : 0<v) :
    (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v =
      summand (upperSection ((x:ℂ)+(y:ℂ)*Complex.I) v hv) s r := by
  rw [summand_upperSection]
  rfl

end CubicEisenstein

end

end OAI
end OAIOriginalModule0145

/-! Original module: OAI.NumberTheory.DirichletL.Fourier.LogDensity
Source SHA256: a3eb6bed0afbb2e4054ef484b3c57210ac599f953aa5580d27b67988fe1c1032
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0146


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

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation
open FirstPassCubeLabels

def tripleLogDensity (J : ℕ) (t : Frequency) : ℝ :=
  firstLogDensity J t.1 * (firstLogDensity J t.2.1 * firstLogDensity J t.2.2)

lemma tripleLogDensity_integrable (J : ℕ) : Integrable (tripleLogDensity J) :=
  (firstLogDensity_integrable J).mul_prod
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J))

lemma tripleLogDensity_nonneg (J : ℕ) (t : Frequency) : 0 ≤ tripleLogDensity J t :=
  mul_nonneg (firstLogDensity_nonneg _ _) (mul_nonneg
    (firstLogDensity_nonneg _ _) (firstLogDensity_nonneg _ _))

lemma tripleLogDensity_bounded_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => tripleLogDensity J t * G t) :=
  (tripleLogDensity_integrable J).mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleLogDensity_slice_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun yz : ℝ × ℝ => tripleLogDensity J (x,yz) * G (x,yz)) := by
  have hc : Integrable (fun yz : ℝ × ℝ =>
      firstLogDensity J x * (firstLogDensity J yz.1 * firstLogDensity J yz.2)) :=
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J)).const_mul _
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

theorem triple_coefficient_density_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ)
    (G : Frequency → ℝ) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (M : ℝ) (hM : ∀ t, G t ≤ M) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ,
      S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) ≤
    C * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleLogDensity J (t₁,t₂,t₃) * G (t₁,t₂,t₃)) := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hc := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  have hd := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hc (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb),
    nested_eq_integral _ hd (tripleLogDensity_slice_integrable J G hG M hGb),
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono (hc.const_mul S) (hd.const_mul C)
  intro t
  have hh := mul_le_mul_of_nonneg_right (hpoint t.1 t.2.1 t.2.2) (hG0 t)
  simpa only [tripleCoefficient, tripleLogDensity, mul_assoc] using hh

end JointLogSeparation

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation

def densityChildEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) : ℝ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    tripleLogDensity J (t₁,t₂,t₃) *
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

theorem child_coefficient_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
      C * FirstPassCubeLabels.firstLogDensity J t₁ *
        FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
        childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) ≤
    C * densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  exact triple_coefficient_density_bound b₁ b₂ b₃ J G hG hG0 M hM S C hpoint

end SecondPassIntegration

namespace JointLogSeparation
open FirstPassCubeLabels

lemma one_add_norm_sub_le (x y : ℝ) :
    1 + ‖x-y‖ ≤ (1+‖x‖)*(1+‖y‖) := by
  have hn := norm_sub_le x y
  have hprod := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  nlinarith

theorem difference_height_weight_le (x y z : ℝ) (J : ℕ) :
    (1+‖x-z‖)^J * (1+‖y-z‖)^J ≤
      (1+‖x‖)^(2*J) * (1+‖y‖)^(2*J) * (1+‖z‖)^(2*J) := by
  have hx := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x-z‖) (one_add_norm_sub_le x z) J
  have hy := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖y-z‖) (one_add_norm_sub_le y z) J
  calc
    _ ≤ ((1+‖x‖)*(1+‖z‖))^J * ((1+‖y‖)*(1+‖z‖))^J :=
      mul_le_mul hx hy (by positivity) (by positivity)
    _ = (1+‖x‖)^J * (1+‖y‖)^J * (1+‖z‖)^(2*J) := by
      rw [mul_pow, mul_pow, two_mul, pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1+‖x‖) (by omega : J ≤ 2*J))
        (pow_le_pow_right₀ (by linarith [norm_nonneg y] : 1 ≤ 1+‖y‖) (by omega : J ≤ 2*J))
        (by positivity) (by positivity)

theorem triple_density_polynomial_bound (G : Frequency → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) (M : ℝ) (hM : ∀ t, G t ≤ M)
    (J : ℕ) (D : ℝ)
    (hbound : ∀ t, G t ≤ D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, tripleLogDensity J (x,y,z) * G (x,y,z)) ≤
      D * (∫ t : ℝ, firstLogDensity 0 t)^3 := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hi := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hi (tripleLogDensity_slice_integrable J G hG M hGb)]
  have hh : ∀ t : Frequency, tripleLogDensity J t * G t ≤ D * tripleLogDensity 0 t := by
    intro t
    calc
      _ ≤ tripleLogDensity J t *
          (D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :=
        mul_le_mul_of_nonneg_left (hbound t) (tripleLogDensity_nonneg J t)
      _ = _ := by
        dsimp only [tripleLogDensity]
        rw [← density_weight_identity J t.1, ← density_weight_identity J t.2.1,
          ← density_weight_identity J t.2.2]
        ring
  calc
    _ ≤ ∫ t : Frequency, D * tripleLogDensity 0 t :=
      integral_mono hi ((tripleLogDensity_integrable 0).const_mul D) hh
    _ = D * (∫ t : Frequency, tripleLogDensity 0 t) := integral_const_mul _ _
    _ = _ := by
      have hslice (x : ℝ) : Integrable (fun yz : ℝ × ℝ => tripleLogDensity 0 (x,yz)) := by
        simpa only [tripleLogDensity, Measure.volume_eq_prod] using
          ((firstLogDensity_integrable 0).mul_prod (firstLogDensity_integrable 0)).const_mul
            (firstLogDensity 0 x)
      rw [← nested_eq_integral _ (tripleLogDensity_integrable 0) hslice]
      simp only [tripleLogDensity, integral_const_mul, integral_mul_const]
      ring

end JointLogSeparation
end

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem ideals_coprime_of_relprime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_gcd.mpr
  simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp (h (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B))

theorem squarefree_quotient_gcd_coprime (B G : Ideal O) (hB : Squarefree B) :
    IsCoprime (idealQuotient (gcd B G) B) G := by
  let D := gcd B G
  have hDB : D ∣ B := GCDMonoid.gcd_dvd_left B G
  have hDG : D ∣ G := GCDMonoid.gcd_dvd_right B G
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hB.ne_zero hDB
  have hc : IsCoprime (idealQuotient D B) (idealQuotient D G) :=
    (gcd_eq_iff_quotient_coprime D B G hD hDB hDG).mp rfl
  have hmul : Squarefree (D * idealQuotient D B) := by rw [idealQuotient_mul hDB]; exact hB
  have hdq : IsCoprime D (idealQuotient D B) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hmul).1
  have hh := hdq.symm.mul_right hc
  rw [idealQuotient_mul hDG] at hh
  exact hh

theorem gcd_mul_of_coprime_divisor (D H G : Ideal O) (hDG : D ∣ G) (hHG : IsCoprime H G) :
    gcd (D * H) G = D := by
  have hleft : D ∣ gcd (D * H) G := GCDMonoid.dvd_gcd (dvd_mul_right D H) hDG
  have hcop : IsCoprime (gcd (D * H) G) H :=
    (hHG.mono (dvd_refl H) (GCDMonoid.gcd_dvd_right (D * H) G)).symm
  have hright : gcd (D * H) G ∣ D := hcop.dvd_of_dvd_mul_right (GCDMonoid.gcd_dvd_left _ _)
  exact associated_iff_eq.mp (associated_of_dvd_dvd hright hleft)

def squarefreeGcdEquiv (G : Ideal O) (hG : Squarefree G) :
    {B : Ideal O // Squarefree B} ≃
      (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G} where
  toFun B := (⟨gcd B.val G, (mem_idealDivisors hG.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)⟩,
    ⟨idealQuotient (gcd B.val G) B.val,
      B.property.squarefree_of_dvd (idealQuotient_dvd (GCDMonoid.gcd_dvd_left _ _)),
      squarefree_quotient_gcd_coprime B.val G B.property⟩)
  invFun p := ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
    ⟨(p.2.property.2.mono (dvd_refl _) ((mem_idealDivisors hG.ne_zero).mp p.1.property)).symm.isRelPrime,
      hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp p.1.property), p.2.property.1⟩⟩
  left_inv B := Subtype.ext (idealQuotient_mul (GCDMonoid.gcd_dvd_left B.val G))
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2
    · apply Subtype.ext
      change idealQuotient (gcd (p.1.val * p.2.val) G) (p.1.val * p.2.val) = p.2.val
      rw [gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2]
      have hD : p.1.val ≠ 0 := ne_zero_of_dvd_ne_zero hG.ne_zero
        ((mem_idealDivisors hG.ne_zero).mp p.1.property)
      exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right p.1.val p.2.val))

theorem squarefree_gcd_tsum (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, f B.val) =
      ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        f (p.1.val * p.2.val) :=
  ((squarefreeGcdEquiv G hG).symm.tsum_eq (fun B => f B.val)).symm

def coprimeSquarefreeRange (G : Ideal O) (K : ℝ) : Finset (Ideal O) :=
  (squarefreeIdealRange K).filter (fun H => IsCoprime H G)

theorem squarefree_cutoff_summable (K : ℝ) (f : Ideal O → ℂ) :
    Summable (fun B : {B : Ideal O // Squarefree B} =>
      if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) := by
  let e : squarefreeIdealRange K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealRange.mp B.property).1⟩
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range e).subset
  intro B hB
  have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
    by_contra hn
    exact hB (ite_eq_right hn)
  exact ⟨⟨B.val, mem_squarefreeIdealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩

theorem norm_le_mul_of_ne_zero (D H : Ideal O) (hD : D ≠ 0) :
    Ideal.absNorm H ≤ Ideal.absNorm (D * H) := by
  have hD1 : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr
    (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  simpa only [one_mul, map_mul] using Nat.mul_le_mul_right (Ideal.absNorm H) hD1

theorem coprime_squarefree_cutoff (G D : Ideal O) (hD : D ≠ 0) (K : ℝ) (f : Ideal O → ℂ) :
    (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
      if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0) =
      ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0 := by
  let e : coprimeSquarefreeRange G K → {H : Ideal O // Squarefree H ∧ IsCoprime H G} :=
    fun H => ⟨H.val, (mem_squarefreeIdealRange.mp (Finset.mem_filter.mp H.property).1).1,
      (Finset.mem_filter.mp H.property).2⟩
  have he : Function.Injective e := by
    intro H J h
    apply Subtype.ext
    exact congrArg (fun C : {H : Ideal O // Squarefree H ∧ IsCoprime H G} => C.val) h
  let F : {H : Ideal O // Squarefree H ∧ IsCoprime H G} → ℂ := fun H =>
    if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro H hH
    have hN : (Ideal.absNorm (D * H.val) : ℝ) ≤ K := by
      by_contra hn
      exact hH (ite_eq_right hn)
    have hHN : (Ideal.absNorm H.val : ℝ) ≤ K :=
      (Nat.cast_le.mpr (norm_le_mul_of_ne_zero D H.val hD)).trans hN
    exact ⟨⟨H.val, Finset.mem_filter.mpr
      ⟨mem_squarefreeIdealRange.mpr ⟨H.property.1, hHN⟩, H.property.2⟩⟩, Subtype.ext rfl⟩
  simpa only [tsum_fintype, F, e] using (he.tsum_eq hs).symm

theorem squarefree_gcd_finite_sum (G : Ideal O) (hG : Squarefree G) (K : ℝ) (f : Ideal O → ℂ) :
    (∑ B : squarefreeIdealRange K, f B.val) =
      ∑ D : idealDivisors G, ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0 := by
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs := (squarefreeGcdEquiv G hG).symm.summable_iff.mpr (squarefree_cutoff_summable K f)
  have he := ((squarefreeGcdEquiv G hG).symm.tsum_eq F).symm
  calc
    _ = ∑' B : {B : Ideal O // Squarefree B}, F B := (tsum_squarefree_norm_cutoff K f).symm
    _ = ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm p) := he
    _ = ∑' D : idealDivisors G, ∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm (D, H)) := hs.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro D _
      change (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0) = _
      exact coprime_squarefree_cutoff G D.val
        (ne_zero_of_dvd_ne_zero hG.ne_zero ((mem_idealDivisors hG.ne_zero).mp D.property)) K f

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem canonical_quadraticRow_one (I : Ideal O) (hI : Admissible I) : quadraticRow I 1 = 1 := by
  rw [quadraticRow, dite_eq_left hI]
  simp [idealSexticRow, finiteSquarefreeRow]

theorem unrestrictedPairCharacter_one (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : unrestrictedPairCharacter I J 1 = 1 := by
  have h := unrestrictedPairCharacter_span I J hI hJ hray 1
  simpa only [Ideal.span_singleton_one, canonical_quadraticRow_one I hI,
    canonical_quadraticRow_one J hJ, one_mul, Ideal.one_eq_top] using h

def normalizedIdealPair (I J lengthScale : Ideal O) : ℂ :=
  unrestrictedPairCharacter I J lengthScale / (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ)

theorem normalizedIdealPair_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    normalizedIdealPair I J (A * B) = normalizedIdealPair I J A * normalizedIdealPair I J B := by
  simp only [normalizedIdealPair, unrestrictedPairCharacter_mul I J hI hJ hray,
    map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, div_mul_div_comm]

def normalizedIdealPairHom (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : Ideal O →* ℂ where
  toFun := normalizedIdealPair I J
  map_one' := by
    rw [normalizedIdealPair, unrestrictedPairCharacter_one I J hI hJ hray, map_one]
    norm_num
  map_mul' := normalizedIdealPair_mul I J hI hJ hray

theorem normalizedIdealPair_square (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    normalizedIdealPair I J lengthScale ^ 2 =
      (idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale)) / (Ideal.absNorm lengthScale : ℂ) := by
  have hc : unrestrictedPairCharacter I J lengthScale ^ 2 =
      idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale) := by
    unfold unrestrictedPairCharacter
    calc
      _ = (quadraticRow I (idealGenerator lengthScale) * quadraticRow I (idealGenerator lengthScale)) *
        (quadraticRow J (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)) := by ring
      _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]
  have hn : (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ) ^ 2 = (Ideal.absNorm lengthScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm lengthScale) : (0 : ℝ) ≤ _)
  rw [normalizedIdealPair, div_pow, hc, hn]

theorem squarefree_divisor_sum_eq_support (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors G, f D) =
      ∑ S ∈ (IdealMobiusDivisorSum.primeSupport G).powerset, f (∏ P ∈ S, P) := by
  have hfilter : (idealDivisors G).filter Squarefree = idealDivisors G := by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp hD)
  rw [← hfilter, squarefree_divisors_eq_image G hG.ne_zero, Finset.sum_image]
  intro S hS T hT hST
  exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST

theorem normalizedIdealPair_double_divisor
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hray : columnRay I = columnRay J)
    (G : Ideal O) (hG : Squarefree G) :
    (∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J (D * E)) =
      ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
        (1 - (idealZeroMask I (idealGenerator P) * idealZeroMask J (idealGenerator P)) /
          (Ideal.absNorm P : ℂ)) := by
  rw [squarefree_divisor_sum_eq_support G hG]
  simp_rw [squarefree_divisor_sum_eq_support G hG]
  have hprod (S : Finset (Ideal O)) : normalizedIdealPair I J (∏ P ∈ S, P) =
      ∏ P ∈ S, normalizedIdealPair I J P := map_prod (normalizedIdealPairHom I J hI hJ hray) (fun P => P) S
  have hm (E : Finset (Ideal O)) (hE : E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset) :
      (UniqueFactorizationMonoid.moebius (∏ P ∈ E, P) : ℂ) = (-1 : ℂ) ^ E.card :=
    moebius_support_product (Finset.mem_powerset.mp hE)
  have heq : (∑ D ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
      ∑ E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
        (UniqueFactorizationMonoid.moebius (∏ P ∈ E, P) : ℂ) *
          normalizedIdealPair I J ((∏ P ∈ D, P) * ∏ P ∈ E, P)) =
      ∑ D ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
        ∑ E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
          (-1 : ℂ) ^ E.card * (∏ P ∈ D, normalizedIdealPair I J P) *
            ∏ P ∈ E, normalizedIdealPair I J P := by
    apply Finset.sum_congr rfl
    intro D hD
    apply Finset.sum_congr rfl
    intro E hE
    rw [hm E hE, normalizedIdealPair_mul I J hI hJ hray, hprod D, hprod E]
    ring
  rw [heq]
  have hh := QuadraticDivisorCancellation.double_divisor_factorization
    (normalizedIdealPair I J) (IdealMobiusDivisorSum.primeSupport G) ∅ (by simp)
  simpa only [Finset.union_empty, Finset.powerset_empty, Finset.sum_singleton,
    Finset.prod_empty, Finset.card_empty, pow_zero, mul_one,
    normalizedIdealPair_square I J hI hJ] using hh

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary

def idealNormCutoff (K : ℝ) (H : Ideal O) : ℂ := if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0

def normalizedPairPartial (I J : Ideal O) (K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, normalizedIdealPair I J B.val

def normalizedPairCoprimePartial (I J G : Ideal O) (K : ℝ) : ℂ :=
  ∑ H : coprimeSquarefreeRange G K, normalizedIdealPair I J H.val

def normalizedPairDivisors (I J G : Ideal O) : ℂ :=
  ∑ E ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J E

def normalizedPairDensity (I J G : Ideal O) : ℂ :=
  ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
    (1 - (idealZeroMask I (ConcretePrimeRowBridge.idealGenerator P) *
      idealZeroMask J (ConcretePrimeRowBridge.idealGenerator P)) / (Ideal.absNorm P : ℂ))

theorem normalizedPairPartial_split (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    normalizedPairPartial I J K =
      ∑ H : coprimeSquarefreeRange G K, ∑ D ∈ idealDivisors G,
        normalizedIdealPair I J H.val * normalizedIdealPair I J D * idealNormCutoff K (H.val * D) := by
  rw [normalizedPairPartial, squarefree_gcd_finite_sum G hG K]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_coe_sort (idealDivisors G)
    (fun D => if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then normalizedIdealPair I J (D * H.val) else 0)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [mul_comm D H.val]
  rw [normalizedIdealPair_mul I J hI hJ hray]
  unfold idealNormCutoff
  split_ifs <;> ring

theorem normalizedPair_main_difference
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hray : columnRay I = columnRay J)
    (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    normalizedPairPartial I J K * normalizedPairDivisors I J G -
      normalizedPairCoprimePartial I J G K * normalizedPairDensity I J G =
      ∑ H : coprimeSquarefreeRange G K, ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J (H.val * D * E) *
          (cutoffDifference K H.val D : ℂ) := by
  have hd : normalizedPairDensity I J G =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (normalizedIdealPair I J D * normalizedIdealPair I J E) := by
    rw [normalizedPairDensity, ← normalizedIdealPair_double_divisor I J hI hJ hray G hG]
    simp only [normalizedIdealPair_mul I J hI hJ hray]
  rw [normalizedPairPartial_split I J hI hJ hray G hG K, hd]
  unfold normalizedPairDivisors normalizedPairCoprimePartial
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHN : (Ideal.absNorm H.val : ℝ) ≤ K :=
    (mem_squarefreeIdealRange.mp (Finset.mem_filter.mp H.property).1).2
  have hc : (cutoffDifference K H.val D : ℂ) = idealNormCutoff K (H.val * D) - 1 := by
    unfold cutoffDifference idealNormCutoff
    rw [ite_eq_left hHN]
    split_ifs <;> norm_num
  rw [hc, normalizedIdealPair_mul I J hI hJ hray,
    normalizedIdealPair_mul I J hI hJ hray]
  ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def commonMaskIdeal (D : Ideal O) : Ideal O := ∏ P ∈ gcdMaskPrimes D, P

theorem commonMaskIdeal_squarefree (D : Ideal O) : Squarefree (commonMaskIdeal D) := by
  have hp (P : Ideal O) (hP : P ∈ gcdMaskPrimes D) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro P hP Q hQ hne
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    let : Q.IsMaximal := gcdMaskPrimes_maximal D ⟨Q, hQ⟩
    exact (Ideal.isCoprime_of_isMaximal hne).isRelPrime
  · intro P hP
    exact (hp P hP).squarefree

theorem fixedBadPrimes_dvd_commonMaskIdeal (D P : Ideal O) (hP : P ∈ fixedBadPrimes) :
    P ∣ commonMaskIdeal D := by
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_union_left _ hP

theorem admissible_of_squarefree_coprime_bad
    (H G : Ideal O) (hH : Squarefree H) (hc : IsCoprime H G)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) : Admissible H := by
  refine ⟨hH.ne_zero, hH, ?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hp.not_isUnit (hc.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) (hbad P hb))

theorem coprimeSquarefreeRange_subset_idealRange (G : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) (K : ℝ) :
    coprimeSquarefreeRange G K ⊆ idealRange K := by
  intro H hH
  obtain ⟨hHs, hc⟩ := Finset.mem_filter.mp hH
  obtain ⟨hsf, hN⟩ := mem_squarefreeIdealRange.mp hHs
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad H G hsf hc hbad, hN⟩

theorem commonMask_coprimeSquarefreeRange_subset (D : Ideal O) (K : ℝ) :
    coprimeSquarefreeRange (commonMaskIdeal D) K ⊆ idealRange K :=
  coprimeSquarefreeRange_subset_idealRange _ (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP) K

theorem commonMaskIdeal_eq_fixed_mul (D : Ideal O) (hD : Admissible D) :
    commonMaskIdeal D = (∏ P ∈ fixedBadPrimes, P) * D := by
  have hd : Disjoint fixedBadPrimes (IdealMobiusDivisorSum.primeSupport D) := by
    apply Finset.disjoint_left.mpr
    intro P hp hP
    have hfac := Multiset.mem_toFinset.mp hP
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hfac
    let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
    exact (prime_good_iff_not_bad P).mp (hD.2.2 P hfac) hp
  change (∏ P ∈ fixedBadPrimes ∪ IdealMobiusDivisorSum.primeSupport D, P) = _
  rw [Finset.prod_union hd, squarefree_support_product_self hD.2.1]

theorem commonMaskIdeal_norm (D : Ideal O) (hD : Admissible D) :
    Ideal.absNorm (commonMaskIdeal D) = Ideal.absNorm (∏ P ∈ fixedBadPrimes, P) * Ideal.absNorm D := by
  rw [commonMaskIdeal_eq_fixed_mul D hD, map_mul]

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0146

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff
Source SHA256: dc60af6029b452d8f51cbf0d0e57059efa948c2d1324b0716925a58e4dd0bcd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0147



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

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def firstCoreSecondCutoff {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : Finset ι) (X Y A H : ℝ) (G E : Finset ι) : Finset O :=
  secondFrequencyCutoff
    (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
      (((X / primeProductNorm p D) / primeProductNorm p G) * Real.exp A)^2)) H

theorem firstCoreSecondCutoff_zero {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : Finset ι) (X Y A H : ℝ) (G E : Finset ι) :
    (0 : O) ∈ firstCoreSecondCutoff p D X Y A H G E :=
  secondFrequencyCutoff_zero _ _

theorem firstCoreSecondCutoff_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t A : ℝ)
    (hgA : ∀ s, g s ≠ 0 → |s| ≤ A)
    (D G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T) (hST : Disjoint S T)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hS : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)) (G∪S) ≠ 0)
    (hT : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)) (G∪T) ≠ 0)
    (k : O) (hk : k ∉ firstCoreSecondCutoff p D X Y A H G E) :
    H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have hXD : 0 < X / primeProductNorm p D := div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hXG : 0 < (X / primeProductNorm p D) / primeProductNorm p G :=
    div_pos hXD (FirstPassCubeLabels.primeProductNorm_pos p hp G)
  have hSup (S : Finset ι) (hGS : Disjoint G S)
      (hS : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
        (columnLog p (X / primeProductNorm p D) A)) (G∪S) ≠ 0) :
      columnLog p ((X / primeProductNorm p D) / primeProductNorm p G) S ≤ A := by
    have hs : firstCoreModeProfile g V negative t (columnLog p (X / primeProductNorm p D) (G∪S)) ≠ 0 := by
      intro hz
      apply hS
      simp only [normalizedColumn, hz, zero_div]
    have ha := hgA _ (firstCoreModeProfile_support g V negative t _ hs).1
    rw [SecondPassIntegration.columnLog_extract_common p hp G S hGS _ hXD] at ha
    exact le_trans (le_abs_self _) ha
  exact secondFrequencyCutoff_uniform p hp ((X / primeProductNorm p D) / primeProductNorm p G)
    Y A H hXG hY (primeSubsetGenerator (fun i => Ideal.span {p i}) E)
    (primeSubsetGenerator_ne_zero _ _) S T hST (hSup S hGS hS) (hSup T hGT hT) k hk

theorem first_second_normalization_factor {ι : Type*}
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (D : Finset ι) (X Y R : ℝ) (hX : 0 < X) :
    (primeProductNorm p D)⁻¹ * (Y * R / (X / primeProductNorm p D)^2) =
      Y * primeProductNorm p D * R / X^2 := by
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp D).ne'
  have hx := hX.ne'
  field_simp

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply halfNormalization_twist
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean)

theorem normalized_twisted_second_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 (frequencyTwist A₁ (-θ₁))) t₁*(𝓕 (frequencyTwist A₂ θ₂)) t₂*b t₃‖ ≤
          Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₁ θ₁) (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₂ θ₂) (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
              (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  have hn₁ : ∀ t, halfNormalizationCLM U g₁ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₁ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  have hn₂ : ∀ t, halfNormalizationCLM U g₂ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₂ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hW,htrans⟩ :=
    actual_raw_twisted_sector_transfer p hp hcop hg hinj
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A H hA hH hn₁ hn₂ ε hε decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨b,hb⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  refine ⟨b,?_⟩
  intro θ₁ θ₂
  obtain ⟨hb',hbound⟩ := hb θ₁ θ₂
  refine ⟨hb',?_⟩
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL hz hud hue huv hkap hmap hT hnorm
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  have hsector : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x (hs hx)
  have hU₁' : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    apply hs
    simp only [frequencyTwist_apply, hz, mul_zero]
  have hU₂' : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    apply hs
    simp only [frequencyTwist_apply, hz, mul_zero]
  rw [secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F v₁ v₂ ε₁ ε₂
    Ψ m r z s hsector X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W hU₁' hU₂']
  simp only [halfNormalization_twist U hUc hUs]
  have hrow : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact secondExpansionSector_frequency_ne_zero F K R x (hs hx)
  have liftP : ∀ P : SecondSupportData ι → Prop,
      (∀ x ∈ s, P (expansionSupportData C D x)) →
      ∀ y ∈ s.image (expansionSupportData C D), P y := by
    intro P hP y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hP x hx
  have hxscale : ∀ y : SecondSupportData ι, 0 < secondExpansionScale p X r y := by
    intro y
    exact div_pos hX (mul_pos
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _))
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)))
  have hw : ∀ y ∈ s.image (expansionSupportData C D),
      ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
        (secondExpansionScale p X r y : ℂ)⁻¹‖ *
      ‖outerWindow windows (secondSectorZ p (secondExpansionScale p X r y) X₀ y)
        (secondSectorUd p D₀ y) (secondSectorUe p E₀ y) (secondSectorUv p V₀ y)
        (secondSectorKap p K₀ y)‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw := by
    intro y hy
    exact mul_le_mul (secondNormalizedPushWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z
      X Y hX hY.le s hsector (fun x hx => hΨ _) (fun x hx => hΨ _) y hy)
      (hW _ _ _ _ _) (norm_nonneg _) (by positivity)
  exact hbound B v₁ v₂ ε₁ ε₂ (s.image (expansionSupportData C D)) T
    (secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
    (Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw) lengthScale F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m r (secondExpansionScale p X r)
    hv (liftP _ (fun x hx => hCB)) (liftP _ (fun x hx => hD))
    (fun y hy => hxscale y) (liftP _ hrow) (liftP _ hz) (liftP _ hud)
    (liftP _ hue) (liftP _ huv) (liftP _ hkap) (by positivity) hL
    (liftP _ hmap) hT hnorm hw

end

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply halfNormalization_twist
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean densityChildEnergy child_coefficient_density_bound)

theorem normalized_twisted_second_sector_density_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∀ θ₁ θ₂ : ℝ,
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₁ θ₁) (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₂ θ₂) (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2) /
          (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder) *
        densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
          (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
          (windows 5) (windows 6) X₀ X₀ J := by
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_twisted_second_sector_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g₁ g₂ W hU₁ hU₂ A H hA hH hg₁ hg₂ ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY θ₁ θ₂
  obtain ⟨b,hb⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨hpoint,hbound⟩ := hb θ₁ θ₂
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL
    hz hud hue huv hkap hmap hT hnorm
  have hh := hbound B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL
    hz hud hue huv hkap hmap hT hnorm
  let scale := (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hd := child_coefficient_density_bound p hp hcop hg F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z)
    (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
    (windows 5) (windows 6) X₀ X₀
    (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b J scale
    (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)) hpoint
  have hi := (le_div_iff₀' hscale).2 hd
  apply hh.trans
  calc
    _ ≤ (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        ((Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2) *
          densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
            (windows 5) (windows 6) X₀ X₀ J) / scale) := by
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [scale]; ring

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (tripleCoefficient frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (childGeometricMean densityChildEnergy)

theorem secondInputCoefficient_frequencyTwist_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (Ψ : O →* ℂ) (m c d : O)
    (g : 𝓢(ℝ, ℂ)) (θ X : ℝ) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) G‖ =
    ‖secondInputCoefficient p hg Ψ m c d
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖ := by
  simp only [secondInputCoefficient, normalizedColumn, frequencyTwist_apply, norm_mul, norm_div,
    FourierBridge.logPhase_norm, one_mul]

theorem normalized_truncated_second_density_transfer
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (D₀ E₀ V₀ X₀ K₀ : Finset ι → κ → ℝ) (Y : ℝ),
        (∀ R j, 0 < D₀ R j) → (∀ R j, 0 < E₀ R j) → (∀ R j, 0 < V₀ R j) →
        (∀ R j, 0 < X₀ R j) → (∀ R j, 0 < K₀ R j) → 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X : ℝ) (K : Finset ι → Finset ι → Finset O)
        (label : Finset ι → SecondExpansionData ι → κ)
        (T : Finset ι → κ → Finset (Ideal O × O)) (lengthScale : Finset ι → κ → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ j, 0 ≤ lengthScale R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorZ p
            (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (expansionSupportData C D x)) (X₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUd p (D₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUe p (E₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUv p (V₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorKap p (K₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
            secondSupportRow p (expansionSupportData C D x)) ∈ T R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, t.1 ≠ ⊥) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale R j) →
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖ ^ 2) +
          ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
            (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
                X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (lengthScale R j * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*K₀ R j/(D₀ R j*(E₀ R j)^2*(V₀ R j)^2*(X₀ R j)^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) (T R j)
              (windows 5) (windows 6) (X₀ R j) (X₀ R j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU A H hA hH hgA hgA ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY θ
    B C D F v₁ v₂ ε₁ ε₂ Ψ m X K label T lengthScale hv hCB hD hΨ hX hzero hL
    hz hud hue huv hkap hmap hT hnorm
  dsimp only
  apply (truncatedSecondSource_norm_le_zero_add_dyadic p hp hcop hg hinj hc hpr F Ψ m
    _ _ _ W Y K label).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz'
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    exact hbound (D₀ R j) (E₀ R j) (V₀ R j) (X₀ R j) (K₀ R j) Y
      (hD₀ R j) (hE₀ R j) (hV₀ R j) (hX₀ R j) (hK₀ R j) hY θ θ
      B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondDyadicSector F K R label j) (T R j) X (lengthScale R j)
      (secondDyadicSector_subset F K R label j) hv hCB hD hΨ hX (hL R hR j)
      (hz R hR j) (hud R hR j) (hue R hR j) (huv R hR j) (hkap R hR j)
      (hmap R hR j) (hT R hR j) (hnorm R hR j)

end

open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem firstCoreBaseProfile_frequencyTwist (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (θ : ℝ) :
    firstCoreBaseProfile (frequencyTwist g θ) V negative =
      frequencyTwist (firstCoreBaseProfile g V negative) θ := by
  ext s
  simp only [firstCoreBaseProfile_apply, frequencyTwist_apply]
  ring

theorem firstCoreModeProfile_frequencyTwist (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (θ t : ℝ) :
    firstCoreModeProfile (frequencyTwist g θ) V negative t =
      frequencyTwist (firstCoreBaseProfile g V negative) (θ + firstCoreModeHeight negative t) := by
  rw [firstCoreModeProfile, firstCoreBaseProfile_frequencyTwist,
    JointLogSeparation.frequencyTwist_twice]

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

def HasSieveExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M * N) ^ ε * (M + N ^ α)

theorem hasSieveExponent_two : HasSieveExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN
  have hc : (⌈N⌉₊ : ℝ) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N by linarith)
    linarith
  have hc2 : (⌈N⌉₊ : ℝ) ^ 2 ≤ 4 * N ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌈N⌉₊]
  have hmn : 1 ≤ M * N := by nlinarith [mul_le_mul hM hN (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ M by linarith)]
  have he : 1 ≤ (M * N) ^ ε := Real.one_le_rpow hmn hε.le
  rw [Real.rpow_two]
  calc
    _ ≤ C * (M + (⌈N⌉₊ : ℝ) ^ 2) := sieveNorm_initial M N hM hN
    _ ≤ 4 * C * (M + N ^ 2) := by nlinarith
    _ ≤ (4 * C) * (M * N) ^ ε * (M + N ^ 2) := by
      nlinarith [show 0 ≤ (4 * C) * (M + N ^ 2) by positivity]

theorem HasSieveExponent.reverse {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C * (M * N) ^ ε * (N + M ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨262144 * C, by positivity, ?_⟩
  intro M N hM hN
  calc
    _ ≤ 262144 * sieveNorm N M := sieveNorm_reverse_le M N
    _ ≤ 262144 * (C * (N * M) ^ ε * (N + M ^ α)) :=
      mul_le_mul_of_nonneg_left (hb N M hN hM) (by norm_num)
    _ = _ := by rw [mul_comm N M]; ring

theorem sqrt_divisor_sieve_pair_le (M N D₁ D₂ Q C : ℝ)
    (hN : 0 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (h₁ : sieveNorm M (N / D₁) ≤ C * (N / D₁ + Q))
    (h₂ : sieveNorm M (N / D₂) ≤ C * (N / D₂ + Q)) :
    Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
      C * (N + Q * (D₁ * D₂)) := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD₁le : D₁ ≤ D₁ * D₂ := by nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ D₁ * D₂ * (C * (N / D₁ + Q)) * (C * (N / D₂ + Q)) := by
      gcongr
      exact sieveNorm_nonneg _ _
    _ = C ^ 2 * ((N + Q * D₁) * (N + Q * D₂)) := by field_simp
    _ ≤ C ^ 2 * ((N + Q * (D₁ * D₂)) * (N + Q * (D₁ * D₂))) := by gcongr
    _ = _ := by ring

theorem HasSieveExponent.divisor_pair {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N D₁ D₂ : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
      Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
        C * (M * N) ^ ε * (N + M ^ α * (D₁ * D₂)) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.reverse ε hε
  refine ⟨C, hC, ?_⟩
  intro M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N
  have hbound (D : ℝ) (hD : 1 ≤ D) (hDN : D ≤ N) :
      sieveNorm M (N / D) ≤ (C * (M * N) ^ ε) * (N / D + M ^ α) := by
    have hD0 : 0 < D := by linarith
    have hND : 1 ≤ N / D := (le_div_iff₀ hD0).mpr (by simpa using hDN)
    apply (hb M (N / D) hM hND).trans
    have hprod : M * (N / D) ≤ M * N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_self (by linarith) hD
    gcongr
  exact sqrt_divisor_sieve_pair_le M N D₁ D₂ (M ^ α) (C * (M * N) ^ ε)
    (by linarith) hD₁ hD₂ (Real.rpow_nonneg (by linarith) _) (by positivity)
    (hbound D₁ hD₁ hD₁N) (hbound D₂ hD₂ hD₂N)

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

def divisorEnergyFactor (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2 *
    Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ k, ‖b k‖ ^ 2)

theorem divisorEnergyFactor_nonneg (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) :
    0 ≤ divisorEnergyFactor ε hε N a b := by
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  positivity

theorem divisorBlockCost_sqrt (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) =
      divisorEnergyFactor ε hε N a b *
        Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) := by
  have hA := sieveNorm_nonneg M (N / D₁)
  have hB := sieveNorm_nonneg M (N / D₂)
  have hp : 0 ≤ D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) := by positivity
  have ha : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := by
    unfold divisorBlockCost
    positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (divisorEnergyFactor_nonneg ε hε N a b) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hc]
  simp only [divisorEnergyFactor, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp]
  unfold divisorBlockCost
  ring

theorem HasSieveExponent.divisor_cost {α : ℝ} (h : HasSieveExponent α) :
    ∀ deltaLoss : ℝ, 0 < deltaLoss → ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (M N D₁ D₂ : ℝ),
        1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
        ∀ (a : n → ℂ) (b : p → ℂ),
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) ≤
          divisorEnergyFactor ε hε N a b * (C * (M * N) ^ deltaLoss * (N + M ^ α * (D₁ * D₂))) := by
  intro deltaLoss hδ
  obtain ⟨C, hC, hc⟩ := h.divisor_pair deltaLoss hδ
  refine ⟨C, hC, ?_⟩
  intro ε hε M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N a b
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ M N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left (hc M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0147

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
Source SHA256: 828764d399499da3f836a248fae75ca97b686cd5c18db7a34077c5f1f13eb7b8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0148



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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary QuadraticMainOperatorBound IdealCoprimeSieveOperator

theorem normalizedPair_boundary_term
    (I J H D E : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hH : Supported H) (K : ℝ) (a b : ℂ) :
    (star a * b) * ((UniqueFactorizationMonoid.moebius E : ℂ) *
      normalizedIdealPair I J (H * D * E) * (cutoffDifference K H D : ℂ)) =
    (UniqueFactorizationMonoid.moebius E : ℂ) * mainWeight K H D E *
      (star (quadraticRow I (primaryGenerator H) *
        (a * quadraticRow I (idealGenerator D * idealGenerator E))) *
       (quadraticRow J (primaryGenerator H) *
        (b * quadraticRow J (idealGenerator D * idealGenerator E)))) := by
  have hspan : Ideal.span {idealGenerator D * idealGenerator E} = D * E := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_idealGenerator, span_idealGenerator]
  have hde := unrestrictedPairCharacter_span I J hI hJ hray (idealGenerator D * idealGenerator E)
  rw [hspan] at hde
  have hp : unrestrictedPairCharacter I J (H * D * E) =
      (quadraticRow I (primaryGenerator H) * quadraticRow J (primaryGenerator H)) *
      (quadraticRow I (idealGenerator D * idealGenerator E) *
        quadraticRow J (idealGenerator D * idealGenerator E)) := by
    rw [mul_assoc, unrestrictedPairCharacter_mul I J hI hJ hray,
      unrestrictedPairCharacter_eq_primary I J hI hJ hray H hH, hde]
  rw [normalizedIdealPair, hp]
  simp only [mainWeight, div_eq_mul_inv, star_mul,
    canonical_quadraticRow_star I hI]
  ring

def actualPrincipalDifference {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k *
      (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
       normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G)
    else 0

theorem actualPrincipalDifference_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (N : ℝ) (hN : 0 ≤ N) (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (cols j) = columnRay (cols k)) (a : n → ℂ)
    (G : Ideal O) (hG : Squarefree G) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G)
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ‖actualPrincipalDifference cols a G K‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) := by
  let S := coprimeSquarefreeRange G K
  have hS : S ⊆ idealRange K := coprimeSquarefreeRange_subset_idealRange G hbad K
  let A : Matrix S n ℂ := fun H j => quadraticRow (cols j) (primaryGenerator H.val)
  let r : Ideal O → Ideal O → n → ℂ := fun D E j =>
    quadraticRow (cols j) (idealGenerator D * idealGenerator E)
  have hpoint (j k : n) :
      (if IsCoprime (cols j) (cols k) then star (a j) * a k *
        (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
         normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G) else 0) =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, ∑ H : S,
        (UniqueFactorizationMonoid.moebius E : ℂ) * mainWeight K H.val D E *
          (if IsCoprime (cols j) (cols k) then
            star (A H j * (a j * r D E j)) * (A H k * (a k * r D E k)) else 0) := by
    dsimp only [A, r]
    by_cases hc : IsCoprime (cols j) (cols k)
    · rw [ite_eq_left hc, normalizedPair_main_difference (cols j) (cols k) (hcols j).1 (hcols k).1 (hray j k) G hG K]
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (coprimeSquarefreeRange G K))) (t := idealDivisors G)]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro H _
      rw [ite_eq_left hc]
      exact normalizedPair_boundary_term (cols j) (cols k) H.val D E (hcols j).1 (hcols k).1
        (hray j k) (admissible_supported (mem_idealRange.mp (hS H.property)).1) K (a j) (a k)
    · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]
  have heq : actualPrincipalDifference cols a G K =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (∑ H : S, mainWeight K H.val D E *
            (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
              star (A H j * (a j * r D E j)) * (A H k * (a k * r D E k)) else 0)) := by
    dsimp only [A, r]
    unfold actualPrincipalDifference
    simp_rw [hpoint]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset S))]
    simp only [Finset.mul_sum, mul_assoc, A, r]
  rw [heq]
  have hb := main_difference_operator_bound ε hε K hK G hG.ne_zero (fun H : S => H.val)
    cols (fun j => (hcols j).1.1) N hN (fun j => (hcols j).2) A a r
    (fun D E j => quadraticRow_norm_le_one (cols j) _)
  have hA : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤ sieveNorm K N :=
    family_squared_norm_le (fun H : S => H.val) cols Subtype.val_injective hinj K N
      (fun H => mem_idealRange.mp (hS H.property)) hcols
  apply hb.trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleRatio (B b D₁ d D₂ e : ℝ) : ℝ := Real.sqrt (B / b) * (D₁ / d) * (D₂ / e)

theorem middleRatio_bounds (B b D₁ d D₂ e : ℝ)
    (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    1 / 4 ≤ middleRatio B b D₁ d D₂ e ∧ middleRatio B b D₁ d D₂ e ≤ 2 := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hu1 : 1 ≤ Real.sqrt (B / b) := by
    have hq : 1 ≤ B / b := (le_div_iff₀ hb0).mpr (by simpa using hb.2)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hu2 : Real.sqrt (B / b) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hv : (1 / 2 : ℝ) ≤ D₁ / d ∧ D₁ / d ≤ 1 :=
    ⟨(le_div_iff₀ hd0).mpr (by linarith), (div_le_one hd0).mpr hd.1⟩
  have hw : (1 / 2 : ℝ) ≤ D₂ / e ∧ D₂ / e ≤ 1 :=
    ⟨(le_div_iff₀ he0).mpr (by linarith), (div_le_one he0).mpr he.1⟩
  have hv0 : 0 ≤ D₁ / d := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hv.1
  have hw0 : 0 ≤ D₂ / e := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hw.1
  have hvw1 : (1 / 4 : ℝ) ≤ (D₁ / d) * (D₂ / e) := by
    nlinarith [mul_le_mul hv.1 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0]
  have hvw2 : (D₁ / d) * (D₂ / e) ≤ 1 := by
    nlinarith [mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 1)]
  unfold middleRatio
  constructor
  · nlinarith [mul_le_mul hu1 hvw1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.sqrt_nonneg (B / b))]
  · nlinarith [mul_le_mul hu2 hvw2 (mul_nonneg hv0 hw0) (by norm_num : (0 : ℝ) ≤ 2)]

theorem middleRatio_log_bound (r : ℝ) (hr : (1 / 4 : ℝ) ≤ r ∧ r ≤ 2) : |Real.log r| ≤ 4 := by
  have hr0 : 0 < r := by linarith
  have hi : r⁻¹ ≤ 4 := by
    have h : (1 : ℝ) / r ≤ 4 := (div_le_iff₀ hr0).mpr (by linarith)
    simpa only [one_div] using h
  have h₁ := Real.log_le_sub_one_of_pos hr0
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem middleRatio_argument (M B b D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (Real.sqrt (M / B) * q / (D₁ * D₂)) * Real.exp (Real.log (middleRatio B b D₁ d D₂ e)) =
      Real.sqrt (M / b) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_log hr]
  have hs : Real.sqrt (M / B) * Real.sqrt (B / b) = Real.sqrt (M / b) := by
    rw [← Real.sqrt_mul (div_nonneg hM.le hB.le)]
    congr 1
    field_simp
  unfold middleRatio
  calc
    _ = (Real.sqrt (M / B) * Real.sqrt (B / b)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [hs]

theorem actual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N) (_hM : 0 < M)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k *
              paperRadialFourier W
                (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 0 0 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  let R := Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (Real.sqrt_pos.mpr (div_pos hM hB0))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b x (fun _ => 0) (fun _ => 0) hx
    (fun _ => by simp) (fun _ => by simp)
  have harg (D : S) (E : T) (i : m) : R * Real.exp (x D E i + (0 + 0)) =
      Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) := by
    simp only [add_zero]
    exact middleRatio_argument _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp

theorem firstCoreInputRow_smoothed_mode
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ)) =
      ((primeProductNorm p D)⁻¹ : ℝ) *
      ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
        (‖inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
            (columnLog p (X / primeProductNorm p D) A))) z‖ ^ 2 : ℝ) := by
  let P := inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)))
  have he (z : O) : W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ) =
      (((primeProductNorm p D)⁻¹ : ℝ) : ℂ) *
        (W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P (if negative then -z else z)‖ ^ 2 : ℝ)) := by
    rw [firstCoreInputRow_mode_norm_sq p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V X hX c d r t z]
    push_cast
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  have hsign : (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖P (if negative then -z else z)‖ ^ 2 : ℝ)) =
      ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ) := by
    cases negative
    · rfl
    · simpa only [Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
        (Equiv.neg O).tsum_eq (fun z : O => W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ))
  rw [hsign]

theorem firstCoreInputRow_smoothed_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (hY : 0 < Y) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (K : Finset ι → Finset ι → Finset O) :
    let Hmode := normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A))
    let Ψmode := firstCoreTwist negative χ Ψ r
    let m' := m * b0Label p B v ε₁ ε₂
    let c' := c * jLabel p B v ε₁ ε₂
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ)) =
      ((primeProductNorm p D)⁻¹ : ℝ) *
        (truncatedSecondSource p hp hg hinj (F\D) Ψmode m' c' d Hmode W Y K +
          secondSourceTail p hp hg hinj (F\D) Ψmode m' c' d Hmode W Y K) := by
  dsimp only
  rw [firstCoreInputRow_smoothed_mode p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V W X hX Y c d r t,
    inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc]
  exact hY

theorem firstCoreInputRow_finite_le_truncated_tail
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (hY : 0 < Y) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) (K : Finset ι → Finset ι → Finset O) :
    let Hmode := normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A))
    let Ψmode := firstCoreTwist negative χ Ψ r
    let m' := m * b0Label p B v ε₁ ε₂
    let c' := c * jLabel p B v ε₁ ε₂
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2) +
      ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X)
        negative t D ∅‖ ^ 2 ≤
      (primeProductNorm p D)⁻¹ *
        (‖truncatedSecondSource p hp hg hinj (F\D) Ψmode m' c' d Hmode rowMajorant Y K‖ +
          ‖secondSourceTail p hp hg hinj (F\D) Ψmode m' c' d Hmode rowMajorant Y K‖) := by
  dsimp only
  have h := firstCoreInputRow_finite_le_corrected_source p hg F D B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t T Y hY hT hT0
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    g V rowMajorant X hX Y hY c d r t K
  rw [he] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re] at h
  apply (le_sub_iff_add_le.mp h).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp D).le

end SecondPassArithmetic

namespace SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma childEnergy_eq_difference (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X a b : ℝ)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b =
      childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative (a-b) 0 := by
  have he : fixedSecondTest p V X a b testNegative =
      fixedSecondTest p V X (a-b) 0 testNegative := by
    funext N
    simp only [fixedSecondTest, sub_zero]
  simp only [childEnergy, he]

theorem densityChildEnergy_polynomial_bound (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ a : ℝ, childEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false a 0 ≤
      B₁ * (1+‖a‖)^(2*J))
    (h₂ : ∀ a : ℝ, childEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true a 0 ≤
      B₂ * (1+‖a‖)^(2*J)) :
    densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (2*J) ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hsqrt (B a e : ℝ) (hB : 0 ≤ B) (he : e ≤ B*(1+‖a‖)^(2*J)) :
      Real.sqrt e ≤ Real.sqrt B * (1+‖a‖)^J := by
    calc
      _ ≤ Real.sqrt (B*(1+‖a‖)^(2*J)) := Real.sqrt_le_sqrt he
      _ = _ := by
        rw [Real.sqrt_mul hB, mul_comm 2 J, pow_mul, Real.sqrt_sq (by positivity)]
  have hbound (q : Frequency) : G q ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (1+‖q.1‖)^(2*J)*(1+‖q.2.1‖)^(2*J)*(1+‖q.2.2‖)^(2*J) := by
    have hleft := h₁ (q.1-q.2.2)
    have hright := h₂ (q.2.1-q.2.2)
    rw [← childEnergy_eq_difference p hp hcop hg F Ψ₁ m T V₁ X₁ q.1 q.2.2 true false] at hleft
    rw [← childEnergy_eq_difference p hp hcop hg F Ψ₂ m T V₂ X₂ q.2.1 q.2.2 false true] at hright
    calc
      _ ≤ (Real.sqrt B₁ * (1+‖q.1-q.2.2‖)^J) *
          (Real.sqrt B₂ * (1+‖q.2.1-q.2.2‖)^J) :=
        mul_le_mul (hsqrt B₁ _ _ hB₁ hleft) (hsqrt B₂ _ _ hB₂ hright)
          (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt B₁ * Real.sqrt B₂) *
          ((1+‖q.1-q.2.2‖)^J * (1+‖q.2.1-q.2.2‖)^J) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (difference_height_weight_le q.1 q.2.1 q.2.2 J)
          (mul_nonneg (Real.sqrt_nonneg B₁) (Real.sqrt_nonneg B₂))
        simpa only [mul_assoc] using hh
  exact triple_density_polynomial_bound G hG hG0 M hM (2*J)
    (Real.sqrt B₁ * Real.sqrt B₂) hbound

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def residualPairWeight (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
    (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T)

theorem residualSecondMode_tail_eq (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset O) :
    (∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y) =
    ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
      residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        ∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : {k : O // k ∉ K} =>
      if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd]
      exact ((secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).subtype _).mul_left _
    · simp only [ite_eq_right hd]
      exact summable_zero
  change (∑' k : {k : O // k ∉ K}, ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
    if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
      secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) = _
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Summable.tsum_finsetSum (fun T _ => hs S T)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, tsum_mul_left]
  · simp [hd]

def residualTailCost (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (Y H : ℝ) (A : ℕ) (P : ℝ) : ℝ :=
  ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
    let n := ∏ i : activeSupport T S, p i.val
    let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
    ‖residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T‖ *
      ((Y/‖eisEmbedding n‖) * (P / ((min 1 scale)^2 * (1+H)^A)))
    else 0

theorem residualSecondMode_tail_bound
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem secondSourceTail_bound
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := residualSecondMode_tail_bound p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_eq_ideal_norm (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    FiniteGaussPhase.span_finset_prod]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_ge_one (S : Finset ι) : 1 ≤ primeProductNorm p S :=
  by
    rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {∏ i ∈ S, p i}) ≠ 0 by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_mono {S T : Finset ι} (hST : S ⊆ T) :
    primeProductNorm p S ≤ primeProductNorm p T := by
  have hd : Disjoint S (T\S) := Finset.disjoint_sdiff
  have hu : S ∪ (T\S) = T := Finset.union_sdiff_of_subset hST
  rw [← hu, FirstPassCubeLabels.primeProductNorm_union p S (T\S) hd]
  exact le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
    (primeProductNorm_ge_one p hp _)

def boundedPrimeSupports (F : Finset ι) (X : ℝ) : Finset (Finset ι) :=
  F.powerset.filter (fun S => primeProductNorm p S ≤ X)

include hinj in
theorem boundedPrimeSupports_card (F : Finset ι) (X : ℝ) (hX : 1 ≤ X) :
    ((boundedPrimeSupports p F X).card : ℝ) ≤ 128*X := by
  let q : Finset ι → Ideal O := fun S => ∏ i ∈ S, Ideal.span {p i}
  have hq : Function.Injective q := FirstCauchyArithmetic.family_product_injective _ hinj
  let I := (boundedPrimeSupports p F X).image q
  have hcard : I.card = (boundedPrimeSupports p F X).card := Finset.card_image_of_injective _ hq
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real I X hX
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    rw [← primeProductNorm_eq_ideal_norm p S]
    exact (Finset.mem_filter.mp hS).2

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_subset_norm_bound (g : 𝓢(ℝ, ℂ)) (A X : ℝ)
    (hX : 0 < X) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A) (G S U : Finset ι)
    (hU : U ⊆ G∪S)
    (hn : FirstPassCubeLabels.normalizedColumn p
      (fun R => g (FirstPassCubeLabels.columnLog p X R)) (G∪S) ≠ 0) :
    primeProductNorm p U ≤ X*Real.exp A := by
  have hval : g (FirstPassCubeLabels.columnLog p X (G∪S)) ≠ 0 := by
    intro h
    apply hn
    simp only [FirstPassCubeLabels.normalizedColumn,h,zero_div]
  exact (primeProductNorm_mono p hp hU).trans
    (columnLog_norm_upper p hp X A hX (G∪S) ((le_abs_self _).trans (hgA _ hval)))

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0148

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.SpatialDerivatives
Source SHA256: f5a86610579017593edc584076d431f4e47ea76c558bee132412d6746682a5b6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0149


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
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem column_sqrt_ratio_bounds (N n : ℝ) (hN : 0 < N) (hn : N / 2 ≤ n ∧ n ≤ N) :
    1 / 4 ≤ Real.sqrt (n / N) ∧ Real.sqrt (n / N) ≤ 2 := by
  have hq0 : 0 ≤ n / N := div_nonneg (by linarith) hN.le
  have hq1 : (1 / 2 : ℝ) ≤ n / N := (le_div_iff₀ hN).mpr (by linarith)
  have hq2 : n / N ≤ 1 := (div_le_one hN).mpr hn.2
  have hs := Real.sq_sqrt hq0
  have hp := Real.sqrt_nonneg (n / N)
  constructor <;> nlinarith

theorem dual_middle_sqrt_identity (M B b N i j F : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : 0 < b) (hN : 0 < N)
    (hi : 0 < i) (hj : 0 < j) (hF : 0 < F) :
    N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N) =
      Real.sqrt (F * i * j / (M * b)) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity),
    Real.sq_sqrt (show 0 ≤ B / b by positivity), Real.sq_sqrt (show 0 ≤ i / N by positivity),
    Real.sq_sqrt (show 0 ≤ j / N by positivity), Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity)]
  field_simp

theorem dual_middle_argument (M B b N i j F D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) (hF : 0 < F)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (N * Real.sqrt (F / (M * B)) * q / (D₁ * D₂)) *
      Real.exp (Real.log (middleRatio B b D₁ d D₂ e) +
        (Real.log (Real.sqrt (i / N)) + Real.log (Real.sqrt (j / N)))) =
      Real.sqrt (F * i * j / (M * b)) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_add, Real.exp_add, Real.exp_log hr,
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hi0 hN)),
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hj0 hN))]
  unfold middleRatio
  calc
    _ = (N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [dual_middle_sqrt_identity M B b N i j F hM hB hb0 hN hi0 hj0 hF]

theorem actual_dual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M F : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N)
        (_hM : 0 < M) (_hF : 0 < F)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
              (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
                (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 4 4 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 < N := by linarith
  let R := N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (mul_pos hN0 (Real.sqrt_pos.mpr (by positivity)))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  let y : n → ℝ := fun j => Real.log (Real.sqrt ((Ideal.absNorm (left j) : ℝ) / N))
  let z : p → ℝ := fun k => Real.log (Real.sqrt ((Ideal.absNorm (right k) : ℝ) / N))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have hy (j : n) : |y j| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hleft j).2)
  have hz (k : p) : |z k| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hright k).2)
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) (fun j => ⟨(hleft j).1, (hleft j).2.2⟩)
    (fun k => ⟨(hright k).1, (hright k).2.2⟩) a b x y z hx hy hz
  have harg (D : S) (E : T) (i : m) (j : n) (k : p) : R * Real.exp (x D E i + (y j + z k)) =
      Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) :=
    dual_middle_argument _ _ _ _ _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hN0 (hleft j).2 (hright k).2 hF
      hD₁0 (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

theorem principal_middle_prefactor_bound (M B b D₁ d D₂ e : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d) (hD₂ : 0 < D₂) (he : D₂ ≤ e) :
    Real.sqrt (M / b) / (d * e) ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd
  have he0 : 0 < e := hD₂.trans_le he
  have hq : M / b ≤ 4 * (M / B) := by
    calc
      _ ≤ (4 * M) / B := (div_le_div_iff₀ hb0 hB).mpr (by nlinarith [mul_nonneg hM.le (show 0 ≤ 4 * b - B by linarith)])
      _ = _ := by ring
  have hs : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
    have hh := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hs4] at hh
    exact hh
  calc
    _ ≤ (2 * Real.sqrt (M / B)) / (d * e) := div_le_div_of_nonneg_right hs (mul_pos hd0 he0).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hD₁ hD₂)
      (mul_le_mul hd he hD₂.le hd0.le)

theorem principal_middle_prefactor_sum {m : Type*} [Fintype m]
    (S T : Finset (Ideal O)) (rows : m → Ideal O) (f : S → T → m → ℝ)
    (hf : ∀ D E i, 0 ≤ f D E i) (M B D₁ D₂ : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i) : ℝ))
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ)) (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ)) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) * f D E i) ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) * ∑ D : S, ∑ E : T, ∑ i, f D E i := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hf D E i)
  exact principal_middle_prefactor_bound M B _ D₁ _ D₂ _ hM hB (hrows i) hD₁
    (hS D.val D.property) hD₂ (hT E.val E.property)

def originalMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose

def dualMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose

theorem dual_principal_prefactor_identity (M F b i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    (M / (Real.sqrt (i * j) * F)) * Real.sqrt (F * i * j / (M * b)) =
      Real.sqrt ((M / F) / b) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ i * j by positivity),
    Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity),
    Real.sq_sqrt (show 0 ≤ (M / F) / b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a : n → ℂ) (b : p → ℂ) (h : O) (hh : h ≠ 0)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hh

theorem actual_original_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt (M / B) / (D₁ * D₂)) * originalMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M
    hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ originalMiddleConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T rows _ (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).2.1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) by positivity)

theorem actual_dual_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt ((M / F) / B) / (D₁ * D₂)) * dualMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M F
    hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ dualMiddleConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T rows _ (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF)
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).2.1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) by positivity)

end CanonicalQuadraticSieve

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma abs_le_inv_of_mul_sq_le_one {v t : ℝ} (hv : 0<v) (h : v^2*t^2≤1) :
    |t|≤1/v := by
  apply (le_div_iff₀ hv).mpr
  have he : |v*t|≤1 := (sq_le_one_iff_abs_le_one _).mp (by simpa only [mul_pow] using h)
  simpa only [abs_mul,abs_of_pos hv,mul_comm] using he

lemma heightLog_first_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    |heightLogDx A B C D x y v|≤1/v ∧
    |heightLogDy A B C D x y v|≤1/v ∧
    |heightLogDv A B C D x y v|≤1/v := by
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  exact ⟨abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith)⟩

lemma heightLog_second_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hA : 0≤A) (hq : 0<quadraticHeightDenominator A B C D x y v)
    (hAv : A*v^2≤quadraticHeightDenominator A B C D x y v) :
    |heightLogDxx A B C D x y v|≤7/v^2 ∧
    |heightLogDyy A B C D x y v|≤7/v^2 ∧
    |heightLogDvv A B C D x y v|≤7/v^2 := by
  let q := quadraticHeightDenominator A B C D x y v
  let r := v^2*A/q
  have hr0 : 0≤r := div_nonneg (mul_nonneg (sq_nonneg v) hA) hq.le
  have hr1 : r≤1 := (div_le_one hq).mpr (by simpa only [mul_comm] using hAv)
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq.ne'
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  have hx1 : v^2*(heightLogDx A B C D x y v)^2≤1 := by nlinarith
  have hy1 : v^2*(heightLogDy A B C D x y v)^2≤1 := by nlinarith
  have hxx : v^2*heightLogDxx A B C D x y v =
      v^2*(heightLogDx A B C D x y v)^2-2*r := by
    dsimp [heightLogDxx,heightLogDx,r,q]
    field_simp
    ; ring
  have hyy : v^2*heightLogDyy A B C D x y v =
      v^2*(heightLogDy A B C D x y v)^2-2*r := by
    dsimp [heightLogDyy,heightLogDy,r,q]
    field_simp
    ; ring
  have hvv : v^2*heightLogDvv A B C D x y v = -1-2*r+4*r^2 := by
    dsimp [heightLogDvv,r,q]
    field_simp [hv.ne',hq.ne']
    ; ring
  have hconv (a : ℝ) (ha : |v^2*a|≤7) : |a|≤7/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg v),mul_comm] using ha
  refine ⟨hconv _ (abs_le.mpr ⟨?_,?_⟩), hconv _ (abs_le.mpr ⟨?_,?_⟩),
    hconv _ (abs_le.mpr ⟨?_,?_⟩)⟩
  all_goals nlinarith [sq_nonneg r,mul_nonneg hr0 (sub_nonneg.mpr hr1)]

lemma actual_quadraticHeight_nonneg (u : Fin 2 → ℂ) (x y v : ℝ) :
    Complex.normSq (u 0)*v^2 ≤
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [← heightDenominator_eq_quadratic]
  unfold heightDenominator
  rw [Complex.normSq_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

open Filter
open scoped BigOperators Classical Topology Matrix

abbrev SpatialCoordinates := Fin 3 → ℝ

def axisSlice (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ → ℂ :=
  fun t => f (Function.update p j t)

def spatialLogD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDx A B C D (p 0) (p 1) (p 2),
    heightLogDy A B C D (p 0) (p 1) (p 2),
    heightLogDv A B C D (p 0) (p 1) (p 2)]
def spatialLogDD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDxx A B C D (p 0) (p 1) (p 2),
    heightLogDyy A B C D (p 0) (p 1) (p 2),
    heightLogDvv A B C D (p 0) (p 1) (p 2)]

lemma spatial_axis_hasDerivAt (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j)
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*s*(spatialLogD A B C D p j:ℂ)) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 0) (p 2))
      (quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDx] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 1) (p 2))
      (quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDy] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_id (p 2))
      (quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDv] using h

lemma spatial_axis_hasDerivAt_deriv (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (deriv (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j))
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*
        (s^2*(spatialLogD A B C D p j:ℂ)^2+s*(spatialLogDD A B C D p j:ℂ))) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDx,heightLogDxx] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDy,heightLogDyy] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDv,heightLogDvv,div_eq_mul_inv] using h

def rowSmoothPower (s : ℂ) (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℂ :=
  spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

def rowLogD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

def rowLogDD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogDD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

lemma row_denominator_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) :
    0 < quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
      (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2) := by
  rw [← heightDenominator_eq_quadratic]
  exact heightDenominator_pos _ _ hv u hu

lemma rowLogD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogD u p j| ≤ 1/(p 2) := by
  have h := heightLog_first_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (row_denominator_pos u hu p hv).ne'
  fin_cases j <;> simp only [rowLogD,spatialLogD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma rowLogDD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogDD u p j| ≤ 7/(p 2)^2 := by
  have h := heightLog_second_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (Complex.normSq_nonneg _)
    (row_denominator_pos u hu p hv) (actual_quadraticHeight_nonneg u (p 0) (p 1) (p 2))
  fin_cases j <;> simp only [rowLogDD,spatialLogDD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma row_axis_hasDerivAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (rowSmoothPower s u) p j)
      (rowSmoothPower s u p*s*(rowLogD u p j:ℂ)) (p j) :=
  spatial_axis_hasDerivAt _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

lemma row_axis_hasDerivAt_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (axisSlice (rowSmoothPower s u) p j))
      (rowSmoothPower s u p*(s^2*(rowLogD u p j:ℂ)^2+s*(rowLogDD u p j:ℂ))) (p j) :=
  spatial_axis_hasDerivAt_deriv _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma hasDerivAt_deriv_tsum_of_bounds {ι : Type*} (f : ι → ℝ → ℂ)
    (M₁ M₂ : ι → ℝ) (U : Set ℝ) (x : ℝ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hfirst : ∀i y, y∈U → DifferentiableAt ℝ (f i) y)
    (hsecond : ∀i y, y∈U → DifferentiableAt ℝ (deriv (f i)) y)
    (hbound₁ : ∀i y, y∈U → ‖deriv (f i) y‖≤M₁ i)
    (hbound₂ : ∀i y, y∈U → ‖deriv (deriv (f i)) y‖≤M₂ i)
    (hsum : Summable (fun i => f i x)) :
    HasDerivAt (deriv (fun y => ∑'i,f i y)) (∑'i,deriv (deriv (f i)) x) x := by
  have hfirstSum (y : ℝ) (hy : y∈U) :=
    hasDerivAt_tsum_of_isPreconnected hM₁ hU hUc
      (fun i z hz => (hfirst i z hz).hasDerivAt) hbound₁ hx hsum hy
  have hsumFirst : Summable (fun i => deriv (f i) x) :=
    Summable.of_norm_bounded hM₁ (fun i => hbound₁ i x hx)
  have hsecondSum := hasDerivAt_tsum_of_isPreconnected hM₂ hU hUc
    (fun i z hz => (hsecond i z hz).hasDerivAt) hbound₂ hx hsumFirst hx
  apply hsecondSum.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hfirstSum y hy).deriv

lemma norm_row_axis_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (rowSmoothPower s u) p j) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖ * (1/(p 2))) := by
  rw [(row_axis_hasDerivAt s u hu p hv j).deriv,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖rowSmoothPower s u p‖*‖s‖*(1/(p 2)) :=
      mul_le_mul_of_nonneg_left (rowLogD_bound u hu p hv j) (by positivity)
    _ = _ := by ring

lemma norm_row_axis_deriv2 (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (rowSmoothPower s u) p j)) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  rw [(row_axis_hasDerivAt_deriv s u hu p hv j).deriv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖s^2*(rowLogD u p j:ℂ)^2‖+‖s*(rowLogDD u p j:ℂ)‖ := norm_add_le _ _
    _ = ‖s‖^2*|rowLogD u p j|^2 + ‖s‖*|rowLogDD u p j| := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by
      have hfirst := rowLogD_bound u hu p hv j
      have hsecond := rowLogDD_bound u hu p hv j
      gcongr

def smoothSummand (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹ * rowSmoothPower s (embeddedRow r) p

lemma smoothSummand_eq_actual (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSummand s r p =
      summand (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv) s r := by
  rw [smoothSummand,← eigenfunction_summand_eq_actual_series]
  congr 1
  exact (actualHeightPower_eq_spatial s (embeddedRow r) (embeddedRow_ne_zero r)
    (p 0) (p 1) (p 2) hv).symm

lemma smooth_axis_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) (p j) :=
  ((row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma smooth_axis_deriv_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  change DifferentiableAt ℝ (deriv (fun t => (cosetCharacter r)⁻¹ *
    axisSlice (rowSmoothPower s (embeddedRow r)) p j t)) (p j)
  rw [deriv_const_mul_field']
  exact ((row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma norm_smooth_axis_deriv (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (smoothSummand s r) p j) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖ * (1/(p 2))) := by
  have h := norm_row_axis_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma norm_smooth_axis_deriv2 (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  have h := norm_row_axis_deriv2 s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field',deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma smoothSummand_axis_update (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (j : Fin 3) (t : ℝ) :
    axisSlice (smoothSummand s r) (Function.update p j t) j =
      axisSlice (smoothSummand s r) p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) : UpperCoordinates :=
  ⟨((p 0:ℂ)+(p 1:ℂ)*Complex.I,max deltaLoss (p 2)),lt_of_lt_of_le hδ (le_max_left _ _)⟩

lemma continuous_clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    Continuous (clampedCoordinates deltaLoss hδ) := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
    ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul_const Complex.I)).prodMk
      (continuous_const.max (continuous_apply 2))

lemma continuous_axis_update (p : SpatialCoordinates) (j : Fin 3) :
    Continuous (fun t : ℝ => Function.update p j t) := by
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => p k))

lemma smoothSummand_eq_clamped (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (hp : deltaLoss≤p 2) :
    smoothSummand s r p = summand (coordinateSection (clampedCoordinates deltaLoss hδ p)) s r := by
  have hv : 0<p 2 := lt_of_lt_of_le hδ hp
  simpa only [coordinateSection,clampedCoordinates,max_eq_right hp] using smoothSummand_eq_actual s r p hv

theorem axis_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀ t ∈ Metric.ball (p j) ε,
        0 < (Function.update p j t) 2 ∧ ∀ r : CuspCosets,
        ‖axisSlice (smoothSummand s r) p j t‖≤M₀ r ∧
        ‖deriv (axisSlice (smoothSummand s r) p j) t‖≤M₁ r ∧
        ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) t‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := fun t => clampedCoordinates deltaLoss hδ (Function.update p j t)
  have hpath : Continuous path := (continuous_clampedCoordinates deltaLoss hδ).comp (continuous_axis_update p j)
  let C := rowBound (coordinateSection (path (p j)))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path (p j)))]
  have hb : ∀ᶠ t in 𝓝 (p j), rowBound (coordinateSection (path t))<C :=
    (continuous_coordinate_rowBound.comp hpath).continuousAt.eventually_lt_const (by dsimp [C]; linarith)
  have hh : ∀ᶠ t in 𝓝 (p j), deltaLoss < (Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change deltaLoss < (Function.update p j (p j)) 2
    rw [Function.update_eq_self]
    dsimp [deltaLoss]
    linarith
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff_ball.mp (hh.and hb)
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨ε,hε,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro t ht
  obtain ⟨hht,hbt⟩ := hball t ht
  have hpos : 0 < (Function.update p j t) 2 := lt_trans hδ hht
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r (Function.update p j t)‖≤M r := by
    rw [smoothSummand_eq_clamped s r _ deltaLoss hδ hht.le]
    exact hbound (path t,s) hbt.le le_rfl le_rfl r
  have hfrac : 1 / (Function.update p j t) 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hht.le
  have hfrac₂ : 7 / ((Function.update p j t) 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith
  have hd₁ := norm_smooth_axis_deriv s r (Function.update p j t) hpos j
  have hd₂ := norm_smooth_axis_deriv2 s r (Function.update p j t) hpos j
  rw [smoothSummand_axis_update,Function.update_self] at hd₁ hd₂
  refine ⟨hm,hd₁.trans ?_,hd₂.trans ?_⟩
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

lemma smooth_axis_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t := by
  have h := smooth_axis_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

lemma smooth_axis_deriv_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t := by
  have h := smooth_axis_deriv_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

end CubicEisenstein

end

end OAI
end OAIOriginalModule0149

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
Source SHA256: 3ca1acd9402fc3df665d38d035b7b956ad9160474719991b6f95bf2b16e423bb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0150



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
open Filter
open scoped BigOperators Classical Topology Matrix

def smoothEisenstein (s : ℂ) (p : SpatialCoordinates) : ℂ := ∑'r, smoothSummand s r p

lemma smoothEisenstein_eq_actual (s : ℂ) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothEisenstein s p = upperEisenstein ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s := by
  unfold smoothEisenstein upperEisenstein eisenstein
  exact tsum_congr (fun r => smoothSummand_eq_actual s r p hv)

lemma summable_smoothSummand (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Summable (fun r => smoothSummand s r p) :=
  (summable_summand (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv) s hs).congr
    (fun r => (smoothSummand_eq_actual s r p hv).symm)

theorem eisenstein_axis_termwise (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) ∧
    Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) ∧
    HasDerivAt (axisSlice (smoothEisenstein s) p j)
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j)) (p j) ∧
    HasDerivAt (deriv (axisSlice (smoothEisenstein s) p j))
      (∑'r,deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) (p j) := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  have hx : p j ∈ Metric.ball (p j) ε := Metric.mem_ball_self hε
  have hs₀ : Summable (fun r => axisSlice (smoothSummand s r) p j (p j)) :=
    Summable.of_norm_bounded hM₀ (fun r => ((hbound (p j) hx).2 r).1)
  have hs₁ : Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) :=
    Summable.of_norm_bounded hM₁ (fun r => ((hbound (p j) hx).2 r).2.1)
  have hs₂ : Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) :=
    Summable.of_norm_bounded hM₂ (fun r => ((hbound (p j) hx).2 r).2.2)
  have hd₁ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t :=
    smooth_axis_differentiable_at s r p j t (hbound t ht).1
  have hd₂ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t :=
    smooth_axis_deriv_differentiable_at s r p j t (hbound t ht).1
  refine ⟨hs₁,hs₂,?_,?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected hM₁ Metric.isOpen_ball Metric.isPreconnected_ball
      (fun r t ht => (hd₁ r t ht).hasDerivAt) (fun r t ht => ((hbound t ht).2 r).2.1) hx hs₀ hx
  · exact hasDerivAt_deriv_tsum_of_bounds (fun r => axisSlice (smoothSummand s r) p j)
      M₁ M₂ _ (p j) Metric.isOpen_ball Metric.isPreconnected_ball hx hM₁ hM₂ hd₁ hd₂
      (fun r t ht => ((hbound t ht).2 r).2.1) (fun r t ht => ((hbound t ht).2 r).2.2) hs₀

def axisLaplacian (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  (p 2:ℂ)^2 * (∑ j : Fin 3, deriv (deriv (axisSlice f p j)) (p j)) -
    (p 2:ℂ)*deriv (axisSlice f p 2) (p 2)

lemma axisSlice_zero (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 0 = fun t => f t (p 1) (p 2) := by
  funext t
  simp [axisSlice,Function.update]
lemma axisSlice_one (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 1 = fun t => f (p 0) t (p 2) := by
  funext t
  simp [axisSlice,Function.update]
lemma axisSlice_two (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisSlice (fun q => f (q 0) (q 1) (q 2)) p 2 = fun t => f (p 0) (p 1) t := by
  funext t
  simp [axisSlice,Function.update]

lemma axisLaplacian_eq_hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => f (q 0) (q 1) (q 2)) p =
      hyperbolicLaplacian f (p 0) (p 1) (p 2) := by
  simp only [axisLaplacian,Fin.sum_univ_three,axisSlice_zero,axisSlice_one,axisSlice_two,
    hyperbolicLaplacian]

lemma smoothSummand_axisLaplacian (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothSummand s r) p = s*(s-2)*smoothSummand s r p := by
  unfold smoothSummand rowSmoothPower
  rw [axisLaplacian_eq_hyperbolicLaplacian
    (fun x y v => (cosetCharacter r)⁻¹ *
      spatialHeightPower s (Complex.normSq (embeddedRow r 0))
        ((embeddedRow r 0*star (embeddedRow r 1)).re)
        (-(embeddedRow r 0*star (embeddedRow r 1)).im)
        (Complex.normSq (embeddedRow r 1)) x y v) p,
    hyperbolicLaplacian_const_mul,spatialHeightPower_eigenfunction]
  · ring
  · exact complex_row_quadratic_relation _ _
  · exact hv.ne'
  · exact (row_denominator_pos _ (embeddedRow_ne_zero r) p hv).ne'

theorem smoothEisenstein_eigenfunction (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothEisenstein s) p = s*(s-2)*smoothEisenstein s p := by
  have hterms := eisenstein_axis_termwise s hs p hv
  let second := fun (j : Fin 3) (r : CuspCosets) =>
    deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)
  let first := fun r : CuspCosets => deriv (axisSlice (smoothSummand s r) p 2) (p 2)
  have hsecond (j : Fin 3) : Summable (second j) := (hterms j).2.1
  have hfirst : Summable first := (hterms 2).1
  have hsum : Summable (fun r => ∑ j : Fin 3, second j r) := by
    simpa only [Fin.sum_univ_three] using ((hsecond 0).add (hsecond 1)).add (hsecond 2)
  have hcomm : (∑ j : Fin 3, ∑'r,second j r) = ∑'r,∑ j : Fin 3,second j r := by
    exact (Summable.tsum_finsetSum (fun j _ => hsecond j)).symm
  unfold axisLaplacian
  simp_rw [fun j => (hterms j).2.2.2.deriv]
  rw [(hterms 2).2.2.1.deriv]
  change (p 2:ℂ)^2*(∑j : Fin 3,∑'r,second j r) - (p 2:ℂ)*(∑'r,first r) = _
  rw [hcomm,← tsum_mul_left,← tsum_mul_left,← (hsum.mul_left _).tsum_sub (hfirst.mul_left _)]
  change (∑'r,axisLaplacian (smoothSummand s r) p) = _
  simp_rw [smoothSummand_axisLaplacian s _ p hv]
  rw [tsum_mul_left]
  rfl

lemma axisSlice_eventuallyEq_of_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
  have hnear : ∀ᶠ t in 𝓝 (p j), 0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change 0<(Function.update p j (p j)) 2
    simpa only [Function.update_eq_self] using hv
  filter_upwards [hnear] with t ht
  exact heq _ ht

lemma axisLaplacian_congr_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian f p = axisLaplacian g p := by
  have h (j : Fin 3) := axisSlice_eventuallyEq_of_positive f g heq p hv j
  unfold axisLaplacian
  rw [(h 2).deriv_eq]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact (h j).deriv.deriv_eq

def upperEisensteinField (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hv : 0<p 2 then upperEisenstein ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s else 0

lemma upperEisensteinField_eq_smooth (s : ℂ) (p : SpatialCoordinates) (hv : 0<p 2) :
    upperEisensteinField s p=smoothEisenstein s p := by
  rw [upperEisensteinField,dite_eq_left hv]
  exact (smoothEisenstein_eq_actual s p hv).symm

theorem upperEisenstein_eigenfunction (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (upperEisensteinField s) p = s*(s-2)*upperEisensteinField s p := by
  rw [axisLaplacian_congr_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) p hv,
    smoothEisenstein_eigenfunction s hs p hv,upperEisensteinField_eq_smooth s p hv]

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

lemma firstCoreModeHeight_norm (negative : Bool) (t : ℝ) :
    ‖firstCoreModeHeight negative t‖ = ‖t‖ := by
  cases negative <;> simp [firstCoreModeHeight]

theorem firstCoreInputRow_finite_second_transfer
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (D₀ E₀ V₀ X₀ K₀ : Finset ι → κ → ℝ) (Y : ℝ),
        (∀ R j, 0 < D₀ R j) → (∀ R j, 0 < E₀ R j) → (∀ R j, 0 < V₀ R j) →
        (∀ R j, 0 < X₀ R j) → (∀ R j, 0 < K₀ R j) → 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z t : ℝ) (Srows : Finset O)
        (label : Finset ι → SecondExpansionData ι → κ)
        (T : Finset ι → κ → Finset (Ideal O × O)) (lengthScale : Finset ι → κ → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        (∀ R ∈ (F\A₀).powerset, ∀ j, 0 ≤ lengthScale R j) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorZ p
            (secondExpansionScale p (X / primeProductNorm p A₀)
              (primeSubsetGenerator (fun i => Ideal.span {p i}) R) (expansionSupportData C D x))
            (X₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorUd p (D₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorUe p (E₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorUv p (V₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorKap p (K₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
            secondSupportRow p (expansionSupportData C D x)) ∈ T R j) →
        (∀ R ∈ (F\A₀).powerset, ∀ j, ∀ q ∈ T R j, q.1 ≠ ⊥) →
        (∀ R ∈ (F\A₀).powerset, ∀ j, ∀ q ∈ T R j, (Ideal.absNorm q.1 : ℝ) ≤ lengthScale R j) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
        (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖ ^ 2) +
          ‖firstCoreTest (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X)
            negative t A₀ ∅‖ ^ 2 ≤
        (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖ ^ 2) +
            (∑ z : SecondRayIndex, ∑ R ∈ (F\A₀).powerset, ∑ j : κ,
              (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
                  X' ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (lengthScale R j * Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
                (1+Y*K₀ R j/(D₀ R j*(E₀ R j)^2*(V₀ R j)^2*(X₀ R j)^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R) (T R j)
                (windows 5) (windows 6) (X₀ R j) (X₀ R j) J) +
            ‖secondSourceTail p hp hg hinj (F\A₀) Ψ' m' c' d Hmode rowMajorant Y
              (firstCoreSecondCutoff p A₀ X Y M Z)‖) := by
  have hUbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU s
    intro hz
    apply hs
    simp only [firstCoreBaseProfile_apply, hz, zero_mul]
  have hMbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → |s| ≤ M := by
    intro s hs
    apply hgM s
    intro hz
    apply hs
    simp only [firstCoreBaseProfile_apply, hz, zero_mul]
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_truncated_second_density_transfer (κ := κ) p hp hcop hg hinj hc hpr U hUc hUs
      (firstCoreBaseProfile g V negative) rowMajorant hUbase M H hM hH hMbase ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
    A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows label T lengthScale hv hCB hD hΨ hX hZ hSrows hSrows0
    hL hz hud hue huv hkap hmap hT hnorm
  dsimp only
  have hX' : 0 < X / primeProductNorm p A₀ :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A₀)
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have hcut : ∀ G ∈ (F\A₀).powerset, ∀ E ∈ G.powerset,
      (0 : O) ∈ firstCoreSecondCutoff p A₀ X Y M Z G E := by
    intro G hG E hE
    exact firstCoreSecondCutoff_zero p A₀ X Y M Z G E
  have hb := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY (firstCoreModeHeight negative t)
    B C D (F\A₀) v₁ v₂ ε₁ ε₂ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂) (X / primeProductNorm p A₀)
    (firstCoreSecondCutoff p A₀ X Y M Z) label T lengthScale hv hCB hD hΨ' hX' hcut hL
    hz hud hue huv hkap hmap hT hnorm
  simp only [firstCoreModeHeight_norm] at hb
  have hf := firstCoreInputRow_finite_le_truncated_tail p hp hg hinj hc F A₀ B
    (fun i => v₁ i+v₂ i) ε₁ ε₂ negative χ Ψ m g V X hX Y hY
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r₁ t Srows hSrows hSrows0
    (firstCoreSecondCutoff p A₀ X Y M Z)
  simp only [firstCoreModeProfile] at hf ⊢
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact hb
    · exact le_rfl
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma residualPairWeight_test_ne_zero
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι)
    (hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0) :
    H₁ S ≠ 0 ∧ H₂ T ≠ 0 := by
  constructor
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero, star_zero, zero_mul]
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero]

theorem residualTailCost_frequencyTwist
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d e : O)
    (g : 𝓢(ℝ, ℂ)) (θ X Y H : ℝ) (A : ℕ) (P : ℝ) :
    residualTailCost p hg F G Ψ₁ Ψ₂ m c d
      (fun S => normalizedColumn p (fun U => (frequencyTwist g θ) (columnLog p X U)) (G∪S))
      (fun S => normalizedColumn p (fun U => (frequencyTwist g θ) (columnLog p X U)) (G∪S)) e Y H A P =
    residualTailCost p hg F G Ψ₁ Ψ₂ m c d
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S)) e Y H A P := by
  simp only [residualTailCost, residualPairWeight, secondInputCoefficient, normalizedColumn,
    frequencyTwist_apply, norm_mul, norm_star, norm_div, FourierBridge.logPhase_norm, one_mul]

end

theorem firstCoreSecondCutoff_tail_bound
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
      ∑ G ∈ (F\D).powerset, ∑ E : G.powerset,
        ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg (F\D) G Ψ Ψ m c d (fun S => Hbase (G∪S)) (fun S => Hbase (G∪S))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := secondSourceTail_bound p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F D Ψ m c d g V W negative t X Y M H hX hY hH hgM
  dsimp only
  have hcut : ∀ G ∈ (F\D).powerset, ∀ E : G.powerset,
      ∀ S ∈ ((F\D)\G).powerset, ∀ T ∈ ((F\D)\G).powerset, Disjoint S T →
      residualPairWeight p hg Ψ Ψ m c d
        (fun U => normalizedColumn p (fun R => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) R)) (G∪U))
        (fun U => normalizedColumn p (fun R => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) R)) (G∪U)) S T ≠ 0 →
      ∀ k : O, k ∉ firstCoreSecondCutoff p D X Y M H G E.val →
        H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
    intro G hG E S hS T hT hST hw k hk
    have hGS : Disjoint G S := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    obtain ⟨hs,ht⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    exact firstCoreSecondCutoff_uniform p hp g V negative t M hgM D G E.val S T hGS hGT hST
      X Y H hX hY hs ht k hk
  have h := hb (F\D) Ψ m c d
    (normalizedColumn p (fun S => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) S))) W Y H hY hH
    (firstCoreSecondCutoff p D X Y M H) hcut
  simpa only [firstCoreModeProfile, residualTailCost_frequencyTwist] using h

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

lemma divisorPool_filter (S : Finset (Ideal O)) (B : Ideal O) (hB : B ≠ 0)
    (hS : ∀ D, D ∣ B → D ∈ S) :
    S.filter (fun D => D ∣ B) = idealDivisors B := by
  ext D
  simp only [Finset.mem_filter, mem_idealDivisors hB]
  exact ⟨And.right, fun h => ⟨hS D h,h⟩⟩

lemma divisor_product_delta (S T : Finset (Ideal O)) (B C d : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsCoprime B C)
    (hS : ∀ D, D ∣ B → D ∈ S) (hT : ∀ E, E ∣ C → E ∈ T)
    (f : Ideal O → ℂ) :
    (∑ D ∈ S, if D ∣ B then
      ∑ E ∈ T, if E ∣ C then (if D*E=d then f (D*E) else 0) else 0 else 0) =
      if d ∣ B*C then f d else 0 := by
  have hs := QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hBC
    (fun q => if q=d then f q else 0)
  have hleft : (∑ q ∈ idealDivisors (B*C), if q=d then f q else 0) =
      if d ∣ B*C then f d else 0 := by
    simp [mem_idealDivisors (mul_ne_zero hB hC)]
  rw [hleft] at hs
  rw [← divisorPool_filter S B hB hS, ← divisorPool_filter T C hC hT] at hs
  simpa only [Finset.sum_filter] using hs.symm

private lemma four_sums_exchange {α β γ deltaLoss : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset deltaLoss)
    (f : α → β → γ → deltaLoss → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d) =
      ∑ c ∈ U, ∑ d ∈ V, ∑ a ∈ S, ∑ b ∈ T, f a b c d := by
  have h : (∑ ab ∈ S ×ˢ T, ∑ cd ∈ U ×ˢ V, f ab.1 ab.2 cd.1 cd.2) =
      ∑ cd ∈ U ×ˢ V, ∑ ab ∈ S ×ˢ T, f ab.1 ab.2 cd.1 cd.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

private lemma three_sums_exchange {α β γ : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (f : α → β → γ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, f a b c) =
      ∑ b ∈ T, ∑ c ∈ U, ∑ a ∈ S, f a b c := by
  have h : (∑ a ∈ S, ∑ bc ∈ T ×ˢ U, f a bc.1 bc.2) =
      ∑ bc ∈ T ×ˢ U, ∑ a ∈ S, f a bc.1 bc.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_product_divisor (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m) (j : n) (k : p)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      originalTerm rows left right a b D E i j k * F (D*E) i j k else 0) =
    (if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) := by
  by_cases hc : IsCoprime (left j) (right k)
  · have hd := divisor_product_delta S T (left j) (right k) d (hleft j) (hright k) hc
      (hS j) (hT k) (fun q =>
        star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * a j) *
          (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * b k) * F q i j k)
    calc
      _ = (∑ D ∈ S, if D ∣ left j then ∑ E ∈ T, if E ∣ right k then
          (if D*E=d then
            star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * a j) *
              (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * b k) * F (D*E) i j k
          else 0) else 0 else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        by_cases hd : D ∣ left j
        · simp only [ite_eq_left hd]
          apply Finset.sum_congr rfl
          intro E hE
          by_cases he : E ∣ right k <;> by_cases hde : D*E=d <;>
            simp [originalTerm,hc,hd,he,hde]
        · simp [originalTerm,hc,hd]
      _ = _ := by simpa [originalTerm,hc] using hd
  · simp [originalTerm,hc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_product_divisor (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ j, ∑ k, if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) =
    ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      (∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k) else 0 := by
  calc
    _ = ∑ j, ∑ k, ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact (originalTerm_product_divisor S T rows left right a b d i j k hleft hright hS hT F).symm
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ j, ∑ k, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 :=
      four_sums_exchange Finset.univ Finset.univ S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      by_cases h : D*E=d <;> simp [h]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_divisor_rectangles (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (P : Ideal O → m → Prop) [DecidablePred (fun d => P d i)]
    (F : Ideal O → m → n → p → ℂ) :
    (∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
    ∑ D ∈ S, ∑ E ∈ T, if D*E ∈ K then if P (D*E) i then
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k‖ else 0 else 0 := by
  let B := fun D E => ∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k
  have hpoint (d : Ideal O) :
      (if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
      ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 := by
    by_cases hp : P d i
    · simp only [hp, and_true]
      rw [originalColumnSum_product_divisor S T rows left right a b d i hleft hright hS hT F]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      by_cases h : D*E=d <;> simp [h,B]
    · simp [hp]
  calc
    _ ≤ ∑ d ∈ K, ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      Finset.sum_le_sum (fun d hd => hpoint d)
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ d ∈ K, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      three_sums_exchange K S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      have heq (d : Ideal O) : (if D*E=d ∧ P d i then ‖B D E‖ else 0) =
          if d=D*E then (if P (D*E) i then ‖B D E‖ else 0) else 0 := by
        by_cases h : d=D*E
        · subst d
          simp
        · simp [h,Ne.symm h]
      simp_rw [heq]
      simp only [Finset.sum_ite_eq', B]

end

open ActualEisensteinCubic

lemma positive_ideal_dyadic_exists (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    ∃ j ∈ Finset.range (columnDyadicLength N + 1),
      (2 : ℝ)^j/2 < (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^j := by
  have hp : 1 ≤ Ideal.absNorm D := by exact_mod_cast hD
  exact exists_dyadic_shell (Ideal.absNorm D) (columnDyadicLength N) hp
    (hDN.trans (columnDyadicLength_cover N))

def divisorDyadicLabel (N : ℝ) (D : Ideal O) : Fin (columnDyadicLength N+1) :=
  if h : 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N then
    ⟨(positive_ideal_dyadic_exists N D h.1 h.2).choose,
      Finset.mem_range.mp (positive_ideal_dyadic_exists N D h.1 h.2).choose_spec.1⟩
  else ⟨0,by omega⟩

def divisorDyadicBin (S : Finset (Ideal O)) (N : ℝ)
    (j : Fin (columnDyadicLength N+1)) : Finset (Ideal O) :=
  S.filter (fun D => divisorDyadicLabel N D = j)

def divisorDyadicScale (j : ℕ) : ℝ := max 1 ((2 : ℝ)^j/2)

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dite_eq_left ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (D : Ideal O) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS,hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ)^j.val/2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem divisorDyadicBin_scale_le (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (hj : (divisorDyadicBin S N j).Nonempty) :
    divisorDyadicScale j.val ≤ N := by
  obtain ⟨D,hD⟩ := hj
  exact (divisorDyadicBin_bounds S N hS j D hD).1.trans (hS D (Finset.mem_filter.mp hD).1).2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

theorem sum_divisorDyadicRectangles {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (N : ℝ) (f : Ideal O → Ideal O → A) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) =
      ∑ j : Fin (columnDyadicLength N+1), ∑ k : Fin (columnDyadicLength N+1),
        ∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E := by
  calc
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ E ∈ T, f D E := sum_divisorDyadicBins S N _
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ k : Fin (columnDyadicLength N+1), ∑ E ∈ divisorDyadicBin T N k, f D E := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro D hD
      exact sum_divisorDyadicBins T N (f D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

def columnDivisorPool {n : Type*} [Fintype n] (left : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.biUnion (fun j => IdealMobiusDivisorSum.idealDivisors (left j))

theorem mem_columnDivisorPool_of_dvd {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (j : n) (D : Ideal O)
    (hD : D ∣ left j) : D ∈ columnDivisorPool left := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j,Finset.mem_univ j,(IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mpr hD⟩

theorem columnDivisorPool_norm_bounds {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N)
    (D : Ideal O) (hD : D ∈ columnDivisorPool left) :
    1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N := by
  obtain ⟨j,hj,hDj⟩ := Finset.mem_biUnion.mp hD
  have hd := (IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mp hDj
  have hDz : D ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact hleft j hd
  have hDN : Ideal.absNorm D ≤ Ideal.absNorm (left j) :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hleft j (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hd)
  refine ⟨?_,(Nat.cast_le.mpr hDN).trans (hN j)⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hDz (Ideal.absNorm_eq_zero_iff.mp h))

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0150

/-! Original module: OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
Source SHA256: f14ab74f6e52c9b8ce94799157dcd2a129e78ef990c3521d74fdeaf7f5c36835
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0151



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

namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

def nonzeroLatticeEnvelopeConstant : ℝ :=
  4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass

theorem nonzeroLatticeEnvelopeConstant_nonneg :
    0 ≤ nonzeroLatticeEnvelopeConstant := by
  have := eisensteinCauchyMass_nonneg
  unfold nonzeroLatticeEnvelopeConstant
  positivity

theorem scaled_cauchy_nonzero_mass (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤
        nonzeroLatticeEnvelopeConstant := by
  let F : ℝ → ℂ := fun x => (((1 + x) ^ 2)⁻¹ : ℝ)
  have hF (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 * ‖F x‖ ≤ 1 := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_inv_cancel₀ (by positivity : (1 + x) ^ 2 ≠ 0)]
  have hh := lattice_profile_nonzero_scaled_bound F 1 (by norm_num) hF t ht
  change t * (∑' h : {h : O // h ≠ 0}, ‖F (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
    nonzeroLatticeEnvelopeConstant * 1 at hh
  simpa only [F, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((1 + t * ‖eisEmbedding _‖ ^ 2) ^ 2)⁻¹ by positivity),
    mul_one] using hh

theorem nonzero_lattice_envelope_sum
    (t C : ℝ) (ht : 0 < t) (hC : 0 ≤ C)
    (f : {h : O // h ≠ 0} → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hbound : ∀ h, (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * f h ≤ C) :
    Summable f ∧ t * (∑' h, f h) ≤ nonzeroLatticeEnvelopeConstant * C := by
  have hp (h : {h : O // h ≠ 0}) :
      f h ≤ C * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hbound h
  have hs := (scaled_eisenstein_cauchy_summable t ht).subtype (fun h : O => h ≠ 0)
  have hfs : Summable f := Summable.of_nonneg_of_le hf hp (hs.mul_left C)
  refine ⟨hfs, ?_⟩
  have hh := hfs.tsum_le_tsum hp (hs.mul_left C)
  rw [tsum_mul_left] at hh
  calc
    _ ≤ t * (C * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
    _ = C * (t * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
    _ ≤ C * nonzeroLatticeEnvelopeConstant :=
      mul_le_mul_of_nonneg_left (scaled_cauchy_nonzero_mass t ht) hC
    _ = _ := mul_comm _ _

end EisensteinSchwartzPoisson

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def originalMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose

def dualMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose

theorem originalMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ originalMiddleDecayConstant W :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem dualMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ dualMiddleDecayConstant W :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem divisorBlockCost_mono_coefficients
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (D₁ D₂ B N : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (a a₀ : n → ℂ) (b b₀ : p → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ ‖a₀ j‖) (hb : ∀ k, ‖b k‖ ≤ ‖b₀ k‖) :
    divisorBlockCost ε hε D₁ D₂ B N a b ≤ divisorBlockCost ε hε D₁ D₂ B N a₀ b₀ := by
  have hA := sieveNorm_nonneg B (N / D₁)
  have hB := sieveNorm_nonneg B (N / D₂)
  unfold divisorBlockCost
  gcongr
  · exact ha _
  · exact hb _

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

def dualMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) :
    0 ≤ originalMiddleAt W S T rows left right a b M h := by
  unfold originalMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) :
    0 ≤ dualMiddleAt W S T rows left right a b M F h := by
  unfold dualMiddleAt
  positivity

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows ha hb

theorem actual_original_middle_all_frequencies
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
        2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := Real.sqrt (M / B) / (D₁ * D₂)
  have ht : 0 < t := by dsimp only [t]; positivity
  let C := originalMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (originalMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ 2 * t * C := by
    have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M
      hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ originalMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (originalMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h.val‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : Real.sqrt (M / B) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt (M / B) / (D₁ * D₂) = 2 * t := by dsimp only [t]; ring
    rw [hpre] at hp
    change originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * (2 * t * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = 2 * t * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ 2 * t * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t (2 * t * C) ht (by positivity)
    _ (fun h => originalMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * (2 * t * C) := hv
    _ = _ := by dsimp only [C]; ring

end

theorem dual_middle_scale_identity (M F B N : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N) :
    Real.sqrt ((M / F) / B) = (M / (F * N)) * (N * Real.sqrt (F / (M * B))) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ (M / F) / B by positivity),
    Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem actual_dual_middle_all_frequencies
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
        (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N)) *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := (N * Real.sqrt (F / (M * B))) / (D₁ * D₂)
  let r := M / (F * N)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr0 : 0 < r := by dsimp only [r]; positivity
  let C := dualMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (dualMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ (2 * t * r) * C := by
    have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M F
      hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ dualMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (dualMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h.val‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF) (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) = 2 * t * r := by
      rw [dual_middle_scale_identity M F B N hM hF (by linarith) (by linarith)]
      dsimp only [t, r]
      ring
    rw [hpre] at hp
    change dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * ((2 * t * r) * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = (2 * t * r) * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ (2 * t * r) * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t ((2 * t * r) * C) ht (by positivity)
    _ (fun h => dualMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M F h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * ((2 * t * r) * C) := hv
    _ = _ := by dsimp only [C, r]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def divisorExponentConstant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) : ℝ :=
  (h.divisor_pair deltaLoss hδ).choose

theorem divisorExponentConstant_pos {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    0 < divisorExponentConstant h deltaLoss hδ := (h.divisor_pair deltaLoss hδ).choose_spec.1

theorem divisor_cost_with_constant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (B N D₁ D₂ : ℝ)
    (hB : 1 ≤ B) (hN : 1 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) ≤
      divisorEnergyFactor ε hε N a b *
        (divisorExponentConstant h deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂))) := by
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ B N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left
    ((h.divisor_pair deltaLoss hδ).choose_spec.2 B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

theorem sqrt_div_mul_rpow (M B α : ℝ) (hM : 0 ≤ M) (hB : 0 < B) :
    Real.sqrt (M / B) * B ^ α = Real.sqrt M * B ^ (α - 1 / 2) := by
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow, Real.sqrt_div hM]
  ring

theorem original_middle_scale_shape (M B N D T α : ℝ)
    (hM : 0 ≤ M) (hB : 0 < B) (hD : D ≤ T * Real.sqrt (M / B)) :
    N + B ^ α * D ≤ N + T * Real.sqrt M * B ^ (α - 1 / 2) := by
  calc
    _ ≤ N + B ^ α * (T * Real.sqrt (M / B)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hB.le α))
    _ = _ := by rw [mul_left_comm (B ^ α) T, mul_comm (B ^ α), sqrt_div_mul_rpow M B α hM hB]; ring

theorem dual_middle_scale_shape (M F B N D T α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N)
    (hD : D ≤ T * (N * Real.sqrt (F / (M * B)))) :
    (M / (F * N)) * (N + B ^ α * D) ≤
      M / F + T * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hratio : 0 ≤ M / (F * N) := by positivity
  calc
    _ ≤ (M / (F * N)) * (N + B ^ α * (T * (N * Real.sqrt (F / (M * B))))) := by gcongr
    _ = M / F + T * (Real.sqrt ((M / F) / B) * B ^ α) := by
      rw [dual_middle_scale_identity M F B N hM hF hB hN]
      field_simp

    _ = _ := by rw [sqrt_div_mul_rpow (M / F) B α (by positivity) hB]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.original_middle_block
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * Real.sqrt (M / B)) :
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + U * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (originalMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc hk)
    _ = ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          (N + B ^ α * (D₁ * D₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (original_middle_scale_shape M B N (D₁ * D₂) U α hM.le (by linarith) hcut) (by positivity)

theorem HasSieveExponent.dual_middle_block
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * (N * Real.sqrt (F / (M * B)))) :
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + U * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (dualMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N))) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          ((M / (F * N)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁ * D₂) U α hM hF (by linarith) (by linarith) hcut) (by positivity)

end CanonicalQuadraticSieve

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology Matrix MatrixGroups

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def integralComplexMatrix : SL(2,O) →* SL(2,ℂ) := Matrix.SpecialLinearGroup.map eisEmbedding

@[simp] lemma integralComplexMatrix_apply (M : SL(2,O)) (i j : Fin 2) :
    integralComplexMatrix M i j = eisEmbedding (M i j) := rfl

lemma integralComplexMatrix_levelThree (M : levelThree) :
    integralComplexMatrix (M : SL(2,O)) = complexMatrix M := rfl

lemma row_wedge_gram (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) +
      Complex.normSq (u 0*star (v 0)+u 1*star (v 1)) = rowEnergy u * rowEnergy v := by
  simp only [rowEnergy,← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma row_wedge_le_energy (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) ≤ rowEnergy u * rowEnergy v := by
  rw [← row_wedge_gram u v]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

lemma bottom_row_wedge_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) 0 * complexBottomRow h 1 -
      complexBottomRow (g*h) 1 * complexBottomRow h 0 = g 1 0 := by
  have hd : h 0 0*h 1 1-h 0 1*h 1 0=1 := by
    simpa only [Matrix.det_fin_two] using h.property
  simp only [complexBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination g 1 0 * hd

theorem hyperbolicHeight_mul_bound (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicHeight (g • w) * hyperbolicHeight w * Complex.normSq (g 1 0) ≤ 1 := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) ≤ 1
    have hw := row_wedge_le_energy (complexBottomRow (g*h)) (complexBottomRow h)
    rw [bottom_row_wedge_mul] at hw
    have hp : 0 < rowEnergy (complexBottomRow (g*h)) * rowEnergy (complexBottomRow h) :=
      mul_pos (rowEnergy_pos _ (complexBottomRow_ne_zero _))
        (rowEnergy_pos _ (complexBottomRow_ne_zero _))
    have he : liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) =
        Complex.normSq (g 1 0) /
          (rowEnergy (complexBottomRow (g*h))*rowEnergy (complexBottomRow h)) := by
      simp only [liftedHeight,div_eq_mul_inv,mul_inv]
      ring
    rw [he]
    exact (div_le_one hp).mpr hw

lemma one_le_normSq_embedding (c : O) (hc : c≠0) : 1 ≤ Complex.normSq (eisEmbedding c) := by
  rw [Complex.normSq_eq_norm_sq,eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))

theorem integral_hyperbolicHeight_mul_le_one (M : SL(2,O)) (hc : M 1 0≠0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w) * hyperbolicHeight w ≤ 1 := by
  have hb := hyperbolicHeight_mul_bound (integralComplexMatrix M) w
  have hc1 := one_le_normSq_embedding (M 1 0) hc
  have hp := mul_pos (hyperbolicHeight_pos (integralComplexMatrix M • w)) (hyperbolicHeight_pos w)
  change _ * _ * Complex.normSq (eisEmbedding (M 1 0)) ≤ 1 at hb
  nlinarith

def cuspHoroball (σ : SL(2,O)) (Y : ℝ) : Set HyperbolicSpace :=
  {w | Y < hyperbolicHeight (integralComplexMatrix σ⁻¹ • w)}

theorem cuspHoroball_disjoint (σ τ : SL(2,O)) (Y Z : ℝ)
    (hY : 1≤Y) (hZ : 1≤Z) (hc : (σ⁻¹*τ) 1 0≠0) :
    Disjoint (cuspHoroball σ Y) (cuspHoroball τ Z) := by
  apply Set.disjoint_left.mpr
  intro w hwσ hwτ
  have hprod := integral_hyperbolicHeight_mul_le_one (σ⁻¹*τ) hc
    (integralComplexMatrix τ⁻¹ • w)
  simp only [map_mul,map_inv,mul_smul,smul_inv_smul] at hprod
  have hσ : 1 < hyperbolicHeight (integralComplexMatrix σ⁻¹ • w) := lt_of_le_of_lt hY hwσ
  have hτ : 1 < hyperbolicHeight (integralComplexMatrix τ⁻¹ • w) := lt_of_le_of_lt hZ hwτ
  simp only [map_inv] at hσ hτ
  nlinarith [mul_pos (sub_pos.mpr hσ) (sub_pos.mpr hτ)]

def InequivalentCusps (σ τ : SL(2,O)) : Prop :=
  ∀ M : levelThree, (σ⁻¹*(M : SL(2,O))*τ) 1 0≠0

def cuspNeighborhood (σ : SL(2,O)) (Y : ℝ) : Set HyperbolicSpace :=
  {w | ∃ M : levelThree, w ∈ cuspHoroball ((M : SL(2,O))*σ) Y}

lemma cuspNeighborhood_invariant (σ : SL(2,O)) (Y : ℝ) (M : levelThree) (w : HyperbolicSpace) :
    complexMatrix M • w ∈ cuspNeighborhood σ Y ↔ w ∈ cuspNeighborhood σ Y := by
  constructor
  · rintro ⟨N,hN⟩
    refine ⟨M⁻¹*N,?_⟩
    change Y < hyperbolicHeight (integralComplexMatrix (((M⁻¹*N : levelThree) : SL(2,O))*σ)⁻¹ • w)
    change Y < hyperbolicHeight (integralComplexMatrix ((N : SL(2,O))*σ)⁻¹ • (complexMatrix M • w)) at hN
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,inv_inv,map_mul,map_inv,mul_smul,
      integralComplexMatrix_levelThree] using hN
  · rintro ⟨N,hN⟩
    refine ⟨M*N,?_⟩
    change Y < hyperbolicHeight (integralComplexMatrix (((M*N : levelThree) : SL(2,O))*σ)⁻¹ • (complexMatrix M • w))
    change Y < hyperbolicHeight (integralComplexMatrix ((N : SL(2,O))*σ)⁻¹ • w) at hN
    simpa only [Subgroup.coe_mul,mul_inv_rev,map_mul,map_inv,mul_smul,
      integralComplexMatrix_levelThree,inv_smul_smul] using hN

theorem cuspNeighborhood_disjoint (σ τ : SL(2,O)) (hστ : InequivalentCusps σ τ)
    (Y Z : ℝ) (hY : 1≤Y) (hZ : 1≤Z) :
    Disjoint (cuspNeighborhood σ Y) (cuspNeighborhood τ Z) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨M,hM⟩ ⟨N,hN⟩
  apply Set.disjoint_left.mp (cuspHoroball_disjoint ((M : SL(2,O))*σ) ((N : SL(2,O))*τ) Y Z hY hZ ?_) hM hN
  have hc := hστ (M⁻¹*N)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,mul_assoc] using hc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma cosetHeight_pos (x : CuspCosets) (w : HyperbolicSpace) : 0<cosetHeight x w := by
  induction x using Quotient.inductionOn with
  | _ M => exact (cosetHeight_cosetOf M w).symm ▸ hyperbolicHeight_pos _

lemma cosetHeight_rightEquiv (M : levelThree) (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight (rightEquiv M x) w = cosetHeight x (complexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf (N*M)) w = cosetHeight (cosetOf N) (complexMatrix M • w)
    rw [cosetHeight_cosetOf,cosetHeight_cosetOf,map_mul,mul_smul]

lemma high_coset_unique (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace)
    (x y : CuspCosets) (hx : Y<cosetHeight x w) (hy : Y<cosetHeight y w) : x=y := by
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      by_contra hne
      have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0≠0 := by
        intro hc
        have hT : M*N⁻¹ ∈ cuspStabilizer := (mem_cuspStabilizer_iff _).mpr hc
        exact hne ((cosetOf_eq_iff M N).mpr ⟨M*N⁻¹,hT,by group⟩)
      have hp := integral_hyperbolicHeight_mul_le_one
        ((M*N⁻¹ : levelThree) : SL(2,O)) hc (complexMatrix N • w)
      rw [integralComplexMatrix_levelThree,map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change Y<cosetHeight (cosetOf M) w at hx
      change Y<cosetHeight (cosetOf N) w at hy
      rw [cosetHeight_cosetOf] at hx hy
      have hm := lt_of_le_of_lt hY hx
      have hn := lt_of_le_of_lt hY hy
      nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hn)]

lemma high_cosets_finite (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace) :
    Set.Finite {x : CuspCosets | Y<cosetHeight x w} := by
  have h : Set.Subsingleton {x : CuspCosets | Y<cosetHeight x w} :=
    fun x hx y hy => high_coset_unique Y hY w x y hx hy
  exact h.finite

def cuspCutoffTerm (Y : ℝ) (F : ℝ → ℂ) (x : CuspCosets) (w : HyperbolicSpace) : ℂ :=
  if Y<cosetHeight x w then (cosetCharacter x)⁻¹ * F (cosetHeight x w) else 0

lemma cuspCutoffTerm_finiteSupport (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x => cuspCutoffTerm Y F x w) := by
  apply (high_cosets_finite Y hY w).subset
  intro x hx
  by_contra hn
  simp only [Function.mem_support] at hx
  change ¬Y<cosetHeight x w at hn
  exact hx (by simp [cuspCutoffTerm,hn])

