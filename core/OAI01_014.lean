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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open MixedCrossSeparation (columnG columnPrimeCoprime quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)

def rayMonoid (χ : RayCharacter) : O →* ℂ where
  toFun := rayCharacter χ
  map_one' := by simp [rayCharacter]
  map_mul' := RayFourExpansion.rayCharacter_mul χ

def conjugateRayMonoid (χ : RayCharacter) : O →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp (rayMonoid χ)

@[simp] theorem rayMonoid_apply (χ : RayCharacter) (a : O) :
    rayMonoid χ a = rayCharacter χ a := rfl
@[simp] theorem conjugateRayMonoid_apply (χ : RayCharacter) (a : O) :
    conjugateRayMonoid χ a = star (rayCharacter χ a) := rfl

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem columnG_eq_ray_sum
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i ∈ S, p i) := by
  have h := RayFourExpansion.canonicalProductG_character_expansion
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, Finset.prod_coe_sort] using h

def secondInputCoefficient (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * H S

theorem secondColumnMinus_ray_expansion
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondColumnMinus p hp hcop hg (secondInputCoefficient p hg Ψ m c d H) e k S =
      ∑ χ : RayCharacter, star (gCoeff χ) *
        secondPreColumn p hp hcop hg (conjugateRayMonoid χ * Ψ) m c d e k H S := by
  simp only [secondColumnMinus, columnG_eq_ray_sum p hp hcop hg hc hpr,
    star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ hχ
  simp only [secondPreColumn, secondInputCoefficient, MonoidHom.mul_apply, conjugateRayMonoid_apply]
  ring

theorem secondColumnPlus_ray_expansion
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondColumnPlus p hp hcop hg (secondInputCoefficient p hg Ψ m c d H) e k S =
      ∑ χ : RayCharacter, star (gCoeff χ) *
        secondPreColumn p hp hcop hg (conjugateRayMonoid χ * Ψ) m c d e (-k) H S := by
  have hk : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-k) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k := by
    simpa only [neg_one_mul] using finiteSquarefreeRow_mul (fun i => Ideal.span {p i}) hg S (-1) k
  simp only [secondColumnPlus, columnG_eq_ray_sum p hp hcop hg hc hpr,
    star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ hχ
  simp only [secondPreColumn, secondInputCoefficient, MonoidHom.mul_apply, conjugateRayMonoid_apply, hk]
  ring

theorem second_gauss_ray_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) (hd : Disjoint S T) :
    star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    ∑ b : RayCharacter, ∑ a : RayCharacter, ∑ χ : RayCharacter, ∑ η : RayCharacter,
      (crossCoeff χ η * gCoeff a * star (gCoeff b)) *
        star (secondPreColumn p hp hcop hg
          (conjugateRayMonoid η * (conjugateRayMonoid a * Ψ₁)) m c d e k H₁ S) *
        secondPreColumn p hp hcop hg
          (rayMonoid χ * (conjugateRayMonoid b * Ψ₂)) m c d e (-k) H₂ T := by
  rw [mobius_second_gauss_restore p hp hinj hcop hg hc hpr S T hd,
    secondColumnMinus_ray_expansion p hp hcop hg hc hpr,
    secondColumnPlus_ray_expansion p hp hcop hg hc hpr,
    RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc T S hd.symm]
  simp only [star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro η hη
  simp only [secondPreColumn, MonoidHom.mul_apply, conjugateRayMonoid_apply,
    rayMonoid_apply, star_mul, star_star]
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

abbrev SecondRayIndex := (RayCharacter × RayCharacter) × (RayCharacter × RayCharacter)

def secondRayCoefficient (r : SecondRayIndex) : ℂ :=
  crossCoeff r.2.1 r.2.2 * gCoeff r.1.2 * star (gCoeff r.1.1)

def secondRayMinus (Ψ : O →* ℂ) (r : SecondRayIndex) : O →* ℂ :=
  conjugateRayMonoid r.2.2 * (conjugateRayMonoid r.1.2 * Ψ)

def secondRayPlus (Ψ : O →* ℂ) (r : SecondRayIndex) : O →* ℂ :=
  rayMonoid r.2.1 * (conjugateRayMonoid r.1.1 * Ψ)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondActualPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S *
      secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
    (supportMobius (fun i => Ideal.span {p i}) T *
      secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k else 0

theorem secondActualPair_eq_separated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ =
      ∑ z : SecondRayIndex, secondRayCoefficient z *
        secondSeparatedPair p hp hcop hg F (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
          m r c d e k (-k) H₁ H₂ := by
  have hh (S T : Finset ι) :
      (if Disjoint S T then
        star (supportMobius (fun i => Ideal.span {p i}) S *
          secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
        (supportMobius (fun i => Ideal.span {p i}) T *
          secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
          activeGaussRowFactor p hp hinj hg T S e k else 0) =
        ∑ z : SecondRayIndex, secondRayCoefficient z *
          (if Disjoint S T then
            star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z)
              (m * (e * r)) c d e k H₁ S) *
            secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z)
              (m * (e * r)) c d e (-k) H₂ T else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd]
      simpa only [Fintype.sum_prod_type, secondRayCoefficient, secondRayMinus,
        secondRayPlus, mul_assoc] using
        second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ₁ Ψ₂
          (m * (e * r)) c d e k H₁ H₂ S T hd
    · simp [hd]
  unfold secondActualPair
  simp_rw [hh]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : SecondRayIndex, ∑ T ∈ F.powerset,
        secondRayCoefficient z *
          (if Disjoint S T then
            star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z)
              (m * (e * r)) c d e k H₁ S) *
            secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z)
              (m * (e * r)) c d e (-k) H₂ T else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondSeparatedPair, Finset.mul_sum]

def secondTotalWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (z : SecondRayIndex × Finset ι) : ℂ :=
  secondRayCoefficient z.1 *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ₁ z.1) (secondRayPlus Ψ₂ z.1)
      m r c d e k (-k) z.2

def secondTotalEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) : ℝ :=
  ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V)‖ *
      ‖secondChildSum p hp hcop hg F V
        (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
        m r c d e (if negative then k else -k) H‖ ^ 2

theorem secondActualPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          star (secondChildSum p hp hcop hg F V (secondRayMinus Ψ₁ z) m r c d e k H₁) *
          secondChildSum p hp hcop hg F V (secondRayPlus Ψ₂ z) m r c d e (-k) H₂ := by
  rw [secondActualPair_eq_separated p hp hcop hg hinj hc hpr]
  simp only [secondSeparatedPair_eq_children p hp hcop hg hinj hpr,
    Finset.mul_sum, secondTotalWeight, mul_assoc]

private theorem weighted_star_cauchy {α : Type*} (s : Finset α)
    (w U V : α → ℂ) :
    ‖∑ i ∈ s, w i * star (U i) * V i‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    DescentWeightedCauchy.weighted_cauchy s w V U

theorem secondActualPair_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    ‖secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂‖ ≤
      Real.sqrt (secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ true) *
      Real.sqrt (secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ false) := by
  rw [secondActualPair_eq_children p hp hcop hg hinj hc hpr]
  have h := weighted_star_cauchy
    ((Finset.univ : Finset SecondRayIndex) ×ˢ F.powerset)
    (secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k)
    (fun z => secondChildSum p hp hcop hg F z.2 (secondRayMinus Ψ₁ z.1) m r c d e k H₁)
    (fun z => secondChildSum p hp hcop hg F z.2 (secondRayPlus Ψ₂ z.1) m r c d e (-k) H₂)
  simpa only [Finset.sum_product, secondTotalEnergy, ite_true,
    Bool.false_eq_true, ite_false] using h

end

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_zero_of_overlap
    (Ψ : O →* ℂ) (m c e y : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : ¬ Disjoint V N) :
    secondChildColumn p hp hcop hg Ψ m (c * e * ∏ i ∈ V, p i) y H N = 0 := by
  obtain ⟨i, hiV, hiN⟩ := Finset.not_disjoint_iff.mp hd
  have hdiv : p i ∣ c * e * ∏ j ∈ V, p j :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiV) (c * e)
  have hmask : rowCoprimeMask (fun i => Ideal.span {p i}) N (c * e * ∏ j ∈ V, p j) = 0 := by
    have hx : ∃ j ∈ N, c * e * ∏ a ∈ V, p a ∈ Ideal.span {p j} :=
      ⟨i, hiN, Ideal.mem_span_singleton.mpr hdiv⟩
    simp [rowCoprimeMask, hx]
  have hzero := FirstPassCubeLabels.row_zero_of_mask_zero
    (fun i => Ideal.span {p i}) hg N _ hmask
  simp only [secondChildColumn, hzero, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul]

theorem secondChildSum_fixed_pool
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k H =
      ∑ N ∈ F.powerset,
        secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
          (fun U => H (V ∪ U)) N := by
  unfold secondChildSum
  apply Finset.sum_subset
  · exact Finset.powerset_mono.mpr Finset.sdiff_subset
  · intro N hNF hNV
    apply secondChildColumn_zero_of_overlap
    intro hd
    apply hNV
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hNF) hi,
      fun hiv => Finset.disjoint_left.mp hd hiv hi⟩

end SecondPassArithmetic

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified

theorem symbol_ne_zero_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ≠ 0 := by
  classical
  have ha0 := primary_ne_zero a ha
  have hI0 : (Ideal.span {a} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr ha0
  rw [symbol, idealSymbol, ite_eq_right hI0]
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨P,hP,hzero⟩ := Multiset.mem_map.mp hzero
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
  have haP : a ∈ P := hle (Ideal.subset_span (by simp))
  have hg := primary_maximal_divisor_good a ha P haP
  have hxP : x ∉ P := by
    intro hxP
    obtain ⟨r,s,hrs⟩ := hcop
    have hmem := P.add_mem (P.mul_mem_left r hxP) (P.mul_mem_left s haP)
    rw [hrs] at hmem
    exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
      ((Ideal.eq_top_iff_one P).mpr hmem)
  rw [primeValue_eq P hg] at hzero
  exact cubicValue_ne_zero P hg x hxP hzero

theorem primary_mul (a b : O) (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) :
    lambda ^ 2 ∣ a*b-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left ha b) hb
  convert h using 1 ; ring

theorem primary_add_multiple_three (a c t : O) (ha : lambda ^ 2 ∣ a-1) :
    lambda ^ 2 ∣ (a+3*t*c)-1 := by
  have h := dvd_add ha (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left lambda_sq_dvd_three t) c)
  convert h using 1 ; ring

theorem kubota_mul_of_isCoprime (a b c d e g : O)
    (hdet : a*d-b*c=1) (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hg : (3 : O) ∣ g) (hag : IsCoprime a g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  let productA := a*e+b*g
  let productC := c*e+d*g
  have hA : lambda ^ 2 ∣ productA-1 := by
    have h := dvd_add (primary_mul a e ha he)
      (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans hb) g)
    convert h using 1 ; dsimp [productA] ; ring
  have hrelation : a*productC-c*productA=g := by
    dsimp [productA,productC]
    linear_combination g*hdet
  have hcop : IsCoprime a productA := by
    obtain ⟨r,s,hrs⟩ := hag
    refine ⟨r+s*productC,-s*c,?_⟩
    linear_combination hrs + s*hrelation
  have hnonzero := symbol_ne_zero_of_isCoprime a productA hA hcop
  have h1 : symbol a productA * symbol productC productA = symbol g productA := by
    rw [← symbol_mul_numerator _ _ productA hA]
    exact symbol_congr ⟨c, by linear_combination hrelation⟩
  have h2 : symbol a productA * symbol c a = symbol g a := by
    rw [symbol_reciprocity a productA (primary_ne_zero a ha) (primary_ne_zero productA hA) ha hA,
      ← symbol_mul_numerator _ _ a ha]
    calc
      symbol (productA*c) a = symbol (-g) a := by
        apply symbol_congr
        refine ⟨productC,?_⟩
        linear_combination -hrelation
      _ = symbol g a := symbol_neg_numerator g a ha
  have h3 : symbol g productA = symbol g a * symbol g e := by
    rw [← symbol_mul_denominator]
    apply symbol_denominator_congr g productA (a*e) hA (primary_mul a e ha he)
    · obtain ⟨b0,hb0⟩ := hb
      obtain ⟨g0,hg0⟩ := hg
      refine ⟨b0*g0,?_⟩
      dsimp [productA]
      rw [hb0,hg0]
      ring
    · exact ⟨b,by dsimp [productA];ring⟩
  change symbol productC productA = _
  apply mul_left_cancel₀ hnonzero
  rw [h1,h3,← h2]
  ring

lemma three_dvd_primary_sub_one (a : O) (ha : lambda ^ 2 ∣ a-1) : (3 : O) ∣ a-1 := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  rw [primaryCoord_eq]
  exact ⟨(A : O)+(B : O)*omega,by ring⟩

theorem exists_coprime_three_shift (a c g : O)
    (ha : lambda ^ 2 ∣ a-1) (hac : IsCoprime a c) (hg0 : g ≠ 0) :
    ∃ t : O, IsCoprime (a+3*t*c) g := by
  classical
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (UniqueFactorizationMonoid.normalizedFactors g).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, ?_⟩
  apply IsCoprime.symm
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hg0 h)
  intro p hp hpg hpnew
  by_cases hpa : p ∣ a
  · have hp3 : ¬p ∣ (3 : O) := by
      intro h3
      have hsub : p ∣ a-1 := h3.trans (three_dvd_primary_sub_one a ha)
      have hone : p ∣ (1 : O) := by
        convert dvd_sub hpa hsub using 1 ; ring
      exact hp.not_dvd_one hone
    have hpc : ¬p ∣ c := by
      intro hpc
      exact hp.not_isUnit (hac.isUnit_of_dvd' hpa hpc)
    have hps : ¬p ∣ s.prod := by
      intro hdiv
      obtain ⟨q,hqs,hpq⟩ := hp.exists_mem_multiset_dvd hdiv
      have hqs' : q ∈ UniqueFactorizationMonoid.normalizedFactors g ∧ ¬q ∣ a :=
        Multiset.mem_filter.mp hqs
      have hqprime := UniqueFactorizationMonoid.prime_of_normalized_factor q hqs'.1
      have hqp : q ∣ p := (hp.associated_of_dvd hqprime hpq).dvd'
      exact hqs'.2 (hqp.trans hpa)
    have hpterm : p ∣ 3*s.prod*c := by
      convert dvd_sub hpnew hpa using 1 ; ring
    rcases hp.dvd_or_dvd hpterm with hleft | hright
    · rcases hp.dvd_or_dvd hleft with h3 | hs
      · exact hp3 h3
      · exact hps hs
    · exact hpc hright
  · obtain ⟨q,hq,hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hg0 hp.irreducible hpg
    have hqa : ¬q ∣ a := fun hqa => hpa (hpq.dvd.trans hqa)
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,hqa⟩
    have hps : p ∣ s.prod := hpq.dvd.trans (Multiset.dvd_prod hqs)
    have hpterm : p ∣ 3*s.prod*c :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hps 3) c
    have hpa' : p ∣ a := by
      convert dvd_sub hpnew hpterm using 1 ; ring
    exact hpa hpa'

lemma symbol_three_shift (c a t : O) (ha : lambda ^ 2 ∣ a-1) (hc : (3 : O) ∣ c) :
    symbol c (a+3*t*c) = symbol c a := by
  apply symbol_denominator_congr c (a+3*t*c) a (primary_add_multiple_three a c t ha) ha
  · obtain ⟨c0,hc0⟩ := hc
    refine ⟨t*c0,?_⟩
    rw [hc0]
    ring
  · exact ⟨3*t,by ring⟩

theorem kubota_mul (a b c d e f g h : O)
    (hdet : a*d-b*c=1) (hdet' : e*h-f*g=1)
    (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ c) (hg : (3 : O) ∣ g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  by_cases hg0 : g = 0
  · have heh : e*h=1 := by simpa only [hg0,mul_zero,sub_zero] using hdet'
    have he1 : e=1 := A3_primary_unit_eq_one e (IsUnit.of_mul_eq_one h heh) he
    simp only [hg0,he1,mul_one,mul_zero,add_zero,symbol_one]
  have hac : IsCoprime a c := by
    refine ⟨d,-b,?_⟩
    linear_combination hdet
  obtain ⟨t,ht⟩ := exists_coprime_three_shift a c g ha hac hg0
  have hdetShift : (a+3*t*c)*d-(b+3*t*d)*c=1 := by linear_combination hdet
  have hbShift : (3 : O) ∣ b+3*t*d :=
    dvd_add hb (dvd_mul_of_dvd_left (dvd_mul_right 3 t) d)
  have hcalc := kubota_mul_of_isCoprime (a+3*t*c) (b+3*t*d) c d e g
    hdetShift (primary_add_multiple_three a c t ha) he hbShift hg ht
  have hC : (3 : O) ∣ c*e+d*g :=
    dvd_add (dvd_mul_of_dvd_left hc e) (dvd_mul_of_dvd_right hg d)
  have hA : lambda ^ 2 ∣ (a*e+b*g)-1 := by
    have hh := dvd_add (primary_mul a e ha he)
      (dvd_mul_of_dvd_left (lambda_sq_dvd_three.trans hb) g)
    convert hh using 1 ; ring
  calc
    symbol (c*e+d*g) (a*e+b*g) =
        symbol (c*e+d*g) ((a*e+b*g)+3*t*(c*e+d*g)) :=
      (symbol_three_shift _ _ _ hA hC).symm
    _ = symbol c (a+3*t*c) * symbol g e := by
      convert hcalc using 1 ; congr 1 ; ring
    _ = symbol c a * symbol g e := by rw [symbol_three_shift c a t ha hc]

end CubicJacobiGlobal

open scoped BigOperators Classical MatrixGroups

namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified

theorem symbol_cube_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ^ 3 = 1 := by
  classical
  have hI0 : (Ideal.span {a} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primary_ne_zero a ha)
  rw [symbol, idealSymbol, ite_eq_right hI0, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hy
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
  have haP : a ∈ P := hle (Ideal.subset_span (by simp))
  have hg := primary_maximal_divisor_good a ha P haP
  have hxP : x ∉ P := by
    intro hxP
    obtain ⟨r,t,hrt⟩ := hcop
    have hmem := P.add_mem (P.mul_mem_left r hxP) (P.mul_mem_left t haP)
    rw [hrt] at hmem
    exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
      ((Ideal.eq_top_iff_one P).mpr hmem)
  rw [primeValue_eq P hg]
  exact cubicValue_cube P hg x hxP
end CubicJacobiGlobal

namespace CubicKubota
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified

def levelThree : Subgroup (SL(2, O)) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)}))).ker

lemma levelThree_entry (M : levelThree) (i j : Fin 2) :
    (3 : O) ∣ (M : SL(2,O)) i j - (if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3 : O)})) (M : SL(2,O)) = 1 := M.property
  have h := congrArg (fun N : SL(2, O ⧸ (Ideal.span {(3 : O)})) => N i j) hm
  change (Ideal.Quotient.mk (Ideal.span {(3 : O)})) ((M : SL(2,O)) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ (Ideal.span {(3 : O)}))) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h

lemma levelThree_primary (M : levelThree) :
    lambda ^ 2 ∣ (M : SL(2,O)) 0 0 - 1 := by
  exact lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 0 0)
lemma levelThree_upper (M : levelThree) : (3 : O) ∣ (M : SL(2,O)) 0 1 := by
  simpa using levelThree_entry M 0 1
lemma levelThree_lower (M : levelThree) : (3 : O) ∣ (M : SL(2,O)) 1 0 := by
  simpa using levelThree_entry M 1 0

def value (M : levelThree) : O :=
  symbol ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 0 0)

theorem value_mul (M N : levelThree) : value (M*N) = value M * value N := by
  have hM : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  have hN : (N : SL(2,O)) 0 0 * (N : SL(2,O)) 1 1 -
      (N : SL(2,O)) 0 1 * (N : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (N : SL(2,O)).property
  have hh := kubota_mul ((M : SL(2,O)) 0 0) ((M : SL(2,O)) 0 1)
    ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 1 1)
    ((N : SL(2,O)) 0 0) ((N : SL(2,O)) 0 1)
    ((N : SL(2,O)) 1 0) ((N : SL(2,O)) 1 1) hM hN
    (levelThree_primary M) (levelThree_primary N)
    (levelThree_upper M) (levelThree_lower M) (levelThree_lower N)
  change symbol (((M : SL(2,O)) * (N : SL(2,O))) 1 0)
    (((M : SL(2,O)) * (N : SL(2,O))) 0 0) = _
  simpa only [value, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using hh

@[simp] theorem value_one : value 1 = 1 := by
  change symbol (0 : O) 1 = 1
  exact symbol_one 0

def character : levelThree →* O where
  toFun := value
  map_one' := value_one
  map_mul' := value_mul

theorem value_isUnit (M : levelThree) : IsUnit (value M) :=
  (Group.isUnit M).map character

theorem value_zero_lower_left (M : levelThree) (hc : (M : SL(2,O)) 1 0 = 0) :
    value M = 1 := by
  have hm : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd := (M : SL(2,O)).property
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using hd
  have ha := A3_primary_unit_eq_one _ (IsUnit.of_mul_eq_one _ hm) (levelThree_primary M)
  simp only [value, hc, ha, symbol_one]

theorem value_cube (M : levelThree) : value M ^ 3 = 1 := by
  apply symbol_cube_of_isCoprime _ _ (levelThree_primary M)
  have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 1 1, ?_⟩
  linear_combination hd

def complexCharacter : levelThree →* ℂ :=
  ConcreteTraceCRT.eisEmbedding.toMonoidHom.comp character

theorem complexCharacter_cube (M : levelThree) : complexCharacter M ^ 3 = 1 := by
  change ConcreteTraceCRT.eisEmbedding (value M) ^ 3 = 1
  rw [← map_pow, value_cube, map_one]

theorem norm_complexCharacter (M : levelThree) : ‖complexCharacter M‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm (complexCharacter_cube M)

end CubicKubota

end

end OAI
end OAIOriginalModule0117

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson
Source SHA256: f232672f377173ca9f828f3ce1c77489054d642e327a11916adbc97bf27f28d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0118


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

section

open scoped BigOperators Classical SchwartzMap ContDiff
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (activeGaussRowFactor)

theorem masked_pair_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let n := ∏ i : activeSupport T S, p i.val
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z) *
      W (‖eisEmbedding z‖ ^ 2 / Y)) =
    ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
          ∑' k : O, paperRadialFourier W
            (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
              activeGaussRowFactor p hp hinj hg T S e k := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let Q := activePrimes P T S
  let q : activeSupport T S → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime P hinj T S
  let j := activeExponent T S
  let row := finiteSexticRow Q (fun i => hg i.val) j
  let n := ∏ i, q i
  have hr (z : O) : star (finiteSquarefreeRow P hg T z) * finiteSquarefreeRow P hg S z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask, row, Q, j]
  have h := canonical_masked_radial_poisson_collected P hinj M Q hQ
    (fun i => hg i.val) (fun i => hc i.val) j
    (activeExponent_ne_zero T S) (activeExponent_lt_six T S) W Y hY
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q
  dsimp only at h
  rw [hn] at h
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset
    (fun E => let e := primeSubsetGenerator P E
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
        (‖eisEmbedding e‖ ^ 2 : ℝ))
    (fun E t => let e := primeSubsetGenerator P E
      paperRadialFourier W (Y * t / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)))
  calc
    _ = ∑' z : O, rowCoprimeMask P M z * row z * W (‖eisEmbedding z‖ ^ 2 / Y) := by
      apply tsum_congr
      intro z
      rw [hr]
    _ = ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
          ∑ E ∈ M.powerset,
            ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row (primeSubsetGenerator P E) /
              (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 : ℝ)) *
            ∑' k : O, star (row k) * paperRadialFourier W
              (Y * ‖eisEmbedding k‖ ^ 2 /
                (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))) := by
      rw [h]
      ring
    _ = _ := by
      rw [ht]
      simp only [Finset.mul_sum, ← tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      apply tsum_congr
      intro k
      dsimp only [activeGaussRowFactor]
      ring

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (columnLog primeProductNorm firstDualScale normalizedColumn)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondGaussTerm (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S *
    secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
  (supportMobius (fun i => Ideal.span {p i}) T *
    secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
    activeGaussRowFactor p hp hinj hg T S e k

def actualSecondKernel (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T)) *
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T
    else 0

def secondLogTest (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) : ℂ :=
  (V (columnLog p X S) *
    (if negative then star (logPhase t (-(columnLog p X S))) else logPhase t (-(columnLog p X S)))) /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)

theorem secondGaussTerm_log_twist (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t : ℝ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T =
    (logPhase t (-(columnLog p X₁ S)) * logPhase t (-(columnLog p X₂ T))) *
      (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) := by
  simp only [secondGaussTerm, secondInputCoefficient, secondLogTest, normalizedColumn,
    ite_true, Bool.false_eq_true, ite_false, star_mul, star_div₀, star_star,
    one_div, star_inv₀]
  ring

theorem actualSecondKernel_eq_integral
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, star (V₁ x) * V₂ y *
      paperRadialFourier W (firstDualScale p ∅ Y X₁ X₂ e k * Real.exp (-x-y)) =
      ∫ t : ℝ, (star (V₁ x) * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false)) volume ∧
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
  let G := fun (t : ℝ) (S T : Finset ι) => if Disjoint S T then b t *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T else 0
  have hGi (S T : Finset ι) : Integrable (fun t => G t S T) volume := by
    by_cases hd : Disjoint S T
    · simp only [G, ite_eq_left hd, secondGaussTerm_log_twist]
      convert FirstPassCubeLabels.integrable_log_pair b (-(columnLog p X₁ S)) (-(columnLog p X₂ T))
        (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
            (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) using 1
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGs (t : ℝ) : (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) =
      b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
    simp only [G, secondActualPair, secondGaussTerm, Finset.mul_sum, mul_ite, mul_zero]
  have hI : Integrable (fun t => ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) volume :=
    integrable_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T))
  constructor
  · simpa only [hGs] using hI
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hGs)]
    rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T)), Finset.mul_sum]
    unfold actualSecondKernel
    apply Finset.sum_congr rfl
    intro S hS
    rw [integral_finsetSum _ (fun T _ => hGi S T), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hd : Disjoint S T
    · simp only [G, ite_eq_left hd, secondGaussTerm_log_twist]
      have harg := FirstPassCubeLabels.actual_radial_argument p hp S T ∅ hd
        (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) Y X₁ X₂ hX₁ hX₂ e k
      simp only [Finset.union_empty] at harg
      rw [← harg]
      have hn : secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T =
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
        simp only [secondGaussTerm, secondInputCoefficient, normalizedColumn, one_div,
          mul_one, star_mul, map_inv₀, Complex.star_def, Complex.conj_ofReal]
        ring
      rw [hn]
      rw [Finset.prod_union hd]
      simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
      have hh := congrArg (fun z : ℂ => (Y : ℂ) * z *
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T)
        (hsep (columnLog p X₁ S) (columnLog p X₂ T))
      rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const] at hh
      convert hh using 1
      · ring
      · rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        ring
    · simp [hd, G]

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildSum_continuous
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) :
    Continuous (fun t : ℝ => secondChildSum p hp hcop hg F V Ψ m r c d e k (H t)) := by
  unfold secondChildSum
  apply continuous_finsetSum
  intro N hN
  have hh := hc (V ∪ N)
  unfold secondChildColumn
  fun_prop

theorem secondChildSum_uniform_bound
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖secondChildSum p hp hcop hg F V Ψ m r c d e k (H t)‖ ≤ M := by
  refine ⟨∑ N ∈ (F \ V).powerset,
    ‖secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H 0 (V ∪ U)) N‖, by positivity, ?_⟩
  intro t
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro N hN
  simp only [secondChildColumn, norm_mul, hn]
  exact le_rfl

theorem secondTotalEnergy_nonneg
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) :
    0 ≤ secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H negative := by
  unfold secondTotalEnergy
  positivity

theorem secondTotalEnergy_continuous
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) (negative : Bool) :
    Continuous (fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) := by
  unfold secondTotalEnergy
  apply continuous_finsetSum
  intro z hz
  apply continuous_finsetSum
  intro V hV
  exact continuous_const.mul ((secondChildSum_continuous p hp hcop hg F V
    (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
    m r c d e (if negative then k else -k) H hc).norm.pow 2)

theorem secondTotalEnergy_uniform_bound
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative ≤ M := by
  choose M hM hbound using fun (z : SecondRayIndex) (V : Finset ι) =>
    secondChildSum_uniform_bound p hp hcop hg F V
      (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
      m r c d e (if negative then k else -k) H hn
  refine ⟨∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V)‖ * (M z V)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro z hz
  apply Finset.sum_le_sum
  intro V hV
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hbound z V t) 2) (norm_nonneg _)

theorem secondTotalEnergy_integrable
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S))
    (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) volume := by
  obtain ⟨M, hM, hb⟩ := secondTotalEnergy_uniform_bound p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hn negative
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hc negative).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative)]
      exact hb t)

theorem second_integral_norm_le_energy
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => H₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => H₂ t S))
    (hn₁ : ∀ t S, ‖H₁ t S‖ = ‖H₁ 0 S‖)
    (hn₂ : ∀ t S, ‖H₂ t S‖ = ‖H₂ 0 S‖) (b : 𝓢(ℝ, ℂ)) :
    ‖∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false) := by
  let E₁ := fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  let E₂ := fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  let w := fun t : ℝ => ‖b t‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  have hw : ∀ t, 0 ≤ w t := fun t => norm_nonneg _
  have i₁ : Integrable (fun t => w t * E₁ t) volume :=
    secondTotalEnergy_integrable p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ hn₁ true b
  have i₂ : Integrable (fun t => w t * E₂ t) volume :=
    secondTotalEnergy_integrable p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ hn₂ false b
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ true))
  have hg' : Continuous g := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ false))
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
  have hnorm : ‖∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (secondActualPair_norm_le p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)) (hw t))
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

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (firstDualScale firstLogDensity primeProductNorm_pos)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (S : Finset ι) :
    Continuous (fun t : ℝ => secondLogTest p V X t negative S) := by
  have h := FourierBridge.logPhase_continuous_left (-(FirstPassCubeLabels.columnLog p X S))
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogTest_norm (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) :
    ‖secondLogTest p V X t negative S‖ = ‖secondLogTest p V X 0 negative S‖ := by
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true,
    norm_div, norm_mul, norm_star, FourierBridge.logPhase_norm]

def secondKernelEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k
    (secondLogTest p V X t negative) negative

theorem actual_second_kernel_uniform_energy_envelope
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ x, V₂ x ≠ 0 → |x| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ e k : O, e ≠ 0 → k ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p ∅ Y X₁ X₂ e k) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ (Ψ₁ Ψ₂ : O →* ℂ) (m r c d : O),
          ‖actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y‖ ≤
            Y * Real.sqrt (secondKernelEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k V₁ X₁ true b) *
              Real.sqrt (secondKernelEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k V₂ X₂ false b) := by
  have hV₁' : ∀ x, star (V₁ x) ≠ 0 → |x| ≤ M₁ := by
    intro x hx
    exact hV₁ x (by intro h; simp [h] at hx)
  obtain ⟨K, hK, hs⟩ := FirstPassCubeLabels.two_variable_radial_envelope W (fun x => star (V₁ x)) V₂
    M₁ M₂ hM₁ hM₂ hV₁' hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro Y hY e k he hk
  have hR : 0 < firstDualScale p ∅ Y X₁ X₂ e k := by
    unfold firstDualScale
    exact div_pos (mul_pos hY (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hk)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro Ψ₁ Ψ₂ m r c d
  rw [(actualSecondKernel_eq_integral p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y
    hX₁ hX₂ b hsep).2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have hi := second_integral_norm_le_energy p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k
    (fun t => secondLogTest p V₁ X₁ t true) (fun t => secondLogTest p V₂ X₂ t false)
    (secondLogTest_continuous p V₁ X₁ true) (secondLogTest_continuous p V₂ X₂ false)
    (fun t S => secondLogTest_norm p V₁ X₁ t true S)
    (fun t S => secondLogTest_norm p V₂ X₂ t false S) b
  change Y * _ ≤ Y * Real.sqrt _ * Real.sqrt _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi hY.le

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem second_energy_selected_family {κ : Type*} [Fintype κ] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (P : κ → Ideal O × O → ℂ) (sel : OldTuple → κ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (sel x) (newLabel x, newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : κ, ∑ z ∈ t, ‖P u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := SecondPassFiber.second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale P sel hb0 hB hL hvalid hmap ht hnorm hw
  calc
    _ ≤ ∑ x ∈ s, ‖w x‖ * ∑ u : κ, ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum
        (s := Finset.univ) (a := sel x)
        (f := fun u : κ => ‖P u (newLabel x, newRow x)‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ (sel x))
    _ = ∑ u : κ, ∑ x ∈ s, ‖w x‖ * ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ u : κ, B * C * (lengthScale * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P u z‖ ^ 2 := by
      exact Finset.sum_le_sum (fun u _ => hb s t b0 w (P u) B lengthScale hb0 hB hL hvalid hmap ht hnorm hw)
    _ = _ := by rw [Finset.mul_sum]

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)

local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def tupleLabelElement (x : OldTuple) : O :=
  idealGenerator (x.core 0) * idealGenerator (x.core 1) * idealGenerator (x.core 2) * idealGenerator x.v

theorem tupleLabelElement_span (x : OldTuple) :
    Ideal.span {tupleLabelElement x} = newLabel x := by
  simp only [tupleLabelElement, newLabel, ← Ideal.span_singleton_mul_span_singleton, span_idealGenerator]

theorem exists_label_unit (f : O) (I : Ideal O) (hf : Ideal.span {f} = I) :
    ∃ u : Oˣ, f = (u : O) * idealGenerator I := by
  have hs : Ideal.span {idealGenerator I} = Ideal.span {f} := (span_idealGenerator I).trans hf.symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def tupleLabelUnit (x : OldTuple) : Oˣ :=
  Classical.choose (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

theorem tupleLabelUnit_spec (x : OldTuple) :
    tupleLabelElement x = (tupleLabelUnit x : O) * idealGenerator (newLabel x) :=
  Classical.choose_spec (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (f y : O) : ℂ :=
  ∑ N ∈ F.powerset, secondChildColumn p hp hcop hg Ψ m f y H N

def idealChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ) (z : Ideal O × O) : ℂ :=
  fixedChildRow p hp hcop hg F Ψ m H ((u : O) * idealGenerator z.1)
    (if negative then -z.2 else z.2)

theorem tuple_child_eq_unit_sector (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (x : OldTuple) :
    fixedChildRow p hp hcop hg F Ψ m H (tupleLabelElement x)
      (if negative then -newRow x else newRow x) =
    idealChildRow p hp hcop hg F Ψ m H negative (tupleLabelUnit x) (newLabel x, newRow x) := by
  rw [tupleLabelUnit_spec]
  rfl

theorem fixed_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hp hcop hg F Ψ m H (tupleLabelElement x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw
  have hh := hb s t b0 w B lengthScale (idealChildRow p hp hcop hg F Ψ m H negative)
    tupleLabelUnit hb0 hB hL hvalid hmap ht hnorm hw
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [tuple_child_eq_unit_sector]

theorem idealChildRow_unit_energy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (t : Finset (Ideal O × O)) (E : ℝ)
    (hE : ∀ u : Oˣ, (∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ E) :
    (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ 6 * E := by
  have hc : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  calc
    _ ≤ ∑ u : Oˣ, E := Finset.sum_le_sum (fun u _ => hE u)
    _ = _ := by simp [hc]

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0118

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.Rows
Source SHA256: e1dc4f2c8f0112180e67fcde0714b1e6b5c029e6b87adfecab3860a573a508aa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0119


namespace OAI

noncomputable section

namespace CubicEisenstein

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
open scoped BigOperators Classical MatrixGroups

section
abbrev K := ActualEisensteinCubic.K
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def row (M : levelThree) : Fin 2 → O := (M : SL(2,O)) 1

lemma row_mul (M N : levelThree) :
    row (M*N) = Matrix.vecMul (row M) (N : SL(2,O)) := by
  funext j
  simp only [row, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma row_ne_zero (M : levelThree) : row M ≠ 0 := by
  intro hz
  have hc : (M : SL(2,O)) 1 0 = 0 := congrFun hz 0
  have hd : (M : SL(2,O)) 1 1 = 0 := congrFun hz 1
  have h : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

lemma character_eq_of_row_eq (M N : levelThree) (hr : row M = row N) :
    complexCharacter M = complexCharacter N := by
  have hrow : row (M*N⁻¹) = row 1 := by
    rw [row_mul, hr, ← row_mul]
    simp
  have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0 = 0 := by
    simpa [row, Matrix.one_apply] using congrFun hrow 0
  have hchar : complexCharacter (M*N⁻¹) = 1 := by
    change eisEmbedding (value (M*N⁻¹)) = 1
    rw [value_zero_lower_left _ hc, map_one]
  calc
    complexCharacter M = complexCharacter ((M*N⁻¹)*N) := by congr 1; group
    _ = complexCharacter (M*N⁻¹) * complexCharacter N := map_mul _ _ _
    _ = complexCharacter N := by rw [hchar, one_mul]

lemma row_eq_one_of_lower_left_zero (M : levelThree)
    (hc : (M : SL(2,O)) 1 0 = 0) : row M = row 1 := by
  have hdet : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
        (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
    simpa only [hc, mul_zero, sub_zero] using hd
  have ha := A3_primary_unit_eq_one _ (IsUnit.of_mul_eq_one _ hdet)
    (levelThree_primary M)
  have hd : (M : SL(2,O)) 1 1 = 1 := by simpa only [ha, one_mul] using hdet
  funext j
  fin_cases j <;> simp [row, hc, hd]

def cuspStabilizer : Subgroup levelThree where
  carrier := {M | row M = row 1}
  one_mem' := rfl
  mul_mem' := by
    intro M N hM hN
    change row (M*N) = row 1
    rw [row_mul, hM, ← row_mul]
    simpa using hN
  inv_mem' := by
    intro M hM
    have h : row (M*M⁻¹) = row 1 := by simp
    rw [row_mul, hM, ← row_mul] at h
    simpa using h

lemma mem_cuspStabilizer_iff (M : levelThree) :
    M ∈ cuspStabilizer ↔ (M : SL(2,O)) 1 0 = 0 := by
  constructor
  · intro h
    simpa [row, Matrix.one_apply] using congrFun h 0
  · exact row_eq_one_of_lower_left_zero M

lemma row_eq_iff_left_cusp (M N : levelThree) : row M = row N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  constructor
  · intro h
    refine ⟨M*N⁻¹, ?_, by group⟩
    change row (M*N⁻¹) = row 1
    rw [row_mul, h, ← row_mul]
    simp
  · rintro ⟨T,hT,rfl⟩
    change row T = row 1 at hT
    rw [row_mul, hT, ← row_mul, one_mul]

def cuspRelation : Setoid levelThree := Setoid.ker row

abbrev CuspCosets := Quotient cuspRelation

def cosetOf (M : levelThree) : CuspCosets := Quotient.mk _ M

lemma cosetOf_eq_iff (M N : levelThree) : cosetOf M = cosetOf N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  rw [← row_eq_iff_left_cusp]
  exact Quotient.eq

def cosetRow : CuspCosets → (Fin 2 → O) :=
  Quotient.lift row (fun _ _ h => h)

@[simp] lemma cosetRow_cosetOf (M : levelThree) : cosetRow (cosetOf M) = row M := rfl

lemma cosetRow_injective : Function.Injective cosetRow := by
  intro x y
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      intro h
      exact Quotient.sound h

lemma cosetRow_ne_zero (x : CuspCosets) : cosetRow x ≠ 0 := by
  induction x using Quotient.inductionOn with | _ M => exact row_ne_zero M

def cosetCharacter : CuspCosets → ℂ :=
  Quotient.lift complexCharacter (fun M N h => character_eq_of_row_eq M N h)

@[simp] lemma cosetCharacter_cosetOf (M : levelThree) :
    cosetCharacter (cosetOf M) = complexCharacter M := rfl

lemma norm_cosetCharacter (x : CuspCosets) : ‖cosetCharacter x‖ = 1 := by
  induction x using Quotient.inductionOn with | _ M => exact norm_complexCharacter M

def rightTranslate (M : levelThree) : CuspCosets → CuspCosets :=
  Quotient.map (fun N => N*M) (by
    intro A B h
    change row (A*M) = row (B*M)
    rw [row_mul, row_mul, show row A = row B from h])

@[simp] lemma rightTranslate_cosetOf (M N : levelThree) :
    rightTranslate M (cosetOf N) = cosetOf (N*M) := rfl

lemma rightTranslate_mul (M N : levelThree) (x : CuspCosets) :
    rightTranslate N (rightTranslate M x) = rightTranslate (M*N) x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf ((A*M)*N) = cosetOf (A*(M*N))
    rw [mul_assoc]

@[simp] lemma rightTranslate_one (x : CuspCosets) : rightTranslate 1 x = x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf (A*1) = cosetOf A
    rw [mul_one]

def rightEquiv (M : levelThree) : CuspCosets ≃ CuspCosets where
  toFun := rightTranslate M
  invFun := rightTranslate M⁻¹
  left_inv x := by rw [rightTranslate_mul]; simp
  right_inv x := by rw [rightTranslate_mul]; simp

lemma cosetRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetRow (rightEquiv M x) = Matrix.vecMul (cosetRow x) (M : SL(2,O)) := by
  induction x using Quotient.inductionOn with | _ N => exact row_mul N M

lemma cosetCharacter_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetCharacter (rightEquiv M x) = cosetCharacter x * complexCharacter M := by
  induction x using Quotient.inductionOn with | _ N => exact map_mul _ _ _

def complexMatrix : levelThree →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) eisEmbedding).comp levelThree.subtype

lemma complexMatrix_apply (M : levelThree) (i j : Fin 2) :
    complexMatrix M i j = eisEmbedding ((M : SL(2,O)) i j) := rfl

def embeddedRow (x : CuspCosets) : Fin 2 → ℂ := eisEmbedding ∘ cosetRow x

lemma embeddedRow_ne_zero (x : CuspCosets) : embeddedRow x ≠ 0 := by
  intro hz
  apply cosetRow_ne_zero x
  funext i
  apply eisEmbedding_injective
  simpa only [embeddedRow, Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i

lemma embeddedRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    embeddedRow (rightEquiv M x) = Matrix.vecMul (embeddedRow x) (complexMatrix M : SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow, Function.comp_apply, cosetRow_rightEquiv,
    Matrix.vecMul, dotProduct, map_sum, map_mul, complexMatrix_apply]

end

section
open ActualEisensteinCubic ConcreteTraceCRT

def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))

instance : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance

instance : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance

def integerPoint (n : (Fin 2 × Fin 2) → ℤ) : integerLattice :=
  ⟨fun i => (n i : ℝ), by
    rw [integerLattice, (Pi.basisFun ℝ (Fin 2 × Fin 2)).mem_span_iff_repr_mem ℤ]
    intro i
    exact ⟨n i, by simp⟩⟩

lemma integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  funext i
  have h := congrArg (fun x : integerLattice => (x : (Fin 2 × Fin 2) → ℝ) i) hab
  change (a i : ℝ) = (b i : ℝ) at h
  exact_mod_cast h

lemma integerPoint_norm (n : (Fin 2 × Fin 2) → ℤ) : ‖integerPoint n‖ = ‖n‖ := by
  change ‖fun i => (n i : ℝ)‖ = ‖n‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm n i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm (fun i => (n i : ℝ)) i

lemma summable_integer_four_rpow (k : ℝ) (hk : 4 < k) :
    Summable (fun n : (Fin 2 × Fin 2) → ℤ => ‖n‖ ^ (-k)) := by
  have hf : Module.finrank ℤ integerLattice = 4 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := ZLattice.summable_norm_rpow integerLattice (-k) (by rw [hf]; norm_num; linarith)
  apply (hs.comp_injective integerPoint_injective).congr
  intro n
  change ‖integerPoint n‖ ^ (-k) = ‖n‖ ^ (-k)
  rw [integerPoint_norm]

def rowCoordinates (v : Fin 2 → O) : (Fin 2 × Fin 2) → ℤ :=
  fun i => if i.2 = 0 then (ActualEisensteinCoordinates.coords (v i.1)).1
    else (ActualEisensteinCoordinates.coords (v i.1)).2

lemma rowCoordinates_injective : Function.Injective rowCoordinates := by
  intro v w hvw
  funext i
  apply latticeCoordEquiv.injective
  apply Prod.ext
  · exact congrFun hvw (i,0)
  · exact congrFun hvw (i,1)

lemma coordinates_norm_bound (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ 2 * ‖fun i => eisEmbedding (v i)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hi := norm_le_pi_norm (fun j => eisEmbedding (v j)) i.1
  have hq := eisEmbedding_eval_norm_sq
    (ActualEisensteinCoordinates.coords (v i.1)).1
    (ActualEisensteinCoordinates.coords (v i.1)).2
  rw [ActualEisensteinCoordinates.eval_coords] at hq
  push_cast at hq
  have hcoord (a b : ℝ) (t : ℝ) (ht : 0 ≤ t)
      (heq : t ^ 2 = a*a-a*b+b*b) : |a| ≤ 2*t ∧ |b| ≤ 2*t := by
    constructor <;> apply (abs_le).mpr <;> constructor <;>
      nlinarith [sq_nonneg (a-b), sq_nonneg (a+b), sq_nonneg (a-2*b), sq_nonneg (b-2*a)]
  have hh := hcoord _ _ ‖eisEmbedding (v i.1)‖ (norm_nonneg _) hq
  dsimp only [rowCoordinates]
  split_ifs
  · simpa only [Int.norm_eq_abs] using hh.1.trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  · simpa only [Int.norm_eq_abs] using hh.2.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def rowEnergy (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

lemma rowEnergy_nonneg (v : Fin 2 → ℂ) : 0 ≤ rowEnergy v := by
  unfold rowEnergy; positivity

lemma norm_le_sqrt_rowEnergy (v : Fin 2 → ℂ) : ‖v‖ ≤ Real.sqrt (rowEnergy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply Real.le_sqrt_of_sq_le
  fin_cases i <;> dsimp [rowEnergy] <;> nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

lemma rowEnergy_pos (v : Fin 2 → ℂ) (hv : v ≠ 0) : 0 < rowEnergy v := by
  have h := norm_le_sqrt_rowEnergy v
  have hn := norm_pos_iff.mpr hv
  exact Real.sqrt_pos.mp (lt_of_lt_of_le hn h)

def rowOperator (g : SL(2,ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearMapRight' (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap

@[simp] lemma rowOperator_apply (g : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator g v = Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma rowOperator_mul (g h : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator h (rowOperator g v) = rowOperator (g*h) v := by
  simp only [rowOperator_apply, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul]

@[simp] lemma rowOperator_one (v : Fin 2 → ℂ) : rowOperator 1 v = v := by
  simp only [rowOperator_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

lemma rowOperator_ne_zero (g : SL(2,ℂ)) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    rowOperator g v ≠ 0 := by
  intro hz
  have h := congrArg (rowOperator g⁻¹) hz
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one, map_zero] at h
  exact hv h

def rowBound (g : SL(2,ℂ)) : ℝ := 2 * (1 + ‖rowOperator g⁻¹‖)

lemma rowBound_pos (g : SL(2,ℂ)) : 0 < rowBound g := by unfold rowBound; positivity

lemma coordinates_le_transformed_energy (g : SL(2,ℂ)) (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ rowBound g *
      Real.sqrt (rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))) := by
  have hi := (rowOperator g⁻¹).le_opNorm (rowOperator g (fun i => eisEmbedding (v i)))
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one] at hi
  have hb := coordinates_norm_bound v
  have he := norm_le_sqrt_rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (rowOperator g⁻¹))
  dsimp only [rowBound]
  nlinarith [Real.sqrt_nonneg (rowEnergy (rowOperator g (fun i => eisEmbedding (v i))))]

lemma norm_coordinates_ne_zero (x : CuspCosets) : 0 < ‖rowCoordinates (cosetRow x)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply cosetRow_ne_zero x
  apply rowCoordinates_injective
  have hz0 : rowCoordinates (0 : Fin 2 → O) = 0 := by
    apply norm_le_zero_iff.mp
    have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → O) i)) =
        (0 : Fin 2 → ℂ) := by
      funext i
      exact map_zero _
    have hh := coordinates_norm_bound (0 : Fin 2 → O)
    rw [he, norm_zero, mul_zero] at hh
    exact hh
  rw [hz0]
  exact hz

def summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) : ℂ :=
  (cosetCharacter x)⁻¹ *
    (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s)

lemma norm_summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    ‖summand g s x‖ = rowEnergy (rowOperator g (embeddedRow x)) ^ (-s.re) := by
  rw [summand, norm_mul, norm_inv, norm_cosetCharacter, inv_one, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x)))]
  rfl

lemma norm_summand_bound (g : SL(2,ℂ)) (s : ℂ) (hs : 0 < s.re) (x : CuspCosets) :
    ‖summand g s x‖ ≤ (rowBound g) ^ (2*s.re) *
      ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re)) := by
  rw [norm_summand]
  have hn := norm_coordinates_ne_zero x
  have hb := rowBound_pos g
  have he := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  have hbd := coordinates_le_transformed_energy g (cosetRow x)
  change ‖rowCoordinates (cosetRow x)‖ ≤ rowBound g *
    Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) at hbd
  have hle : (‖rowCoordinates (cosetRow x)‖ / rowBound g) ^ 2 ≤
      rowEnergy (rowOperator g (embeddedRow x)) := by
    have hd : ‖rowCoordinates (cosetRow x)‖ / rowBound g ≤
        Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hbd)
    have hsq := Real.sq_sqrt he.le
    nlinarith [div_pos hn hb, Real.sqrt_nonneg (rowEnergy (rowOperator g (embeddedRow x)))]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (div_pos hn hb)) hle (by linarith : -s.re ≤ 0)
  convert hp using 1
  rw [← Real.rpow_natCast_mul (div_nonneg hn.le hb.le) 2 (-s.re),
    Real.div_rpow hn.le hb.le]
  simp only [Nat.cast_ofNat, mul_neg, Real.rpow_neg hb.le, div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

theorem summable_norm_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => ‖summand g s x‖) := by
  have hsum := summable_integer_four_rpow (2*s.re) (by linarith)
  have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
    rowCoordinates_injective.comp cosetRow_injective
  have hcomp : Summable (fun x : CuspCosets => ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re))) := by
    apply (hsum.comp_injective hinj).congr
    intro x
    rfl
  exact (hcomp.mul_left ((rowBound g) ^ (2*s.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun x => norm_summand_bound g s (by linarith) x)

theorem summable_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (summand g s) := (summable_norm_summand g s hs).of_norm

def eisenstein (g : SL(2,ℂ)) (s : ℂ) : ℂ := ∑' x : CuspCosets, summand g s x

lemma transformedRow_rightEquiv (M : levelThree) (g : SL(2,ℂ)) (x : CuspCosets) :
    rowOperator g (embeddedRow (rightEquiv M x)) =
      rowOperator (complexMatrix M * g) (embeddedRow x) := by
  rw [embeddedRow_rightEquiv, ← rowOperator_apply, rowOperator_mul]

lemma summand_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (complexMatrix M * g) s x =
      complexCharacter M * summand g s (rightEquiv M x) := by
  have hM : complexCharacter M ≠ 0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  simp only [summand, cosetCharacter_rightEquiv, transformedRow_rightEquiv,
    mul_inv_rev]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hM, one_mul]

theorem eisenstein_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    eisenstein (complexMatrix M * g) s = complexCharacter M * eisenstein g s := by
  have hleft := summable_summand (complexMatrix M * g) s hs
  have hright := summable_summand g s hs
  have hreindex : HasSum (fun x : CuspCosets => summand g s (rightEquiv M x))
      (eisenstein g s) := (rightEquiv M).hasSum_iff.mpr hright.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact hleft.hasSum.unique (hscale.congr_fun (fun x => summand_automorphy M g s x))

lemma summand_differentiable (g : SL(2,ℂ)) (x : CuspCosets) :
    Differentiable ℂ (fun s : ℂ => summand g s x) := by
  have hq : (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))).ne'
  exact ((differentiable_id.neg).const_cpow (Or.inl hq)).const_mul _

lemma norm_summand_strip (g : SL(2,ℂ)) (a b : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : CuspCosets) :
    ‖summand g s x‖ ≤ ‖summand g (a : ℂ) x‖ + ‖summand g (b : ℂ) x‖ := by
  simp only [norm_summand, Complex.ofReal_re]
  have hq := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  by_cases hq1 : 1 ≤ rowEnergy (rowOperator g (embeddedRow x))
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg ha)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hq (le_of_not_ge hq1)
        (neg_le_neg hb)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _))

theorem eisenstein_differentiableOn_strip (g : SL(2,ℂ)) (a b : ℝ)
    (ha : 2 < a) (hab : a < b) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | a < s.re ∧ s.re < b} := by
  have hsa := summable_norm_summand g (a : ℂ) (by simpa using ha)
  have hsb := summable_norm_summand g (b : ℂ) (by simpa using lt_trans ha hab)
  apply Complex.differentiableOn_tsum_of_summable_norm (hsa.add hsb)
    (fun x => (summand_differentiable g x).differentiableOn)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro x s hs
    exact norm_summand_strip g a b s hs.1.le hs.2.le x

theorem eisenstein_differentiableAt (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    DifferentiableAt ℂ (eisenstein g) s := by
  let a := (2+s.re)/2
  let b := s.re+1
  have ha : 2 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hsU : s ∈ {z : ℂ | a < z.re ∧ z.re < b} := by
    constructor <;> dsimp [a,b] <;> linarith
  exact (eisenstein_differentiableOn_strip g a b ha hab s hsU).differentiableAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hsU)

theorem eisenstein_differentiableOn (g : SL(2,ℂ)) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | 2 < s.re} := by
  intro s hs
  exact (eisenstein_differentiableAt g s hs).differentiableWithinAt

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹], by
    have hr : (Real.sqrt v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
    simp [Matrix.det_fin_two, hr]⟩

lemma rowOperator_upperSection_zero (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 0 = u 0 * (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma rowOperator_upperSection_one (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 1 = (u 0*z + u 1) / (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

def heightDenominator (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  ‖u 0*z + u 1‖ ^ 2 + ‖u 0‖ ^ 2 * v ^ 2

lemma rowEnergy_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowEnergy (rowOperator (upperSection z v hv) u) = heightDenominator z v u / v := by
  rw [rowEnergy, rowOperator_upperSection_zero, rowOperator_upperSection_one,
    norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
    mul_pow, div_pow, Real.sq_sqrt hv.le]
  unfold heightDenominator
  field_simp
  ring

lemma heightDenominator_pos (z : ℂ) (v : ℝ) (hv : 0 < v)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) : 0 < heightDenominator z v u := by
  have h := rowEnergy_pos _ (rowOperator_ne_zero (upperSection z v hv) u hu)
  rw [rowEnergy_upperSection] at h
  exact ((div_pos_iff.mp h).resolve_right (by rintro ⟨_,hneg⟩; linarith)).1

def transformedHeight (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  v / heightDenominator z v u

lemma summand_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    summand (upperSection z v hv) s x = (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s := by
  rw [summand, rowEnergy_upperSection]
  congr 1
  have hq := heightDenominator_pos z v hv (embeddedRow x) (embeddedRow_ne_zero x)
  have hinv : (transformedHeight z v (embeddedRow x) : ℂ) =
      ((heightDenominator z v (embeddedRow x) / v : ℝ) : ℂ)⁻¹ := by
    simp only [transformedHeight, Complex.ofReal_div, inv_div]
  rw [hinv, Complex.inv_cpow_ofReal_nonneg (div_nonneg hq.le hv.le), Complex.cpow_neg]

def upperEisenstein (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) : ℂ :=
  eisenstein (upperSection z v hv) s

theorem upperEisenstein_eq_source_series (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' x : CuspCosets, (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s :=
  tsum_congr (summand_upperSection z v hv s)

theorem source_series_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s) :=
  (summable_summand (upperSection z v hv) s hs).congr (summand_upperSection z v hv s)

lemma ofReal_rowEnergy (u : Fin 2 → ℂ) :
    (rowEnergy u : ℂ) = dotProduct u (star u) := by
  simp only [rowEnergy, Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, Complex.mul_conj]

lemma rowEnergy_unitary (k : SL(2,ℂ))
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (u : Fin 2 → ℂ) : rowEnergy (rowOperator k u) = rowEnergy u := by
  apply Complex.ofReal_injective
  rw [ofReal_rowEnergy, ofReal_rowEnergy, rowOperator_apply, Matrix.star_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  change (k : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.conjTranspose (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 at hu
  rw [hu, Matrix.vecMul_one]

theorem eisenstein_right_unitary (g k : SL(2,ℂ)) (s : ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    eisenstein (g*k) s = eisenstein g s := by
  apply tsum_congr
  intro x
  simp only [summand, ← rowOperator_mul, rowEnergy_unitary k hk]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0119

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
Source SHA256: 7e26e3e66e8e46814a84e5a03d223547d497327f5177a8f9b9306016f253c29d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0120


namespace OAI

noncomputable section

namespace CubicEisenstein

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
open scoped BigOperators Classical MatrixGroups Matrix

section
open CubicKubota

def compactSubgroup : Subgroup (SL(2,ℂ)) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}
  one_mem' := (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
  mul_mem' := by
    intro a b ha hb
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ha hb
  inv_mem' := by
    intro k hk
    have hinv : (k⁻¹ : SL(2,ℂ)) * k = 1 := inv_mul_cancel k
    have hmat : ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg
          (fun a : SL(2,ℂ) => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk

abbrev HyperbolicSpace := SL(2,ℂ) ⧸ compactSubgroup

def hyperbolicEisenstein (s : ℂ) : HyperbolicSpace → ℂ :=
  Quotient.lift (fun g => eisenstein g s) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (eisenstein_right_unitary g (g⁻¹*h) s hk).symm)

@[simp] lemma hyperbolicEisenstein_mk (s : ℂ) (g : SL(2,ℂ)) :
    hyperbolicEisenstein s (g : HyperbolicSpace) = eisenstein g s := rfl

theorem hyperbolicEisenstein_automorphy (M : levelThree) (s : ℂ) (hs : 2 < s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (complexMatrix M • w) =
      complexCharacter M * hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_automorphy M g s hs

def upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) : HyperbolicSpace :=
  (upperSection z v hv : HyperbolicSpace)

lemma hyperbolicEisenstein_upperPoint (s : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicEisenstein s (upperPoint z v hv) = upperEisenstein z v hv s := rfl

def complexBottomRow (g : SL(2,ℂ)) : Fin 2 → ℂ := g 1

lemma complexBottomRow_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) = rowOperator h (complexBottomRow g) := by
  funext j
  simp only [complexBottomRow, rowOperator_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma complexBottomRow_ne_zero (g : SL(2,ℂ)) : complexBottomRow g ≠ 0 := by
  intro hz
  have hc : g 1 0 = 0 := congrFun hz 0
  have hd : g 1 1 = 0 := congrFun hz 1
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

def liftedHeight (g : SL(2,ℂ)) : ℝ := (rowEnergy (complexBottomRow g))⁻¹

lemma liftedHeight_pos (g : SL(2,ℂ)) : 0 < liftedHeight g :=
  inv_pos.mpr (rowEnergy_pos _ (complexBottomRow_ne_zero g))

lemma liftedHeight_right_unitary (g k : SL(2,ℂ)) (hk : k ∈ compactSubgroup) :
    liftedHeight (g*k) = liftedHeight g := by
  simp only [liftedHeight, complexBottomRow_mul, rowEnergy_unitary k hk]

def hyperbolicHeight : HyperbolicSpace → ℝ :=
  Quotient.lift liftedHeight (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (liftedHeight_right_unitary g (g⁻¹*h) hk).symm)

@[simp] lemma hyperbolicHeight_mk (g : SL(2,ℂ)) :
    hyperbolicHeight (g : HyperbolicSpace) = liftedHeight g := rfl

lemma hyperbolicHeight_pos (w : HyperbolicSpace) : 0 < hyperbolicHeight w := by
  induction w using Quotient.inductionOn with | _ g => exact liftedHeight_pos g

theorem hyperbolicHeight_action_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (g • upperPoint z v hv) =
      v / (‖g 1 0*z + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * v ^ 2) := by
  change liftedHeight (g * upperSection z v hv) = _
  rw [liftedHeight, complexBottomRow_mul, rowEnergy_upperSection, inv_div]
  rfl

def cosetHeight (x : CuspCosets) : HyperbolicSpace → ℝ :=
  Quotient.lift (fun g : SL(2,ℂ) => (rowEnergy (rowOperator g (embeddedRow x)))⁻¹) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh, ← rowOperator_mul, rowEnergy_unitary (g⁻¹*h) hk])

lemma cosetHeight_cosetOf (M : levelThree) (w : HyperbolicSpace) :
    cosetHeight (cosetOf M) w = hyperbolicHeight (complexMatrix M • w) := by
  induction w using Quotient.inductionOn with | _ g =>
    change (rowEnergy (rowOperator g (embeddedRow (cosetOf M))))⁻¹ =
      liftedHeight (complexMatrix M * g)
    rw [liftedHeight, complexBottomRow_mul]
    rfl

theorem hyperbolicEisenstein_eq_height_series (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w = ∑' x : CuspCosets,
      (cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s := by
  induction w using Quotient.inductionOn with | _ g =>
    apply tsum_congr
    intro x
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem height_series_summable_norm (s : ℂ) (hs : 2 < s.re) (w : HyperbolicSpace) :
    Summable (fun x : CuspCosets =>
      ‖(cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s‖) := by
  induction w using Quotient.inductionOn with | _ g =>
    apply (summable_norm_summand g s hs).congr
    intro x
    congr 1
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem hyperbolicEisenstein_differentiableOn (w : HyperbolicSpace) :
    DifferentiableOn ℂ (fun s : ℂ => hyperbolicEisenstein s w) {s : ℂ | 2 < s.re} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_differentiableOn g

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperTranslation (a : O) : levelThree := by
  let M : SL(2,O) := ⟨!![1, 3*a; 0, 1], by simp⟩
  refine ⟨M, ?_⟩
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  have h3 : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (3 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) ((!![(1 : O), 3*a; 0, 1]) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  fin_cases i <;> fin_cases j <;> simp [h3, map_mul]

lemma complexCharacter_upperTranslation (a : O) : complexCharacter (upperTranslation a) = 1 := by
  change eisEmbedding (value (upperTranslation a)) = 1
  rw [value_zero_lower_left _ (by rfl), map_one]

lemma upperTranslation_section (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    complexMatrix (upperTranslation a) * upperSection z v hv =
      upperSection (z + 3*eisEmbedding a) v hv := by
  apply Subtype.ext
  funext i j
  change (((!![(1 : O), 3*a; 0, 1]).map eisEmbedding) *
    !![(Real.sqrt v : ℂ), z/(Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) i j =
    (!![(Real.sqrt v : ℂ), (z+3*eisEmbedding a)/(Real.sqrt v : ℂ);
      0, (Real.sqrt v : ℂ)⁻¹]) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul] ;
    norm_num only [map_ofNat] ; ring

theorem upperEisenstein_periodic (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein (z + 3*eisEmbedding a) v hv s = upperEisenstein z v hv s := by
  unfold upperEisenstein
  rw [← upperTranslation_section, eisenstein_automorphy _ _ _ hs,
    complexCharacter_upperTranslation, one_mul]

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

def hyperbolicKernel (s : ℂ) (z : ℂ) : ℂ := ((1+‖z‖^2 : ℝ) : ℂ) ^ (-s)

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma breveE_norm (z : ℂ) : ‖ShortDraftTrace.breveE z‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))‖ = 1
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

def sourceFourierKernel (s freq : ℂ) : ℂ :=
  ∫ z : ℂ, hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)

lemma sourceFourierKernel_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun z : ℂ => hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)) := by
  apply (hyperbolicKernel_integrable s hs).norm.mono'
  · have hker : Continuous (hyperbolicKernel s) := by
      unfold hyperbolicKernel
      apply Continuous.cpow
      · fun_prop
      · exact continuous_const
      · intro z
        exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
    have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
      change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
        ((-freq*z)+starRingEnd ℂ (-freq*z))))
      fun_prop
    exact (hker.mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by simp only [norm_mul, breveE_norm, mul_one, le_refl])

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
    using integral_hyperbolicKernel s hs

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * ShortDraftTrace.breveE (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma sourceFourierKernel_eq_fourier (s freq : ℂ) :
    sourceFourierKernel s freq = 𝓕 (hyperbolicKernel s) (2*starRingEnd ℂ freq) :=
  traceIntegral_eq_fourier (hyperbolicKernel s) freq

lemma hyperbolicKernel_laplace (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    hyperbolicKernel s z * Complex.Gamma s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(s-1) *
        Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ) * t) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : 0 < 1+‖z‖^2)
  simp only [neg_mul]
  rw [h]
  congr 1
  rw [hyperbolicKernel, one_div, Complex.inv_cpow_ofReal_nonneg (by positivity),
    Complex.cpow_neg]

lemma source_gaussian_fourier (t : ℝ) (ht : 0 < t) (freq : ℂ) :
    𝓕 (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) (2*starRingEnd ℂ freq) =
      (Real.pi : ℂ)/t * Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  rw [fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ)≠0),
    Complex.cpow_one, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
  congr 2
  push_cast
  ring

def gaussianMixture (s freq : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ)^(s-1) * Complex.exp (-t) *
    Complex.exp (-(t : ℂ)*‖z‖^2) * ShortDraftTrace.breveE (-freq*z)

lemma norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖gaussianMixture s freq t z‖ =
      t ^ (s.re-1) * Real.exp (-t) * Real.exp (-t*‖z‖^2) := by
  simp only [gaussianMixture, norm_mul, breveE_norm, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.neg_im, neg_zero, zero_mul, sub_zero]

lemma gaussianMixture_slice_integrable (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianMixture s freq t) := by
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa using ht : 0 < (t : ℂ).re) 0 (0 : ℂ)
  apply ((hg.const_mul ((t : ℂ)^(s-1)*Complex.exp (-t))).norm).mono'
  · unfold gaussianMixture
    change AEStronglyMeasurable (fun z : ℂ => (t : ℂ)^(s-1)*Complex.exp (-t)*
      Complex.exp (-(t : ℂ)*‖z‖^2) *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  · exact Eventually.of_forall fun z => by
      simp only [gaussianMixture, norm_mul, breveE_norm, mul_one, le_refl]

lemma integral_norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, ‖gaussianMixture s freq t z‖) =
      Real.pi * (Real.exp (-t)*t^(s.re-2)) := by
  simp_rw [norm_gaussianMixture s freq t ht]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ)≠0),
    Real.rpow_one]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      t^(s.re-1)/t = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((s.re-1)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    t^(s.re-1)*Real.exp (-t)*(Real.pi/t) = Real.pi*(Real.exp (-t)*(t^(s.re-1)/t)) := by ring
    _ = _ := by rw [hp]

theorem gaussianMixture_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    unfold gaussianMixture
    change AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (p.1 : ℂ)^(s-1)*Complex.exp (-p.1)*Complex.exp (-(p.1 : ℂ)*‖p.2‖^2)*
      Complex.exp (2*Real.pi*Complex.I*((-freq*p.2)+starRingEnd ℂ (-freq*p.2)))) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gaussianMixture_slice_integrable s freq t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < s.re-1)).const_mul Real.pi
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_norm_gaussianMixture s freq t ht]
    congr 2
    ring_nf

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma gaussianMixture_laplace_form (s freq : ℂ) (t : ℝ) (z : ℂ) :
    gaussianMixture s freq t z =
      ((t : ℂ)^(s-1) * Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t)) *
        ShortDraftTrace.breveE (-freq*z) := by
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2) =
      Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (t : ℂ)^(s-1) * (Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2)) *
        ShortDraftTrace.breveE (-freq*z) := by unfold gaussianMixture; ring
    _ = _ := by rw [he]

lemma integral_gaussianMixture_t (s freq : ℂ) (hs : 0 < s.re) (z : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z) =
      (hyperbolicKernel s z * Complex.Gamma s)*ShortDraftTrace.breveE (-freq*z) := by
  simp_rw [gaussianMixture_laplace_form]
  rw [integral_mul_const, ← hyperbolicKernel_laplace s hs z]

lemma integral_gaussianMixture_z (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, gaussianMixture s freq t z) =
      (Real.pi : ℂ) * ((t : ℂ)^(s-2) *
        Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) := by
  have hfac : (fun z : ℂ => gaussianMixture s freq t z) =
      (fun z : ℂ => ((t : ℂ)^(s-1)*Complex.exp (-t))*
        (Complex.exp (-(t : ℂ)*‖z‖^2)*ShortDraftTrace.breveE (-freq*z))) := by
    funext z
    unfold gaussianMixture
    ring
  rw [hfac, integral_const_mul, traceIntegral_eq_fourier, source_gaussian_fourier t ht freq]
  have hp : (t : ℂ)^(s-1)/(t : ℂ) = (t : ℂ)^(s-2) := by
    calc
      _ = (t : ℂ)^(s-1)/(t : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^((s-1)-1) := (Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = _ := by congr 1; ring
  calc
    _ = (Real.pi : ℂ)*(((t : ℂ)^(s-1)/t)*
        (Complex.exp (-(t : ℂ))*Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t))) := by ring
    _ = _ := by rw [hp, ← Complex.exp_add]; congr 2; ring_nf

theorem sourceFourierKernel_gamma (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  have hmix := gaussianMixture_integrable s freq hs
  calc
    _ = ∫ z : ℂ, (hyperbolicKernel s z * Complex.Gamma s)*
        ShortDraftTrace.breveE (-freq*z) := by
      rw [sourceFourierKernel, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = ∫ z : ℂ, ∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (integral_gaussianMixture_t s freq (by linarith) z).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ z : ℂ, gaussianMixture s freq t z :=
      (integral_integral_swap hmix).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_gaussianMixture_z s freq t ht

def schlafliIntegral (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(ν-1)*
    Complex.exp (-(t : ℂ) - (x : ℂ)^2/(4*t))

lemma schlafliIntegral_integrable (ν : ℂ) (x : ℝ) (hν : 0 < ν.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(ν-1)*
      Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t))) (Set.Ioi 0) := by
  apply (Real.GammaIntegral_convergent hν).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hre : (-(t : ℂ)-(x : ℂ)^2/(4*t)).re = -t-x^2/(4*t) := by
      rw [show -(t : ℂ)-(x : ℂ)^2/(4*t) = ((-t-x^2/(4*t) : ℝ) : ℂ) by push_cast; rfl]
      rfl
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, hre]
    simp only [Complex.sub_re, Complex.one_re]
    have he := Real.exp_le_exp.mpr (show -t-x^2/(4*t) ≤ -t by linarith [div_nonneg (sq_nonneg x) (show 0 ≤ 4*t by positivity)])
    have hb := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le (ν.re-1))
    simpa only [mul_comm] using hb

def schlafliBesselK (ν : ℂ) (x : ℝ) : ℂ :=
  (1/2 : ℂ)*(x/2 : ℂ)^(-ν)*schlafliIntegral ν x

lemma sourceFourierKernel_gamma_schlafli (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖) := by
  rw [sourceFourierKernel_gamma s freq hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [show s-2=(s-1)-1 by ring]
  apply congrArg (fun w : ℂ => (t : ℂ)^((s-1)-1)*Complex.exp w)
  push_cast
  ring

theorem sourceFourierKernel_bessel (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s *
        (2*Real.pi*‖freq‖ : ℂ)^(s-1) *
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : (2*Real.pi*‖freq‖ : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf))
  have hp : (2*Real.pi*‖freq‖ : ℂ)^(s-1) * (2*Real.pi*‖freq‖ : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hz, add_neg_cancel, Complex.cpow_zero]
  have hreorder : (2*Real.pi : ℂ)/Complex.Gamma s *
      (2*Real.pi*‖freq‖ : ℂ)^(s-1) * schlafliBesselK (s-1) (4*Real.pi*‖freq‖) =
      ((2*Real.pi : ℂ)*(2*Real.pi*‖freq‖ : ℂ)^(s-1)*
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖))/Complex.Gamma s := by ring
  rw [hreorder]
  apply (eq_div_iff hg).mpr
  rw [sourceFourierKernel_gamma_schlafli s freq hs]
  unfold schlafliBesselK
  push_cast
  have hhalf : (4*(Real.pi : ℂ)*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  rw [hhalf]
  linear_combination -((Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖))*hp

theorem sourceFourierKernel_four_thirds (freq : ℂ) (hf : freq ≠ 0) :
    sourceFourierKernel (4/3 : ℂ) freq =
      (2*Real.pi : ℂ)/Complex.Gamma (4/3) *
        (2*Real.pi*‖freq‖ : ℂ)^(1/3 : ℂ) *
        schlafliBesselK (1/3) (4*Real.pi*‖freq‖) := by
  convert sourceFourierKernel_bessel (4/3) freq (by norm_num) hf using 1 ; norm_num

end CubicEisenstein

end

end OAI
end OAIOriginalModule0120

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.PrimitiveRows
Source SHA256: c6154e230f6a02734a1c6dd0e6c206d2f4786d0365b9eece1996ed7b67737149
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0121


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

namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma levelThree_of_entries (M : SL(2,O))
    (h : ∀ i j : Fin 2, (3 : O) ∣ M i j - (if i=j then 1 else 0)) :
    M ∈ levelThree := by
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  have hh : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
      Ideal.Quotient.mk (Ideal.span {(3 : O)}) (if i=j then 1 else 0) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using hh

lemma row_coprime (M : levelThree) : IsCoprime (row M 0) (row M 1) := by
  have h : (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 0 0, ?_⟩
  change -(M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 +
    (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 = 1
  linear_combination h

lemma exists_matrix_of_primitive_row (c d : O) (hcop : IsCoprime c d)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    ∃ M : levelThree, row M = ![c,d] := by
  obtain ⟨r,s,hrs⟩ := hcop
  let M : SL(2,O) := ⟨!![s+r*c,r*(d-1); c,d], by
    rw [Matrix.det_fin_two]
    change (s+r*c)*d-(r*(d-1))*c=1
    linear_combination hrs⟩
  have hA : s+r*c-1 = -s*(d-1) := by linear_combination hrs
  have hM : M ∈ levelThree := by
    apply levelThree_of_entries
    intro i j
    fin_cases i <;> fin_cases j
    · change (3 : O) ∣ s+r*c-1
      rw [hA]
      exact hd.mul_left (-s)
    · change (3 : O) ∣ r*(d-1)-0
      simpa only [sub_zero] using hd.mul_left r
    · change (3 : O) ∣ c-(if (1 : Fin 2)=0 then 1 else 0)
      simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, sub_zero] using hc
    · change (3 : O) ∣ d-1
      exact hd
  exact ⟨⟨M,hM⟩, rfl⟩

def PrimitiveRow := {v : Fin 2 → O //
  IsCoprime (v 0) (v 1) ∧ (3 : O) ∣ v 0 ∧ (3 : O) ∣ v 1-1}

def cosetPrimitiveRow (x : CuspCosets) : PrimitiveRow :=
  ⟨cosetRow x, by
    induction x using Quotient.inductionOn with | _ M =>
      change IsCoprime (row M 0) (row M 1) ∧ (3 : O) ∣ row M 0 ∧ (3 : O) ∣ row M 1-1
      exact ⟨row_coprime M, levelThree_lower M, by simpa [row] using levelThree_entry M 1 1⟩⟩

lemma cosetPrimitiveRow_bijective : Function.Bijective cosetPrimitiveRow := by
  constructor
  · intro x y hxy
    exact cosetRow_injective (congrArg Subtype.val hxy)
  · intro v
    obtain ⟨M,hM⟩ := exists_matrix_of_primitive_row (v.1 0) (v.1 1)
      v.2.1 v.2.2.1 v.2.2.2
    refine ⟨cosetOf M, ?_⟩
    apply Subtype.ext
    change row M = v.1
    rw [hM]
    funext i
    fin_cases i <;> rfl

def primitiveRowEquiv : CuspCosets ≃ PrimitiveRow := Equiv.ofBijective _ cosetPrimitiveRow_bijective

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal

lemma inverse_character_eq_row_symbol (M : levelThree) :
    (complexCharacter M)⁻¹ = eisEmbedding (symbol (row M 0) (row M 1)) := by
  let a := (M : SL(2,O)) 0 0
  let b := (M : SL(2,O)) 0 1
  let c := (M : SL(2,O)) 1 0
  let d := (M : SL(2,O)) 1 1
  have hdet : a*d-b*c=1 := by
    simpa only [a,b,c,d,Matrix.det_fin_two] using (M : SL(2,O)).property
  have had : a*d-1=b*c := by linear_combination hdet
  have ha : lambda^2 ∣ a-1 := levelThree_primary M
  have hd3 : (3 : O) ∣ d-1 := by simpa [d] using levelThree_entry M 1 1
  have hd : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd3
  obtain ⟨b0,hb⟩ := levelThree_upper M
  obtain ⟨c0,hc⟩ := levelThree_lower M
  change b=3*b0 at hb
  change c=3*c0 at hc
  have h9 : (9 : O) ∣ a*d-1 := by
    refine ⟨b0*c0, ?_⟩
    rw [had,hb,hc]
    ring
  have hcd : c ∣ a*d-1 := by rw [had]; exact dvd_mul_left c b
  have hs := symbol_denominator_congr c (a*d) 1 (primary_mul a d ha hd) (by simp) h9 hcd
  rw [symbol_mul_denominator, symbol_one] at hs
  have hm : eisEmbedding (symbol c a)*eisEmbedding (symbol c d)=1 := by
    simpa only [map_mul, map_one] using congrArg eisEmbedding hs
  change (eisEmbedding (symbol c a))⁻¹ = eisEmbedding (symbol c d)
  exact inv_eq_of_mul_eq_one_right hm

lemma inverse_cosetCharacter_eq_row_symbol (x : CuspCosets) :
    (cosetCharacter x)⁻¹ = eisEmbedding (symbol (cosetRow x 0) (cosetRow x 1)) := by
  induction x using Quotient.inductionOn with | _ M => exact inverse_character_eq_row_symbol M

def primitiveRowPhase (v : PrimitiveRow) : ℂ :=
  eisEmbedding (symbol (v.1 0) (v.1 1))

lemma primitiveRowEquiv_val (x : CuspCosets) : (primitiveRowEquiv x).1 = cosetRow x := rfl

lemma primitiveRowEquiv_symm_row (v : PrimitiveRow) :
    cosetRow (primitiveRowEquiv.symm v) = v.1 := by
  exact congrArg Subtype.val (primitiveRowEquiv.apply_symm_apply v)

theorem upperEisenstein_eq_primitive_rows (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' row : PrimitiveRow,
      primitiveRowPhase row *
        ((v / (‖eisEmbedding (row.1 0)*z+eisEmbedding (row.1 1)‖^2 +
          ‖eisEmbedding (row.1 0)‖^2*v^2) : ℝ) : ℂ)^s := by
  rw [upperEisenstein_eq_source_series]
  rw [← primitiveRowEquiv.symm.tsum_eq]
  apply tsum_congr
  intro r
  rw [inverse_cosetCharacter_eq_row_symbol, primitiveRowEquiv_symm_row]
  simp only [primitiveRowPhase, transformedHeight, heightDenominator, embeddedRow,
    Function.comp_apply, primitiveRowEquiv_symm_row]

theorem primitive_rows_summable_norm (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun row : PrimitiveRow => ‖primitiveRowPhase row *
      ((v / (‖eisEmbedding (row.1 0)*z+eisEmbedding (row.1 1)‖^2 +
        ‖eisEmbedding (row.1 0)‖^2*v^2) : ℝ) : ℂ)^s‖) := by
  apply primitiveRowEquiv.summable_iff.mp
  apply (summable_norm_summand (upperSection z v hv) s hs).congr
  intro x
  rw [summand_upperSection, inverse_cosetCharacter_eq_row_symbol]
  rfl

lemma primitiveRow_zero_left (row : PrimitiveRow) (hc : row.1 0 = 0) : row.1 1 = 1 := by
  have hu : IsUnit (row.1 1) := by simpa only [hc, isCoprime_zero_left] using row.2.1
  exact A3_primary_unit_eq_one _ hu (lambda_sq_dvd_three.trans row.2.2.2)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def radialSource (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)

def radialDual (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)

theorem radialSource_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun z : O => if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)) := by
  have hs : Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  convert hs.indicator {z : O | z ≠ 0} using 1
  ext z
  by_cases hz : z = 0 <;> simp [hz]

theorem radialSource_poisson (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    radialSource W X = (X : ℂ) * paperRadialFourier W 0 - W 0 +
      (X : ℂ) * radialDual W X := by
  let P : Empty → Ideal O := Empty.elim
  let : ∀ i, (P i).IsMaximal := fun i => nomatch i
  have hi : Function.Injective P := by intro i; cases i
  have hp := masked_principal_radial_poisson_zero_split P hi ∅ W X hX
  simp only [maskedPrincipalRemainder, Finset.prod_empty, Finset.powerset_empty,
    Finset.sum_singleton, UniqueFactorizationMonoid.moebius_one, map_one,
    Int.cast_one, Nat.cast_one, div_one, mul_one] at hp
  simp only [rowCoprimeMask, Finset.notMem_empty, false_and, exists_false,
    ite_false, one_mul] at hp
  have hs : Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  have hz := hs.tsum_eq_add_tsum_ite 0
  simp only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hz
  change (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / X)) =
    (X : ℂ) * paperRadialFourier W 0 + (X : ℂ) * radialDual W X at hp
  change (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / X)) = W 0 + radialSource W X at hz
  linear_combination hp - hz

def subsetNorm {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℝ :=
  Ideal.absNorm (∏ i ∈ E, P i)

def subsetMobius {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℂ :=
  UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i)

def smallDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => subsetNorm P E ≤ Z)

def largeDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => Z < subsetNorm P E)

theorem subsetNorm_pos {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    0 < subsetNorm P E := by
  rw [subsetNorm, ← primeSubsetGenerator_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))

theorem sum_small_add_large {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Z : ℝ) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Z, f E) + (∑ E ∈ largeDivisors P S Z, f E) =
      ∑ E ∈ S.powerset, f E := by
  simpa only [smallDivisors, largeDivisors, not_le] using
    Finset.sum_filter_add_sum_filter_not S.powerset (fun E => subsetNorm P E ≤ Z) f

theorem masked_radialSource_dilations {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      ∑ E ∈ S.powerset, subsetMobius P E * radialSource W (X / subsetNorm P E) := by
  rw [tsum_rowCoprimeMask_dilations P hinj S _ (radialSource_summable W X hX)]
  apply Finset.sum_congr rfl
  intro E hE
  change subsetMobius P E * _ = _
  congr 1
  apply tsum_congr
  intro z
  rw [mul_eq_zero, or_iff_right (primeSubsetGenerator_ne_zero P E)]
  by_cases hz : z = 0
  · simp [hz]
  · rw [ite_eq_right hz, ite_eq_right hz, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_sq]
    congr 1
    simp only [subsetNorm, div_div_eq_mul_div]
    ring

theorem masked_radialSource_truncated {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ smallDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_dilations P hinj S W X hX,
    ← sum_small_add_large P S Z]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  rw [radialSource_poisson W _ (div_pos hX (subsetNorm_pos P E))]
  push_cast
  ring

theorem masked_radialSource_truncated_euler {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated P hinj S W X Z hX]
  have hs := sum_small_add_large P S Z (fun E => subsetMobius P E / (subsetNorm P E : ℂ))
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  have he := primeSubset_moebius_norm_sum P hprime hinj S
  change (∑ E ∈ S.powerset, subsetMobius P E / (subsetNorm P E : ℂ)) = _ at he
  rw [he] at hs
  linear_combination (X : ℂ) * paperRadialFourier W 0 * hs

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Y Z : ℝ) :=
  (smallDivisors P S Z).filter (fun E => Y < subsetNorm P E)

def dualNear (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0

def dualFar (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if lengthScale < ‖eisEmbedding h‖ ^ 2 then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0

theorem radialDual_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun h : O => if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) := by
  have hs := (paperRadialFourier_lattice_summable_norm W X hX).of_norm
  convert hs.indicator {z : O | z ≠ 0} using 1
  ext z
  by_cases hz : z = 0 <;> simp [hz]

theorem radialDual_near_add_far (W : 𝓢(ℝ, ℂ)) (X lengthScale : ℝ) (hX : 0 < X) :
    radialDual W X = dualNear W X lengthScale + dualFar W X lengthScale := by
  have hs := radialDual_summable W X hX
  have hn : Summable (fun h : O => if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | ‖eisEmbedding h‖ ^ 2 ≤ lengthScale}
  have hf : Summable (fun h : O => if lengthScale < ‖eisEmbedding h‖ ^ 2 then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}
  unfold radialDual dualNear dualFar
  rw [← hn.tsum_add hf]
  apply tsum_congr
  intro h
  by_cases hL : ‖eisEmbedding h‖ ^ 2 ≤ lengthScale <;> simp [hL, not_lt_of_ge, lt_of_not_ge]

theorem sum_small_add_middle {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Y Z : ℝ) (hYZ : Y ≤ Z) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Y, f E) + (∑ E ∈ middleDivisors P S Y Z, f E) =
      ∑ E ∈ smallDivisors P S Z, f E := by
  have hsmall : (smallDivisors P S Z).filter (fun E => subsetNorm P E ≤ Y) =
      smallDivisors P S Y := by
    ext E
    simp only [Finset.mem_filter, smallDivisors]
    constructor
    · rintro ⟨⟨hE, hEZ⟩, hEY⟩
      exact ⟨hE, hEY⟩
    · rintro ⟨hE, hEY⟩
      exact ⟨⟨hE, hEY.trans hYZ⟩, hEY⟩
  have hs := Finset.sum_filter_add_sum_filter_not (smallDivisors P S Z)
    (fun E => subsetNorm P E ≤ Y) f
  rw [hsmall] at hs
  simpa only [middleDivisors, not_le] using hs

theorem masked_radialSource_five_pieces {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated_euler P hinj S W X Z hX]
  have hs := sum_small_add_middle P S Y Z hYZ (fun E =>
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E))
  rw [← hs]
  have hm : (∑ E ∈ middleDivisors P S Y Z,
      (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) =
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    rw [radialDual_near_add_far W _ lengthScale (div_pos hX (subsetNorm_pos P E)), mul_add]
  rw [hm]
  ring

end TruncatedPrincipalPoisson

namespace EisensteinSchwartzPoisson
open ConcreteTraceCRT

theorem radial_source_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  let s : Finset (ℕ × ℕ) := Finset.Iic (A + 2, 0)
  let C : ℝ := 2 ^ (A + 2) * (eisensteinCauchyMass + 1)
  have hC : 0 < C := by
    have hm := eisensteinCauchyMass_nonneg
    dsimp [C]
    positivity
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : ℝ := 2 ^ (A + 2) * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (q : ℝ) (hq : 0 ≤ q) : (1 + q) ^ (A + 2) * ‖W q‖ ≤ B := by
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (A + 2, 0)) (k := A + 2) (n := 0) le_rfl le_rfl W q
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    change (1 + q) ^ (A + 2) * ‖W q‖ ≤ B at hh
    exact hh
  have hp (h : {h : O // h ≠ 0}) : ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      (B / (1 + K) ^ A) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    have hq : K ≤ K * ‖eisEmbedding h.val‖ ^ 2 := by
      nlinarith [one_le_eisenstein_norm_sq h.val h.property]
    have hh := polynomial_tail_majorant A K K (‖eisEmbedding h.val‖ ^ 2) B
      ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖ hK0 hK0.le (sq_nonneg _) (norm_nonneg _) hq
      (hb _ (by positivity))
    simpa only [min_eq_left hK, one_pow, one_mul] using hh
  have hmajor := (eisenstein_cauchy_summable.subtype (fun h => h ≠ 0)).mul_left
    (B / (1 + K) ^ A)
  have hs : Summable (fun h : {h : O // h ≠ 0} => ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : {h : O // h ≠ 0},
        (B / (1 + K) ^ A) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / (1 + K) ^ A) * ∑' h : {h : O // h ≠ 0},
        ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / (1 + K) ^ A) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype {h : O | h ≠ 0}) (by positivity)
    _ ≤ (B / (1 + K) ^ A) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, C]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

private theorem zero_removed_tsum (f : O → ℂ) :
    (∑' h : O, if h = 0 then 0 else f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
  rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
    intro h hh hz
    subst h
    exact hh (by simp))]
  apply tsum_congr
  intro h
  simp only [ite_eq_right h.property]

theorem radialSource_inverse_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialSource W K⁻¹‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radial_source_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs : Summable (fun h : O => W (K * ‖eisEmbedding h‖ ^ 2)) := by
    simpa only [scaledRadialTest_apply, div_inv_eq_mul, mul_comm] using
      (actual_eisenstein_summable_norm (scaledRadialTest W K⁻¹ (inv_pos.mpr hK0))).of_norm
  unfold radialSource
  rw [zero_removed_tsum]
  simp only [div_inv_eq_mul, mul_comm (‖eisEmbedding _‖ ^ 2) K]
  exact (norm_tsum_le_tsum_norm (hs.norm.subtype _)).trans (hb W K hK)

theorem radialDual_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialDual W K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simp only [min_eq_left hK, one_pow, one_mul] at ht
  unfold radialDual
  rw [zero_removed_tsum]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans ht)

theorem subsetMobius_norm_le_one {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖subsetMobius P E‖ ≤ 1 := QuadraticInitialBound.norm_ideal_moebius_le_one _

private theorem scale_tail_bound (A : ℕ) (B x Y X : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxY : x ≤ Y) (hX : 0 < X) :
    (X / x) * (B / (1 + X / x) ^ (A + 1)) ≤ B * (Y / X) ^ A := by
  have hu : 0 < X / x := div_pos hX hx
  calc
    _ ≤ (X / x) * (B / (X / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / X) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (Y / X) ^ A := by gcongr

private theorem norm_sum_subsets_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T : Finset (Finset ι)) (hT : T ⊆ S.powerset) (f : Finset ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ E ∈ T, ‖f E‖ ≤ B) :
    ‖∑ E ∈ T, f E‖ ≤ (2 : ℝ) ^ S.card * B := by
  calc
    _ ≤ ∑ E ∈ T, ‖f E‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ T, B := Finset.sum_le_sum hf
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (2 : ℝ) ^ S.card * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc := Finset.card_le_card hT
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc

theorem small_divisor_dual_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y : ℝ), 0 < X → 0 ≤ Y → Y ≤ X →
        ‖(X : ℂ) * ∑ E ∈ smallDivisors P S Y,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (Y / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialDual_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y hX hY hYX
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ smallDivisors P S Y) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        radialDual W (X / subsetNorm P E))‖ ≤ B * (Y / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEY : subsetNorm P E ≤ Y := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ X / subsetNorm P E := (le_div_iff₀ hn).mpr (by simpa using hEY.trans hYX)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖radialDual W (X / subsetNorm P E)‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / subsetNorm P E) * 1 * (B / (1 + X / subsetNorm P E) ^ (A + 1)) := by
        gcongr
        · exact subsetMobius_norm_le_one P E
        · exact hb W _ hscale
      _ ≤ B * (Y / X) ^ A := by
        simpa only [mul_one] using scale_tail_bound A B (subsetNorm P E) Y X hB hn hEY hX
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

theorem large_divisor_source_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ), 0 < X → X ≤ Z →
        ‖∑ E ∈ largeDivisors P S Z,
          subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + Z / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialSource_inverse_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Z hX hXZ
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hX.trans_le hXZ
  have hf (E : Finset ι) (hE : E ∈ largeDivisors P S Z) :
      ‖subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤ B / (1 + Z / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEZ : Z < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ subsetNorm P E / X := (le_div_iff₀ hX).mpr (by simpa using hXZ.trans hEZ.le)
    have hh := hb W (subsetNorm P E / X) hscale
    rw [inv_div] at hh
    calc
      _ = ‖subsetMobius P E‖ * ‖radialSource W (X / subsetNorm P E)‖ := norm_mul _ _
      _ ≤ 1 * (B / (1 + subsetNorm P E / X) ^ A) :=
        mul_le_mul (subsetMobius_norm_le_one P E) hh (norm_nonneg _) (by norm_num)
      _ ≤ B / (1 + Z / X) ^ A := by
        simp only [one_mul]
        apply div_le_div_of_nonneg_left hB (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by gcongr) A
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

end TruncatedPrincipalPoisson

end

end OAI
end OAIOriginalModule0121

/-! Original module: OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
Source SHA256: 92b624322980b29e4756775d4d7f2b40d00c3f8c6eb9b94641db126a51a24e5d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0122


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

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem mem_rowNormDisk_floor {lengthScale : ℝ} (hL : 0 ≤ lengthScale) (z : O) :
    z ∈ rowNormDisk ⌊lengthScale⌋₊ ↔ z ≠ 0 ∧ ‖eisEmbedding z‖ ^ 2 ≤ lengthScale := by
  rw [mem_rowNormDisk]
  constructor
  · rintro ⟨hp, hN⟩
    refine ⟨?_, ?_⟩
    · intro hz
      subst z
      simp at hp
    · rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hL)
  · rintro ⟨hz, hN⟩
    have hp := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hz))
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hp hN
    exact ⟨by exact_mod_cast hp, Nat.le_floor hN⟩

theorem dualNear_eq_finite (W : ℝ → ℂ) (X lengthScale : ℝ) (hL : 0 ≤ lengthScale) :
    dualNear W X lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2) := by
  unfold dualNear
  rw [tsum_eq_sum (s := rowNormDisk ⌊lengthScale⌋₊) (fun h hh => ?_)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hd := (mem_rowNormDisk_floor hL h).mp hh
    simp only [ite_eq_left hd.2, ite_eq_right hd.1]
  · by_cases hz : h = 0
    · simp [hz]
    · have hn : ¬ ‖eisEmbedding h‖ ^ 2 ≤ lengthScale := fun hn => hh ((mem_rowNormDisk_floor hL h).mpr ⟨hz, hn⟩)
      simp only [ite_eq_right hn]

theorem dualFar_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K lengthScale : ℝ), 0 < K → 0 ≤ lengthScale →
        ‖dualFar W K lengthScale‖ ≤ (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + K * lengthScale) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K lengthScale hK hL
  have he : dualFar W K lengthScale =
      ∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    unfold dualFar
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}) (by
      intro h hh
      by_contra hn
      change ¬ lengthScale < ‖eisEmbedding h‖ ^ 2 at hn
      exact hh (by simp only [ite_eq_right hn]))]
    apply tsum_congr
    intro h
    have hqh : lengthScale < ‖eisEmbedding h.val‖ ^ 2 := h.property
    have hz : h.val ≠ 0 := by
      intro hz
      have hp := hqh
      simp only [hz, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp
      linarith
    simp only [ite_eq_left hqh, ite_eq_right hz]
  rw [he]
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  let f : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2} →
      {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, mul_le_mul_of_nonneg_left h.property.le hK.le⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2},
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans (hb W K (K * lengthScale) hK (mul_nonneg hK.le hL)))

end

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem middle_divisor_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ Z → 0 ≤ lengthScale →
        ‖(X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (X / Y) * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := dualFar_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y Z lengthScale hX hY hYZ hL
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Q := (min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hY.trans_le hYZ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ middleDivisors P S Y Z) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        dualFar W (X / subsetNorm P E) lengthScale)‖ ≤ (X / Y) * (B / Q) := by
    have hn := subsetNorm_pos P E
    have hEY : Y < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hEZ : subsetNorm P E ≤ Z := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hk : X / Z ≤ X / subsetNorm P E := div_le_div_of_nonneg_left hX.le hn hEZ
    have hden : Q ≤ (min 1 (X / subsetNorm P E)) ^ 2 *
        (1 + (X / subsetNorm P E) * lengthScale) ^ A := by
      dsimp [Q]
      have hmul : X * lengthScale / Z ≤ (X / subsetNorm P E) * lengthScale := by
        calc
          _ = (X / Z) * lengthScale := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hL
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hk) 2
      · exact pow_le_pow_left₀ (by positivity) (by linarith) A
      · positivity
      · positivity
    have hh : ‖dualFar W (X / subsetNorm P E) lengthScale‖ ≤ B / Q :=
      (hb W _ lengthScale (div_pos hX hn) hL).trans (div_le_div_of_nonneg_left hB hQ hden)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖dualFar W (X / subsetNorm P E) lengthScale‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / Y) * 1 * (B / Q) := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_left hX.le hY hEY.le)
            (subsetMobius_norm_le_one P E) (norm_nonneg _) (by positivity)
        · exact hh
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ middleDivisors P S Y Z,
        ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale)‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ middleDivisors P S Y Z, (X / Y) * (B / Q) := Finset.sum_le_sum hf
    _ = ((middleDivisors P S Y Z).card : ℝ) * ((X / Y) * (B / Q)) := by simp
    _ ≤ (2 : ℝ) ^ S.card * ((X / Y) * (B / Q)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : middleDivisors P S Y Z ⊆ S.powerset :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
    _ = _ := by dsimp [B, Q]; ring

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def principalTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Z : ℝ) : ℂ :=
  (X : ℂ) * paperRadialFourier W 0 * (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
  (X : ℂ) * paperRadialFourier W 0 *
    (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
  W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E)

def middleTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) *
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W ((X / subsetNorm P E) * ‖eisEmbedding h‖ ^ 2)

def truncationError {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (∑' z : O, rowCoprimeMask P S z * (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) -
    (principalTruncation P S W X Z + middleTruncation P S W X Y Z lengthScale)

theorem truncationError_eq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ lengthScale) :
    truncationError P S W X Y Z lengthScale =
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  unfold truncationError principalTruncation middleTruncation
  rw [masked_radialSource_five_pieces P hinj S W X Y Z lengthScale hX hYZ]
  simp_rw [dualNear_eq_finite W _ lengthScale hL]
  ring

theorem truncationError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖truncationError P S W X Y Z lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Y / X) ^ A + (1 / (1 + Z / X) ^ A) +
              (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := small_divisor_dual_tail A
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := large_divisor_source_tail A
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := middle_divisor_frequency_tail A
  refine ⟨(s₀ ∪ s₁) ∪ s₂, C₀ + C₁ + C₂, by positivity, ?_⟩
  intro ι _ P _ hinj S W X Y Z lengthScale hX hY hYX hXZ hL
  let Q := ((s₀ ∪ s₁) ∪ s₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C := C₀ + C₁ + C₂
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) W
  have hq₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hz : 0 < Z := hX.trans_le hXZ
  let lo : ℂ := (X : ℂ) * ∑ E ∈ smallDivisors P S Y,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)
  let mid : ℂ := (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale
  let hi : ℂ := ∑ E ∈ largeDivisors P S Z,
    subsetMobius P E * radialSource W (X / subsetNorm P E)
  have hlo : ‖lo‖ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A := by
    apply (h₀ P S W X Y hX hY.le hYX).trans
    gcongr
  have hhi : ‖hi‖ ≤ (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := by
    apply (h₁ P S W X Z hX hXZ).trans
    gcongr
  have hmid : ‖mid‖ ≤ (2 : ℝ) ^ S.card * (X / Y) * (C * Q) /
      ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
    apply (h₂ P S W X Y Z lengthScale hX hY (hYX.trans hXZ) hL).trans
    gcongr
  rw [truncationError_eq P hinj S W X Y Z lengthScale hX (hYX.trans hXZ) hL]
  change ‖lo + mid + hi‖ ≤ _
  calc
    _ ≤ ‖lo‖ + ‖mid‖ + ‖hi‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le lo mid) le_rfl)
    _ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A +
        (2 : ℝ) ^ S.card * (X / Y) * (C * Q) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) +
        (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := add_le_add (add_le_add hlo hmid) hhi
    _ = _ := by change _ = (2 : ℝ) ^ S.card * (C * Q) * _; ring

end TruncatedPrincipalPoisson

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open FourierBridge FirstPassCubeLabels

lemma schwartz_phase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  simpa only [logPhase, Real.inner_apply, mul_assoc, mul_comm, mul_left_comm] using
    FourierBridge.schwartz_log_inversion g x

lemma product_three_integrals (f g h : ℝ → ℂ) :
    (∫ t, f t) * (∫ t, g t) * (∫ t, h t) =
      ∫ t₁, ∫ t₂, ∫ t₃, f t₁ * g t₂ * h t₃ := by
  simp_rw [integral_const_mul, integral_mul_const]
  simp_rw [integral_const_mul, integral_mul_const]

def profileSourceBound (g : 𝓢(ℝ, ℂ)) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    ((SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)

lemma profileSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    0 ≤ profileSourceBound g J := by
  unfold profileSourceBound
  positivity

lemma source_le_profileSourceBound (g : 𝓢(ℝ, ℂ)) (J i : ℕ) (hi : i ≤ J) :
    (SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g ≤
      profileSourceBound g J := by
  unfold profileSourceBound
  apply Finset.single_le_sum (s := Finset.range (J + 1)) (a := i)
    (f := fun k : ℕ => (SchwartzMap.seminorm ℝ 0 k) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower k) g)
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (by omega)

lemma profile_fourier_envelope (g : 𝓢(ℝ, ℂ)) (J : ℕ) (t : ℝ) :
    ‖(𝓕 g) t‖ ≤ fourierPointBound (J + 2) (profileSourceBound g (J + 2)) *
      firstLogDensity J t := by
  have h := uniform_fourier_pointwise g (J + 2) 1 (profileSourceBound g (J + 2))
    (by norm_num) (profileSourceBound_nonneg g _)
    (fun i hi => by simpa using source_le_profileSourceBound g (J + 2) i hi) t
  rw [firstLogDensity, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
  simpa only [one_mul, mul_comm] using h

theorem joint_separation_identity
    (A₁ A₂ : 𝓢(ℝ, ℂ)) (b : 𝓢(ℝ, ℂ)) (P F : ℂ) (s₁ s₂ s₃ : ℝ)
    (hr : P * F = ∫ t : ℝ, P * logPhase t s₃ * b t) :
    P * A₁ s₁ * A₂ s₂ * F =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        P * logPhase t₁ s₁ * logPhase t₂ s₂ * logPhase t₃ s₃ *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by
  calc
    _ = A₁ s₁ * A₂ s₂ * (P * F) := by ring
    _ = (∫ t : ℝ, logPhase t s₁ * (𝓕 A₁) t) *
        (∫ t : ℝ, logPhase t s₂ * (𝓕 A₂) t) *
        (∫ t : ℝ, P * logPhase t s₃ * b t) := by
      rw [← schwartz_phase_inversion, ← schwartz_phase_inversion, ← hr]
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        (logPhase t₁ s₁ * (𝓕 A₁) t₁) * (logPhase t₂ s₂ * (𝓕 A₂) t₂) *
          (P * logPhase t₃ s₃ * b t₃) := by
      exact product_three_integrals
        (fun t : ℝ => logPhase t s₁ * (𝓕 A₁) t)
        (fun t : ℝ => logPhase t s₂ * (𝓕 A₂) t)
        (fun t : ℝ => P * logPhase t s₃ * b t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      ring

theorem joint_separation_envelope {ι : Type*} [Fintype ι]
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ a₃ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ j, V j (y j)) * A₁ (∑ j, a₁ j * y j) * A₂ (∑ j, a₂ j * y j) *
          EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (∑ j, a₃ j * y j)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          (∏ j, V j (y j)) * logPhase t₁ (∑ j, a₁ j * y j) *
            logPhase t₂ (∑ j, a₂ j * y j) * logPhase t₃ (∑ j, a₃ j * y j) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  classical
  obtain ⟨C₃, hC₃, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V a₃ M hM hV A (J + 2)
  let C₁ := fourierPointBound (J + 2) (profileSourceBound A₁ (J + 2))
  let C₂ := fourierPointBound (J + 2) (profileSourceBound A₂ (J + 2))
  have hC₁ : 0 ≤ C₁ := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_, AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J |>.congr ?_⟩
  · intro y
    let P : ℂ := ∏ j, V j (y j)
    let s₁ : ℝ := ∑ j, a₁ j * y j
    let s₂ : ℝ := ∑ j, a₂ j * y j
    let s₃ : ℝ := ∑ j, a₃ j * y j
    have hr : P * EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp s₃) =
        ∫ t, P * logPhase t s₃ * b t := by
      have hh := hb y
      simpa only [Finset.prod_mul_distrib, ← logPhase_sum, P, s₃] using hh
    exact joint_separation_identity A₁ A₂ b P
      (EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp s₃)) s₁ s₂ s₃ hr
  · intro t₁ t₂ t₃
    have hb₃ : (1 + R) ^ A * ‖b t₃‖ ≤ C₃ * firstLogDensity J t₃ := by
      rw [firstLogDensity, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t₃‖) (J + 2))).mpr
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hpoint t₃
    have h₁ := profile_fourier_envelope A₁ J t₁
    have h₂ := profile_fourier_envelope A₂ J t₂
    simp only [norm_mul]
    calc
      _ = ‖(𝓕 A₁) t₁‖ * ‖(𝓕 A₂) t₂‖ * ((1 + R)^A * ‖b t₃‖) := by ring
      _ ≤ (C₁ * firstLogDensity J t₁) * (C₂ * firstLogDensity J t₂) * (C₃ * firstLogDensity J t₃) := by
        exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg hC₁ (firstLogDensity_nonneg _ _))) hb₃ (by positivity)
          (mul_nonneg (mul_nonneg hC₁ (firstLogDensity_nonneg _ _))
            (mul_nonneg hC₂ (firstLogDensity_nonneg _ _)))
      _ = _ := by ring
  · filter_upwards [] with t
    simp

lemma seven_phase_factor (z ud ue uv kap x₁ x₂ t₁ t₂ t₃ : ℝ) :
    logPhase t₁ (z + x₁) * logPhase t₂ (z + x₂) *
      logPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂) =
    logPhase (t₁ + t₂) z * logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
      logPhase (t₁ - t₃) x₁ * logPhase (t₂ - t₃) x₂ := by
  unfold logPhase
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

def outerWindow (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : ℝ) : ℂ :=
  V 0 z * V 1 ud * V 2 ue * V 3 uv * V 4 kap

def fixedColumnTest (V : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ := V x * logPhase t x

theorem seven_kernel_separation (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * A₁ (z + x₁) * A₂ (z + x₂) *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * logPhase (t₁ + t₂) z *
            logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  let a₁ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 1, 0]
  let a₂ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 0, 1]
  let a₃ : Fin 7 → ℝ := ![0, -1, -2, -2, 1, -1, -1]
  obtain ⟨C, hC, hsep⟩ := joint_separation_envelope A₁ A₂ W V a₁ a₂ a₃ M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, ?_, hpoint, hint⟩
  intro z ud ue uv kap x₁ x₂
  let y : Fin 7 → ℝ := ![z, ud, ue, uv, kap, x₁, x₂]
  have h₁ : (∑ j, a₁ j * y j) = z + x₁ := by
    simp [a₁, y, Fin.sum_univ_succ]
  have h₂ : (∑ j, a₂ j * y j) = z + x₂ := by
    simp [a₂, y, Fin.sum_univ_succ]
  have h₃ : (∑ j, a₃ j * y j) = kap - ud - 2 * ue - 2 * uv - x₁ - x₂ := by
    simp [a₃, y, Fin.sum_univ_succ]
    ring
  have hp : (∏ j, V j (y j)) = outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ := by
    simp [outerWindow, y, Fin.prod_univ_succ, mul_assoc]
  have h := hb y
  rw [h₁, h₂, h₃, hp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with t₁
  apply integral_congr_ae
  filter_upwards [] with t₂
  apply integral_congr_ae
  filter_upwards [] with t₃
  have heq := seven_phase_factor z ud ue uv kap x₁ x₂ t₁ t₂ t₃
  unfold fixedColumnTest
  calc
    _ = (outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂) *
      (logPhase t₁ (z + x₁) * logPhase t₂ (z + x₂) *
      logPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) *
      ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
    _ = _ := by rw [heq]; ring

end

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

lemma density_weight_identity (J : ℕ) (t : ℝ) :
    (1 + ‖t‖) ^ J * firstLogDensity J t = firstLogDensity 0 t := by
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

lemma triple_product_integral_bound (f₁ f₂ f₃ g₁ g₂ g₃ : ℝ → ℝ)
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (hf₃ : Integrable f₃)
    (hg₁ : Integrable g₁) (hg₂ : Integrable g₂) (hg₃ : Integrable g₃)
    (S C : ℝ) (hpoint : ∀ x y z, S * f₁ x * f₂ y * f₃ z ≤ C * g₁ x * g₂ y * g₃ z) :
    S * (∫ x, f₁ x) * (∫ y, f₂ y) * (∫ z, f₃ z) ≤
      C * (∫ x, g₁ x) * (∫ y, g₂ y) * (∫ z, g₃ z) := by
  have hi₃ (x y : ℝ) := integral_mono (hf₃.const_mul (S * f₁ x * f₂ y))
    (hg₃.const_mul (C * g₁ x * g₂ y)) (hpoint x y)
  simp only [integral_const_mul] at hi₃
  have hi₂ (x : ℝ) := integral_mono
    ((hf₂.const_mul (S * f₁ x)).mul_const (∫ z, f₃ z))
    ((hg₂.const_mul (C * g₁ x)).mul_const (∫ z, g₃ z)) (hi₃ x)
  simp only [integral_const_mul, integral_mul_const] at hi₂
  have hi₁ := integral_mono
    (((hf₁.const_mul S).mul_const (∫ y, f₂ y)).mul_const (∫ z, f₃ z))
    (((hg₁.const_mul C).mul_const (∫ y, g₂ y)).mul_const (∫ z, g₃ z)) hi₂
  simpa only [integral_const_mul, integral_mul_const] using hi₁

theorem triple_coefficient_moment_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖ ≤
      C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * (1 + ‖t₃‖) ^ J *
        ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖) ≤ C * (∫ t : ℝ, firstLogDensity 0 t) ^ 3 := by
  let f₁ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₁ t‖
  let f₂ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₂ t‖
  let f₃ : ℝ → ℝ := fun t => (1 + ‖t‖) ^ J * ‖b₃ t‖
  have hprod : ∀ t₁ t₂ t₃ : ℝ,
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * (1 + ‖t₃‖) ^ J *
        ‖b₁ t₁ * b₂ t₂ * b₃ t₃‖ = f₁ t₁ * (f₂ t₂ * f₃ t₃) := by
    intro t₁ t₂ t₃
    simp only [norm_mul, f₁, f₂, f₃]
    ring
  have hb : ∀ t₁ t₂ t₃ : ℝ, S * f₁ t₁ * f₂ t₂ * f₃ t₃ ≤
      C * firstLogDensity 0 t₁ * firstLogDensity 0 t₂ * firstLogDensity 0 t₃ := by
    intro t₁ t₂ t₃
    have h := mul_le_mul_of_nonneg_left (hpoint t₁ t₂ t₃)
      (show 0 ≤ (1 + ‖t₁‖)^J * (1 + ‖t₂‖)^J * (1 + ‖t₃‖)^J by positivity)
    have hd₁ := density_weight_identity J t₁
    have hd₂ := density_weight_identity J t₂
    have hd₃ := density_weight_identity J t₃
    simp only [norm_mul] at h
    rw [← hd₁, ← hd₂, ← hd₃]
    dsimp [f₁, f₂, f₃]
    simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using h
  have hbound := triple_product_integral_bound f₁ f₂ f₃
    (firstLogDensity 0) (firstLogDensity 0) (firstLogDensity 0)
    (weighted_schwartz_integrable b₁ J) (weighted_schwartz_integrable b₂ J)
    (weighted_schwartz_integrable b₃ J)
    (firstLogDensity_integrable 0) (firstLogDensity_integrable 0) (firstLogDensity_integrable 0)
    S C hb
  simp_rw [hprod, integral_const_mul]
  simp_rw [integral_mul_const]
  convert hbound using 1 <;> ring

end JointLogSeparation

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

abbrev Triple (ι : Type*) := Σ _ : Finset ι, Finset ι × Finset ι

def triples (F : Finset ι) : Finset (Triple ι) :=
  F.powerset.sigma fun G => ((F \ G).powerset ×ˢ (F \ G).powerset).filter fun UV => Disjoint UV.1 UV.2

def split (ST : Finset ι × Finset ι) : Triple ι :=
  ⟨ST.1 ∩ ST.2, ST.1 \ ST.2, ST.2 \ ST.1⟩

def join (GUV : Triple ι) : Finset ι × Finset ι :=
  (GUV.1 ∪ GUV.2.1, GUV.1 ∪ GUV.2.2)

lemma join_split (ST : Finset ι × Finset ι) : join (split ST) = ST := by
  apply Prod.ext
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

lemma split_mem {F : Finset ι} {ST : Finset ι × Finset ι}
    (hST : ST ∈ F.powerset ×ˢ F.powerset) : split ST ∈ triples F := by
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  have hSF := Finset.mem_powerset.mp hS
  have hTF := Finset.mem_powerset.mp hT
  simp only [triples, split, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_left.trans hSF, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hSF hi.1, by tauto⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hTF hi.1, by tauto⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

lemma join_mem {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    join GUV ∈ F.powerset ×ˢ F.powerset := by
  rcases (by simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset] using h) with ⟨hG, ⟨hU, hV⟩, _⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_powerset.mpr
  · exact Finset.union_subset hG (hU.trans Finset.sdiff_subset)
  · exact Finset.union_subset hG (hV.trans Finset.sdiff_subset)

lemma split_join {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    split (join GUV) = GUV := by
  rcases GUV with ⟨G, U, V⟩
  have hh : G ⊆ F ∧ (U ⊆ F \ G ∧ V ⊆ F \ G) ∧ Disjoint U V := by
    simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powerset] using h
  rcases hh with ⟨_, ⟨hU, hV⟩, hd⟩
  have hUG : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hU hi)).2 hg)
  have hVG : Disjoint V G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hV hi)).2 hg)
  have h₀ : (G ∪ U) ∩ (G ∪ V) = G := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h₁ : (G ∪ U) \ (G ∪ V) = U := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    have hj : i ∈ U → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hUG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h₂ : (G ∪ V) \ (G ∪ U) = V := by
    ext i
    have hi : i ∈ V → i ∈ U → False := fun hi hj => Finset.disjoint_left.mp hd.symm hi hj
    have hj : i ∈ V → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hVG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simp only [split, join, h₀, h₁, h₂]

theorem sum_pair_eq_overlap {β : Type*} [AddCommMonoid β]
    (F : Finset ι) (C : Finset ι → Finset ι → β) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, C S T) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then C (G ∪ U) (G ∪ V) else 0 := by
  classical
  have hs : (∑ ST ∈ F.powerset ×ˢ F.powerset, C ST.1 ST.2) =
      ∑ GUV ∈ triples F, C (join GUV).1 (join GUV).2 := by
    apply Finset.sum_bij (fun ST _ => split ST)
    · intro ST hST
      exact split_mem hST
    · intro ST hST SU hSU heq
      have hh := congrArg join heq
      simpa only [join_split] using hh
    · intro GUV hGUV
      exact ⟨join GUV, join_mem hGUV, split_join hGUV⟩
    · intro ST hST
      rw [join_split]
  simpa only [triples, Finset.sum_sigma, Finset.sum_filter, Finset.sum_product, join] using hs

end FiniteOverlapDecomposition

end

end OAI
end OAIOriginalModule0122

/-! Original module: OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
Source SHA256: b0adf20206c6e064a5bb9d82eda42b5a63aad139140f496803b87d804b46c551
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0123



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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_temperate (t : ℝ) : (logPhase t).HasTemperateGrowth := by
  have hl : Function.HasTemperateGrowth (fun x : ℝ => (2 * Real.pi * t) * x) := by
    simpa [Pi.smul_def, smul_eq_mul] using (((2 * Real.pi * t) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth)
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hl

def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (logPhase t) g

@[simp] lemma frequencyTwist_apply (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    frequencyTwist g t x = logPhase t x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (logPhase_temperate t) g x

lemma logPhase_add_frequency (t s x : ℝ) :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma frequencyTwist_twice (g : 𝓢(ℝ, ℂ)) (t s : ℝ) :
    frequencyTwist (frequencyTwist g t) s = frequencyTwist g (t + s) := by
  ext x
  simp only [frequencyTwist_apply, logPhase_add_frequency]
  ring

@[simp] lemma frequencyTwist_norm (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    ‖frequencyTwist g t x‖ = ‖g x‖ := by simp [logPhase_norm]

lemma frequencyTwist_tsupport (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    tsupport (frequencyTwist g t) = tsupport g := by
  apply congrArg (fun s : Set ℝ => closure s)
  ext x
  have hp : logPhase t x ≠ 0 := by
    intro hz
    have hn := logPhase_norm t x
    rw [hz, norm_zero] at hn
    norm_num at hn
  simp only [Function.mem_support, frequencyTwist_apply, ne_eq, mul_eq_zero, hp, false_or]

def phaseDerivative (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

