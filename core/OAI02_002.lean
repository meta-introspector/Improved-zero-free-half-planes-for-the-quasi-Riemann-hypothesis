lemma cuspCutoffTerm_summable (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Summable (fun x => cuspCutoffTerm Y F x w) :=
  summable_of_hasFiniteSupport (cuspCutoffTerm_finiteSupport Y hY F w)

def cuspCutoffCorrection (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑'x,cuspCutoffTerm Y F x w

lemma cuspCutoffTerm_automorphy (Y : ℝ) (F : ℝ → ℂ) (M : levelThree)
    (x : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm Y F x (complexMatrix M • w) =
      complexCharacter M * cuspCutoffTerm Y F (rightEquiv M x) w := by
  have hM : complexCharacter M≠0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  simp only [cuspCutoffTerm,cosetHeight_rightEquiv,cosetCharacter_rightEquiv]
  split_ifs <;> simp [mul_inv_rev,hM,mul_assoc,mul_left_comm,mul_comm]

theorem cuspCutoffCorrection_automorphy (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (M : levelThree) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (complexMatrix M • w) = complexCharacter M*cuspCutoffCorrection Y F w := by
  have hsum := cuspCutoffTerm_summable Y hY F w
  have hreindex := (rightEquiv M).hasSum_iff.mpr hsum.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact (cuspCutoffTerm_summable Y hY F (complexMatrix M • w)).hasSum.unique
    (hscale.congr_fun (fun x => cuspCutoffTerm_automorphy Y F M x w))

lemma cuspCutoffCorrection_eq (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (w : HyperbolicSpace) (x : CuspCosets) (hx : Y<cosetHeight x w) :
    cuspCutoffCorrection Y F w = (cosetCharacter x)⁻¹*F (cosetHeight x w) := by
  unfold cuspCutoffCorrection
  rw [tsum_eq_single x]
  · simp [cuspCutoffTerm,hx]
  · intro y hy
    have hn : ¬Y<cosetHeight y w := fun hh => hy (high_coset_unique Y hY w y x hh hx)
    simp [cuspCutoffTerm,hn]

lemma hyperbolicHeight_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (upperPoint z v hv)=v := by
  have h := hyperbolicHeight_action_upperPoint 1 z v hv
  simpa [Matrix.one_apply] using h

def infinityConstantMode (s : ℂ) (v : ℝ) : ℂ :=
  if hv : 0<v then eisensteinFourierCoefficient v hv s 0 else 0

def truncatedAtInfinity (Y : ℝ) (s : ℂ) (w : HyperbolicSpace) : ℂ :=
  hyperbolicEisenstein s w-cuspCutoffCorrection Y (infinityConstantMode s) w

theorem truncatedAtInfinity_automorphy (Y : ℝ) (hY : 1≤Y) (s : ℂ) (hs : 2<s.re)
    (M : levelThree) (w : HyperbolicSpace) :
    truncatedAtInfinity Y s (complexMatrix M • w) = complexCharacter M*truncatedAtInfinity Y s w := by
  rw [truncatedAtInfinity,hyperbolicEisenstein_automorphy M s hs,
    cuspCutoffCorrection_automorphy Y hY]
  unfold truncatedAtInfinity
  ring

theorem truncatedAtInfinity_upperPoint (Y : ℝ) (hY : 1≤Y) (s : ℂ)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hYv : Y<v) :
    truncatedAtInfinity Y s (upperPoint z v hv) =
      upperEisenstein z v hv s-eisensteinFourierCoefficient v hv s 0 := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [truncatedAtInfinity,cuspCutoffCorrection_eq Y hY _ _ (cosetOf 1) (hh.symm ▸ hYv),
    hh,cosetCharacter_cosetOf,map_one,inv_one,one_mul,hyperbolicEisenstein_upperPoint]
  rw [infinityConstantMode,dite_eq_left hv]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0151

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.SupportNorms
Source SHA256: 49f4e662cf8f7407826a23a91786d14ee429c203361723b603d518e76df97bf9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0152



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
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem sourceSupportMobius_norm (E : Finset ι) :
    ‖supportMobius (fun i => Ideal.span {p i}) E‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj E)
  simp only [norm_mul, norm_one] at h
  nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) E)]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem norm_primeProduct_ge_one (S : Finset ι) :
    1 ≤ ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
  have h := primeProductNorm_ge_one p hp S
  dsimp only [primeProductNorm] at h
  nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ S, p i))]

include hp hinj in
theorem secondSourceCommonCoefficient_norm_le_one
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (G E : Finset ι) :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ 1 := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hN := primeProductNorm_ge_one p hp E
  have hμ := sourceSupportMobius_norm p hinj E
  change ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ)‖ = 1 at hμ
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), primeSubsetGenerator_norm_eq_productNorm,
    Complex.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp E).le, hμ]
  exact (mul_le_of_le_one_left (div_nonneg zero_le_one (zero_le_one.trans hN))
    hA2).trans ((div_le_one (by linarith)).mpr hN)

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d H S‖ ≤ ‖H S‖ := by
  have he : secondInputCoefficient p hg Ψ m c d H S =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) S * H S := by
    simp only [secondInputCoefficient, mul_one]
  rw [he, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((secondInputCoefficient_norm_le p hg Ψ m c d S).trans (hΨ _))

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_schwartz_bound (g : 𝓢(ℝ, ℂ)) (X : ℝ) (S : Finset ι) :
    ‖normalizedColumn p (fun U => g (columnLog p X U)) S‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  simp only [normalizedColumn, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact (div_le_self (norm_nonneg _) (norm_primeProduct_ge_one p hp S)).trans (g.norm_le_seminorm ℝ _)

include hp hinj in
theorem residualPairWeight_schwartz_bound
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (g : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 g) ^ 2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S).trans
    (normalizedColumn_schwartz_bound p hp g X (G∪S))
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) T).trans
    (normalizedColumn_schwartz_bound p hp g X (G∪T))
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) (apply_nonneg _ _)

include hp in
theorem residualPairWeight_support_bounds
    (Ψ : O →* ℂ) (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (G E S T : Finset ι) (hEG : E ⊆ G)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T ≠ 0) :
    primeProductNorm p G ≤ X*Real.exp M ∧ primeProductNorm p E ≤ X*Real.exp M ∧
      primeProductNorm p S ≤ X*Real.exp M ∧ primeProductNorm p T ≤ X*Real.exp M := by
  obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hG := normalizedColumn_subset_norm_bound p hp g M X hX hgM G S G Finset.subset_union_left hS
  exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G S S Finset.subset_union_right hS,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G T T Finset.subset_union_right hT⟩

end
section

theorem tail_radial_scalar_le (Y E n lengthScale H P : ℝ) (A : ℕ)
    (hY : 0 < Y) (hE : 0 < E) (hn : 1 ≤ n) (hL : 1 ≤ lengthScale)
    (hden : E*n^2 ≤ lengthScale^3) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    (Y/n) * (P / ((min 1 (Y/(E*n^2)))^2 * (1+H)^A)) ≤
      Y*P*(1+lengthScale^3/Y)^2 / (1+H)^A := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 0 < E*n^2 := mul_pos hE (sq_pos_of_pos hn0)
  have hs : 0 < Y/(E*n^2) := div_pos hY he
  have hr : 0 ≤ lengthScale^3/Y := div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hY.le
  have hi : (min 1 (Y/(E*n^2)))⁻¹ ≤ 1+lengthScale^3/Y := by
    by_cases h : 1 ≤ Y/(E*n^2)
    · rw [min_eq_left h, inv_one]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_div]
      exact (div_le_div_of_nonneg_right hden hY.le).trans (by linarith)
  have hi0 : 0 ≤ (min 1 (Y/(E*n^2)))⁻¹ := inv_nonneg.mpr (le_min zero_le_one hs.le)
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  have hyn : Y/n ≤ Y := div_le_self hY.le hn
  calc
    _ = (Y/n)*P*((min 1 (Y/(E*n^2)))⁻¹)^2 / (1+H)^A := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hyn hP) hi2 (sq_nonneg _) (mul_nonneg hY.le hP)

theorem sum_pair_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (U : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, if P a ∧ P b then U else 0) =
      ((s.filter P).card : ℝ)^2 * U := by
  calc
    _ = ∑ a ∈ s.filter P, ∑ b ∈ s.filter P, U := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : P a
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, Finset.sum_const_zero]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hp hinj

theorem residualTailCost_polynomial
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X Y H lengthScale P : ℝ) (A : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hXL : X * Real.exp M ≤ lengthScale) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * ((SchwartzMap.seminorm ℝ 0 0 g)^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := (SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
    (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hG,hE,hS,hT⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M X hX hgM G E S T hEG hw
    exact ⟨hG.trans hXL,hE.trans hXL,hS.trans hXL,hT.trans hXL⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [ite_eq_left hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [ite_eq_left hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [ite_eq_left ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_schwartz_bound p hp hg hinj Ψ hΨ m c d g X G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [ite_eq_right hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [ite_eq_right hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [ite_eq_left hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [ite_eq_right hd]
    exact hz.le

theorem secondSourceTailCost_polynomial
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X Y H lengthScale P : ℝ) (A : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hXL : X * Real.exp M ≤ lengthScale) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := (SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [ite_eq_left hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_polynomial p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d g M X Y H lengthScale P A hX hY hH hP hL hXL hgM
            rw [ite_eq_left hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [ite_eq_right hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_polynomial p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d g M X Y H lengthScale P A hX hY hH hP hL hXL hgM
        rw [ite_eq_right hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg hB _) hC)
    _ = _ := by ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

theorem firstCoreSecondCutoff_tail_polynomial
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
          (Y*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := firstCoreSecondCutoff_tail_bound p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  dsimp only
  have hX' : 0 < X / primeProductNorm p D :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hgbase : ∀ u, firstCoreBaseProfile g V negative u ≠ 0 → |u| ≤ M := by
    intro u hu
    apply hgM u
    intro hz
    apply hu
    simp only [firstCoreBaseProfile_apply, hz, zero_mul]
  have hP : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := mul_nonneg hC.le (apply_nonneg _ _)
  exact (hb F D Ψ m c d g V W negative t X Y M H hX hY hH hgM).trans
    (secondSourceTailCost_polynomial p hp hg hinj (F\D) Ψ hΨ m c d
      (firstCoreBaseProfile g V negative) M (X / primeProductNorm p D) Y H
      (1 + X / primeProductNorm p D * Real.exp M) (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) A
      hX' hY hH hP (by linarith [mul_pos hX' (Real.exp_pos M)]) (by linarith) hgbase)

theorem firstCoreSecondCutoff_tail_fixed_source
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A : ℕ) (g V W : 𝓢(ℝ, ℂ)) (negative : Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        C*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^A := by
  obtain ⟨s,C,hC,hb⟩ := firstCoreSecondCutoff_tail_polynomial p hp hg hinj hc A
  let C₀ := 128^4 * (SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀, by linarith, ?_⟩
  intro F D Ψ m c d t X Y M H hΨ hX hY hH hgM
  dsimp only
  have h := hb F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  apply h.trans
  calc
    _ = C₀*(1+X/primeProductNorm p D*Real.exp M)^4*Y*
        (1+(1+X/primeProductNorm p D*Real.exp M)^3/Y)^2/(1+H)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_complete_finite_transfer
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
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
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
        let Ltail := 1 + X' * Real.exp M
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        let _Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
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
            Ctail*Ltail^4*Y*(1+Ltail^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    firstCoreInputRow_finite_second_transfer (κ := κ) p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M H hM hH hgM ε hε decayOrder J
  obtain ⟨Ctail,hCtail,htail⟩ :=
    firstCoreSecondCutoff_tail_fixed_source p hp hg hinj hc tailOrder g V rowMajorant negative
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
    A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows label T lengthScale hv hCB hD hΨ hX hZ hSrows hSrows0
    hL hz hud hue huv hkap hmap hT hnorm
  dsimp only
  have hf := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
    A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows label T lengthScale hv hCB hD hΨ hX hZ hSrows hSrows0
    hL hz hud hue huv hkap hmap hT hnorm
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have ht := htail F A₀ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) t X Y M Z hΨ' hX hY hZ hgM
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact le_rfl
    · exact ht
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem sqrt_scale_shell_upper (M B b : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hb : B / 2 ≤ b) : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
  simpa only [one_mul, div_one] using principal_middle_prefactor_bound
    M B b 1 1 1 1 hM hB hb (by norm_num) le_rfl (by norm_num) le_rfl

theorem original_middle_rectangle_upper (M B b D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * Real.sqrt (M / b)) :
    D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B) := by
  calc
    _ ≤ d * e := mul_le_mul hd he hD₂ (hD₁.trans hd)
    _ ≤ U * Real.sqrt (M / b) := hcut
    _ ≤ U * (2 * Real.sqrt (M / B)) :=
      mul_le_mul_of_nonneg_left (sqrt_scale_shell_upper M B b hM hB hb) hU
    _ = _ := by ring

theorem dual_middle_rectangle_upper (M F B b N D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : B / 2 ≤ b) (hN : 0 ≤ N) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * (N * Real.sqrt (F / (M * b)))) :
    D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B))) := by
  have harg (z : ℝ) : F / (M * z) = (F / M) / z := by ring
  simp only [harg] at hcut ⊢
  have hh := original_middle_rectangle_upper (F / M) B b D₁ D₂ d e (U * N)
    (div_pos hF hM) hB hb (mul_nonneg hU hN) hD₁ hD₂ hd he
    (by simpa only [mul_assoc] using hcut)
  simpa only [mul_assoc] using hh

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

def dualMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalMiddleWindowAt W S T rows left right a b M P h ∧
    originalMiddleWindowAt W S T rows left right a b M P h ≤
      originalMiddleAt W S T rows left right a b M h := by
  classical
  constructor
  · unfold originalMiddleWindowAt
    positivity
  · unfold originalMiddleWindowAt originalMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualMiddleWindowAt W S T rows left right a b M F P h ∧
    dualMiddleWindowAt W S T rows left right a b M F P h ≤
      dualMiddleAt W S T rows left right a b M F h := by
  classical
  constructor
  · unfold dualMiddleWindowAt
    positivity
  · unfold dualMiddleWindowAt dualMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    originalMiddleWindowAt W S T rows left right a b M P h = 0 := by
  classical
  simp only [originalMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    dualMiddleWindowAt W S T rows left right a b M F P h = 0 := by
  classical
  simp only [dualMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0152

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows
Source SHA256: eddcf852b416ad861398e43fcd11e2187c9f9cb287a2a511e761343b881e16df
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0153


namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

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

theorem HasSieveExponent.original_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    originalMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B)
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.original_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply original_middle_rectangle_upper M B (Ideal.absNorm (rows i)) D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM (by linarith) (hrows i).2.1 hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) = fun _ => 0 :=
      funext (fun h => originalMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.dual_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U *
        (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    dualMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M F P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B)))
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.dual_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W F hF hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM hF (by linarith) (hrows i).2.1 (by linarith) hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) = fun _ => 0 :=
      funext (fun h => dualMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M F P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FourierBridge

theorem large_principal_scale_shape (X N Q D V : ℝ) (hD : 0 < D)
    (hcut : X * N ≤ V * D) :
    (X / D) * (N + Q * D) ≤ V + X * Q := by
  have hh : X * N / D ≤ V := (div_le_iff₀ hD).mpr hcut
  calc
    _ = X * N / D + X * Q := by field_simp
    _ ≤ _ := add_le_add hh le_rfl

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalCorrectionAt (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
  (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
  (a : n → ℂ) (b : p → ℂ)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hleft hright

theorem principalCorrectionAt_bound :
    principalCorrectionAt S T rows left right a b M ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hh := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b
    (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add, logPhase_zero, mul_one] at hh
  have heq : (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖) =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ := by
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E.val i j k‖)]
    apply Finset.sum_congr rfl
    intro D hD
    exact Finset.sum_coe_sort T (fun E => ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)
  have hp := principal_middle_prefactor_sum S T rows
    (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖)
    (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
    (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
  change principalCorrectionAt S T rows left right a b M ≤ _ at hp
  rw [heq] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem HasSieveExponent.large_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (V : ℝ)
    (hcut : Real.sqrt (M / B) * N ≤ V * (D₁ * D₂)) :
    principalCorrectionAt S T rows left right a b M ≤
      2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (V + Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hb := principalCorrectionAt_bound ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have hf := divisorEnergyFactor_nonneg ε hε N a b
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        (divisorEnergyFactor ε hε N a b *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        ((Real.sqrt (M / B) / (D₁ * D₂)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        (V + Real.sqrt (M / B) * B ^ α) := mul_le_mul_of_nonneg_left
      (large_principal_scale_shape _ _ _ _ _ (by positivity) hcut) (by positivity)
    _ = _ := by rw [sqrt_div_mul_rpow M B α hM.le (by linarith)]

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem sum_two_subtype_pools {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (f : Ideal O → Ideal O → A) :
    (∑ D : S, ∑ E : T, f D.val E.val) = ∑ D ∈ S, ∑ E ∈ T, f D E := by
  rw [Finset.sum_coe_sort S (fun D => ∑ E : T, f D E.val)]
  apply Finset.sum_congr rfl
  intro D hD
  exact Finset.sum_coe_sort T (f D)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold originalMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M P h := by
  classical
  simp_rw [originalMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.original_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.original_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply originalMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply originalMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact originalMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold dualMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M F P h := by
  classical
  simp_rw [dualMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.dual_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M F P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.dual_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W F hF P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply dualMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply dualMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact dualMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M F P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor {n p : Type*} [Fintype n] [Fintype p]
    (u : n → p → ℂ) (z : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z)‖ = c * ‖∑ j, ∑ k, u j k * z‖ := by
  simp only [← Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (M : ℝ) (h : O)
    (d : Ideal O) (i : m) : ℂ :=
  ((Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) *
      ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def originalProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalProductDivisorMiddleAt W K rows left right a b M P h := by
  classical
  unfold originalProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    originalProductDivisorMiddleAt W K rows left right a b M P h ≤
      originalMiddleWindowAt W S T rows left right a b M (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i _ _ => originalPrincipalKernel W rows M h d i)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [originalMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold originalPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.original_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.original_middle_pool deltaLoss hδ ε hε S T B N M U hB hN hM hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := originalProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => originalProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0153

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals
Source SHA256: 2bbe6a8c3bd1465aa73b7512dc1721a3f2e64188d02ece9b3ab1c385ea5e09ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0154


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

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O)
    (left : n → Ideal O) (right : p → Ideal O) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc in
theorem secondChildColumn_norm_le_test (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ ≤ ‖H S‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondChildColumn,norm_mul,norm_pow,columnCoefficient_norm_one p hp hcop hg hc]
  calc
    _ ≤ 1 * 1 * 1 * 1^4 * 1 * ‖H S‖ := by
      gcongr <;> first
        | exact hΨ _
        | exact hm
        | exact finiteSquarefreeRow_norm_le_one _ hg S f
        | exact finiteSquarefreeRow_norm_le_one _ hg S y
    _ = _ := by ring

include hc in

theorem fixedChildRow_elementary
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (X M : ℝ) (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hH : ∀ S, ‖H S‖ ≤ M) (hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ X) :
    ‖fixedChildRow p hp hcop hg F Ψ m H f y‖ ≤ 128 * X * M := by
  have heq : fixedChildRow p hp hcop hg F Ψ m H f y =
      ∑ S ∈ boundedPrimeSupports p F X, secondChildColumn p hp hcop hg Ψ m f y H S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hHS : H S = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hS,hSupp S h⟩)
    simp only [secondChildColumn,hHS,mul_zero]
  rw [heq]
  calc
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, M :=
      Finset.sum_le_sum (fun S hS => (secondChildColumn_norm_le_test p hp hcop hg hc Ψ hΨ m f y H S).trans (hH S))
    _ = ((boundedPrimeSupports p F X).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F X hX) hM

end SecondPassArithmetic

namespace DescentFiberCost
open ActualEisensteinCubic ConcreteTraceCRT
open ShortDraftLatticeCount ActualEisensteinCoordinates

theorem finite_element_count_real (S : Finset O) (K : ℝ) (hK : 1 ≤ K)
    (hS : ∀ z ∈ S, ‖eisEmbedding z‖^2 ≤ K) : (S.card : ℝ) ≤ 128*K := by
  have hbound : ∀ z ∈ S, q (coords z) ≤ (⌊K⌋₊ : ℕ) := by
    intro z hz
    have hq : (qNat z : ℝ) ≤ K := by
      rw [qNat_eq_absNorm_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
      exact hS z hz
    have hn := Nat.le_floor hq
    have he : (qNat z : ℤ) = q (coords z) := Int.toNat_of_nonneg (qO_nonneg z)
    rw [← he]
    exact_mod_cast hn
  have hcard := actual_eisenstein_count S ⌊K⌋₊ hbound
  have hr : (S.card : ℝ) ≤ 64*((⌊K⌋₊ : ℝ)+1) := by exact_mod_cast hcard
  have hf : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  linarith

theorem finite_label_row_count (T : Finset (Ideal O × O)) (F K : ℝ)
    (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖eisEmbedding z.2‖^2 ≤ K) :
    (T.card : ℝ) ≤ 128^2 * F * K := by
  let I := T.image Prod.fst
  let R := T.image Prod.snd
  have hI : (I.card : ℝ) ≤ 128*F := by
    apply finite_ideal_count_real I F hF
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).1
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).2.1
  have hR : (R.card : ℝ) ≤ 128*K := by
    apply finite_element_count_real R K hK
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact (hT z hz).2.2
  have hsub : T ⊆ I ×ˢ R := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hn := Finset.card_le_card hsub
  rw [Finset.card_product] at hn
  calc
    _ ≤ (I.card : ℝ) * R.card := by exact_mod_cast hn
    _ ≤ (128*F)*(128*K) := mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)
    _ = _ := by ring

end DescentFiberCost

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem childEnergy_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X F K A M a b : ℝ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV : ∀ s, ‖V s‖ ≤ M) (hVsupp : ∀ s, V s ≠ 0 → |s| ≤ A)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b / (X*F) ≤
      6 * 128^4 * K * (max 1 (X*Real.exp A))^2 * M^2 / X := by
  let H := fixedSecondTest p V X a b testNegative
  let Y := max 1 (X*Real.exp A)
  have hX0 : 0 < X := hX
  have hF0 : 0 < F := by linarith
  have hY : 1 ≤ Y := le_max_left _ _
  have hH : ∀ S, ‖H S‖ ≤ M := by
    intro S
    cases testNegative <;>
      simpa only [H,fixedSecondTest,Bool.false_eq_true,ite_false,ite_true,
        fixedColumnTest,norm_mul,norm_star,FourierBridge.logPhase_norm,mul_one] using hV (columnLog p X S)
  have hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ Y := by
    intro S hS
    have hv : V (columnLog p X S) ≠ 0 := by
      intro hz
      apply hS
      cases testNegative <;> simp [H,fixedSecondTest,fixedColumnTest,hz]
    exact (columnLog_norm_upper p hp X A hX0 S ((le_abs_self _).trans (hVsupp _ hv))).trans
      (le_max_right _ _)
  have hrow (f y : O) : ‖fixedChildRow p hp hcop hg pool Ψ m H f y‖ ≤ 128*Y*M :=
    fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m f y H Y M hY hM hH hSupp
  have hu (u : Oˣ) : (∑ z ∈ T, ‖idealChildRow p hp hcop hg pool Ψ m H rowNegative u z‖^2) ≤
      (T.card : ℝ) * (128*Y*M)^2 := by
    calc
      _ ≤ ∑ z ∈ T, (128*Y*M)^2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ (norm_nonneg _) (hrow _ _) 2
      _ = _ := by simp
  have he := idealChildRow_unit_energy_le p hp hcop hg pool Ψ m H rowNegative T
    ((T.card : ℝ)*(128*Y*M)^2) hu
  change childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b ≤ _ at he
  have ht := DescentFiberCost.finite_label_row_count T F K hF hK hT
  apply (div_le_iff₀ (mul_pos hX0 hF0)).mpr
  calc
    _ ≤ 6*((T.card : ℝ)*(128*Y*M)^2) := he
    _ ≤ 6*((128^2*F*K)*(128*Y*M)^2) := by gcongr
    _ = (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F) := by
      dsimp [Y]
      field_simp

end SecondPassIntegration

namespace ShortDraftLatticeCount
open ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT

theorem rowNormBall_norm_sq_le (H : ℕ) (k : ActualEisensteinCubic.O) (hk : k ∈ rowNormBall H) :
    ‖eisEmbedding k‖^2 ≤ 3*((H : ℝ)+1)^2 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hv
  obtain ⟨haL,haU⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hbL,hbU⟩ := Finset.mem_Icc.mp hb
  have ha2 : v.1^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haU) (show 0 ≤ (H : ℤ)+1+v.1 by linarith)]
  have hb2 : v.2^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbU) (show 0 ≤ (H : ℤ)+1+v.2 by linarith)]
  have hq : v.1*v.1-v.1*v.2+v.2*v.2 ≤ 3*((H : ℤ)+1)^2 := by
    nlinarith [sq_nonneg (v.1+v.2)]
  rw [eisEmbedding_eval_norm_sq]
  exact_mod_cast hq

end ShortDraftLatticeCount
namespace SecondPassArithmetic
open ActualEisensteinCubic ConcreteTraceCRT

theorem secondFrequencyCutoff_norm_sq_le (scale H : ℝ) (k : ActualEisensteinCubic.O)
    (hk : k ∈ secondFrequencyCutoff scale H) :
    ‖eisEmbedding k‖^2 ≤ 3*((⌈H/scale⌉₊ : ℝ)+1)^2 :=
  ShortDraftLatticeCount.rowNormBall_norm_sq_le _ k hk

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma green_identity_interval (f g : ℝ → ℂ) (a b : ℝ)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b,deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)) =
      (deriv f b*star (g b)-f b*star (deriv g b)) -
      (deriv f a*star (g a)-f a*star (deriv g a)) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert (((hdf x hx).hasDerivAt.mul (hg x hx).hasDerivAt.star).sub
      ((hf x hx).hasDerivAt.mul (hdg x hx).hasDerivAt.star)) using 1 ; ring
  · have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
      apply hig.mono_fun
        ((aestronglyMeasurable_deriv (deriv g) _).star)
      exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
    exact (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

theorem actual_axis_local_regular (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε C : ℝ, 0<ε ∧ ∀t∈Metric.ball (p j) ε,
      0<(Function.update p j t) 2 ∧
      DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t ∧
      ‖deriv (deriv (axisSlice (upperEisensteinField s) p j)) t‖≤C := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  refine ⟨ε,∑'r,M₂ r,hε,?_⟩
  intro t ht
  have hpos := (hbound t ht).1
  have hterms := eisenstein_axis_termwise s hs (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at hterms
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at heq
  refine ⟨hpos,(hterms.2.2.1.congr_of_eventuallyEq heq).differentiableAt,
    (hterms.2.2.2.congr_of_eventuallyEq heq.deriv).differentiableAt,?_⟩
  rw [heq.deriv.deriv_eq,hterms.2.2.2.deriv]
  exact tsum_of_norm_bounded hM₂.hasSum (fun r => ((hbound t ht).2 r).2.2)

lemma intervalIntegrable_second_of_bound (f : ℝ → ℂ) (C a b : ℝ)
    (hbound : ∀x∈Set.uIcc a b, ‖deriv (deriv f) x‖≤C) :
    IntervalIntegrable (deriv (deriv f)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).mono_fun
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact (hbound x (Set.uIoc_subset_uIcc hx)).trans (le_abs_self C)

theorem actual_eisenstein_local_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∀a b : ℝ, Set.uIcc a b ⊆ Metric.ball (p j) ε →
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  obtain ⟨εs,Cs,hεs,hregs⟩ := actual_axis_local_regular s hs p hv j
  obtain ⟨εt,Ct,hεt,hregt⟩ := actual_axis_local_regular t ht p hv j
  refine ⟨min εs εt,lt_min hεs hεt,?_⟩
  intro a b hab
  have hsa (x : ℝ) (hx : x∈Set.uIcc a b) := hregs x
    (Metric.ball_subset_ball (min_le_left _ _) (hab hx))
  have hta (x : ℝ) (hx : x∈Set.uIcc a b) := hregt x
    (Metric.ball_subset_ball (min_le_right _ _) (hab hx))
  apply green_identity_interval
  · exact fun x hx => (hsa x hx).2.1
  · exact fun x hx => (hta x hx).2.1
  · exact fun x hx => (hsa x hx).2.2.1
  · exact fun x hx => (hta x hx).2.2.1
  · exact intervalIntegrable_second_of_bound _ Cs a b (fun x hx => (hsa x hx).2.2.2)
  · exact intervalIntegrable_second_of_bound _ Ct a b (fun x hx => (hta x hx).2.2.2)

lemma actual_axis_differentiable_at (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (ht : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t := by
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  have h := hreg t (by simpa only [Function.update_self] using Metric.mem_ball_self hε)
  simp only [axisSlice_update] at h
  exact ⟨h.2.1,h.2.2.1⟩

lemma actual_axis_second_locallyIntegrable (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) :
    LocallyIntegrableOn (deriv (deriv (axisSlice (upperEisensteinField s) p j)))
      {t : ℝ | 0<(Function.update p j t) 2} volume := by
  intro t ht
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  simp only [axisSlice_update,Function.update_self,Function.update_idem] at hreg
  refine ⟨Metric.ball t ε,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hε),?_⟩
  have hconst : IntegrableOn (fun _ : ℝ => C) (Metric.ball t ε) volume := integrableOn_const
  apply hconst.mono' (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (hreg x hx).2.2.2

theorem actual_eisenstein_green_interval (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (j : Fin 3) (a b : ℝ)
    (hheight : ∀x∈Set.uIcc a b,0<(Function.update p j x) 2) :
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  apply green_identity_interval
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p j).integrableOn_compact_subset hheight isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p j).integrableOn_compact_subset hheight isCompact_uIcc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT

lemma periodic_deriv {f : ℝ → ℂ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hf

lemma embedding_rectangular_period :
    3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) = (3*Real.sqrt 3:ℝ)*Complex.I := by
  rw [eisEmbedding_eval]
  norm_num only [Int.cast_one,Int.cast_ofNat]
  unfold EisensteinEmbedding.omega3
  push_cast
  ring

lemma actual_axis_periodic_zero (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 0) 3 := by
  intro x
  have h := upperEisenstein_periodic (1:O) ((x:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s hs
  have hz : ((x+3:ℝ):ℂ)+(p 1:ℂ)*Complex.I =
      ((x:ℂ)+(p 1:ℂ)*Complex.I)+3*eisEmbedding (1:O) := by simp; ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    dite_false,dite_true]
  simp only [dite_eq_left hv]
  rw [hz]
  exact h

lemma actual_axis_periodic_one (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 1) (3*Real.sqrt 3) := by
  intro y
  have h := upperEisenstein_periodic (ActualEisensteinCoordinates.eval 1 2)
    ((p 0:ℂ)+(y:ℂ)*Complex.I) (p 2) hv s hs
  have hz : (p 0:ℂ)+((y+3*Real.sqrt 3:ℝ):ℂ)*Complex.I =
      ((p 0:ℂ)+(y:ℂ)*Complex.I)+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) := by
    rw [embedding_rectangular_period]
    push_cast
    ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (0:Fin 3)≠1 by decide,show (2:Fin 3)≠1 by decide,
    dite_false,dite_true]
  simp only [dite_eq_left hv]
  rw [hz]
  exact h

lemma green_periodic_zero {f g : ℝ → ℂ} {T : ℝ}
    (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    (deriv f T*star (g T)-f T*star (deriv g T)) -
      (deriv f 0*star (g 0)-f 0*star (deriv g 0)) = 0 := by
  have hf0 : f T=f 0 := by simpa only [zero_add] using hf 0
  have hg0 : g T=g 0 := by simpa only [zero_add] using hg 0
  have hdf : deriv f T=deriv f 0 := by simpa only [zero_add] using periodic_deriv hf 0
  have hdg : deriv g T=deriv g 0 := by simpa only [zero_add] using periodic_deriv hg 0
  rw [hf0,hg0,hdf,hdg,sub_self]

theorem actual_green_real_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..3,
      deriv (deriv (axisSlice (upperEisensteinField s) p 0)) x *
        star (axisSlice (upperEisensteinField t) p 0 x) -
      axisSlice (upperEisensteinField s) p 0 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 0)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 0 0 3]
  · exact green_periodic_zero (actual_axis_periodic_zero s hs p hv) (actual_axis_periodic_zero t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠0 by decide)] using hv

theorem actual_green_imag_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..(3*Real.sqrt 3),
      deriv (deriv (axisSlice (upperEisensteinField s) p 1)) x *
        star (axisSlice (upperEisensteinField t) p 1 x) -
      axisSlice (upperEisensteinField s) p 1 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 1)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 1 0 (3*Real.sqrt 3)]
  · exact green_periodic_zero (actual_axis_periodic_one s hs p hv) (actual_axis_periodic_one t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠1 by decide)] using hv

def cuspRectangle : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 (3*Real.sqrt 3)

lemma cuspRectangle_volume : volume cuspRectangle = ENNReal.ofReal (9*Real.sqrt 3) := by
  rw [cuspRectangle,MeasureTheory.Measure.volume_eq_prod,MeasureTheory.Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  norm_num only [sub_zero]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

lemma cuspRectangle_volume_twice_period : volume cuspRectangle = 2*volume periodDomain := by
  rw [cuspRectangle_volume,periodDomain_volume]
  have h2 : (2:ENNReal)=ENNReal.ofReal (2:ℝ) := by norm_num
  rw [h2,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

lemma rectangular_period_change_of_basis :
    (3:ℂ)=periodBasis 0 ∧
    (3*Real.sqrt 3:ℝ)*Complex.I=periodBasis 0+2*periodBasis 1 := by
  constructor
  · exact periodBasis_zero.symm
  · rw [periodBasis_zero,periodBasis_one]
    unfold EisensteinEmbedding.omega3
    push_cast
    ring

lemma rectangular_period_matrix_det :
    Matrix.det (!![(1:ℤ),1;0,2]) = 2 := by norm_num [Matrix.det_fin_two]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0154

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
Source SHA256: 6a8cb7a54e025401f4d5d1f2dac3595a53940fec4ed69cbb59c028f68cac209a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0155


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def greenWronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x*star (g x)-f x*star (deriv g x)

def greenSecondTerm (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)

lemma hasDerivAt_greenWronskian (f g : ℝ → ℂ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hdf : DifferentiableAt ℝ (deriv f) x) (hdg : DifferentiableAt ℝ (deriv g) x) :
    HasDerivAt (greenWronskian f g) (greenSecondTerm f g x) x := by
  convert ((hdf.hasDerivAt.mul hg.hasDerivAt.star).sub
    (hf.hasDerivAt.mul hdg.hasDerivAt.star)) using 1
  · rfl
  · dsimp [greenSecondTerm]
    ring

lemma weighted_vertical_green (f g : ℝ → ℂ) (a b : ℝ)
    (hpos : ∀x∈Set.uIcc a b,0<x)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b, greenSecondTerm f g x/(x:ℂ)-greenWronskian f g x/(x:ℂ)^2) =
      greenWronskian f g b/(b:ℂ)-greenWronskian f g a/(a:ℂ) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hdfc : ContinuousOn (deriv f) (Set.uIcc a b) := fun x hx => (hdf x hx).continuousAt.continuousWithinAt
  have hdgc : ContinuousOn (deriv g) (Set.uIcc a b) := fun x hx => (hdg x hx).continuousAt.continuousWithinAt
  have hW : ContinuousOn (greenWronskian f g) (Set.uIcc a b) :=
    (hdfc.mul hgc.star).sub (hfc.mul hdgc.star)
  have hne : ∀x∈Set.uIcc a b,(x:ℂ)≠0 := fun x hx => Complex.ofReal_ne_zero.mpr (hpos x hx).ne'
  have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
    apply hig.mono_fun ((aestronglyMeasurable_deriv (deriv g) _).star)
    exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
  have hG : IntervalIntegrable (greenSecondTerm f g) volume a b :=
    (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h := (hasDerivAt_greenWronskian f g x (hf x hx) (hg x hx) (hdf x hx) (hdg x hx)).div
      ((hasDerivAt_id x).ofReal_comp) (hne x hx)
    convert h using 1
    · rfl
    · simp only [id_eq,Complex.ofReal_one,mul_one]
      field_simp [hne x hx]

  · have hi₁ := hG.mul_continuousOn (Complex.continuous_ofReal.continuousOn.inv₀ hne)
    have hi₂ : IntervalIntegrable (fun x : ℝ => greenWronskian f g x/(x:ℂ)^2) volume a b :=
      (hW.div (Complex.continuous_ofReal.continuousOn.pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx))).intervalIntegrable
    simpa only [div_eq_mul_inv,Pi.inv_apply] using hi₁.sub hi₂

theorem actual_eisenstein_vertical_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫v in a..b,
      greenSecondTerm (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) v/(v:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) v/(v:ℂ)^2) =
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) b/(b:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) a/(a:ℂ) := by
  have hpos (x : ℝ) (hx : x∈Set.uIcc a b) : 0<x :=
    lt_of_lt_of_le (lt_min ha hb) hx.1
  have hsafe (x : ℝ) (hx : x∈Set.uIcc a b) : 0<(Function.update p 2 x) 2 := by
    simpa only [Function.update_self] using hpos x hx
  apply weighted_vertical_green _ _ a b hpos
  · exact fun x hx => (actual_axis_differentiable_at s hs p 2 x (hsafe x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p 2 x (hsafe x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p 2 x (hsafe x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p 2 x (hsafe x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p 2).integrableOn_compact_subset hsafe isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p 2).integrableOn_compact_subset hsafe isCompact_uIcc

lemma axisSlice_self (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) :
    axisSlice f p j (p j)=f p := by
  simp only [axisSlice,Function.update_eq_self]

theorem actual_eisenstein_green_density (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∑j : Fin 3,greenSecondTerm (axisSlice (upperEisensteinField s) p j)
      (axisSlice (upperEisensteinField t) p j) (p j)) / (p 2:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) (p 2) / (p 2:ℂ)^2 =
    (s*(s-2)-star (t*(t-2))) * upperEisensteinField s p * star (upperEisensteinField t p) /
      (p 2:ℂ)^3 := by
  have hne : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  calc
    _ = (axisLaplacian (upperEisensteinField s) p * star (upperEisensteinField t p) -
        upperEisensteinField s p * star (axisLaplacian (upperEisensteinField t) p)) / (p 2:ℂ)^3 := by
      simp only [greenSecondTerm,greenWronskian,axisSlice_self,axisLaplacian,
        Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,map_sub,map_mul,map_pow,
        map_sum,Complex.star_def,Complex.conj_ofReal]
      field_simp [hne]
      ; ring
    _ = _ := by
      rw [upperEisenstein_eigenfunction s hs p hv,upperEisenstein_eigenfunction t ht p hv]
      simp only [star_mul]
      ring

end CubicEisenstein

namespace CanonicalQuadraticSieve

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

def SecondSourceSupport {ι : Type*} [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι) : Prop :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem secondExpansionSource_singleton_zero_of_not_support
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hs : ¬ SecondSourceSupport p X M x) :
    secondExpansionSource p hp hcop hg F Ψ m c d z {x}
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y = 0 := by
  by_cases hd : Disjoint x.sourceCommon x.overlap
  · have hb : ¬ primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M :=
      fun hb => hs ⟨hd,hb⟩
    have hz (N : Finset ι) :
        normalizedColumn p (fun A => g (columnLog p X A))
          (x.sourceCommon ∪ (x.overlap ∪ N)) = 0 := by
      by_contra hn
      have h := normalizedColumn_subset_norm_bound p hp g M X hX hgM
        x.sourceCommon (x.overlap ∪ N) (x.sourceCommon ∪ x.overlap)
        (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left) hn
      rw [FirstPassCubeLabels.primeProductNorm_union p _ _ hd] at h
      exact hb h
    simp only [secondExpansionSource, Finset.sum_singleton]
    have hk : secondChildKernelPair p hp hcop hg F x.overlap
        (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (-x.frequency)
        (secondSourcePairKernel p
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S))
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S)) W Y) = 0 := by
      unfold secondChildKernelPair
      apply Finset.sum_eq_zero
      intro N hN
      apply Finset.sum_eq_zero
      intro Q hQ
      simp only [secondSourcePairKernel, hz N, star_zero, zero_mul, zero_div, mul_zero]
    rw [hk]
    ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj
      (secondRayPlus Ψ z) m c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      (-x.frequency) (fun _ => 1) x.sourceCommon x.overlap (fun h => hd h.symm)
    rw [secondMaskQuotient_spec p x.divisor x.sourceCommon hE] at hz
    simp only [secondExpansionSource, Finset.sum_singleton,
      secondExpansionQuotient_of_subset p x hE, secondTotalWeight, secondCommonWeight, hz,
      mul_zero, zero_mul]

include hinj in

theorem secondExpansionSource_eq_supported
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon) :
    secondExpansionSource p hp hcop hg F Ψ m c d z s
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (SecondSourceSupport p X M))
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y := by
  classical
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p X M x
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hz := secondExpansionSource_singleton_zero_of_not_support
      p hp hcop hg hinj F Ψ m c d z g W X Y M hX hgM x (hE x hx) hs
    simpa only [secondExpansionSource, Finset.sum_singleton] using hz

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_error (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ Real.log (u / normLogScale (normLogBin u)) ∧
      Real.log (u / normLogScale (normLogBin u)) ≤ 1 := by
  rw [Real.log_div (by linarith) (normLogScale_pos _).ne', normLogScale, Real.log_exp]
  exact ⟨sub_nonneg.mpr (Nat.floor_le (Real.log_nonneg hu)),
    by have h := Nat.lt_floor_add_one (Real.log u); dsimp [normLogBin]; linarith⟩

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

abbrev SecondLogIndex := ℕ × ℕ × ℕ

def secondLogE (j : SecondLogIndex) : ℝ := normLogScale j.1
def secondLogV (j : SecondLogIndex) : ℝ := normLogScale j.2.1
def secondLogK (j : SecondLogIndex) : ℝ := normLogScale j.2.2

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogIndex (D : Finset ι) (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor), normLogBin (primeProductNorm p x.overlap),
    normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2))

def secondLogX (R : Finset ι) (X : ℝ) (j : SecondLogIndex) : ℝ :=
  X / (secondLogE j * secondLogV j * primeProductNorm p R)

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogX_pos (R : Finset ι) (X : ℝ) (hX : 0 < X) (j : SecondLogIndex) :
    0 < secondLogX p R X j := by
  exact div_pos hX (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))

omit [DecidableEq ι] in
lemma actualSecondRow_ne_zero (D E : Finset ι) (k : O) (hk : k ≠ 0) :
    actualSecondRow p D E k ≠ 0 :=
  mul_ne_zero (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) hk

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

include hp in

omit [DecidableEq ι] in
theorem secondLogIndex_coordinates (C D R : Finset ι) (X : ℝ) (hX : 0 < X)
    (x : SecondExpansionData ι) (hk : x.frequency ≠ 0) :
    let j := secondLogIndex p D x
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 := by
  dsimp only
  have hE := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hV := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hK := normLogBin_error (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)
    (element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk))
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hX0 := hX.ne'
  have hNE := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have he := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hv := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio :
      primeProductNorm p x.overlap * secondLogX p R X (secondLogIndex p D x) /
        secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (expansionSupportData C D x) =
      (primeProductNorm p x.divisor / normLogScale (normLogBin (primeProductNorm p x.divisor))) *
        (primeProductNorm p x.overlap / normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [secondLogX, secondExpansionScale, expansionSupportData, secondLogIndex,
      secondLogE, secondLogV, primeSubsetGenerator_norm_eq_productNorm]
    field_simp

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change |Real.log (primeProductNorm p x.overlap * _ / _)| ≤ 2
    rw [hratio, Real.log_mul (div_ne_zero hNE he)
      (div_ne_zero (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne' hv)]
    rw [abs_of_nonneg (add_nonneg hE.1 hV.1)]
    linarith [hE.2,hV.2]
  · simp only [secondSectorUd, expansionSupportData, primeSubsetGenerator_norm_eq_productNorm,
      div_self (FirstPassCubeLabels.primeProductNorm_pos p hp D).ne', Real.log_one, abs_zero]
    norm_num
  · change |Real.log (‖eisEmbedding _‖^2 / _)| ≤ 2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    change |Real.log (primeProductNorm p x.divisor / normLogScale (normLogBin (primeProductNorm p x.divisor)))| ≤ 2
    rw [abs_of_nonneg hE.1]
    linarith [hE.2]
  · change |Real.log (primeProductNorm p x.overlap / normLogScale (normLogBin (primeProductNorm p x.overlap)))| ≤ 2
    rw [abs_of_nonneg hV.1]
    linarith [hV.2]
  · change |Real.log (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 /
      normLogScale (normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)))| ≤ 2
    rw [abs_of_nonneg hK.1]
    linarith [hK.2]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_radial_scale (D R : Finset ι) (X Y : ℝ) (hX : X ≠ 0) (j : SecondLogIndex) :
    Y * secondLogK j / (primeProductNorm p D * (secondLogE j)^2 *
      (secondLogV j)^2 * (secondLogX p R X j)^2) =
    Y * secondLogK j * (primeProductNorm p R)^2 / (primeProductNorm p D * X^2) := by
  unfold secondLogX secondLogE secondLogV secondLogK normLogScale
  field_simp

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondBaseLabel (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂

include hp in
omit [DecidableEq ι] in
lemma secondBaseLabel_ne_zero (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    secondBaseLabel p B C v₁ v₂ ε₁ ε₂ ≠ 0 := by
  apply mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (hp i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportNewLabel_norm (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) =
      ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        primeProductNorm p x.divisor * primeProductNorm p x.overlap := by
  rw [← secondSupportLabel_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [secondSupportLabel, expansionSupportData, secondBaseLabel,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm, primeProductNorm]

include hp in
omit [DecidableEq ι] in
lemma secondSupportNewLabel_ne_bot (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) ≠ ⊥ := by
  rw [← secondSupportLabel_span, ne_eq, Ideal.span_singleton_eq_bot]
  exact mul_ne_zero (mul_ne_zero (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator_ne_zero _ _)) (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

def secondLogLabelBound (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (j : SecondLogIndex) : ℝ :=
  ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 * secondLogE j * secondLogV j * Real.exp 2

include hp in
omit [DecidableEq ι] in
lemma secondLogLabelBound_ge_one (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (j : SecondLogIndex) : 1 ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))
        (normLogScale_ge_one _)) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

include hp in

omit [DecidableEq ι] in
theorem secondLogIndex_target_bounds (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) (hk : x.frequency ≠ 0) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) ≤
        secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ (secondLogIndex p D x) ∧
    ‖eisEmbedding (secondSupportRow p (expansionSupportData C D x))‖^2 ≤
        secondLogK (secondLogIndex p D x) * Real.exp 1 := by
  have hE := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).2
  have hV := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).2
  have hK := (normLogBin_scale_bounds (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)
    (element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk))).2
  refine ⟨?_, hK⟩
  rw [secondSupportNewLabel_norm]
  calc
    _ ≤ ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        (normLogScale (normLogBin (primeProductNorm p x.divisor))*Real.exp 1) *
        (normLogScale (normLogBin (primeProductNorm p x.overlap))*Real.exp 1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hE (sq_nonneg _)) hV
        (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
        (mul_nonneg (sq_nonneg _) (mul_pos (normLogScale_pos _) (Real.exp_pos _)).le)
    _ = _ := by
      simp only [secondLogLabelBound, secondLogIndex, secondLogE, secondLogV]
      rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
      ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_label_cost (B C R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (X : ℝ) (j : SecondLogIndex) :
    secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j =
      X * ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 * Real.exp 2 /
        primeProductNorm p R := by
  unfold secondLogX secondLogLabelBound secondLogE secondLogV normLogScale
  field_simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def secondLogBinBox (U K : ℝ) : Finset SecondLogIndex :=
  Finset.range (normLogBin U + 1) ×ˢ
    (Finset.range (normLogBin U + 1) ×ˢ Finset.range (normLogBin K + 1))

lemma secondLogBinBox_card (U K : ℝ) :
    (secondLogBinBox U K).card = (normLogBin U + 1)^2 * (normLogBin K + 1) := by
  simp only [secondLogBinBox, Finset.card_product, Finset.card_range]
  ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSourceSupport_bounds (X M : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon) :
    primeProductNorm p x.sourceCommon ≤ X*Real.exp M ∧
    primeProductNorm p x.divisor ≤ X*Real.exp M ∧
    primeProductNorm p x.overlap ≤ X*Real.exp M := by
  have hG := (le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.overlap)).trans hx.2
  have hV := (le_mul_of_one_le_left (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.sourceCommon)).trans hx.2
  exact ⟨hG, (primeProductNorm_mono p hp hE).trans hG, hV⟩

include hp in
lemma secondLogIndex_mem_box (D : Finset ι) (X M K : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon)
    (hk : x.frequency ≠ 0)
    (hK : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ K) :
    secondLogIndex p D x ∈ secondLogBinBox (X*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp X M x hx hE
  simp only [secondLogBinBox, secondLogIndex, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (by have h := element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk); linarith) hK⟩

def secondSupportedSector (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (SecondSourceSupport p X M)

def secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) : Finset (SecondExpansionData ι) :=
  (secondSupportedSector p F K R X M).filter (fun x => secondLogIndex p D x = j)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_mem (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
      x.frequency ≠ 0 ∧ x.frequency ∈ K x.sourceCommon x.divisor ∧
      x.sourceCommon \ x.divisor = R ∧ SecondSourceSupport p X M x := by
  obtain ⟨hx,hs⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk⟩ := (mem_secondExpansionPool _ _ _).mp hx
  obtain ⟨hk0,hk⟩ := Finset.mem_erase.mp hk
  exact ⟨hG,hE,hV,hk0,hk,hr,hs⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogSector_subset (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondLogSector p D F K R X M j ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

include hp in

theorem sum_secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M Kmax : ℝ)
    (hK : ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax)
    (H : SecondExpansionData ι → ℂ) :
    (∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
      ∑ x ∈ secondLogSector p D F K R X M j, H x) =
      ∑ x ∈ secondSupportedSector p F K R X M, H x := by
  simp only [secondLogSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have hj := secondLogIndex_mem_box p hp D X M Kmax x hs hE hk0 (hK x hx)
  rw [Finset.sum_eq_single_of_mem (secondLogIndex p D x) hj]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_lower (D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    Real.exp (-M) ≤ secondLogX p R X (secondLogIndex p D x) := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have he := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).1
  have hv := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).1
  have hGR : primeProductNorm p x.sourceCommon = primeProductNorm p x.divisor * primeProductNorm p R := by
    rw [← hr, ← FirstPassCubeLabels.primeProductNorm_union p x.divisor (x.sourceCommon\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hE]
  have hprod : secondLogE (secondLogIndex p D x) * secondLogV (secondLogIndex p D x) * primeProductNorm p R ≤ X*Real.exp M := by
    calc
      _ ≤ primeProductNorm p x.divisor * primeProductNorm p x.overlap * primeProductNorm p R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul he hv (normLogScale_pos _).le
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le)
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
      _ = primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap := by rw [hGR]; ring
      _ ≤ _ := hs.2
  unfold secondLogX
  apply (le_div_iff₀ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))).mpr
  calc
    _ ≤ Real.exp (-M) * (X*Real.exp M) := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = X := by rw [Real.exp_neg]; field_simp

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0155

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.LogarithmicTargets
Source SHA256: 1215b854cbf232872a7d4536ab5fbcd4b5b7b48cfb5067b7881316f1f1daa49b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0156


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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogTargets (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (Ideal O × O) :=
  (secondLogSector p D F K R X M j).image (fun x =>
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogTargets_mem (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondLogSector p D F K R X M j) :
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)) ∈
      secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
lemma secondLogTargets_bounds (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    q.1 ≠ ⊥ ∧ (Ideal.absNorm q.1 : ℝ) ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j ∧
      q.2 ≠ 0 ∧ ‖eisEmbedding q.2‖^2 ≤ secondLogK j * Real.exp 1 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hs := secondSupportedSector_mem p F K R X M x hx
  have hb := secondLogIndex_target_bounds p hp B C D v₁ v₂ ε₁ ε₂ x hs.2.2.2.1
  rw [hj] at hb
  exact ⟨secondSupportNewLabel_ne_bot p hp B C D v₁ v₂ ε₁ ε₂ x, hb.1,
    actualSecondRow_ne_zero p D x.divisor x.frequency hs.2.2.2.1, hb.2⟩

include hp in
lemma secondLogSector_coordinates (C D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (j : SecondLogIndex) (x : SecondExpansionData ι)
    (hx : x ∈ secondLogSector p D F K R X M j) :
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 := by
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hs := secondSupportedSector_mem p F K R X M x hx
  have h := secondLogIndex_coordinates p hp C D R X hX x hs.2.2.2.1
  dsimp only at h
  rw [hj] at h
  exact h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_remainder_bound (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (x : SecondExpansionData ι) (hx : x ∈ secondSupportedSector p F K R X M) :
    primeProductNorm p R ≤ X*Real.exp M := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have h := (secondSourceSupport_bounds p hp X M x hs hE).1
  rw [← hr]
  exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_eq_empty (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hR : ¬ primeProductNorm p R ≤ X*Real.exp M) :
    secondSupportedSector p F K R X M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hR (secondSupportedSector_remainder_bound p hp F R K X M x hx)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem truncatedSecondSource_eq_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y := by
  dsimp only
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  simp only [boundedPrimeSupports, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R hR
  have hE : ∀ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R,
      x.divisor ⊆ x.sourceCommon := by
    intro x hx
    exact ((mem_secondExpansionPool _ _ _).mp (Finset.mem_filter.mp hx).1).2.1
  have hs := secondExpansionSource_eq_supported p hp hcop hg hinj F Ψ m c d z
    g W X Y M hX hgM (secondExpansionSector F (fun G E => (K G E).erase 0) R) hE
  rw [hs]
  change secondExpansionSource p hp hcop hg F Ψ m c d z (secondSupportedSector p F K R X M)
      _ _ W Y = _
  by_cases hNR : primeProductNorm p R ≤ X*Real.exp M
  · rw [ite_eq_left hNR]
    simp only [secondExpansionSource]
    exact (sum_secondLogSector p hp D F K R X M Kmax (hK R hR) _).symm
  · rw [ite_eq_right hNR, secondSupportedSector_eq_empty p hp F R K X M hNR]
    simp only [secondExpansionSource, Finset.sum_empty]

include hinj in
theorem truncatedSecondSource_norm_le_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K‖ ≤
      ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            ‖secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y‖ := by
  dsimp only
  rw [truncatedSecondSource_eq_binned p hp hcop hg hinj hc hpr D F Ψ m c d g W X Y M Kmax hX hgM K hK]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact le_rfl
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro R hR
    exact norm_sum_le _ _

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

lemma supported_cutoff_denominator (E G U : ℝ) (hE : E ≤ G) (hG : 1 ≤ G) :
    E * (U/G)^2 ≤ U^2 := by
  have hG0 : 0 < G := by linarith
  have hEG : E ≤ G^2 := by nlinarith
  have he : E/G^2 ≤ 1 := (div_le_one (sq_pos_of_pos hG0)).mpr hEG
  calc
    E*(U/G)^2 = U^2*(E/G^2) := by ring
    _ ≤ U^2*1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := mul_one _

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def firstCoreSecondRowBound (D A : Finset ι) (X Y M Z : ℝ) : ℝ :=
  3 * primeProductNorm p D * ((X/primeProductNorm p A)*Real.exp M) *
    ((⌈Z*(((X/primeProductNorm p A)*Real.exp M)^2)/Y⌉₊ : ℝ)+1)^2

include hp in

theorem firstCoreSecondCutoff_supported_row_bound
    (D A F R : Finset ι) (X Y M Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 ≤ Z)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (firstCoreSecondCutoff p A X Y M Z) R
      (X/primeProductNorm p A) M) :
    ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤
      firstCoreSecondRowBound p D A X Y M Z := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F
    (firstCoreSecondCutoff p A X Y M Z) R (X/primeProductNorm p A) M x hx
  let U := (X/primeProductNorm p A)*Real.exp M
  have hU : 0 < U := mul_pos (div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A)) (Real.exp_pos _)
  have hNE := FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor
  have hNG := FirstPassCubeLabels.primeProductNorm_pos p hp x.sourceCommon
  have hEupper : primeProductNorm p x.divisor ≤ U :=
    (secondSourceSupport_bounds p hp _ M x hs hE).2.1
  have hden : primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 ≤ U^2 := by
    rw [show ((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.sourceCommon by dsimp [U]; ring]
    exact supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hE) (primeProductNorm_ge_one p hp _)
  have hdenpos : 0 < primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 := by
    exact mul_pos hNE (sq_pos_of_pos (mul_pos (div_pos (div_pos hX
      (FirstPassCubeLabels.primeProductNorm_pos p hp A)) hNG) (Real.exp_pos _)))
  have hratio : Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2)) ≤ Z*U^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*U^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hratio
  have hkbound := secondFrequencyCutoff_norm_sq_le _ Z x.frequency hk
  simp only [ primeSubsetGenerator_norm_eq_productNorm] at hkbound
  have hkbound' : ‖eisEmbedding x.frequency‖^2 ≤ 3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hkbound.trans
    gcongr
  have hrow : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 =
      primeProductNorm p D * primeProductNorm p x.divisor * ‖eisEmbedding x.frequency‖^2 := by
    simp only [actualSecondRow, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm]
  rw [hrow]
  calc
    _ ≤ (primeProductNorm p D * U) * (3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hEupper (FirstPassCubeLabels.primeProductNorm_pos p hp D).le)
        hkbound' (sq_nonneg _) (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp D) hU).le
    _ = firstCoreSecondRowBound p D A X Y M Z := by unfold firstCoreSecondRowBound; dsimp [U]; ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (densityChildEnergy)

theorem normalized_binned_second_density_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (Y : ℝ), 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Kmax : ℝ) (K : Finset ι → Finset ι → Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
          ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) →
        let c := secondBaseLabel p B C v₁ v₂ ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖^2) +
          ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
            ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            (Y * primeProductNorm p R / X^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
              (windows 5) (windows 6) (secondLogX p R X j) (secondLogX p R X j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU M 2 hM (by norm_num) hgM hgM ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro Y hY θ B C D F v₁ v₂ ε₁ ε₂ Ψ m X Kmax K hv hCB hD hΨ hX hzero hK
  dsimp only
  have hθ : ∀ t, (frequencyTwist g θ) t ≠ 0 → |t| ≤ M := by
    intro t ht
    exact hgM t (fun hz => ht (by simp only [frequencyTwist_apply,hz,mul_zero]))
  apply (truncatedSecondSource_norm_le_binned p hp hcop hg hinj hc hpr D F Ψ m
    (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
    (frequencyTwist g θ) W X Y M Kmax hX hθ K hK).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := secondLogSector_coordinates p hp C D F R K X M hX j
    have hb := hbound (primeProductNorm p D) (secondLogE j) (secondLogV j)
      (secondLogX p R X j) (secondLogK j) Y
      (FirstPassCubeLabels.primeProductNorm_pos p hp D)
      (normLogScale_pos _) (normLogScale_pos _) (secondLogX_pos p hp R X hX j)
      (normLogScale_pos _) hY θ θ B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondLogSector p D F K R X M j) (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      X (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)
      (secondLogSector_subset p D F K R X M j) hv hCB hD hΨ hX
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))
      (fun x hx => (hcoord x hx).1) (fun x hx => (hcoord x hx).2.1)
      (fun x hx => (hcoord x hx).2.2.1) (fun x hx => (hcoord x hx).2.2.2.1)
      (fun x hx => (hcoord x hx).2.2.2.2)
      (secondLogTargets_mem p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      (fun q hq => (secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).1)
      (fun q hq => (secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).2.1)
    simpa only [secondBaseLabel, primeSubsetGenerator_norm_eq_productNorm,
      secondLogX_radial_scale p D R X Y hX.ne' j] using hb

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_binned_finite_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z t : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2) +
          ‖firstCoreTest (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X)
            negative t A₀ ∅‖^2 ≤
        (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  have hUbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  have hMbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → |s| ≤ M := by
    intro s hs
    apply hgM s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_binned_second_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      (firstCoreBaseProfile g V negative) rowMajorant hUbase M hM hMbase ε hε decayOrder J
  obtain ⟨Ctail,hCtail,htail⟩ :=
    firstCoreSecondCutoff_tail_fixed_source p hp hg hinj hc tailOrder g V rowMajorant negative
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  have hX' : 0 < X / primeProductNorm p A₀ :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A₀)
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have hb := htrans Y hY (firstCoreModeHeight negative t) B C D (F\A₀)
    v₁ v₂ ε₁ ε₂ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂) (X / primeProductNorm p A₀)
    (firstCoreSecondRowBound p D A₀ X Y M Z) (firstCoreSecondCutoff p A₀ X Y M Z)
    hv hCB hD hΨ' hX'
    (fun G hG E hE => firstCoreSecondCutoff_zero p A₀ X Y M Z G E)
    (fun R hR x hx => firstCoreSecondCutoff_supported_row_bound p hp D A₀ (F\A₀) R
      X Y M Z hX hY hZ x hx)
  simp only [firstCoreModeHeight_norm, secondBaseLabel] at hb
  have ht := htail F A₀ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) t X Y M Z hΨ' hX hY hZ hgM
  have hf := firstCoreInputRow_finite_le_truncated_tail p hp hg hinj hc F A₀ B
    (fun i => v₁ i+v₂ i) ε₁ ε₂ negative χ Ψ m g V X hX Y hY
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r₁ t Srows hSrows hSrows0
    (firstCoreSecondCutoff p A₀ X Y M Z)
  simp only [firstCoreModeProfile] at hf ht ⊢
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact hb
    · exact ht
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

@[fun_prop] lemma quadraticHeightDenominator_continuous (A B C D : ℝ) :
    Continuous (fun p : SpatialCoordinates => quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)) := by
  unfold quadraticHeightDenominator
  fun_prop

lemma rowSmoothPower_continuousAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) : ContinuousAt (rowSmoothPower s u) p := by
  have hq := row_denominator_pos u hu p hv
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  have hlog := (hvc.log hv.ne').sub
    ((quadraticHeightDenominator_continuous (Complex.normSq (u 0))
      (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt.log hq.ne')
  exact Complex.continuous_exp.continuousAt.comp
    ((Complex.continuous_ofReal.continuousAt.comp hlog).const_mul s)

lemma rowLogD_continuousAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ContinuousAt (fun q => rowLogD u q j) p := by
  have hq := row_denominator_pos u hu p hv
  have hvn := hv.ne'
  have hqn := hq.ne'
  have hvn2 := pow_ne_zero 2 hvn
  have hqn2 := pow_ne_zero 2 hqn
  have hqc := (quadraticHeightDenominator_continuous (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt (x := p)
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  fin_cases j
  · dsimp [rowLogD,spatialLogD,heightLogDx]
    fun_prop (disch := aesop)
  · dsimp [rowLogD,spatialLogD,heightLogDy]
    fun_prop (disch := aesop)
  · exact (continuousAt_const.div hvc hvn).sub
      ((hvc.const_mul (2*Complex.normSq (u 0))).div hqc hqn)

lemma rowLogDD_continuousAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ContinuousAt (fun q => rowLogDD u q j) p := by
  have hq := row_denominator_pos u hu p hv
  have hvn := hv.ne'
  have hqn := hq.ne'
  have hvn2 := pow_ne_zero 2 hvn
  have hqn2 := pow_ne_zero 2 hqn
  have hqc := (quadraticHeightDenominator_continuous (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt (x := p)
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  fin_cases j
  · dsimp [rowLogDD,spatialLogDD,heightLogDxx]
    fun_prop (disch := aesop)
  · dsimp [rowLogDD,spatialLogDD,heightLogDyy]
    fun_prop (disch := aesop)
  · exact (continuousAt_const.div (hvc.pow 2) hvn2).neg.sub
      (((hqc.const_mul (2*Complex.normSq (u 0))).sub
        ((hvc.const_mul (2*Complex.normSq (u 0))).mul
          (hvc.const_mul (2*Complex.normSq (u 0))))).div (hqc.pow 2) hqn2)

def smoothFirstCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*s*(rowLogD (embeddedRow r) p j:ℂ)
def smoothSecondCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*(s^2*(rowLogD (embeddedRow r) p j:ℂ)^2+s*(rowLogDD (embeddedRow r) p j:ℂ))

lemma smoothFirstCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothFirstCoefficient s r j p=deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothFirstCoefficient smoothSummand
  ring

lemma smoothSecondCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSecondCoefficient s r j p=deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field',deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothSecondCoefficient smoothSummand
  ring

lemma smoothCoefficients_continuousAt (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (smoothFirstCoefficient s r j) p ∧ ContinuousAt (smoothSecondCoefficient s r j) p := by
  have hF : ContinuousAt (smoothSummand s r) p :=
    (rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv).const_mul _
  have hD := Complex.continuous_ofReal.continuousAt.comp
    (rowLogD_continuousAt (embeddedRow r) (embeddedRow_ne_zero r) p hv j)
  have hDD := Complex.continuous_ofReal.continuousAt.comp
    (rowLogDD_continuousAt (embeddedRow r) (embeddedRow_ne_zero r) p hv j)
  exact ⟨(hF.mul_const s).mul hD,hF.mul ((hD.pow 2).const_mul (s^2) |>.add (hDD.const_mul s))⟩

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma spatial_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ∃ U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧
      ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀q∈U, 0<q 2 ∧ ∀r : CuspCosets,
        ‖smoothSummand s r q‖≤M₀ r ∧ ∀j : Fin 3,
        ‖smoothFirstCoefficient s r j q‖≤M₁ r ∧
        ‖smoothSecondCoefficient s r j q‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := clampedCoordinates deltaLoss hδ
  let C := rowBound (coordinateSection (path p))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path p))]
  let U : Set SpatialCoordinates := {q | deltaLoss<q 2 ∧ rowBound (coordinateSection (path q))<C}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (continuous_coordinate_rowBound.comp (continuous_clampedCoordinates deltaLoss hδ)) continuous_const)
  have hpU : p∈U := by constructor <;> dsimp [deltaLoss,C] <;> linarith
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨U,hU,hpU,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro q hq
  have hpos : 0<q 2 := lt_trans hδ hq.1
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r q‖≤M r := by
    rw [smoothSummand_eq_clamped s r q deltaLoss hδ hq.1.le]
    exact hbound (path q,s) hq.2.le le_rfl le_rfl r
  have hfrac : 1 / q 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hq.1.le
  have hfrac₂ : 7 / (q 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith [hq.1]
  refine ⟨hm,fun j => ?_⟩
  rw [smoothFirstCoefficient_eq_deriv _ _ _ _ hpos,smoothSecondCoefficient_eq_deriv _ _ _ _ hpos]
  constructor
  · apply (norm_smooth_axis_deriv s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply (norm_smooth_axis_deriv2 s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

def eisensteinFirstPartial (s : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  deriv (axisSlice (upperEisensteinField s) p j) (p j)

def eisensteinSecondPartial (s : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  deriv (deriv (axisSlice (upperEisensteinField s) p j)) (p j)

lemma eisensteinPartials_eq_tsum (s : ℂ) (hs : 2<s.re) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    eisensteinFirstPartial s j p=(∑'r,smoothFirstCoefficient s r j p) ∧
    eisensteinSecondPartial s j p=(∑'r,smoothSecondCoefficient s r j p) := by
  have ht := eisenstein_axis_termwise s hs p hv j
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) p hv j
  constructor
  · unfold eisensteinFirstPartial
    rw [heq.deriv_eq,ht.2.2.1.deriv]
    exact tsum_congr (fun r => (smoothFirstCoefficient_eq_deriv _ _ _ _ hv).symm)
  · unfold eisensteinSecondPartial
    rw [heq.deriv.deriv_eq,ht.2.2.2.deriv]
    exact tsum_congr (fun r => (smoothSecondCoefficient_eq_deriv _ _ _ _ hv).symm)

lemma actual_spatial_continuousAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (upperEisensteinField s) p ∧ ∀j : Fin 3,
    ContinuousAt (eisensteinFirstPartial s j) p ∧
    ContinuousAt (eisensteinSecondPartial s j) p := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := spatial_summable_derivative_bounds s hs p hv
  have hf (r : CuspCosets) : ContinuousOn (smoothSummand s r) U := by
    intro q hq
    exact ((rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) q
      (hbound q hq).1).const_mul _).continuousWithinAt
  have hsum := continuousOn_tsum hf hM₀ (fun r q hq => ((hbound q hq).2 r).1)
  have heq : (upperEisensteinField s) =ᶠ[𝓝 p] smoothEisenstein s := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact upperEisensteinField_eq_smooth s q (hbound q hq).1
  refine ⟨(hsum.continuousAt (hU.mem_nhds hpU)).congr heq.symm,fun j => ?_⟩
  have hc₁ (r : CuspCosets) : ContinuousOn (smoothFirstCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).1).continuousWithinAt
  have hc₂ (r : CuspCosets) : ContinuousOn (smoothSecondCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).2).continuousWithinAt
  have hsum₁ := continuousOn_tsum hc₁ hM₁ (fun r q hq => (((hbound q hq).2 r).2 j).1)
  have hsum₂ := continuousOn_tsum hc₂ hM₂ (fun r q hq => (((hbound q hq).2 r).2 j).2)
  have heq₁ : eisensteinFirstPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothFirstCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).1
  have heq₂ : eisensteinSecondPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothSecondCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).2
  exact ⟨(hsum₁.continuousAt (hU.mem_nhds hpU)).congr heq₁.symm,
    (hsum₂.continuousAt (hU.mem_nhds hpU)).congr heq₂.symm⟩

end CubicEisenstein

end

end OAI
end OAIOriginalModule0156

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CuspIntegration
Source SHA256: ea45860d5b37638dc7bf498090b3821f11c6320cafe9d5668b942a833f417f3f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0157


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def spatialTriple (x y v : ℝ) : SpatialCoordinates := ![x,y,v]
@[simp] lemma spatialTriple_zero (x y v : ℝ) : spatialTriple x y v 0=x := rfl
@[simp] lemma spatialTriple_one (x y v : ℝ) : spatialTriple x y v 1=y := rfl
@[simp] lemma spatialTriple_two (x y v : ℝ) : spatialTriple x y v 2=v := rfl

def cuspCylinderMeasure (a b : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (volume.restrict (Set.Icc a b)).prod
    ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod
      (volume.restrict (Set.Icc 0 3)))

def cuspBoxIntegral (a b : ℝ) (f : SpatialCoordinates → ℂ) : ℂ :=
  ∫q, f (spatialTriple q.2.2 q.2.1 q.1) ∂cuspCylinderMeasure a b

lemma continuous_spatialTriple {X : Type*} [TopologicalSpace X]
    {x y v : X → ℝ} (hx : Continuous x) (hy : Continuous y) (hv : Continuous v) :
    Continuous (fun p => spatialTriple (x p) (y p) (v p)) := by
  rw [continuous_pi_iff]
  intro j
  fin_cases j <;> assumption

lemma continuous_cuspBox_integrand (f : SpatialCoordinates → ℂ) (hf : Continuous f) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1)) :=
  hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) (by fun_prop))

lemma integrable_cuspBox (f : SpatialCoordinates → ℂ) (hf : Continuous f) (a b : ℝ) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  have h : IntegrableOn (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (Set.Icc a b ×ˢ (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3)) volume :=
    (continuous_cuspBox_integrand f hf).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  simpa only [cuspCylinderMeasure,Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using h

lemma cuspBoxIntegral_add (f g : SpatialCoordinates → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : cuspBoxIntegral a b (fun p => f p+g p)=cuspBoxIntegral a b f+cuspBoxIntegral a b g :=
  integral_add (integrable_cuspBox f hf a b) (integrable_cuspBox g hg a b)
lemma cuspBoxIntegral_sub (f g : SpatialCoordinates → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : cuspBoxIntegral a b (fun p => f p-g p)=cuspBoxIntegral a b f-cuspBoxIntegral a b g :=
  integral_sub (integrable_cuspBox f hf a b) (integrable_cuspBox g hg a b)
lemma cuspBoxIntegral_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (a b : ℝ) :
    cuspBoxIntegral a b (fun p => c*f p)=c*cuspBoxIntegral a b f := integral_const_mul _ _

lemma cuspBoxIntegral_eq_iterated (f : SpatialCoordinates → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v) := by
  unfold cuspBoxIntegral cuspCylinderMeasure
  rw [integral_prod _ (integrable_cuspBox f hf a b)]
  have hY : (0:ℝ)≤3*Real.sqrt 3 := by positivity
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hY,
    intervalIntegral.integral_of_le (show (0:ℝ)≤3 by norm_num),← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    have hc : Continuous (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v)) :=
      hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) continuous_const)
    have hi : IntegrableOn (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v))
        (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3) volume :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hi' : Integrable (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v))
        ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
      simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
    exact integral_prod _ hi')

lemma cuspBoxIntegral_eq_vertical (f : SpatialCoordinates → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, ∫v in a..b, f (spatialTriple x y v) := by
  unfold cuspBoxIntegral cuspCylinderMeasure
  rw [integral_prod_symm _ (integrable_cuspBox f hf a b)]
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => f (spatialTriple q.1.2 q.1.1 q.2)) :=
    hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) (by fun_prop))
  have hcI : Continuous (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v)) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  have hi : IntegrableOn (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v))
      (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3) volume :=
    hcI.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi' : Integrable (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v))
      ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
  rw [integral_prod _ hi']
  have hY : (0:ℝ)≤3*Real.sqrt 3 := by positivity
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hY,
    intervalIntegral.integral_of_le (show (0:ℝ)≤3 by norm_num),← integral_Icc_eq_integral_Ioc]

lemma rectangle_interval_swap (f : ℝ→ℝ→ℂ) (hf : Continuous f.uncurry) :
    (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f x y)=
      ∫x in (0:ℝ)..3, ∫y in (0:ℝ)..(3*Real.sqrt 3), f x y := by
  apply intervalIntegral_intervalIntegral_swap
  have hc : Continuous (Function.uncurry (fun y x => f x y)) := hf.comp continuous_swap
  exact (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

def greenSecondField (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondTerm (axisSlice (upperEisensteinField s) p j)
    (axisSlice (upperEisensteinField t) p j) (p j)
def greenWronskianField (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskian (axisSlice (upperEisensteinField s) p 2)
    (axisSlice (upperEisensteinField t) p 2) (p 2)
def greenAxisDensity (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondField s t j p/(p 2:ℂ)
def greenVerticalDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenAxisDensity s t 2 p-greenWronskianField s t p/(p 2:ℂ)^2
def greenBoundaryFlux (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskianField s t p/(p 2:ℂ)

def clampHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : SpatialCoordinates :=
  spatialTriple (p 0) (p 1) (max deltaLoss (p 2))
lemma clampHeight_continuous (deltaLoss : ℝ) : Continuous (clampHeight deltaLoss) :=
  continuous_spatialTriple (continuous_apply 0) (continuous_apply 1)
    (continuous_const.max (continuous_apply 2))
lemma clampHeight_eq (deltaLoss : ℝ) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) : clampHeight deltaLoss p=p := by
  ext j
  fin_cases j <;> simp [clampHeight,spatialTriple,max_eq_right hp]

def extendAboveHeight (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  f (clampHeight deltaLoss p)
lemma extendAboveHeight_continuous (deltaLoss : ℝ) (hδ : 0<deltaLoss) (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ContinuousAt f p) : Continuous (extendAboveHeight deltaLoss f) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact (hf (clampHeight deltaLoss p) (lt_of_lt_of_le hδ (le_max_left _ _))).comp
    (clampHeight_continuous deltaLoss).continuousAt
lemma extendAboveHeight_eq (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (hp : deltaLoss≤p 2) : extendAboveHeight deltaLoss f p=f p := by
  rw [extendAboveHeight,clampHeight_eq deltaLoss p hp]

lemma greenSecondField_update (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) (x : ℝ) :
    greenSecondField s t j (Function.update p j x)=
      greenSecondTerm (axisSlice (upperEisensteinField s) p j)
        (axisSlice (upperEisensteinField t) p j) x := by
  simp only [greenSecondField,axisSlice_update,Function.update_self]
lemma greenWronskianField_update (s t : ℂ) (p : SpatialCoordinates) (x : ℝ) :
    greenWronskianField s t (Function.update p 2 x)=
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) x := by
  simp only [greenWronskianField,axisSlice_update,Function.update_self]

lemma greenFields_continuousAt (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∀j,ContinuousAt (greenAxisDensity s t j) p) ∧
    ContinuousAt (greenVerticalDensity s t) p ∧ ContinuousAt (greenBoundaryFlux s t) p := by
  have hS := actual_spatial_continuousAt s hs p hv
  have hT := actual_spatial_continuousAt t ht p hv
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  have hn : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hG (j : Fin 3) : ContinuousAt (greenSecondField s t j) p := by
    unfold greenSecondField greenSecondTerm
    simp only [axisSlice_self]
    exact (((hS.2 j).2.mul hT.1.star).sub (hS.1.mul (hT.2 j).2.star))
  have hW : ContinuousAt (greenWronskianField s t) p := by
    unfold greenWronskianField greenWronskian
    simp only [axisSlice_self]
    exact (((hS.2 2).1.mul hT.1.star).sub (hS.1.mul (hT.2 2).1.star))
  exact ⟨fun j => (hG j).div hV hn,((hG 2).div hV hn).sub (hW.div (hV.pow 2) (pow_ne_zero 2 hn)),
    hW.div hV hn⟩

lemma actual_green_fields_density (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    greenAxisDensity s t 0 p+greenAxisDensity s t 1 p+greenVerticalDensity s t p=
      (s*(s-2)-star (t*(t-2)))*upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3 := by
  have h := actual_eisenstein_green_density s t hs ht p hv
  simp only [Fin.sum_univ_three,add_div] at h
  calc
    _ = _ := by
      unfold greenVerticalDensity greenAxisDensity greenSecondField greenWronskianField
      ring
    _ = _ := h

lemma spatialTriple_update_zero (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple 0 y v) 0 x := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]
lemma spatialTriple_update_one (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple x 0 v) 1 y := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]
lemma spatialTriple_update_two (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple x y 0) 2 v := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]

lemma actual_green_axis_zero_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (y v : ℝ) (hv : 0<v) :
    (∫x in (0:ℝ)..3, greenAxisDensity s t 0 (spatialTriple x y v))=0 := by
  have hf : (fun x => greenAxisDensity s t 0 (spatialTriple x y v))=
      (fun x => greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple 0 y v) 0)
        (axisSlice (upperEisensteinField t) (spatialTriple 0 y v) 0) x/(v:ℂ)) := by
    funext x
    unfold greenAxisDensity
    simp only [spatialTriple_two]
    rw [spatialTriple_update_zero,greenSecondField_update]
  rw [hf,intervalIntegral.integral_div]
  have h := actual_green_real_period_zero s t hs ht (spatialTriple 0 y v) hv
  simp only [greenSecondTerm,h,zero_div]

lemma actual_green_axis_one_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (x v : ℝ) (hv : 0<v) :
    (∫y in (0:ℝ)..(3*Real.sqrt 3), greenAxisDensity s t 1 (spatialTriple x y v))=0 := by
  have hf : (fun y => greenAxisDensity s t 1 (spatialTriple x y v))=
      (fun y => greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple x 0 v) 1)
        (axisSlice (upperEisensteinField t) (spatialTriple x 0 v) 1) y/(v:ℂ)) := by
    funext y
    unfold greenAxisDensity
    simp only [spatialTriple_two]
    rw [spatialTriple_update_one,greenSecondField_update]
  rw [hf,intervalIntegral.integral_div]
  have h := actual_green_imag_period_zero s t hs ht (spatialTriple x 0 v) hv
  simp only [greenSecondTerm,h,zero_div]

lemma actual_green_vertical_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (x y a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫v in a..b, greenVerticalDensity s t (spatialTriple x y v))=
      greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have hG (v : ℝ) : greenSecondField s t 2 (spatialTriple x y v)=
      greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple x y 0) 2)
        (axisSlice (upperEisensteinField t) (spatialTriple x y 0) 2) v := by
    rw [spatialTriple_update_two,greenSecondField_update]
  have hW (v : ℝ) : greenWronskianField s t (spatialTriple x y v)=
      greenWronskian (axisSlice (upperEisensteinField s) (spatialTriple x y 0) 2)
        (axisSlice (upperEisensteinField t) (spatialTriple x y 0) 2) v := by
    rw [spatialTriple_update_two,greenWronskianField_update]
  simp only [greenVerticalDensity,greenAxisDensity,greenBoundaryFlux,spatialTriple_two,hG,hW]
  exact actual_eisenstein_vertical_green s t hs ht (spatialTriple x y 0) a b ha hb

lemma cuspCylinder_ae_height (a b : ℝ) :
    ∀ᵐq ∂cuspCylinderMeasure a b, q.1∈Set.Icc a b :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)

lemma cuspBoxIntegral_congr (a b : ℝ) (f g : SpatialCoordinates → ℂ)
    (heq : ∀p, p 2∈Set.Icc a b→f p=g p) :
    cuspBoxIntegral a b f=cuspBoxIntegral a b g := by
  apply integral_congr_ae
  filter_upwards [cuspCylinder_ae_height a b] with q hq
  exact heq (spatialTriple q.2.2 q.2.1 q.1) hq

lemma cuspBoxIntegral_extendAboveHeight (a b : ℝ) (f : SpatialCoordinates → ℂ) :
    cuspBoxIntegral a b (extendAboveHeight a f)=cuspBoxIntegral a b f :=
  cuspBoxIntegral_congr a b _ _ (fun p hp => extendAboveHeight_eq a f p hp.1)

lemma integrable_cuspBox_of_positive_continuity (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ContinuousAt f p) (a b : ℝ) (ha : 0<a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  have hi := integrable_cuspBox (extendAboveHeight a f) (extendAboveHeight_continuous a ha f hf) a b
  apply hi.congr
  filter_upwards [cuspCylinder_ae_height a b] with q hq
  exact extendAboveHeight_eq a f _ hq.1

lemma cuspBox_green_axis_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenAxisDensity s t 0))=0 := by
  let f := extendAboveHeight a (greenAxisDensity s t 0)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  rw [cuspBoxIntegral_eq_iterated _ hf a b hab]
  trans ∫v in a..b, (0:ℂ)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hav : a≤v := by simpa only [min_eq_left hab,spatialTriple_two] using hv.1
    have hext (x y : ℝ) : f (spatialTriple x y v)=greenAxisDensity s t 0 (spatialTriple x y v) :=
      extendAboveHeight_eq a _ _ hav
    change (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v))=0
    simp_rw [hext,actual_green_axis_zero_integral s t hs ht _ v (lt_of_lt_of_le ha hav)]
    simp only [intervalIntegral.integral_zero]
  · simp only [intervalIntegral.integral_zero]

lemma cuspBox_green_axis_one (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenAxisDensity s t 1))=0 := by
  let f := extendAboveHeight a (greenAxisDensity s t 1)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  rw [cuspBoxIntegral_eq_iterated _ hf a b hab]
  trans ∫v in a..b, (0:ℂ)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hav : a≤v := by simpa only [min_eq_left hab,spatialTriple_two] using hv.1
    have hext (x y : ℝ) : f (spatialTriple x y v)=greenAxisDensity s t 1 (spatialTriple x y v) :=
      extendAboveHeight_eq a _ _ hav
    change (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v))=0
    rw [rectangle_interval_swap (fun x y => f (spatialTriple x y v))
      (hf.comp (continuous_spatialTriple continuous_fst continuous_snd continuous_const))]
    simp_rw [hext,actual_green_axis_one_integral s t hs ht _ v (lt_of_lt_of_le ha hav)]
    simp only [intervalIntegral.integral_zero]
  · simp only [intervalIntegral.integral_zero]

lemma cuspBox_green_vertical (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenVerticalDensity s t))=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f := extendAboveHeight a (greenVerticalDensity s t)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  rw [cuspBoxIntegral_eq_vertical _ hf a b hab]
  apply intervalIntegral.integral_congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  calc
    _ = ∫v in a..b, greenVerticalDensity s t (spatialTriple x y v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      exact extendAboveHeight_eq a _ _ (by simpa only [min_eq_left hab,spatialTriple_two] using hv.1)
    _ = _ := actual_green_vertical_integral s t hs ht x y a b ha (lt_of_lt_of_le ha hab)

def eisensteinHermitianDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3

lemma integrable_eisensteinHermitianDensity (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => eisensteinHermitianDensity s t (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  apply integrable_cuspBox_of_positive_continuity _ _ a b ha
  intro p hp
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  exact (((actual_spatial_continuousAt s hs p hp).1).mul
    (actual_spatial_continuousAt t ht p hp).1.star).div (hV.pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem actual_eisenstein_cylinder_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f₀ := extendAboveHeight a (greenAxisDensity s t 0)
  let f₁ := extendAboveHeight a (greenAxisDensity s t 1)
  let f₂ := extendAboveHeight a (greenVerticalDensity s t)
  have h₀ : Continuous f₀ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  have h₁ : Continuous f₁ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  have h₂ : Continuous f₂ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  have hD : cuspBoxIntegral a b (fun p => f₀ p+f₁ p+f₂ p)=
      (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t) := by
    rw [← cuspBoxIntegral_const_mul]
    apply cuspBoxIntegral_congr
    intro p hp
    change extendAboveHeight a (greenAxisDensity s t 0) p+
      extendAboveHeight a (greenAxisDensity s t 1) p+
      extendAboveHeight a (greenVerticalDensity s t) p=_
    rw [extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,
      actual_green_fields_density s t hs ht p (lt_of_lt_of_le ha hp.1)]
    unfold eisensteinHermitianDensity
    ring
  rw [← hD,cuspBoxIntegral_add (fun p => f₀ p+f₁ p) f₂ (h₀.add h₁) h₂,
    cuspBoxIntegral_add f₀ f₁ h₀ h₁]
  rw [cuspBox_green_axis_zero s t hs ht a b ha hab,cuspBox_green_axis_one s t hs ht a b ha hab,
    cuspBox_green_vertical s t hs ht a b ha hab]
  simp only [zero_add]

lemma cuspBoxIntegral_eq_iterated_positive (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ContinuousAt f p) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v) := by
  rw [← cuspBoxIntegral_extendAboveHeight a b f,
    cuspBoxIntegral_eq_iterated _ (extendAboveHeight_continuous a ha f hf) a b hab]
  apply intervalIntegral.integral_congr
  intro v hv
  have hav : a≤v := by simpa only [min_eq_left hab] using hv.1
  apply intervalIntegral.integral_congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  exact extendAboveHeight_eq a f _ hav

lemma eisensteinHermitianDensity_continuousAt (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContinuousAt (eisensteinHermitianDensity s t) p := by
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  exact (((actual_spatial_continuousAt s hs p hp).1).mul
    (actual_spatial_continuousAt t ht p hp).1.star).div (hV.pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem actual_eisenstein_cylinder_green_iterated (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*
      (∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        upperEisensteinField s (spatialTriple x y v)*star (upperEisensteinField t (spatialTriple x y v))/(v:ℂ)^3)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have h := actual_eisenstein_cylinder_green s t hs ht a b ha hab
  rw [cuspBoxIntegral_eq_iterated_positive _
    (eisensteinHermitianDensity_continuousAt s t hs ht) a b ha hab] at h
  exact h

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro E hE
    congr 1
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => Subtype.val_injective h
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

theorem primePool_singleton_eq_primeSupport (G : Ideal O) :
    primePool {G} = primeSupport G := by
  simp [primePool, primeSupport]

theorem primePool_subset_sum_eq_divisors (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (primePool {G})).powerset,
      f (∏ P ∈ E, P.val)) = ∑ d ∈ idealDivisors G, f d := by
  rw [sum_subtype_powerset_products, primePool_singleton_eq_primeSupport]
  exact (squarefree_divisor_sum_eq_support G hG f).symm

theorem middleTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      (X : ℂ) * ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
            ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
              paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
        else 0 := by
  classical
  let f : Ideal O → ℂ := fun d =>
    if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
        ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
          paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
    else 0
  change middleTruncation _ _ W X Y Z lengthScale = (X : ℂ) * ∑ d ∈ idealDivisors G, f d
  rw [← primePool_subset_sum_eq_divisors G hG f]
  unfold middleTruncation middleDivisors smallDivisors
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [f, subsetNorm, subsetMobius]
  push_cast
  by_cases hY : Y < (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) <;>
    by_cases hZ : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Z <;> simp only [hY, hZ, and_self,
      false_and, and_false, ite_true, ite_false]

theorem middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_divisors G hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
