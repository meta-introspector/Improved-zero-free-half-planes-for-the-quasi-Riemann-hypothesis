    refine ⟨mul_ne_zero hA.1 hB.1, ?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hA.1 hB.1] at hP
    rcases Multiset.mem_add.mp hP with hP | hP
    · exact hA.2 P hP
    · exact hB.2 P hP

theorem supported_sq_iff (A : Ideal O) : Supported (A ^ 2) ↔ Supported A := by
  rw [pow_two, supported_mul_iff, and_self]

theorem supported_square_parts (lengthScale : Ideal O) :
    Supported lengthScale ↔ Supported (squarePart lengthScale) ∧ Admissible (squarefreePart lengthScale) := by
  have he := supported_mul_iff (squarePart lengthScale ^ 2) (squarefreePart lengthScale)
  rw [squarePart_sq_mul_squarefreePart, supported_sq_iff] at he
  rw [he]
  have hsf := squarefree_squarefreePart lengthScale
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hsf, hB.2⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hB.2.2⟩

def supportedSquarefreeEquiv : {lengthScale : Ideal O // Supported lengthScale} ≃
    ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) where
  toFun lengthScale := (⟨squarePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).1⟩,
    ⟨squarefreePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).2⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val,
    (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩⟩
  left_inv lengthScale := Subtype.ext (squarePart_sq_mul_squarefreePart lengthScale.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2

theorem supported_tsum_squarefree_decomposition (f : Ideal O → ℂ) :
    (∑' lengthScale : Ideal O, if Supported lengthScale then f lengthScale else 0) =
      ∑' p : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}), f (p.1.val ^ 2 * p.2.val) := by
  calc
    _ = ∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, f lengthScale.val := by
      calc
        _ = ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator f lengthScale := by
          apply tsum_congr
          intro lengthScale
          rfl
        _ = _ := (tsum_subtype ({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)) f).symm
    _ = _ := (supportedSquarefreeEquiv.symm.tsum_eq (fun lengthScale => f lengthScale.val)).symm

theorem canonical_quadraticRow_argument_mul (D : Ideal O) (hD : Admissible D) (a b : O) :
    quadraticRow D (a * b) = quadraticRow D a * quadraticRow D b := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  simp only [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ a b

theorem canonical_quadraticRow_square_argument (D : Ideal O) (hD : Admissible D) (a : O) :
    quadraticRow D (a ^ 2) = idealZeroMask D a := by
  rw [pow_two, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_squared D hD]

theorem canonical_quadraticRow_primary_squarefree (D : Ideal O) (hD : Admissible D)
    (A B : Ideal O) :
    quadraticRow D (primaryGenerator (A ^ 2 * B)) =
      idealZeroMask D (primaryGenerator A) * quadraticRow D (primaryGenerator B) := by
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (A ^ 2) = primaryGenerator A ^ 2 := map_pow primaryGeneratorHom A 2
  rw [hpow, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_square_argument D hD]

theorem canonical_high_pair_squarefree_decomposition
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : ℝ → ℂ) (M K : ℝ) :
    (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
    ∑' p : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}),
      if K < (Ideal.absNorm p.2.val : ℝ) then
        (idealZeroMask I (primaryGenerator p.1.val) * idealZeroMask J (primaryGenerator p.1.val)) *
        (quadraticRow I (primaryGenerator p.2.val) * quadraticRow J (primaryGenerator p.2.val)) *
        W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) / M) else 0 := by
  let f : Ideal O → ℂ := fun lengthScale => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0
  have he : (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then f lengthScale else 0 := by
    apply tsum_congr
    intro lengthScale
    by_cases hL : Supported lengthScale <;> simp [hL, f]
  rw [he, supported_tsum_squarefree_decomposition]
  apply tsum_congr
  intro p
  dsimp only [f]
  rw [(squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2]
  by_cases hK : K < (Ideal.absNorm p.2.val : ℝ)
  · rw [ite_eq_left hK, ite_eq_left hK, canonical_quadraticRow_primary_squarefree I hI,
      canonical_quadraticRow_primary_squarefree J hJ]
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    ring
  · simp only [ite_eq_right hK]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson PrimaryIdealUnitReindex QuadraticSquarefreeKernel

theorem supported_generator_injective :
    Function.Injective (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => primaryGenerator lengthScale.val) := by
  intro I J h
  change primaryGenerator I.val = primaryGenerator J.val at h
  have hi := primaryGenerator_ne_zero_of_good_factors I.val I.property.1 (fun P hP => (I.property.2 P hP).1)
  have hj := primaryGenerator_ne_zero_of_good_factors J.val J.property.1 (fun P hP => (J.property.2 P hP).1)
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.val hi).1, ← (primaryGenerator_spec J.val hj).1, h]

theorem supported_radial_norm_summable (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun lengthScale : Ideal O => if Supported lengthScale then ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ else 0) := by
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  have hp := hs.comp_injective supported_generator_injective
  have hi : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => ‖W ((Ideal.absNorm lengthScale.val : ℝ) / M)‖) := by
    apply hp.congr
    intro lengthScale
    dsimp only [Function.comp_def]
    rw [primaryGenerator_norm_sq lengthScale.val (primaryGenerator_ne_zero_of_good_factors lengthScale.val
      lengthScale.property.1 (fun P hP => (lengthScale.property.2 P hP).1))]
  have ht : Summable (({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator
      (fun lengthScale => ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖)) := (summable_subtype_iff_indicator).mp hi
  exact ht

def originalPairSource (I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) (lengthScale : Ideal O) : ℂ :=
  if Supported lengthScale then (star (quadraticRow I (primaryGenerator lengthScale)) *
    quadraticRow J (primaryGenerator lengthScale)) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0

def originalPairLow (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K then originalPairSource I J W M lengthScale else 0

def originalPairHigh (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then originalPairSource I J W M lengthScale else 0

theorem originalPairSource_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (originalPairSource I J W M) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun lengthScale => norm_nonneg _) _ (supported_radial_norm_summable W M hM)
  intro lengthScale
  by_cases hL : Supported lengthScale
  · simp only [originalPairSource, ite_eq_left hL, norm_mul, norm_star]
    calc
      _ ≤ (1 * 1) * ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ := by
        gcongr
        · exact quadraticRow_norm_le_one I _
        · exact quadraticRow_norm_le_one J _
      _ = _ := by ring
  · simp only [originalPairSource, ite_eq_right hL, norm_zero, le_refl]

theorem originalPairLow_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairLow I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairHigh I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_eq_source_sub_low (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairHigh I J W M K lengthScale) =
      (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) -
        ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
  calc
    _ = ∑' lengthScale : Ideal O, (originalPairSource I J W M lengthScale - originalPairLow I J W M K lengthScale) := by
      apply tsum_congr
      intro lengthScale
      by_cases hK : (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K
      · simp [originalPairHigh, originalPairLow, hK, not_lt.mpr hK]
      · simp [originalPairHigh, originalPairLow, hK, lt_of_not_ge hK]
    _ = _ := (originalPairSource_summable I J W M hM).tsum_sub (originalPairLow_summable I J W M K hM)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem canonical_gcd_masked_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
      χ (primaryGenerator lengthScale) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let R := fun P : gcdMaskPrimes D => P.val
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask R Finset.univ z = 0 := by
    rw [gcdMaskPrimes_mask, badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => (supported_span_iff z).mp h |>.1 hz
    simp only [ite_eq_right hns, zero_mul]
  have hlat := canonical_same_ray_pair_poisson R Subtype.val_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_mask_lattice_eq_six_all_ideals R Finset.univ hm I J hI hJ hray W M hM
  have he : (∑' lengthScale : Ideal O, rowCoprimeMask R Finset.univ (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M)) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
        (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
    apply tsum_congr
    intro lengthScale
    rw [gcdMaskPrimes_mask, badPrime_mask_primaryGenerator]
    by_cases hL : Supported lengthScale <;> simp [hL]
  rw [he] at hid
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

theorem canonical_pair_divisor_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (z : O) :
    star (quadraticRow I z) * quadraticRow J z =
      idealZeroMask D z *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by
  rw [canonical_quadraticRow_star I hI, quadraticRow_divisor_factor I D hI hDI,
    quadraticRow_divisor_factor J D hJ hDJ]
  calc
    _ = (quadraticRow D z * quadraticRow D z) *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared D (admissible_of_dvd hI hDI)]

theorem canonical_original_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let I' := idealQuotient D I
    let J' := idealQuotient D J
    let n := primaryGenerator I' * primaryGenerator J'
    let χ := fun z => quadraticRow I' z * quadraticRow J' z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then
      (star (quadraticRow I (primaryGenerator lengthScale)) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hDI : D ∣ I := hgcd ▸ gcd_dvd_left I J
  have hDJ : D ∣ J := hgcd ▸ gcd_dvd_right I J
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hcop := (gcd_eq_iff_quotient_coprime D I J hD.1 hDI hDJ).mp hgcd
  have hqray := columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray
  have h := canonical_gcd_masked_pair_poisson D (idealQuotient D I) (idealQuotient D J)
    hIq hJq hcop hqray W M hM
  simpa only [canonical_pair_divisor_mask D I J hI hJ hDI hDJ] using h

theorem residual_pair_nontrivial (D I J : Ideal O) (hDI : D ∣ I) (hDJ : D ∣ J)
    (hIJ : I ≠ J) : idealQuotient D I ≠ 1 ∨ idealQuotient D J ≠ 1 := by
  by_contra hn
  push Not at hn
  apply hIJ
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hDI).symm
    _ = D := by rw [hn.1, mul_one]
    _ = D * idealQuotient D J := by rw [hn.2, mul_one]
    _ = J := idealQuotient_mul hDJ

theorem original_pair_dual_remove_zero (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (f : O → ℂ) :
    (∑' z : O, quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z * f z) =
      ∑' z : O, if z = 0 then 0 else
        quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z * f z :=
  quadratic_pair_tsum_remove_zero _ _ (admissible_idealQuotient hI hDI)
    (admissible_idealQuotient hJ hDJ) (residual_pair_nontrivial D I J hDI hDJ hIJ) f

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

def rayPairCoefficient (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I J : idealRange N) : ℂ :=
  if gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c then star (a I) * a J else 0

theorem annularRayGcdBlock_eq_pair_high
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ∑' lengthScale : Ideal O, originalPairHigh I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale := by
  let W := QuadraticInitialBound.annularSieveCutoff
  let f := fun (I J : idealRange N) (lengthScale : Ideal O) =>
    rayPairCoefficient N D c a I J * originalPairHigh I.val J.val W M K lengthScale
  have hf (I J : idealRange N) : Summable (f I J) :=
    (originalPairHigh_summable I.val J.val W M K hM).mul_left _
  have hterm (lengthScale : Ideal O) :
      (if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
        W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) =
      ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := by
    rw [rayPairValue_eq]
    by_cases hs : Supported lengthScale
    · by_cases hk : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)
      · have hsk : Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) := ⟨hs, hk⟩
        rw [ite_eq_left hsk]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro J _
        dsimp only [f, rayPairCoefficient, originalPairHigh, originalPairSource]
        rw [ite_eq_left hk, ite_eq_left hs]
        by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
        · rw [ite_eq_left hc, ite_eq_left hc]
          simp only [star_mul]
          ring
        · rw [ite_eq_right hc, ite_eq_right hc, zero_mul, mul_zero]
      · simp [f, originalPairHigh, hk]
    · simp [f, originalPairHigh, originalPairSource, hs]
  rw [annularRayGcdBlock_eq_tsum M N K hM D c a]
  change (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) = _
  calc
    _ = ∑' lengthScale : Ideal O, ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := tsum_congr hterm
    _ = ∑ I : idealRange N, ∑' lengthScale : Ideal O, ∑ J : idealRange N, f I J lengthScale :=
      Summable.tsum_finsetSum (fun I _ => summable_sum (fun J _ => hf I J))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [Summable.tsum_finsetSum (fun J _ => hf I J)]
      apply Finset.sum_congr rfl
      intro J _
      exact tsum_mul_left

theorem annularRayGcdBlock_eq_source_sub_low
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ((∑' lengthScale : Ideal O, originalPairSource I.val J.val QuadraticInitialBound.annularSieveCutoff M lengthScale) -
          ∑' lengthScale : Ideal O, originalPairLow I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale) := by
  rw [annularRayGcdBlock_eq_pair_high M N K hM D c a]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  rw [originalPairHigh_eq_source_sub_low I.val J.val _ M K hM]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

def originalPairDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, χ h * paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem originalPairSource_poisson (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) = originalPairDualKernel D I J W M :=
  canonical_original_pair_poisson D I J hI hJ hgcd hray W M hM

theorem annularRayGcdBlock_poisson
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        (originalPairDualKernel D I.val J.val QuadraticInitialBound.annularSieveCutoff M -
          ∑' lengthScale : Ideal O, originalPairLow I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale) := by
  rw [annularRayGcdBlock_eq_source_sub_low M N K hM D c a]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
  · have hray : columnRay I.val = columnRay J.val := hc.2.1.trans hc.2.2.symm
    rw [originalPairSource_poisson D I.val J.val (mem_idealRange.mp I.property).1
      (mem_idealRange.mp J.property).1 hc.1 hray _ M hM]
  · simp only [rayPairCoefficient, ite_eq_right hc, zero_mul]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels JointLogSeparation

theorem columnLog_extract_common {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N : Finset ι) (hd : Disjoint G N)
    (X : ℝ) (hX : 0 < X) :
    columnLog p X (G∪N) = columnLog p (X / primeProductNorm p G) N := by
  have hG := primeProductNorm_pos p hp G
  unfold columnLog
  rw [primeProductNorm_union p G N hd]
  congr 1
  field_simp

theorem normalizedColumn_extract_fixed_profile {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N : Finset ι) (hd : Disjoint G N)
    (X : ℝ) (hX : 0 < X) (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) :
    normalizedColumn p (fun S => g (columnLog p X S)) (G∪N) =
      halfNormalizationCLM U g (columnLog p (X / primeProductNorm p G) N) /
        (Real.sqrt X : ℂ) := by
  have hG := primeProductNorm_pos p hp G
  rw [normalizedColumn_union_test p hp G N hd X (X / primeProductNorm p G)
    hX (div_pos hX hG) U hUc hUs g hU]
  have he : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by field_simp
  rw [he, Real.log_one, zero_add]

theorem normalizedColumn_pair_extract_fixed_profiles {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N M : Finset ι)
    (hGN : Disjoint G N) (hGM : Disjoint G M) (X : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun S => g₁ (columnLog p X S)) (G∪N)) *
      normalizedColumn p (fun S => g₂ (columnLog p X S)) (G∪M) =
      (X : ℂ)⁻¹ * conjugateProfile (halfNormalizationCLM U g₁)
        (columnLog p (X / primeProductNorm p G) N) *
      halfNormalizationCLM U g₂ (columnLog p (X / primeProductNorm p G) M) := by
  have hG := primeProductNorm_pos p hp G
  rw [normalizedColumn_pair_union p hp G N M hGN hGM X (X / primeProductNorm p G)
    hX (div_pos hX hG) U hUc hUs g₁ g₂ hU₁ hU₂]
  have he : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by field_simp
  rw [he, Real.log_one, zero_add, zero_add]

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondVariableSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ : ℝ) (X : SecondSupportData ι → ℝ) (X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p (X x) X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))

theorem actual_second_variable_sector_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
          Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
            FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D₀ x) (secondSectorUe p E₀ x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
          A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X₀ K Y hD₀ hE₀ hV₀ hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb, hbound⟩ := htrans _ hR
  refine ⟨b, hb, ?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m X hv hCB hD hBnd hL hmap hT0 hnorm hw
  let encode := secondSupportTuple p B v₁ v₂ ε₁ ε₂
  have hi : Function.Injective encode := secondSupportTuple_injective p hinj B v₁ v₂ ε₁ ε₂
  let decode := Function.invFun encode
  have hdec (x : SecondSupportData ι) : decode (encode x) = x := Function.leftInverse_invFun hi x
  let s' := s.image encode
  let w' := fun x => w (decode x)
  let label' := fun x => secondSupportLabel p B v₁ v₂ ε₁ ε₂ (decode x)
  let z' := fun x => secondSectorZ p (X (decode x)) X₀ (decode x)
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
      actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y := by
    unfold tupleSourceSum actualSecondVariableSectorSource
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
end OAIOriginalModule0135

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
Source SHA256: af8d601f6afdf6c21a37503080f62050ea51220ed4e8a58b706b9c82305bfdca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0136


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

theorem second_common_support_reconstruct {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (E G G' : Finset ι) (hEG : E ⊆ G) (hEG' : E ⊆ G')
    (hr : Ideal.span {secondMaskQuotient p E G hEG} =
      Ideal.span {secondMaskQuotient p E G' hEG'}) : G = G' := by
  apply FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj
  have hprod (A : Finset ι) (hEA : E ⊆ A) :
      (∏ i ∈ A, (Ideal.span {p i} : Ideal O)) =
        (∏ i ∈ E, Ideal.span {p i}) * Ideal.span {secondMaskQuotient p E A hEA} := by
    rw [secondMaskQuotient_span]
    simpa only [mul_comm] using (Finset.prod_sdiff (f := fun i => (Ideal.span {p i} : Ideal O)) hEA).symm
  change (∏ i ∈ G, (Ideal.span {p i} : Ideal O)) = ∏ i ∈ G', Ideal.span {p i}
  rw [hprod G hEG, hprod G' hEG', hr]

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondSourcePairKernel (e k : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  (star (H₁ S) * H₂ T /
    ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ) * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * (primeProductNorm p S * primeProductNorm p T)))

theorem secondFrequencyKernel_eq_kernelPair (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  unfold secondFrequencyKernel secondKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, secondSourcePairKernel]
    rw [secondGaussTerm_test_factors, Finset.prod_union hd, map_mul, norm_mul,
      Complex.ofReal_mul, FirstPassCubeLabels.primeProductNorm_union p S T hd]
    ring
  · simp [hd]

theorem secondFrequencyKernel_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  rw [secondFrequencyKernel_eq_kernelPair,
    secondKernelPair_eq_children p hp hcop hg hinj hc hpr]

def secondSourceCommonCoefficient (Ψ : O →* ℂ) (m c d : O) (G E : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))

def truncatedSecondSource (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑ k ∈ K G E.val,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      secondFrequencyKernel p hp hg hinj F Ψ Ψ m
        (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

def secondSourceTail (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      ∑' k : {k : O // k ∉ K G E.val},
        secondFrequencyKernel p hp hg hinj F Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k.val
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem inputConjugateRow_eq_truncated_add_tail
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset ι → Finset ι → Finset O) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K +
        secondSourceTail p hp hg hinj F Ψ m c d H W Y K := by
  rw [inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc F Ψ m c d H W Y hY]
  unfold truncatedSecondSource secondSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hs : Summable (fun k : O => secondFrequencyKernel p hp hg hinj F Ψ Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
    simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
      (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U))]
    exact residualSecondMode_summable p hp hg hinj F G Ψ Ψ m c d
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)
      (primeSubsetGenerator_ne_zero _ _) W Y hY
  rw [← hs.sum_add_tsum_subtype_compl (K G E.val)]
  simp only [secondSourceCommonCoefficient, mul_add, Finset.mul_sum]
  ring_nf

theorem truncatedSecondSource_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ G ∈ F.powerset, ∑ E : G.powerset,
        ∑ z : SecondRayIndex, ∑ V ∈ F.powerset, ∑ k ∈ K G E.val,
          ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d G E.val *
            secondTotalWeight p hp hcop hg Ψ Ψ m
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (z,V)) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            m (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (-k)
            (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
  unfold truncatedSecondSource
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [secondFrequencyKernel_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure SecondExpansionData (ι : Type*) where
  sourceCommon : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def InSecondQuotientSector (r : O) (x : SecondExpansionData ι) : Prop :=
  ∃ h : x.divisor ⊆ x.sourceCommon,
    Ideal.span {secondMaskQuotient p x.divisor x.sourceCommon h} = Ideal.span {r}

def expansionSupportData (C D : Finset ι) (x : SecondExpansionData ι) : SecondSupportData ι where
  common := C
  firstDivisor := D
  secondDivisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency

theorem expansionSupportData_injOn
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (C D : Finset ι) (r : O) :
    Set.InjOn (expansionSupportData (ι := ι) C D) {x | InSecondQuotientSector p r x} := by
  intro x hx y hy h
  obtain ⟨hxE, hxr⟩ := hx
  obtain ⟨hyE, hyr⟩ := hy
  have he := congrArg SecondSupportData.secondDivisor h
  have hv := congrArg SecondSupportData.overlap h
  have hk := congrArg SecondSupportData.frequency h
  change x.divisor = y.divisor at he
  change x.overlap = y.overlap at hv
  change x.frequency = y.frequency at hk
  have hg : x.sourceCommon = y.sourceCommon := by
    cases x with
    | mk G E V k =>
      cases y with
      | mk G' E' V' k' =>
        dsimp only at he hxE hyE hxr hyr ⊢
        subst E'
        exact second_common_support_reconstruct p hinj E G G' hxE hyE (hxr.trans hyr.symm)
  exact SecondExpansionData.ext hg he hv hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_quotient_sector (E G : Finset ι) (hEG : E ⊆ G) (r : O)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r}) :
    primeProductNorm p G =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding r‖ ^ 2 := by
  unfold primeProductNorm
  rw [secondMaskQuotient_spec p E G hEG, map_mul, norm_mul, mul_pow]
  congr 1
  rw [eisEmbedding_norm_sq_eq_absNorm_span, eisEmbedding_norm_sq_eq_absNorm_span, hr]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem residual_scale_quotient_sector (X : ℝ) (E G : Finset ι) (hEG : E ⊆ G) (r : O)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r}) :
    X / primeProductNorm p G = X /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
        ‖eisEmbedding r‖ ^ 2) := by
  rw [primeProductNorm_quotient_sector p E G hEG r hr]

end

theorem rowCoprimeMask_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S a = rowCoprimeMask P S b := by
  have hm (i : ι) : a ∈ P i ↔ b ∈ P i := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem, hab]
  simp only [rowCoprimeMask, hm]

theorem rowCoprimeMask_mul_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) (m : O) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S (m*a) = rowCoprimeMask P S (m*b) := by
  apply rowCoprimeMask_eq_of_span_eq P S
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hab]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels
open SecondPassArithmetic (SecondSupportData secondSectorZ)

def residualColumnScale (X : ℝ) (e r : O) : ℝ :=
  X / (elementNorm e * elementNorm r)

theorem residualColumnScale_pos (X : ℝ) (hX : 0 < X) (e r : O)
    (he : e ≠ 0) (hr : r ≠ 0) : 0 < residualColumnScale X e r :=
  div_pos hX (mul_pos (elementNorm_pos e he) (elementNorm_pos r hr))

theorem secondSectorZ_residualColumnScale {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (X X₀ : ℝ) (hX : 0 < X) (e r : O) (he : e ≠ 0) (hr : r ≠ 0)
    (x : SecondSupportData ι) :
    secondSectorZ p (residualColumnScale X e r) X₀ x =
      Real.log (elementNorm e * elementNorm r * primeProductNorm p x.overlap * X₀ / X) := by
  have hNe := elementNorm_pos e he
  have hNr := elementNorm_pos r hr
  unfold secondSectorZ residualColumnScale
  congr 1
  field_simp

theorem second_divisor_residual_normalization (X : ℝ) (hX : 0 < X)
    (e r : O) (he : e ≠ 0) (hr : r ≠ 0) (a : ℂ) :
    (a / (elementNorm e : ℂ)) * (residualColumnScale X e r : ℂ)⁻¹ =
      a * (elementNorm r : ℂ) / (X : ℂ) := by
  have hNe : (elementNorm e : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (elementNorm_pos e he)
  have hNr : (elementNorm r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (elementNorm_pos r hr)
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
  simp only [residualColumnScale, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondRawVariableSector
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (X : SecondSupportData ι → ℝ) (Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x *
    secondChildKernelPair p hp hcop hg F x.overlap Ψ₁ Ψ₂ m r
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
        jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
      x.frequency (-x.frequency)
      (radialPairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
        x.frequency W g₁ g₂ (X x) (X x) Y)

theorem actualSecondRawVariableSector_fixed_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (D E V₀ X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ x ∈ s, 0 < X x) →
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y =
          actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s
            (fun x => w x * (X x : ℂ)⁻¹) F Ψ₁ Ψ₂ (m*r)
            A₁ A₂ W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X hX hk hz hud hue huv hkap
  simp only [actualSecondRawVariableSector, actualSecondVariableSectorSource]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid D E V₀ (X x) X₀ K Y hD hE hV₀ (hX x hx) hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
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
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation

theorem outerWindow_global_bound (windows : Fin 7 → ℝ → ℂ)
    (hc : ∀ j, HasCompactSupport (windows j)) (hs : ∀ j, Continuous (windows j)) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ z ud ue uv kap : ℝ,
      ‖outerWindow windows z ud ue uv kap‖ ≤ Cw := by
  have hb (j : Fin 7) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖windows j x‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((hc j).isCompact_range (hs j)).bddAbove_image continuous_norm.continuousOn
    have he (x : ℝ) : ‖windows j x‖ ≤ B := hB ⟨windows j x, ⟨x,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  choose B hB hbound using hb
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have h3 := hB 3
  have h4 := hB 4
  refine ⟨B 0 * B 1 * B 2 * B 3 * B 4, by positivity, ?_⟩
  intro z ud ue uv kap
  simp only [outerWindow, norm_mul]
  gcongr
  all_goals first | positivity | apply hbound

theorem actual_raw_variable_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      (∀ z ud ue uv kap : ℝ, ‖outerWindow windows z ud ue uv kap‖ ≤ Cw) ∧
      ∀ D E V₀ X₀ K Y : ℝ, 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K/(D*E^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖ ≤
          Cₛ*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        (∀ x ∈ s, 0 < X x) → (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x * (X x : ℂ)⁻¹‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D x) (secondSectorUe p E x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y‖ ≤
          (Bnd*Cₐ*(lengthScale*Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*r) T (windows 5) (windows 6)
                X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ :=
    actualSecondRawVariableSector_fixed_profiles p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound windows hwc (fun j => (hws j).continuous)
  have hM : ∀ j : Fin 7, 0 ≤ (fun _ : Fin 7 => A+H+1) j := by intro j; dsimp; linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ :=
    actual_second_variable_sector_uniform_transfer p hp hcop hg hinj ε hε A₁ A₂ W windows
      (fun _ => A+H+1) hM hwb decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hwglobal,?_⟩
  intro D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  obtain ⟨b,hb,hbound⟩ := htrans D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  refine ⟨b,hb,?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m r X hv hCB hdiv hX hk hz hud hue huv hkap
    hBnd hL hmap hT hnorm hw
  rw [hid D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X
    hX hk hz hud hue huv hkap]
  exact hbound B v₁ v₂ ε₁ ε₂ s T (fun x => w x*(X x : ℂ)⁻¹) Bnd lengthScale F Ψ₁ Ψ₂ (m*r) X
    hv hCB hdiv hBnd hL hmap hT hnorm hw

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassIntegration (normalizedColumn_pair_extract_fixed_profiles conjugateProfile)

theorem secondSourcePairKernel_normalized_shift {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G S T : Finset ι)
    (hGS : Disjoint G S) (hGT : Disjoint G T)
    (e k : O) (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    secondSourcePairKernel p e k
      (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
      (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y S T =
      (X : ℂ)⁻¹ * radialPairKernel p e k W
        (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
        (X / primeProductNorm p G) (X / primeProductNorm p G) Y S T := by
  unfold secondSourcePairKernel
  rw [normalizedColumn_pair_extract_fixed_profiles p hp G S T hGS hGT X hX U hUc hUs
    g₁ g₂ hU₁ hU₂]
  simp only [radialPairKernel, normalizedColumn, SecondPassIntegration.conjugateProfile_apply,
     Complex.star_def, Complex.conj_ofReal, div_eq_mul_inv,
     mul_inv_rev, map_inv₀, map_mul]
  ring_nf

end SecondPassArithmetic

open scoped BigOperators Classical
namespace UnrestrictedIdealReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open PrimaryIdealUnitReindex CanonicalQuadraticSieve

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}
abbrev NonzeroElement := {z : O // z ≠ 0}

theorem span_unit_generator (u : Oˣ) (I : NonzeroIdeal) :
    Ideal.span {u.val * idealGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, span_idealGenerator]

def unitIdealToElement (p : Oˣ × NonzeroIdeal) : NonzeroElement :=
  ⟨p.1.val * idealGenerator p.2.val, mul_ne_zero p.1.ne_zero (idealGenerator_ne_zero p.2.val p.2.property)⟩

theorem unitIdealToElement_bijective : Function.Bijective unitIdealToElement := by
  constructor
  · intro p q hpq
    have he : p.1.val * idealGenerator p.2.val = q.1.val * idealGenerator q.2.val := congrArg Subtype.val hpq
    have hi : p.2 = q.2 := by
      apply Subtype.ext
      simpa only [span_unit_generator] using congrArg (fun z : O => Ideal.span {z}) he
    have hu : p.1 = q.1 := by
      apply Units.ext
      rw [hi] at he
      exact mul_right_cancel₀ (idealGenerator_ne_zero q.2.val q.2.property) he
    exact Prod.ext hu hi
  · intro z
    let I : NonzeroIdeal := ⟨Ideal.span {z.val}, Ideal.span_singleton_eq_bot.not.mpr z.property⟩
    have ha : Associated (idealGenerator I.val) z.val :=
      Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator I.val)
    obtain ⟨u, hu⟩ := ha
    refine ⟨(u, I), Subtype.ext ?_⟩
    change u.val * idealGenerator I.val = z.val
    simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × NonzeroIdeal ≃ NonzeroElement :=
  Equiv.ofBijective unitIdealToElement unitIdealToElement_bijective

theorem tsum_nonzero_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : NonzeroElement, f z.val) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have he : (∑' z : NonzeroElement, f z.val) =
      ∑' p : Oˣ × NonzeroIdeal, f (p.1.val * idealGenerator p.2.val) :=
    (unitIdealEquiv.tsum_eq (fun z : NonzeroElement => f z.val)).symm
  have hs : Summable (fun p : Oˣ × NonzeroIdeal => f (p.1.val * idealGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr (hf.subtype _)
  rw [he, hs.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card Oˣ = 6 := by simpa only [Nat.card_eq_fintype_card] using card_units_eq_six
  rw [hc]
  norm_num

theorem tsum_unit_invariant_of_zero (f : O → ℂ) (hf : Summable f) (h0 : f 0 = 0)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : O, f z) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  have he : (∑' z : NonzeroElement, f z.val) = ∑' z : O, f z := by
    apply tsum_subtype_eq_of_support_subset
    intro z hz
    exact fun hz0 => hz (hz0 ▸ h0)
  rw [← he]
  exact tsum_nonzero_unit_invariant f hf hu

end UnrestrictedIdealReindex

end

end OAI
end OAIOriginalModule0136

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.UnrestrictedCharacters
Source SHA256: 1fb0c4fc3a3495ff3963cbc320e198a33bef7f062b7be1dc69a8b75d6f6d88df
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0137


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

def unrestrictedPairCharacter (I J lengthScale : Ideal O) : ℂ :=
  quadraticRow I (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)

theorem unrestrictedPairCharacter_span (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (z : O) :
    unrestrictedPairCharacter I J (Ideal.span {z}) = quadraticRow I z * quadraticRow J z := by
  have ha : Associated (idealGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator _)
  obtain ⟨u, hu⟩ := ha
  have hv := canonical_pair_unit_invariant I J hI hJ hray u (idealGenerator (Ideal.span {z}))
  have he : u.val * idealGenerator (Ideal.span {z}) = z := by simpa only [mul_comm] using hu
  rw [he] at hv
  exact hv.symm

theorem unrestrictedPairCharacter_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    unrestrictedPairCharacter I J (A * B) =
      unrestrictedPairCharacter I J A * unrestrictedPairCharacter I J B := by
  have hs : Ideal.span {idealGenerator A * idealGenerator B} = A * B := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_idealGenerator, span_idealGenerator]
  rw [← hs, unrestrictedPairCharacter_span I J hI hJ hray]
  rw [canonical_quadraticRow_argument_mul I hI, canonical_quadraticRow_argument_mul J hJ]
  unfold unrestrictedPairCharacter
  ring

theorem unrestrictedPairCharacter_eq_primary (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (lengthScale : Ideal O) (hL : Supported lengthScale) :
    unrestrictedPairCharacter I J lengthScale =
      quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale) := by
  have hz := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors lengthScale hL.1
    (fun P hP => (hL.2 P hP).1)
  have h := unrestrictedPairCharacter_span I J hI hJ hray (primaryGenerator lengthScale)
  rw [(primaryGenerator_spec lengthScale hz).1] at h
  exact h

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem idealGenerator_norm_sq (lengthScale : Ideal O) :
    ‖eisEmbedding (idealGenerator lengthScale)‖ ^ 2 = (Ideal.absNorm lengthScale : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]

theorem canonical_pair_fourier_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul]
  calc
    _ ≤ (1 * 1) * ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
      gcongr
      · exact quadraticRow_norm_le_one I h
      · exact quadraticRow_norm_le_one J h
    _ = _ := by ring

theorem canonical_nonprincipal_dual_ideal_reindex
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (6 : ℂ) * ∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val *
        paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) := by
  let f : O → ℂ := fun h => (quadraticRow I h * quadraticRow J h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hf : Summable f := canonical_pair_fourier_summable I J W t ht
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [quadratic_pair_zero_of_nontrivial I J hI hJ hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [canonical_pair_unit_invariant I J hI hJ hray, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  simpa only [f, idealGenerator_norm_sq, unrestrictedPairCharacter] using he

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

def fixedBadPrimes : Finset (Ideal O) := {Ideal.span {lambda}, Ideal.span {(2 : O)}}

theorem prime_good_iff_not_bad (P : Ideal O) [P.IsMaximal] :
    (lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2) ↔ P ∉ fixedBadPrimes := by
  constructor
  · rintro ⟨hl, hc⟩ hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact hl (hp ▸ Ideal.subset_span (by simp))
    · have he : P = Ideal.span {(2 : O)} := Finset.mem_singleton.mp hp
      exact hc (he ▸ twoIdeal_characteristic)
  · intro hp
    constructor
    · intro hl
      have he := maximal_ideal_eq_span_of_mem P inferInstance lambda lambdaIdeal_maximal hl
      exact hp (he ▸ Finset.mem_insert_self _ _)
    · intro hc
      have ht : (2 : O) ∈ P := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hz : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
        simpa only [map_ofNat] using hz
      have he := maximal_ideal_eq_span_of_mem P inferInstance (2 : O) twoIdeal_maximal ht
      exact hp (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

def badPrimeSupport (I : Ideal O) : Finset (Ideal O) := IdealMobiusDivisorSum.primeSupport I ∩ fixedBadPrimes

def goodPrimeSupport (I : Ideal O) : Finset (Ideal O) := IdealMobiusDivisorSum.primeSupport I \ fixedBadPrimes

def goodSquarefreePart (I : Ideal O) : Ideal O := ∏ P ∈ goodPrimeSupport I, P

theorem badPrimeSupport_subset (I : Ideal O) : badPrimeSupport I ⊆ fixedBadPrimes :=
  Finset.inter_subset_right

theorem goodSquarefreePart_admissible (I : Ideal O) : Admissible (goodSquarefreePart I) := by
  have hs : goodPrimeSupport I ⊆ IdealMobiusDivisorSum.primeSupport I := Finset.sdiff_subset
  refine ⟨support_product_ne_zero hs, squarefree_support_product hs, ?_⟩
  intro P hP
  change P ∈ UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ goodPrimeSupport I, Q) at hP
  rw [factors_support_product hs] at hP
  have hp : P ∈ goodPrimeSupport I := hP
  have hprime := support_prime (hs hp)
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  exact (prime_good_iff_not_bad P).mpr (Finset.mem_sdiff.mp hp).2

theorem squarefree_bad_good_product (I : Ideal O) (hI : Squarefree I) :
    (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I = I := by
  have hu : badPrimeSupport I ∪ goodPrimeSupport I = IdealMobiusDivisorSum.primeSupport I := by
    ext P
    simp only [badPrimeSupport, goodPrimeSupport, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (badPrimeSupport I) (goodPrimeSupport I) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [goodSquarefreePart, ← Finset.prod_union hd, hu]
  exact squarefree_support_product_self hI

theorem bad_good_coprime (I : Ideal O) :
    IsCoprime (∏ P ∈ badPrimeSupport I, P) (goodSquarefreePart I) := by
  unfold goodSquarefreePart
  apply IsCoprime.prod_left
  intro P hP
  apply IsCoprime.prod_right
  intro Q hQ
  have hp := support_prime (Finset.mem_inter.mp hP).1
  have hq := support_prime (Finset.mem_sdiff.mp hQ).1
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  let : Q.IsMaximal := (Ideal.isPrime_of_prime hq).isMaximal hq.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro heq
  exact (Finset.mem_sdiff.mp hQ).2 (heq ▸ (Finset.mem_inter.mp hP).2)

theorem unrestrictedPairCharacter_squarefree_bad_split
    (I J B : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hB : Squarefree B) :
    unrestrictedPairCharacter I J B =
      unrestrictedPairCharacter I J (∏ P ∈ badPrimeSupport B, P) *
        (quadraticRow I (primaryGenerator (goodSquarefreePart B)) *
          quadraticRow J (primaryGenerator (goodSquarefreePart B))) := by
  conv_lhs => rw [← squarefree_bad_good_product B hB]
  rw [unrestrictedPairCharacter_mul I J hI hJ hray,
    unrestrictedPairCharacter_eq_primary I J hI hJ hray _
      (admissible_supported (goodSquarefreePart_admissible B))]

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge

theorem fixedBadPrimes_card : fixedBadPrimes.card = 2 := by
  have hn : (Ideal.span {lambda} : Ideal O) ≠ Ideal.span {(2 : O)} := by
    intro h
    have hb : badPrime false = badPrime true := h
    have := badPrime_injective hb
    cases this
  simp [fixedBadPrimes, hn]

theorem fixedBadPrimes_powerset_card : fixedBadPrimes.powerset.card = 4 := by
  rw [Finset.card_powerset, fixedBadPrimes_card]
  norm_num

def badPrimeSector (I : Ideal O) : fixedBadPrimes.powerset :=
  ⟨badPrimeSupport I, Finset.mem_powerset.mpr (badPrimeSupport_subset I)⟩

theorem goodSquarefreePart_injective_on_sector (I J : Ideal O) (hI : Squarefree I) (hJ : Squarefree J)
    (hs : badPrimeSector I = badPrimeSector J) (hg : goodSquarefreePart I = goodSquarefreePart J) : I = J := by
  have he : badPrimeSupport I = badPrimeSupport J := congrArg Subtype.val hs
  calc
    I = (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I := (squarefree_bad_good_product I hI).symm
    _ = (∏ P ∈ badPrimeSupport J, P) * goodSquarefreePart J := by rw [he, hg]
    _ = J := squarefree_bad_good_product J hJ

theorem goodSquarefreePart_norm_le (I : Ideal O) (hI : Squarefree I) :
    Ideal.absNorm (goodSquarefreePart I) ≤ Ideal.absNorm I := by
  have hd : goodSquarefreePart I ∣ I := by
    exact ⟨∏ P ∈ badPrimeSupport I, P, (squarefree_bad_good_product I hI).symm.trans (mul_comm _ _)⟩
  apply Nat.le_of_dvd
  · exact Nat.pos_iff_ne_zero.mpr (fun hn => hI.ne_zero (Ideal.absNorm_eq_zero_iff.mp hn))
  · exact map_dvd Ideal.absNorm hd

theorem goodSquarefreePart_mem_idealRange (I : Ideal O) (hI : Squarefree I) (M : ℝ)
    (hM : (Ideal.absNorm I : ℝ) ≤ M) : goodSquarefreePart I ∈ idealRange M := by
  apply mem_idealRange.mpr
  exact ⟨goodSquarefreePart_admissible I, (Nat.cast_le.mpr (goodSquarefreePart_norm_le I hI)).trans hM⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open FiniteSieveOperator

theorem norm_sum_sq_eq_of_pair_gram {n : Type*} [Fintype n] (x y : n → ℂ)
    (h : ∀ j k, star (x j) * x k = star (y j) * y k) :
    ‖∑ j, x j‖ ^ 2 = ‖∑ j, y j‖ ^ 2 := by
  have hs : star (∑ j, x j) * (∑ j, x j) = star (∑ j, y j) * (∑ j, y j) := by
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => h k j))
  have hx : star (∑ j, x j) * (∑ j, x j) = (‖∑ j, x j‖ : ℂ) ^ 2 := Complex.conj_mul' _
  have hy : star (∑ j, y j) * (∑ j, y j) = (‖∑ j, y j‖ : ℂ) ^ 2 := Complex.conj_mul' _
  rw [hx, hy] at hs
  exact_mod_cast hs

theorem squarefree_sector_energy_bound
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Squarefree (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (cols j) = columnRay (cols k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i)) * a j‖ ^ 2) ≤
      sieveNorm M N * ∑ j, ‖a j‖ ^ 2 := by
  let good := fun i => goodSquarefreePart (rows i)
  let d := idealGenerator (∏ P ∈ E.val, P)
  let b := fun j => a j * quadraticRow (cols j) d
  have hgood : Function.Injective good := by
    intro i k h
    apply hr
    exact goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
      ((hE i).trans (hE k).symm) h
  have hgoodrows (i : m) : Admissible (good i) ∧ (Ideal.absNorm (good i) : ℝ) ≤ M := by
    exact mem_idealRange.mp (goodSquarefreePart_mem_idealRange _ (hrows i).1 M (hrows i).2)
  have hnorm (i : m) :
      ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i)) * a j‖ ^ 2 =
      ‖∑ j, quadraticRow (cols j) (primaryGenerator (good i)) * b j‖ ^ 2 := by
    apply norm_sum_sq_eq_of_pair_gram
    intro j k
    have hbad : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    have hp := unrestrictedPairCharacter_squarefree_bad_split (cols j) (cols k) (rows i)
      (hcols j).1 (hcols k).1 (hray j k) (hrows i).1
    simp only [unrestrictedPairCharacter, hbad] at hp
    change quadraticRow (cols j) (idealGenerator (rows i)) * quadraticRow (cols k) (idealGenerator (rows i)) =
      (quadraticRow (cols j) d * quadraticRow (cols k) d) *
      (quadraticRow (cols j) (primaryGenerator (good i)) * quadraticRow (cols k) (primaryGenerator (good i))) at hp
    calc
      _ = (quadraticRow (cols j) (idealGenerator (rows i)) * quadraticRow (cols k) (idealGenerator (rows i))) *
          (star (a j) * a k) := by
            rw [star_mul, canonical_quadraticRow_star _ (hcols j).1]
            ring
      _ = _ := by
        rw [hp]
        simp only [b, star_mul, canonical_quadraticRow_star _ (hcols j).1]
        ring
  have hcoeff : (∑ j, ‖b j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    apply pow_le_pow_left₀ (norm_nonneg _)
    dsimp only [b]
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hfamily := family_squared_norm_le good cols hgood hc M N hgoodrows hcols
  calc
    _ = ∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (good i)) * b j‖ ^ 2 :=
      Finset.sum_congr rfl (fun i _ => hnorm i)
    _ ≤ ‖operator (fun i j => quadraticRow (cols j) (primaryGenerator (good i)))‖ ^ 2 * ∑ j, ‖b j‖ ^ 2 :=
      FiniteSieveOperator.energy_bound _ b
    _ ≤ sieveNorm M N * ∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul hfamily hcoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sieveNorm_nonneg M N)

theorem unrestricted_squarefree_energy_bound
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Squarefree (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (cols j) = columnRay (cols k)) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i)) * a j‖ ^ 2) ≤
      4 * sieveNorm M N * ∑ j, ‖a j‖ ^ 2 := by
  let σ := fun i => badPrimeSector (rows i)
  have h (E : fixedBadPrimes.powerset) :
      (∑ i : {i // σ i = E}, ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i.val)) * a j‖ ^ 2) ≤
        sieveNorm M N * ∑ j, ‖a j‖ ^ 2 := by
    apply squarefree_sector_energy_bound (fun i : {i // σ i = E} => rows i.val) cols
      (fun i k hik => Subtype.ext (hr hik)) hc M N
      (fun i => hrows i.val) hcols hray E (fun i => i.property) a
  calc
    _ = ∑ E : fixedBadPrimes.powerset, ∑ i : {i // σ i = E},
        ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i.val)) * a j‖ ^ 2 :=
      (Fintype.sum_fiberwise σ _).symm
    _ ≤ ∑ _E : fixedBadPrimes.powerset, sieveNorm M N * ∑ j, ‖a j‖ ^ 2 :=
      Finset.sum_le_sum (fun E _ => h E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe,
        fixedBadPrimes_powerset_card]
      ring

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

def originalPairIdealDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I' J' lengthScale.val * paperRadialFourier W
        (M * (Ideal.absNorm lengthScale.val : ℝ) / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem originalPairDualKernel_eq_ideal
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    originalPairDualKernel D I J W M = originalPairIdealDualKernel D I J W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  let n := primaryGenerator Q * primaryGenerator T
  let R := fun P : gcdMaskPrimes D => P.val
  let χ := fun z => quadraticRow Q z * quadraticRow T z
  let a := fun E : Finset (gcdMaskPrimes D) =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let f := fun E : Finset (gcdMaskPrimes D) => ∑' h : O, χ h * paperRadialFourier W
    (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  let g := fun E : Finset (gcdMaskPrimes D) => ∑' lengthScale : NonzeroIdeal,
    unrestrictedPairCharacter Q T lengthScale.val * paperRadialFourier W
      (M * (Ideal.absNorm lengthScale.val : ℝ) / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn0 : n ≠ 0 := mul_ne_zero
    (supported_primaryGenerator_ne_zero Q (admissible_supported hQ))
    (supported_primaryGenerator_ne_zero T (admissible_supported hT))
  have hn : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn0)
  have hfg (E : Finset (gcdMaskPrimes D)) : f E = 6 * g E := by
    have hd : 0 < ‖eisEmbedding (primeSubsetGenerator R E)‖ :=
      norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero R E))
    let X := M / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)
    have hX : 0 < X := div_pos hM (mul_pos (sq_pos_of_pos hd) (sq_pos_of_pos hn))
    have he := canonical_nonprincipal_dual_ideal_reindex Q T hQ hT
      (columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray)
      (residual_pair_nontrivial D I J hDI hDJ hIJ) W X hX
    have harg (r : ℝ) : X * r =
        M * r / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) := by
      dsimp only [X]
      ring
    simpa only [harg, f, g, χ] using he
  have hs : (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * f E) =
      6 * ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * g E := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E _
    rw [hfg]
    ring
  change ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * f E) =
    ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset, a E * g E)
  rw [hs]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

theorem unrestrictedPairCharacter_square
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A : Ideal O) :
    unrestrictedPairCharacter I J (A ^ 2) =
      idealZeroMask I (idealGenerator A) * idealZeroMask J (idealGenerator A) := by
  rw [pow_two, unrestrictedPairCharacter_mul I J hI hJ hray]
  unfold unrestrictedPairCharacter
  calc
    _ = (quadraticRow I (idealGenerator A) * quadraticRow I (idealGenerator A)) *
      (quadraticRow J (idealGenerator A) * quadraticRow J (idealGenerator A)) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]

theorem unrestricted_pair_squarefree_tsum
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (F : ℝ → ℂ) :
    (∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val * F (Ideal.absNorm lengthScale.val)) =
      ∑' p : ({A : Ideal O // A ≠ 0} × {B : Ideal O // Squarefree B}),
        (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
        unrestrictedPairCharacter I J p.2.val *
        F ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) := by
  have he := squarefree_decomposition_tsum (fun lengthScale : Ideal O =>
    unrestrictedPairCharacter I J lengthScale * F (Ideal.absNorm lengthScale))
  rw [he]
  apply tsum_congr
  intro p
  rw [unrestrictedPairCharacter_mul I J hI hJ hray, unrestrictedPairCharacter_square I J hI hJ hray]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem canonical_nonprincipal_dual_squarefree
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0 < t) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      EisensteinSchwartzPoisson.paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (6 : ℂ) * ∑' p : ({A : Ideal O // A ≠ 0} × {B : Ideal O // Squarefree B}),
        (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
        unrestrictedPairCharacter I J p.2.val *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (t * ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ))) := by
  rw [canonical_nonprincipal_dual_ideal_reindex I J hI hJ hray hnt W t ht]
  congr 1
  exact unrestricted_pair_squarefree_tsum I J hI hJ hray
    (fun x => EisensteinSchwartzPoisson.paperRadialFourier W (t * x))

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation
open FourierBridge FirstPassCubeLabels

theorem joint_separation_twisted_profiles {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ a₃ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ j, V j (y j)) * (frequencyTwist g₁ θ₁) (∑ j, a₁ j * y j) * (frequencyTwist g₂ θ₂) (∑ j, a₂ j * y j) *
          EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (∑ j, a₃ j * y j)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          (∏ j, V j (y j)) * logPhase t₁ (∑ j, a₁ j * y j) *
            logPhase t₂ (∑ j, a₂ j * y j) * logPhase t₃ (∑ j, a₃ j * y j) *
            ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1 + ‖θ₁‖)^(J+2) * (1 + ‖θ₂‖)^(J+2) *
          firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  classical
  obtain ⟨C₃, hC₃, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V a₃ M hM hV A (J + 2)
  let C₁ := fourierPointBound (J + 2) (twistSourceBound g₁ (J + 2))
  let C₂ := fourierPointBound (J + 2) (twistSourceBound g₂ (J + 2))
  have hC₁ : 0 ≤ C₁ := fourierPointBound_nonneg _ _ (twistSourceBound_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := fourierPointBound_nonneg _ _ (twistSourceBound_nonneg _ _)
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  let A₁ := frequencyTwist g₁ θ₁
  let A₂ := frequencyTwist g₂ θ₂
  refine ⟨?_, ?_, AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J |>.congr ?_⟩
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
    have hr₁ := firstLogDensity_nonneg J t₁
    have hr₂ := firstLogDensity_nonneg J t₂
    have hr₃ := firstLogDensity_nonneg J t₃
    have hb₃ : (1 + R) ^ A * ‖b t₃‖ ≤ C₃ * firstLogDensity J t₃ := by
      rw [firstLogDensity, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t₃‖) (J + 2))).mpr
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hpoint t₃
    have h₁ := twisted_profile_fourier_envelope g₁ θ₁ t₁ J
    have h₂ := twisted_profile_fourier_envelope g₂ θ₂ t₂ J
    simp only [norm_mul]
    calc
      _ = ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁‖ * ‖(𝓕 (frequencyTwist g₂ θ₂)) t₂‖ * ((1 + R)^A * ‖b t₃‖) := by ring
      _ ≤ (C₁ * (1 + ‖θ₁‖)^(J+2) * firstLogDensity J t₁) *
          (C₂ * (1 + ‖θ₂‖)^(J+2) * firstLogDensity J t₂) * (C₃ * firstLogDensity J t₃) := by
        apply mul_le_mul
        · exact mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
        · exact hb₃
        · positivity
        · positivity
      _ = _ := by ring
  · filter_upwards [] with t
    simp

end JointLogSeparation

end

end OAI
end OAIOriginalModule0137

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
Source SHA256: 66857b9636296724fdaba3c1ba3c30a688727fcc1251ccd7b6410f683ddfcd2c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0138


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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

theorem conjugateProfile_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    conjugateProfile (frequencyTwist g t) = frequencyTwist (conjugateProfile g) (-t) := by
  ext x
  simp only [conjugateProfile_apply, frequencyTwist_apply, star_mul, logPhase_conjugate]
  ring

theorem normalized_conjugate_frequencyTwist (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    conjugateProfile (halfNormalizationCLM U (frequencyTwist g t)) =
      frequencyTwist (conjugateProfile (halfNormalizationCLM U g)) (-t) := by
  rw [halfNormalization_twist U hUc hUs, conjugateProfile_frequencyTwist]

theorem normalized_conjugate_profile_envelope (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t s : ℝ) (J : ℕ) :
    ‖(𝓕 (conjugateProfile (halfNormalizationCLM U (frequencyTwist g t)))) s‖ ≤
      fourierPointBound (J+2)
        (twistSourceBound (conjugateProfile (halfNormalizationCLM U g)) (J+2)) *
          (1 + ‖t‖)^(J+2) * FirstPassCubeLabels.firstLogDensity J s := by
  rw [normalized_conjugate_frequencyTwist U hUc hUs]
  simpa only [norm_neg] using
    twisted_profile_fourier_envelope (conjugateProfile (halfNormalizationCLM U g)) (-t) s J

end SecondPassIntegration

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge FirstPassCubeLabels

theorem seven_kernel_twisted_profiles (g₁ g₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * (frequencyTwist g₁ θ₁) (z + x₁) * (frequencyTwist g₂ θ₂) (z + x₂) *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * logPhase (t₁ + t₂) z *
            logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) *
          firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  let a₁ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 1, 0]
  let a₂ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 0, 1]
  let a₃ : Fin 7 → ℝ := ![0, -1, -2, -2, 1, -1, -1]
  obtain ⟨C, hC, hsep⟩ := joint_separation_twisted_profiles g₁ g₂ W V a₁ a₂ a₃ M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hb, hpoint, hint⟩ := hb θ₁ θ₂
  refine ⟨?_, hpoint, hint⟩
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
      ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃) := by ring
    _ = _ := by rw [heq]; ring

end JointLogSeparation

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem secondPreColumn_zero_of_common_overlap
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (G S : Finset ι)
    (hSG : ¬ Disjoint S G) :
    secondPreColumn p hp hcop hg Ψ (m * ∏ i ∈ G, p i) c d e k H S = 0 := by
  have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S (m * ∏ i ∈ G, p i) = 0 := by
    rw [FirstPassCubeLabels.mask_mul _ hg S,
      commonProduct_mask p hg hinj S G, ite_eq_right hSG, mul_zero]
  simp only [secondPreColumn, hm, mul_zero, zero_mul]

theorem weighted_secondChildKernelPair_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k₁ k₂ : O)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ lengthScale := by
  dsimp only
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let w := secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  have hcoeff :
      w * (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M) =
      supportMobius (fun i => Ideal.span {p i}) V *
        star (secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N)) *
        secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) := by
    rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hVN,
      secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hVM]
    simp only [w, secondCommonWeight, star_mul]
    ring
  change w * (_ * K (V∪N) (V∪M)) = w * (_ * lengthScale (V∪N) (V∪M))
  conv_lhs => rw [← mul_assoc w, hcoeff]
  conv_rhs => rw [← mul_assoc w, hcoeff]
  by_cases hGN : Disjoint G (V∪N)
  · by_cases hGM : Disjoint G (V∪M)
    · rw [hKL _ _ hGN hGM]
    · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₂ m c d e k₂
        (fun _ => 1) G (V∪M) (fun h => hGM h.symm)
      rw [secondMaskQuotient_spec p E G hEG] at hz
      change secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) = 0 at hz
      rw [hz]
      ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₁ m c d e k₁
      (fun _ => 1) G (V∪N) (fun h => hGN h.symm)
    rw [secondMaskQuotient_spec p E G hEG] at hz
    change secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N) = 0 at hz
    rw [hz, star_zero]
    ring

theorem weighted_secondRayChild_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (z : SecondRayIndex)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) K =
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) lengthScale := by
  dsimp only
  simp only [secondTotalWeight, mul_assoc]
  congr 1
  exact weighted_secondChildKernelPair_congr_off_common p hp hcop hg hinj hpr G E hEG F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m c d k (-k) K lengthScale hKL

end
section

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildKernelPair_eq_of_quotient_span
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r r' c d e k₁ k₂ : O)
    (hr : Ideal.span {r} = Ideal.span {r'}) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r' c d e k₁ k₂ K := by
  have hc (Ψ : O →* ℂ) (y : O) (N : Finset ι) :
      secondChildColumn p hp hcop hg Ψ (m*r) (c*e*∏ i ∈ V, p i) y (fun _ => 1) N =
        secondChildColumn p hp hcop hg Ψ (m*r') (c*e*∏ i ∈ V, p i) y (fun _ => 1) N := by
    simp only [secondChildColumn, rowCoprimeMask_mul_eq_of_span_eq (fun i => Ideal.span {p i}) N m hr]
  simp only [secondChildKernelPair, hc]

theorem secondChildKernelPair_const_kernel
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (a : ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ (fun S T => a * K S T) =
      a * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K := by
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem weighted_secondRayChild_normalized
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k r : O) (z : SecondRayIndex)
    (hr : Ideal.span {secondMaskQuotient p E G hEG} = Ideal.span {r})
    (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let q := secondMaskQuotient p E G hEG
    let X' := X / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding r‖ ^ 2)
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m q c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m q c d e k (-k)
        (secondSourcePairKernel p e k
          (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
          (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y) =
    ((X : ℂ)⁻¹ * secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m q c d e k (z,V)) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k)
        (radialPairKernel p e k W (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
          X' X' Y) := by
  dsimp only
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let q := secondMaskQuotient p E G hEG
  let K := secondSourcePairKernel p e k
    (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) (G∪A))
    (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) (G∪A)) W Y
  let lengthScale := radialPairKernel p e k W (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
    (X / primeProductNorm p G) (X / primeProductNorm p G) Y
  have hn := weighted_secondRayChild_congr_off_common p hp hcop hg hinj hpr
    G E hEG F V Ψ₁ Ψ₂ m c d k z K (fun S T => (X : ℂ)⁻¹ * lengthScale S T)
    (fun S T hGS hGT => secondSourcePairKernel_normalized_shift p hp G S T hGS hGT
      e k X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂)
  dsimp only at hn
  rw [secondChildKernelPair_const_kernel] at hn
  rw [secondChildKernelPair_eq_of_quotient_span p hp hcop hg F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m q r c d e k (-k) hr lengthScale] at hn
  dsimp only [K, lengthScale, e, q] at hn
  rw [residual_scale_quotient_sector p X E G hEG r hr] at hn
  simpa only [mul_left_comm, mul_assoc] using hn

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondExpansionQuotient (x : SecondExpansionData ι) : O :=
  if h : x.divisor ⊆ x.sourceCommon then
    secondMaskQuotient p x.divisor x.sourceCommon h else 0

omit [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondExpansionQuotient_of_subset (x : SecondExpansionData ι)
    (h : x.divisor ⊆ x.sourceCommon) :
    secondExpansionQuotient p x = secondMaskQuotient p x.divisor x.sourceCommon h := by
  simp [secondExpansionQuotient, h]

def secondExpansionScale (X : ℝ) (r : O) (x : SecondSupportData ι) : ℝ :=
  X / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)‖ ^ 2 *
    ‖eisEmbedding r‖ ^ 2)

end

def secondExpansionPushWeight {ι : Type*} [DecidableEq ι]
    (C D : Finset ι) (s : Finset (SecondExpansionData ι))
    (w : SecondExpansionData ι → ℂ) (y : SecondSupportData ι) : ℂ :=
  ∑ x ∈ s, if expansionSupportData C D x = y then w x else 0

theorem secondExpansionPushWeight_sum {ι : Type*} [DecidableEq ι]
    (C D : Finset ι) (s : Finset (SecondExpansionData ι))
    (w : SecondExpansionData ι → ℂ) (H : SecondSupportData ι → ℂ) :
    (∑ y ∈ s.image (expansionSupportData C D), secondExpansionPushWeight C D s w y * H y) =
      ∑ x ∈ s, w x * H (expansionSupportData C D x) := by
  unfold secondExpansionPushWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single_of_mem (expansionSupportData C D x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)]
  · simp
  · intro y hy hne
    simp [Ne.symm hne]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem secondExpansionPushWeight_at_source
    (C D : Finset ι) (r : O) (s : Finset (SecondExpansionData ι))
    (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (w : SecondExpansionData ι → ℂ) (x : SecondExpansionData ι) (hx : x ∈ s) :
    secondExpansionPushWeight C D s w (expansionSupportData C D x) = w x := by
  unfold secondExpansionPushWeight
  rw [Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y hy hne
    have hf : expansionSupportData C D y ≠ expansionSupportData C D x := by
      intro h
      exact hne (expansionSupportData_injOn p hinj C D r (hs y hy) (hs x hx) h)
    simp [hf]

def secondExpansionSource
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ x ∈ s,
    ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    (secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap) *
    secondChildKernelPair p hp hcop hg F x.overlap (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency)
      (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (fun A => H₁ (x.sourceCommon∪A)) (fun A => H₂ (x.sourceCommon∪A)) W Y))

def secondNormalizedExpansionWeight
    (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex) (X Y : ℝ)
    (x : SecondExpansionData ι) : ℂ :=
  ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    ((X : ℂ)⁻¹ * secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap))

include hinj in

theorem secondExpansionSource_eq_raw_variable_sector
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m r : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    secondExpansionSource p hp hcop hg F Ψ m c d z s
      (fun A => normalizedColumn p (fun B => g₁ (columnLog p X B)) A)
      (fun A => normalizedColumn p (fun B => g₂ (columnLog p X B)) A) W Y =
    actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂
      (s.image (expansionSupportData C D))
      (secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
      F (secondRayMinus Ψ z) (secondRayPlus Ψ z) m r
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W (secondExpansionScale p X r) Y := by
  dsimp only
  unfold actualSecondRawVariableSector
  rw [secondExpansionPushWeight_sum]
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hE,hr⟩ := hs x hx
  simp only [secondExpansionQuotient_of_subset p x hE, expansionSupportData,
    secondNormalizedExpansionWeight, secondExpansionScale]
  rw [weighted_secondRayChild_normalized p hp hcop hg hinj hpr x.sourceCommon x.divisor hE
    F x.overlap Ψ Ψ m _ _ x.frequency r z hr X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂]
  simp only [mul_assoc]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le (Ψ : O →* ℂ) (m c d : O) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ≤ ‖Ψ (∏ i ∈ G, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondInputCoefficient, norm_mul, norm_pow,  mul_one]
  calc
    _ ≤ ‖Ψ (∏ i ∈ G, p i)‖ * 1 * 1 ^ 4 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg G _
    _ = _ := by ring

theorem secondNormalizedExpansionWeight_after_scale
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (x : SecondExpansionData ι) :
    secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y x *
      (secondExpansionScale p X r (expansionSupportData C D x) : ℂ)⁻¹ =
      ((Y : ℂ) * (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖ ^ 2 : ℝ) *
        (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
        (‖eisEmbedding r‖ ^ 2 : ℝ) / (X : ℂ) ^ 2) *
      secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap) := by
  have hNe : (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)‖ ^ 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _))
  have hNec : ((‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hNe
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
  simp only [secondNormalizedExpansionWeight, secondSourceCommonCoefficient, secondExpansionScale,
    expansionSupportData, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

include hinj in

theorem secondNormalizedExpansionWeight_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (x : SecondExpansionData ι)
    (hΨG : ‖Ψ (∏ i ∈ x.sourceCommon, p i)‖ ≤ 1)
    (hΨV : ‖Ψ (∏ i ∈ x.overlap, p i)‖ ≤ 1) :
    ‖secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y x *
      (secondExpansionScale p X r (expansionSupportData C D x) : ℂ)⁻¹‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d x.sourceCommon).trans hΨG
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hT := secondTotalWeight_norm_le p hp hcop hg hinj hc Ψ Ψ m (secondExpansionQuotient p x)
    c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency z x.overlap hΨV hΨV
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmu : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ)‖ = 1 := by
    have hm := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj x.divisor)
    simp only [norm_mul, norm_one] at hm
    change ‖supportMobius (fun i => Ideal.span {p i}) x.divisor‖ = 1
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) x.divisor)]
  rw [secondNormalizedExpansionWeight_after_scale p hp hcop hg C D Ψ m c d r z X Y hX x]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_of_nonneg hY,
    Complex.norm_of_nonneg (sq_nonneg _), Complex.norm_of_nonneg (le_of_lt hX), hmu, mul_one]
  calc
    _ ≤ Y * 1 * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by ring

include hinj in

theorem secondNormalizedPushWeight_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y)
    (s : Finset (SecondExpansionData ι)) (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (hΨG : ∀ x ∈ s, ‖Ψ (∏ i ∈ x.sourceCommon, p i)‖ ≤ 1)
    (hΨV : ∀ x ∈ s, ‖Ψ (∏ i ∈ x.overlap, p i)‖ ≤ 1)
    (y : SecondSupportData ι) (hy : y ∈ s.image (expansionSupportData C D)) :
    ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
      (secondExpansionScale p X r y : ℂ)⁻¹‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  rw [secondExpansionPushWeight_at_source p hinj C D r s hs _ x hx]
  exact secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z X Y hX hY
    x (hΨG x hx) (hΨV x hx)

end SecondPassArithmetic

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma isUnit_quotient_span_iff (c d : O) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) d) ↔ IsCoprime c d := by
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hd
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hdiv : c ∣ d*b-1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    obtain ⟨k,hk⟩ := hdiv
    exact ⟨-k,b,by linear_combination hk⟩
  · rintro ⟨a,b,hab⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (Ideal.span {c}) b, ?_⟩
    have hc : Ideal.Quotient.mk (Ideal.span {c}) c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {c})) hab
    simpa only [map_add,map_mul,map_one,hc,mul_zero,zero_mul,zero_add,mul_comm] using h

abbrev AffineUnitResidue (c : O) :=
  {u : O ⧸ Ideal.span {c} // IsUnit (1+3*u)}

lemma affine_representative_condition (c : O) (u : AffineUnitResidue c) :
    denominatorCondition c (1+3*GaussianShiftedPartition.representative c u.1) := by
  refine ⟨(isUnit_quotient_span_iff c _).mp ?_, ⟨_,by ring⟩⟩
  simpa only [map_add,map_mul,map_one,map_ofNat,
    GaussianShiftedPartition.representative_spec] using u.2

def affineResidueMap (c : O) (u : AffineUnitResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c})
    (1+3*GaussianShiftedPartition.representative c u.1), by
    apply (denominatorCondition_congr c _
      (1+3*GaussianShiftedPartition.representative c u.1) ?_).mpr
      (affine_representative_condition c u)
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact denominatorRep_spec c _⟩

lemma affineResidueMap_bijective (c : O) : Function.Bijective (affineResidueMap c) := by
  constructor
  · intro u v huv
    have hdiv : 3*c ∣ (1+3*GaussianShiftedPartition.representative c u.1)-
        (1+3*GaussianShiftedPartition.representative c v.1) := by
      apply Ideal.mem_span_singleton.mp
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Subtype.val huv)
    obtain ⟨k,hk⟩ := hdiv
    have hk' : GaussianShiftedPartition.representative c u.1-
        GaussianShiftedPartition.representative c v.1=c*k := by
      have h3 : (3:O) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3
      linear_combination hk
    apply Subtype.ext
    rw [← GaussianShiftedPartition.representative_spec c u.1,
      ← GaussianShiftedPartition.representative_spec c v.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr ⟨k,hk'⟩)
  · intro r
    obtain ⟨u,hu⟩ := r.2.2
    have hd : denominatorRep c r.1=1+3*u := by linear_combination hu
    let q : AffineUnitResidue c := ⟨Ideal.Quotient.mk (Ideal.span {c}) u, by
      have hh := (isUnit_quotient_span_iff c _).mpr r.2.1
      simpa only [hd,map_add,map_one,map_mul,map_ofNat] using hh⟩
    refine ⟨q,Subtype.ext ?_⟩
    change Ideal.Quotient.mk (Ideal.span {3*c})
      (1+3*GaussianShiftedPartition.representative c q.1)=r.1
    rw [← denominatorRep_spec c r.1,hd]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hrep : c ∣ GaussianShiftedPartition.representative c q.1-u := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact GaussianShiftedPartition.representative_spec c q.1
    obtain ⟨k,hk⟩ := hrep
    exact ⟨k,by linear_combination 3*hk⟩

def affineResidueEquiv (c : O) : AffineUnitResidue c ≃ AdmissibleResidue c :=
  Equiv.ofBijective (affineResidueMap c) (affineResidueMap_bijective c)

def unitsSubtypeEquiv (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

def quotientProductEquiv (a b : O) (hab : IsCoprime a b) :
    (O ⧸ Ideal.span {a*b}) ≃+* (O ⧸ Ideal.span {a}) × (O ⧸ Ideal.span {b}) :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _ ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))

def affineCRTEq (a b : O) (hab : IsCoprime a b) :
    AffineUnitResidue (a*b) ≃ AffineUnitResidue a × AffineUnitResidue b :=
  ((quotientProductEquiv a b hab).toEquiv.subtypeEquiv (fun q => by
    rw [← MulEquiv.isUnit_map (quotientProductEquiv a b hab) (x := 1+3*q)]
    simp only [map_add,map_one,map_mul,map_ofNat,Prod.isUnit_iff]
    rfl)).trans Equiv.subtypeProdEquivProd

lemma affine_ramified_unit (n : ℕ) (q : O ⧸ Ideal.span {lambda^n}) : IsUnit (1+3*q) := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  have hcop : IsCoprime lambda (1+3*d) :=
    coprime_of_dvd_sub_one _ _ (by convert hlam3.mul_right d using 1 ; ring)
  have h := (isUnit_quotient_span_iff (lambda^n) (1+3*d)).mpr hcop.pow_left
  simpa only [map_add,map_one,map_mul,map_ofNat] using h

def affineRamifiedEquiv (n : ℕ) : AffineUnitResidue (lambda^n) ≃ (O ⧸ Ideal.span {lambda^n}) :=
  Equiv.subtypeUnivEquiv (affine_ramified_unit n)

def affineUnramifiedEquiv (m : O) (hm : IsCoprime m (3:O)) :
    AffineUnitResidue m ≃ (O ⧸ Ideal.span {m})ˣ := by
  let h3 : IsUnit (3 : O ⧸ Ideal.span {m}) := by
    simpa only [map_ofNat] using (isUnit_quotient_span_iff m 3).mpr hm
  let e : (O ⧸ Ideal.span {m}) ≃ (O ⧸ Ideal.span {m}) :=
    h3.unit.mulLeft.trans (Equiv.addLeft 1)
  refine (e.subtypeEquiv (fun q => ?_)).trans (unitsSubtypeEquiv _).symm
  change IsUnit (1+3*q) ↔ IsUnit (1+(h3.unit : O ⧸ Ideal.span {m})*q)
  rw [h3.unit_spec]

def idealTotient (I : Ideal O) : ℕ := Nat.card (O ⧸ I)ˣ

lemma card_admissible_ramified_product (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) (hlamm : IsCoprime lambda m) :
    Nat.card (AdmissibleResidue (lambda^n*m)) =
      Nat.card (O ⧸ Ideal.span {lambda^n}) * idealTotient (Ideal.span {m}) := by
  calc
    _ = Nat.card (AffineUnitResidue (lambda^n*m)) :=
      Nat.card_congr (affineResidueEquiv _).symm
    _ = Nat.card (AffineUnitResidue (lambda^n) × AffineUnitResidue m) :=
      Nat.card_congr (affineCRTEq _ _ hlamm.pow_left)
    _ = Nat.card ((O ⧸ Ideal.span {lambda^n}) × (O ⧸ Ideal.span {m})ˣ) :=
      Nat.card_congr (Equiv.prodCongr (affineRamifiedEquiv n) (affineUnramifiedEquiv m hm))
    _ = _ := Nat.card_prod _ _

lemma absNorm_span_lambda : Ideal.absNorm (Ideal.span {lambda})=3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclotomicExtension {3^(0+1)} ℚ ActualEisensteinCubic.K := by
    simpa using (inferInstance : IsCyclotomicExtension {3} ℚ ActualEisensteinCubic.K)
  exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 3 0
    (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K)

lemma card_quotient_lambda_pow (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {lambda^n})=3^n := by
  change Ideal.absNorm (Ideal.span {lambda^n})=3^n
  rw [← Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

theorem card_admissible_lambda_pow_mul (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) :
    Nat.card (AdmissibleResidue (lambda^n*m)) = 3^n * idealTotient (Ideal.span {m}) := by
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  rw [card_admissible_ramified_product n m hm
    (hm.symm.of_isCoprime_of_dvd_left hlam3),card_quotient_lambda_pow]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0138

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
Source SHA256: 27ca2eb8d85b202e403789ca080c4efdd8e30f53cbb2061da53fc99789f1c5ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0139


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

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

private def predicateFiberEquiv {R S : Type*} (f : R → S) (P : S → Prop) :
    {x : R // P (f x)} ≃ Σ y : {y : S // P y}, {x : R // f x=y.1} where
  toFun x := ⟨⟨f x.1,x.2⟩,⟨x.1,rfl⟩⟩
  invFun y := ⟨y.2.1,by rw [y.2.2]; exact y.1.2⟩
  left_inv x := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,x,hx⟩
    dsimp at hx
    cases hx
    rfl

private def predicateKernelEquiv {R S : Type*} [AddGroup R] [AddGroup S]
    (f : R →+ S) (hf : Function.Surjective f) (P : S → Prop) :
    {x : R // P (f x)} ≃ {y : S // P y} × f.ker :=
  (predicateFiberEquiv f P).trans
    ((Equiv.sigmaCongrRight (fun y : {y : S // P y} =>
      AddMonoidHom.fiberEquivKerOfSurjective hf y.1)).trans (Equiv.sigmaEquivProd _ _))

lemma card_ring_eq_card_mul_kernel {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Nat.card R=Nat.card S*Nat.card f.toAddMonoidHom.ker := by
  have h := Nat.card_congr (predicateKernelEquiv f.toAddMonoidHom hf (fun _ => True))
  simpa only [Nat.card_prod,Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => True.intro))] using h

lemma card_units_eq_card_mul_kernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card Rˣ=Nat.card Sˣ*Nat.card f.toAddMonoidHom.ker := by
  let e : Rˣ ≃ {x : R // IsUnit (f x)} :=
    (unitsSubtypeEquiv R).trans (Equiv.subtypeEquivRight (fun x => (hunit x).symm))
  calc
    _ = Nat.card ({y : S // IsUnit y} × f.toAddMonoidHom.ker) :=
      Nat.card_congr (e.trans (predicateKernelEquiv f.toAddMonoidHom hf IsUnit))
    _ = Nat.card {y : S // IsUnit y} * Nat.card f.toAddMonoidHom.ker := Nat.card_prod _ _
    _ = _ := by rw [← Nat.card_congr (unitsSubtypeEquiv S)]

lemma card_units_mul_card_target {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card S*Nat.card Rˣ=Nat.card R*Nat.card Sˣ := by
  rw [card_units_eq_card_mul_kernel f hf hunit,card_ring_eq_card_mul_kernel f hf]
  ring

theorem idealTotient_pow_succ (I : Ideal O) (hI : I ≠ 0) (n : ℕ) :
    idealTotient (I^(n+1))=Ideal.absNorm I^n*idealTotient I := by
  let f : (O ⧸ I^(n+1)) →+* (O ⧸ I) :=
    Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hu (x : O ⧸ I^(n+1)) : IsUnit (f x) ↔ IsUnit x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I (Nat.succ_ne_zero n)).symm
  have h := card_units_mul_card_target f hf hu
  change Ideal.absNorm I*idealTotient (I^(n+1))=
    Ideal.absNorm (I^(n+1))*idealTotient I at h
  rw [map_pow] at h
  have hpos : 0<Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = Ideal.absNorm I^(n+1)*idealTotient I := h
    _ = _ := by ring

theorem idealTotient_cube (I : Ideal O) (hI : I ≠ 0) :
    idealTotient (I^3)=Ideal.absNorm I^2*idealTotient I :=
  idealTotient_pow_succ I hI 2

def unitsRingEquiv {R S : Type*} [Monoid R] [Monoid S] (e : R ≃* S) : Rˣ ≃ Sˣ :=
  (unitsSubtypeEquiv R).trans
    ((e.toEquiv.subtypeEquiv (fun _x => (MulEquiv.isUnit_map e).symm)).trans
      (unitsSubtypeEquiv S).symm)

theorem idealTotient_mul (I J : Ideal O) (hIJ : IsCoprime I J) :
    idealTotient (I*J)=idealTotient I*idealTotient J := by
  change Nat.card (O ⧸ I*J)ˣ=Nat.card (O ⧸ I)ˣ*Nat.card (O ⧸ J)ˣ
  calc
    _ = Nat.card ((O ⧸ I)ˣ × (O ⧸ J)ˣ) :=
      Nat.card_congr ((unitsRingEquiv
        (Ideal.quotientMulEquivQuotientProd I J hIJ).toMulEquiv).trans MulEquiv.prodUnits.toEquiv)
    _ = _ := Nat.card_prod _ _

theorem card_admissible_cube_product (n : ℕ) (a : O) (ha : a ≠ 0)
    (hcop : IsCoprime a (3:O)) :
    Nat.card (AdmissibleResidue (lambda^(3*n)*a^3)) =
      3^(3*n)*Ideal.absNorm (Ideal.span {a})^2*idealTotient (Ideal.span {a}) := by
  rw [card_admissible_lambda_pow_mul (3*n) (a^3) hcop.pow_left,
    ← Ideal.span_singleton_pow,idealTotient_cube _ (Ideal.span_singleton_eq_bot.not.mpr ha)]
  ring

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

lemma isUnit_quotient_iff_sup (I : Ideal O) (x : O) :
    IsUnit (Ideal.Quotient.mk I x) ↔ I ⊔ Ideal.span {x}=⊤ := by
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    have hI : x*b-1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    apply (Ideal.eq_top_iff_one _).mpr
    have hx' : x*b ∈ I ⊔ Ideal.span {x} :=
      (le_sup_right : Ideal.span {x} ≤ I ⊔ Ideal.span {x})
        ((Ideal.span {x}).mul_mem_right b (Ideal.subset_span (by simp)))
    convert (I ⊔ Ideal.span {x}).sub_mem hx' ((le_sup_left : I ≤ I ⊔ Ideal.span {x}) hI) using 1 ; ring
  · intro h
    have h1 : (1:O) ∈ I ⊔ Ideal.span {x} := by rw [h]; trivial
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨k,rfl⟩ := Ideal.mem_span_singleton.mp hb
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk I k, ?_⟩
    have ha0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hh := congrArg (Ideal.Quotient.mk I) hab
    simpa only [map_add,map_mul,map_one,ha0,zero_add] using hh

lemma residue_unit_mobius (I : Ideal O) (hI : I ≠ 0) (r : O ⧸ I) :
    (if IsUnit r then (1:ℂ) else 0) =
      ∑ J ∈ idealDivisors I, if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
  let G : Ideal O := I ⊔ Ideal.span {Quotient.out r}
  have hG : G ≠ 0 := by
    intro hG
    apply hI
    apply le_antisymm _ bot_le
    calc
      I ≤ G := le_sup_left
      _ = ⊥ := hG
  have hdiv : (idealDivisors I).filter (fun J => Quotient.out r ∈ J)=idealDivisors G := by
    ext J
    simp only [Finset.mem_filter,mem_idealDivisors hI,mem_idealDivisors hG,
      Ideal.dvd_iff_le,G,sup_le_iff,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
  rw [← Finset.sum_filter,hdiv,sum_moebius_divisors G hG]
  have hu : IsUnit r ↔ G=⊤ := by
    rw [← Ideal.Quotient.mk_out r]
    exact isUnit_quotient_iff_sup I (Quotient.out r)
  simp only [hu]

lemma sum_indicator_const {R : Type*} [Fintype R] (P : R → Prop) (z : ℂ) :
    (∑ r : R, if P r then z else 0)=(Nat.card {r : R // P r}:ℂ)*z := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_eq_fintype_card,Fintype.card_subtype]

lemma card_quotient_multiples (I J : Ideal O) (hI : I ≠ 0) (hIJ : I ≤ J) :
    (Nat.card {r : O ⧸ I // Quotient.out r ∈ J}:ℂ)=
      (Ideal.absNorm I:ℂ)/(Ideal.absNorm J:ℂ) := by
  let f : (O ⧸ I) →+* (O ⧸ J) := Ideal.Quotient.factor hIJ
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have hpred (r : O ⧸ I) : Quotient.out r ∈ J ↔ f r=0 := by
    have hfr : f r=Ideal.Quotient.mk J (Quotient.out r) := by
      calc
        f r = f (Ideal.Quotient.mk I (Quotient.out r)) :=
          congrArg f (Ideal.Quotient.mk_out r).symm
        _ = _ := Ideal.Quotient.factor_mk hIJ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,hfr]
  let e : {r : O ⧸ I // Quotient.out r ∈ J} ≃ f.toAddMonoidHom.ker :=
    Equiv.subtypeEquivRight hpred
  have hcard := card_ring_eq_card_mul_kernel f hf
  have hJ : J ≠ 0 := fun h => hI (le_antisymm (h ▸ hIJ) bot_le)
  have hnJ : (Ideal.absNorm J:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Nat.card_congr e]
  apply (eq_div_iff hnJ).mpr
  have hh : Nat.card f.toAddMonoidHom.ker * Ideal.absNorm J = Ideal.absNorm I :=
    (Nat.mul_comm _ _).trans hcard.symm
  exact_mod_cast hh

theorem idealTotient_moebius (I : Ideal O) (hI : I ≠ 0) :
    (idealTotient I:ℂ)=(Ideal.absNorm I:ℂ)*
      ∑ J ∈ idealDivisors I, (moebius J:ℂ)/(Ideal.absNorm J:ℂ) := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  classical
  have hcount : (idealTotient I:ℂ)=∑ r : O ⧸ I,
      @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0 := by
    have h := sum_indicator_const (R := O ⧸ I) IsUnit (1:ℂ)
    rw [mul_one] at h
    calc
      _ = (Nat.card {r : O ⧸ I // IsUnit r}:ℂ) := by
        exact_mod_cast Nat.card_congr (unitsSubtypeEquiv (O ⧸ I))
      _ = _ := h.symm
  rw [hcount]
  have hs : (∑ r : O ⧸ I, @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0) =
      ∑ r : O ⧸ I, ∑ J ∈ idealDivisors I,
        if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact residue_unit_mobius I hI r
  rw [hs]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sum_indicator_const,card_quotient_multiples I J hI
    (Ideal.dvd_iff_le.mp ((mem_idealDivisors hI).mp hJ))]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def unramifiedNormWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := if primaryGenerator I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)
  map_zero' := by simp
  map_one' := by
    rw [primaryGenerator_one,ite_eq_right one_ne_zero,map_one,Nat.cast_one,Complex.one_cpow]
  map_mul' I J := by
    by_cases hI : primaryGenerator I=0
    · simp [primaryGenerator_mul,hI]
    by_cases hJ : primaryGenerator J=0
    · simp [primaryGenerator_mul,hJ]
    simp only [primaryGenerator_mul,mul_eq_zero,hI,hJ,false_or,ite_false,map_mul,Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

lemma unramifiedNormWeight_of_good (s : ℂ) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    unramifiedNormWeight s I=(Ideal.absNorm I:ℂ)^(-s) := ite_eq_right hI

lemma unramifiedNormWeight_of_bad (s : ℂ) (I : Ideal O) (hI : primaryGenerator I=0) :
    unramifiedNormWeight s I=0 := ite_eq_left hI

lemma primaryGenerator_injective_good :
    Function.Injective (fun I : GoodIdeal => primaryGenerator I.1) := by
  intro I J h
  dsimp only at h
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.1 I.2).1,← (primaryGenerator_spec J.1 J.2).1,h]

lemma norm_unramifiedNormWeight (s : ℂ) (I : GoodIdeal) :
    ‖unramifiedNormWeight s I.1‖=‖eisEmbedding (primaryGenerator I.1)‖^(-2*s.re) := by
  rw [unramifiedNormWeight_of_good s I.1 I.2]
  have hnorm : ‖eisEmbedding (primaryGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.1 I.2).1]
  have hn : 0<‖eisEmbedding (primaryGenerator I.1)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero I.2)
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖eisEmbedding (primaryGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
  rw [← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖unramifiedNormWeight s I‖) := by
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective
    primaryGenerator_injective_good
  have hsub : Summable (fun I : GoodIdeal => ‖unramifiedNormWeight s I.1‖) := by
    simpa only [Function.comp_def, norm_unramifiedNormWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I => ‖unramifiedNormWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : primaryGenerator I=0
  · simp [Set.indicator,hI,unramifiedNormWeight_of_bad s I hI]
  · simp [Set.indicator,hI]

lemma norm_ideal_moebius_le_one (I : Ideal O) : ‖(moebius I:ℂ)‖≤1 := by
  by_cases hI : Squarefree I
  · simp [hI.moebius_eq]
  · simp [moebius_of_not_squarefree hI]

lemma moebius_unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖(moebius I:ℂ)*unramifiedNormWeight s I‖) := by
  apply (unramifiedNormWeight_summable_norm s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one I)

def unramifiedIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O, unramifiedNormWeight s I

def unramifiedMobiusSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I:ℂ)*unramifiedNormWeight s I

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

theorem unramifiedMobiusSeries_mul_zeta (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s*unramifiedIdealZeta s=1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs).mul_norm
    (unramifiedNormWeight_summable_norm s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=if B=1 then 1 else 0 := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,zero_ne_one,ite_false]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ))*unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B; simp only [map_one,mul_one]
          · simp only [zero_mul]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p,F p)=1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O,
        ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs)
        (unramifiedNormWeight_summable_norm s hs)
    _ = ∑' p,F p := by
      apply tsum_congr
      intro p
      simp only [F,map_mul]
      ring
    _ = 1 := hFone

theorem unramifiedIdealZeta_ne_zero (s : ℂ) (hs : 1<s.re) : unramifiedIdealZeta s ≠ 0 := by
  intro hz
  have h := unramifiedMobiusSeries_mul_zeta s hs
  rw [hz,mul_zero] at h
  exact zero_ne_one h

theorem unramifiedMobiusSeries_eq_inv (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s=(unramifiedIdealZeta s)⁻¹ := by
  have h := unramifiedMobiusSeries_mul_zeta s hs
  calc
    _ = (unramifiedMobiusSeries s*unramifiedIdealZeta s)*(unramifiedIdealZeta s)⁻¹ := by
      field_simp [unramifiedIdealZeta_ne_zero s hs]
    _ = _ := by rw [h,one_mul]

lemma unramifiedNormWeight_shift (s : ℂ) (I : Ideal O) :
    unramifiedNormWeight (s-1) I=(Ideal.absNorm I:ℂ)*unramifiedNormWeight s I := by
  by_cases hg : primaryGenerator I=0
  · rw [unramifiedNormWeight_of_bad _ I hg,unramifiedNormWeight_of_bad _ I hg,mul_zero]
  · rw [unramifiedNormWeight_of_good _ I hg,unramifiedNormWeight_of_good _ I hg]
    have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hg))
    rw [show -(s-1)=(1:ℂ)+(-s) by ring,Complex.cpow_add _ _ hn,Complex.cpow_one]

lemma mulFiber_totient_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))=(idealTotient B:ℂ) := by
  let e := mulFiberDivisorEquiv B hB
  have hp (p : MulFiber B) :
      (moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ)=
        (Ideal.absNorm B:ℂ)*((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := by
    have hI : p.1.1 ≠ 0 := by
      intro hz
      have hh := p.2
      rw [hz,zero_mul] at hh
      exact hB hh.symm
    have hn : (Ideal.absNorm p.1.1:ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have heq : (Ideal.absNorm B:ℂ)=(Ideal.absNorm p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ) := by
      calc
        _ = (Ideal.absNorm (p.1.1*p.1.2):ℂ) := congrArg (fun I => (Ideal.absNorm I:ℂ)) p.2.symm
        _ = _ := by rw [map_mul,Nat.cast_mul]
    rw [heq]
    field_simp
  calc
    _ = ∑' p : MulFiber B,(Ideal.absNorm B:ℂ)*
        ((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := tsum_congr hp
    _ = (Ideal.absNorm B:ℂ)*
        ∑' D : {D : Ideal O // D ∈ idealDivisors B},
          ((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)) := by
      rw [← tsum_mul_left]
      exact e.tsum_eq (fun D => (Ideal.absNorm B:ℂ)*((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)))
    _ = (Ideal.absNorm B:ℂ)*
        ∑ D ∈ idealDivisors B,((moebius D:ℂ)/(Ideal.absNorm D:ℂ)) := by
      rw [tsum_fintype]
      apply congrArg (fun z : ℂ => (Ideal.absNorm B:ℂ)*z)
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (moebius D:ℂ)/(Ideal.absNorm D:ℂ))).symm
    _ = _ := (idealTotient_moebius B hB).symm

def unramifiedTotientSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O,(idealTotient I:ℂ)*unramifiedNormWeight s I

theorem unramifiedTotientSeries_product (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedMobiusSeries s*unramifiedIdealZeta (s-1) := by
  have hs1 : 1<s.re := by linarith
  have hs2 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*(Ideal.absNorm p.2:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs1).mul_norm
    (unramifiedNormWeight_summable_norm (s-1) hs2)
  have heq (p : Ideal O × Ideal O) :
      ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight (s-1) p.2=F p := by
    simp only [F,unramifiedNormWeight_shift,map_mul]
    ring
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=
      (idealTotient B:ℂ)*unramifiedNormWeight s B := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,map_zero,mul_zero]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))*
            unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by rw [mulFiber_totient_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = ∑' p,F p := hsum.tsum_eq
    _ = _ := by
      rw [unramifiedMobiusSeries,unramifiedIdealZeta,
        tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs1)
          (unramifiedNormWeight_summable_norm (s-1) hs2)]
      exact tsum_congr (fun p => (heq p).symm)

theorem unramifiedTotientSeries_quotient (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedIdealZeta (s-1)/unramifiedIdealZeta s := by
  rw [unramifiedTotientSeries_product s hs,unramifiedMobiusSeries_eq_inv s (by linarith),div_eq_mul_inv]
  ring

lemma idealTotient_le_absNorm (I : Ideal O) (hI : I ≠ 0) :
    idealTotient I ≤ Ideal.absNorm I := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  change Nat.card (O ⧸ I)ˣ ≤ Nat.card (O ⧸ I)
  exact Nat.card_le_card_of_injective (Units.val : (O ⧸ I)ˣ → O ⧸ I) Units.val_injective

theorem unramifiedTotientSeries_summable_norm (s : ℂ) (hs : 2<s.re) :
    Summable (fun I : Ideal O => ‖(idealTotient I:ℂ)*unramifiedNormWeight s I‖) := by
  have hs1 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  apply (unramifiedNormWeight_summable_norm (s-1) hs1).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  by_cases hI : I=0
  · subst I; simp only [map_zero,mul_zero,norm_zero,le_refl]
  · rw [norm_mul,Complex.norm_natCast,unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (idealTotient_le_absNorm I hI)) (norm_nonneg _)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

theorem originalPairLow_squarefree_tsum
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B},
        if (Ideal.absNorm B.val : ℝ) ≤ K then
          (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
            ∑' A : {A : Ideal O // Supported A},
              (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
                W (((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) / M)
        else 0 := by
  let F : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) → ℂ := fun p =>
    if (Ideal.absNorm p.2.val : ℝ) ≤ K then
      (idealZeroMask I (primaryGenerator p.1.val) * idealZeroMask J (primaryGenerator p.1.val)) *
      (quadraticRow I (primaryGenerator p.2.val) * quadraticRow J (primaryGenerator p.2.val)) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) / M) else 0
  have hterm (p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) :
      originalPairLow I J W M K (p.1.val ^ 2 * p.2.val) = F p := by
    have hs : Supported (p.1.val ^ 2 * p.2.val) :=
      (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩
    unfold originalPairLow
    rw [(squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2]
    by_cases hk : (Ideal.absNorm p.2.val : ℝ) ≤ K
    · rw [ite_eq_left hk]
      unfold originalPairSource
      rw [ite_eq_left hs, canonical_quadraticRow_star I hI,
        canonical_quadraticRow_primary_squarefree I hI, canonical_quadraticRow_primary_squarefree J hJ]
      simp only [F, ite_eq_left hk, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
      ring
    · simp only [ite_eq_right hk, F]
  have hsub : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => originalPairLow I J W M K lengthScale.val) :=
    (originalPairLow_summable I J W M K hM).subtype _
  have hp0 : Summable (fun p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B} =>
      originalPairLow I J W M K (p.1.val ^ 2 * p.2.val)) :=
    supportedSquarefreeEquiv.symm.summable_iff.mpr hsub
  have hp : Summable F := hp0.congr hterm
  have he : (∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, originalPairLow I J W M K lengthScale.val) =
      ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
    apply tsum_subtype_eq_of_support_subset
    intro lengthScale hL
    by_contra hs
    change ¬Supported lengthScale at hs
    exact hL (by simp [originalPairLow, originalPairSource, hs])
  calc
    _ = ∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, originalPairLow I J W M K lengthScale.val := he.symm
    _ = ∑' p : {A : Ideal O // Supported A} × {B : Ideal O // Admissible B},
        originalPairLow I J W M K (p.1.val ^ 2 * p.2.val) :=
      (supportedSquarefreeEquiv.symm.tsum_eq (fun lengthScale => originalPairLow I J W M K lengthScale.val)).symm
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' p : {B : Ideal O // Admissible B} × {A : Ideal O // Supported A}, F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Admissible B}, ∑' A : {A : Ideal O // Supported A}, F (A, B) :=
      hp.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hk : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [ite_eq_left hk, ← tsum_mul_left]
        apply tsum_congr
        intro A
        simp only [F, ite_eq_left hk]
        ring
      · simp only [F, ite_eq_right hk, tsum_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

theorem idealZeroMask_span_eq (D : Ideal O) (x y : O) (hxy : Ideal.span {x} = Ideal.span {y}) :
    idealZeroMask D x = idealZeroMask D y := by
  have hm (P : Ideal O) : x ∈ P ↔ y ∈ P := by
    constructor
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy.symm ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
  unfold idealZeroMask
  simp_rw [hm]

theorem idealZeroMask_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) (z : O) :
    idealZeroMask (I * J) z = idealZeroMask I z * idealZeroMask J z := by
  have he : (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors (I * J), z ∈ P) ↔
      (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P) ∨
        (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P) := by
    simp only [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.mem_add,
      or_and_right, exists_or]
  unfold idealZeroMask
  simp only [he]
  by_cases h₁ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P <;>
    by_cases h₂ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P <;> simp [h₁, h₂]

theorem jointMask_generator (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ (idealGenerator lengthScale) =
      if Supported lengthScale then idealZeroMask I (primaryGenerator lengthScale) * idealZeroMask J (primaryGenerator lengthScale) else 0 := by
  rw [gcdMaskPrimes_mask, idealZeroMask_mul I J hI.1 hJ.1, badPrime_mask, span_idealGenerator]
  by_cases hL : Supported lengthScale
  · rw [ite_eq_left hL, ite_eq_left hL, one_mul]
    have hs : Ideal.span {idealGenerator lengthScale} = Ideal.span {primaryGenerator lengthScale} :=
      (span_idealGenerator lengthScale).trans (primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale hL)).1.symm
    rw [idealZeroMask_span_eq I _ _ hs, idealZeroMask_span_eq J _ _ hs]
  · simp only [ite_eq_right hL, zero_mul]

theorem jointMask_zero (I J : Ideal O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ 0 = 0 := by
  rw [gcdMaskPrimes_mask, badPrime_mask]
  have h : ¬Supported (Ideal.span {(0 : O)}) := by
    intro h
    exact h.1 (by simp)
  rw [ite_eq_right h, zero_mul]

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0139
