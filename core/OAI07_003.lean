    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (GammaIntegral_convergent (by norm_num : 0 < (2 : ℂ).re))
  have hline (t : ℝ) : mellin f (line t) = Gamma (line t) := hm _ (by simp)
  have hv : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun t : ℝ => mellin f (line t))
    simpa only [hline] using gamma_line_integrable
  have hi := mellinInv_mellin_eq 2 f hx hf hv (by unfold f; fun_prop)
  change (1/(2*Real.pi)) • (∫ t : ℝ, (x : ℂ)^(-line t) • mellin f (line t)) = f x at hi
  simp_rw [hline] at hi
  simp only [smul_eq_mul, f, ofReal_exp, ofReal_neg] at hi
  convert hi using 1; simp [one_div, Complex.real_smul]

def gammaTerm (a : ℂ) (N : ℝ) (ρ : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  (Y : ℂ)^(line t)*Gamma (line t)*a*(N : ℂ)^(-(ρ+line t))

theorem gammaTerm_separate (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    gammaTerm a N ρ Y t = (a*(N : ℂ)^(-ρ))*
      (((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by
  rw [gammaTerm, neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hN.ne'),
    ofReal_div, div_cpow_ofReal_nonneg hN.le hY.le, cpow_neg (Y : ℂ), div_inv_eq_mul]
  ring

theorem gammaTerm_integral (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, gammaTerm a N ρ Y t) =
      a*(N : ℂ)^(-ρ)*Complex.exp (-(N : ℂ)/(Y : ℂ)) := by
  simp_rw [gammaTerm_separate a hN hY ρ]
  rw [integral_const_mul]
  calc
    _ = (a*(N : ℂ)^(-ρ))*(((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by ring
    _ = _ := by rw [gamma_mellin_inverse (div_pos hN hY)]; push_cast; rw [neg_div]

@[simp] theorem gammaTerm_zero (N : ℝ) (ρ : ℂ) (Y t : ℝ) : gammaTerm 0 N ρ Y t = 0 := by
  simp [gammaTerm]

theorem gammaTerm_norm (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    ‖gammaTerm a N ρ Y t‖ = (Y^2 * (‖a‖*N^(-(ρ.re+2)))) * ‖Gamma (line t)‖ := by
  simp only [gammaTerm, norm_mul, norm_cpow_eq_rpow_re_of_pos hY,
    norm_cpow_eq_rpow_re_of_pos hN, neg_re, add_re, line_re, Real.rpow_two]
  ring

theorem gammaTerm_integrable (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    Integrable (gammaTerm a N ρ Y) := by
  apply (gamma_line_integrable.norm.const_mul (Y^2*(‖a‖*N^(-(ρ.re+2))))).mono'
  · apply Continuous.aestronglyMeasurable
    have hl : Continuous line := by unfold line; fun_prop
    have hg : Continuous (fun t : ℝ => Gamma (line t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp hl.continuousAt
    have hy := (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hY.ne'))).continuous.comp hl
    have hn := (((differentiable_const ρ).add differentiable_id).neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr hN.ne'))).continuous.comp hl
    exact ((hy.mul hg).mul continuous_const).mul hn
  · exact ae_of_all _ (fun t => (gammaTerm_norm a hN hY ρ t).le)

theorem gamma_expansion {ι : Type*} [Countable ι] (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 ≤ N i) (hzero : ∀ i, N i = 0 → a i = 0)
    (ρ : ℂ) {Y : ℝ} (hY : 0 < Y)
    (hsum : Summable (fun i => ‖a i‖*(N i)^(-(ρ.re+2)))) :
    HasSum (fun i => a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)))
      (((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, ∑' i, gammaTerm (a i) (N i) ρ Y t) := by
  have hint (i : ι) : Integrable (gammaTerm (a i) (N i) ρ Y) := by
    by_cases hi : N i = 0
    · rw [hzero i hi]
      have he : gammaTerm 0 (N i) ρ Y = fun _ : ℝ => 0 := funext (gammaTerm_zero _ _ _)
      rw [he]
      exact integrable_zero ℝ ℂ volume
    · exact gammaTerm_integrable _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ
  have hnorm (i : ι) (t : ℝ) :
      ‖gammaTerm (a i) (N i) ρ Y t‖ =
        (Y^2*(‖a i‖*(N i)^(-(ρ.re+2))))*‖Gamma (line t)‖ := by
    by_cases hi : N i = 0
    · simp [hzero i hi]
    · exact gammaTerm_norm _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ t
  have hnormsum : Summable (fun i => ∫ t : ℝ, ‖gammaTerm (a i) (N i) ρ Y t‖) := by
    simp_rw [hnorm, integral_const_mul]
    convert hsum.mul_left (Y^2*(∫ t : ℝ, ‖Gamma (line t)‖)) using 1
    funext i
    ring
  have hi := (hasSum_integral_of_summable_integral_norm hint hnormsum).mul_left
    (((2*Real.pi : ℝ) : ℂ)⁻¹)
  have he (i : ι) : (((2*Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, gammaTerm (a i) (N i) ρ Y t) =
      a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)) := by
    by_cases hn : N i = 0
    · simp [hzero i hn]
    · exact gammaTerm_integral _ (lt_of_le_of_ne (hN i) (Ne.symm hn)) hY ρ
  simpa only [he] using hi

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

theorem cutoffTerm_weighted (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      V ((J.absNorm : ℝ)/D) * IdealEuler.weighted (idealCoeff χ) s J := by
  simp only [cutoffTerm, HeckeDyadic.coefficient, ite_true,
    IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

theorem cutoffTerm_outside (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (J : Ideal O)
    (hJ : J ∉ cutoffSet D) : cutoffTerm χ V D J s = 0 := by
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_hasSum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    HasSum (fun J : Ideal O => cutoffTerm χ V D J s) (cutoff χ V D s) :=
  hasSum_sum_of_ne_finset_zero (cutoffTerm_outside χ V hD hV s)

def pairCoefficient (χ : Character) (V : ℝ → ℂ) (D : ℝ) (p : Ideal O × Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((p.1.absNorm : ℝ)/D) *
    idealCoeff χ (p.1*p.2)

def pairNorm (p : Ideal O × Ideal O) : ℝ := (p.1*p.2).absNorm

theorem pairCoefficient_zero_norm (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (p : Ideal O × Ideal O) (hp : pairNorm p = 0) : pairCoefficient χ V D p = 0 := by
  have hn : (p.1*p.2).absNorm = 0 := by unfold pairNorm at hp; exact_mod_cast hp
  have hzero := Ideal.absNorm_eq_zero_iff.mp hn
  rw [pairCoefficient, hzero]
  rw [show (⊥ : Ideal O) = 0 from rfl, HeckeFamily.idealCoeff_zero, mul_zero]

theorem pairTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ)
    (p : Ideal O × Ideal O) :
    pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s) =
      cutoffTerm χ V D p.1 s * IdealEuler.weighted (idealCoeff χ) s p.2 := by
  rw [cutoffTerm_weighted]
  by_cases hp : p.1*p.2 = 0
  · have he : pairNorm p = 0 := by simp [pairNorm, hp]
    rw [pairCoefficient_zero_norm χ V D p he, zero_mul]
    rw [mul_assoc, ← map_mul, hp, map_zero, mul_zero]
  · rw [mul_assoc, ← map_mul]
    simp only [pairCoefficient, pairNorm, Complex.ofReal_natCast,
      IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      CubicEisenstein.fullIdealWeight, ite_eq_right hp]
    ring

theorem pairTerm_summable_norm (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)‖) := by
  simpa only [pairTerm_eq] using
    (cutoffTerm_hasSum χ V hD hV s).summable.norm.mul_norm
      (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)

theorem pairSeries_eq (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)) =
      cutoff χ V D s * LFunction χ s := by
  simp_rw [pairTerm_eq]
  rw [← tsum_mul_tsum_of_summable_norm (cutoffTerm_hasSum χ V hD hV s).summable.norm
    (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)]
  rw [(cutoffTerm_hasSum χ V hD hV s).tsum_eq, LFunction_eq_series χ hs]
  rfl

theorem pairMajorant_summable (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p‖*(pairNorm p)^(-(ρ.re+2))) := by
  have h := pairTerm_summable_norm χ V hD hV (ρ+2) (by norm_num; linarith)
  apply h.congr
  intro p
  by_cases hp : pairNorm p = 0
  · simp [pairCoefficient_zero_norm χ V D p hp]
  · have hn : 0 < pairNorm p := lt_of_le_of_ne (by unfold pairNorm; positivity) (Ne.symm hp)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hn]
    simp only [neg_re, add_re]
    norm_num

theorem pairGamma_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re)
    (Y t : ℝ) :
    (∑' p : Ideal O × Ideal O, gammaTerm (pairCoefficient χ V D p) (pairNorm p) ρ Y t) =
      detectorIntegrand χ V D Y ρ (line t) := by
  have hs : 1 < (ρ+line t).re := by simp only [add_re, line_re]; linarith
  calc
    _ = (Y : ℂ)^(line t)*Gamma (line t)*
        (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p*(pairNorm p : ℂ)^(-(ρ+line t))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      unfold gammaTerm
      ring
    _ = _ := by rw [pairSeries_eq χ V hD hV _ hs]; unfold detectorIntegrand; ring

def pairExponential (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairCoefficient χ V D p*(pairNorm p : ℂ)^(-ρ)*Complex.exp (-(pairNorm p : ℂ)/(Y : ℂ))

theorem detector_hasSum_pairs (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairExponential χ V D ρ Y) (detectorIntegral χ V D Y ρ) := by
  have h := gamma_expansion (pairCoefficient χ V D) pairNorm
    (fun p => by unfold pairNorm; positivity) (pairCoefficient_zero_norm χ V D)
    ρ hY (pairMajorant_summable χ V hD hV hρ)
  unfold pairExponential detectorIntegral
  simpa only [pairGamma_tsum χ V hD hV hρ, line] using h

theorem detector_eq_double_sum (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    detectorIntegral χ V D Y ρ = ∑' J : Ideal O, ∑' K : Ideal O,
      (UniqueFactorizationMonoid.moebius J : ℂ) * V ((J.absNorm : ℝ)/D) *
      idealCoeff χ (J*K) * (((J*K).absNorm : ℝ) : ℂ)^(-ρ) *
        Complex.exp (-(((J*K).absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
  have h := detector_hasSum_pairs χ V hD hY hV hρ
  rw [← h.tsum_eq, h.summable.tsum_prod]
  rfl

theorem pairExponential_zero_left (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (K : Ideal O) : pairExponential χ V D ρ Y (0,K) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_zero_right (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) : pairExponential χ V D ρ Y (J,0) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairExponential χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J := by
  have he (p : CompletedGauss.MulFiber J) :
      pairExponential χ V D ρ Y p.val =
        ((UniqueFactorizationMonoid.moebius p.val.1 : ℂ)*V ((p.val.1.absNorm : ℝ)/D)*
          IdealEuler.weighted (idealCoeff χ) ρ (p.val.1*p.val.2))*
          Complex.exp (-((J.absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
    rw [pairExponential, pairTerm_eq, cutoffTerm_weighted, mul_assoc _ _
      (IdealEuler.weighted (idealCoeff χ) ρ p.val.2), ← map_mul]
    congr 2
    rw [pairNorm, p.property]
  simp_rw [he]
  rw [tsum_mul_right, HeckeDetectorWitnessArithmetic.weighted_fiber]
  rfl

theorem detector_hasSum_convolution (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y)
      (detectorIntegral χ V D Y ρ) := by
  have h := (detector_hasSum_pairs χ V hD hY hV hρ).tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairExponential χ V D ρ Y p.val) _ at h
  simpa only [pairExponential_fiber] using h

theorem detector_large_product_tail (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    (∑' J : Ideal O, HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J *
      (1-V (2*(J.absNorm : ℝ)/D))) =
      detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ)) := by
  have h := detector_hasSum_convolution χ V (by linarith : 0 < D) hY hVzero hρ
  rw [HeckeDetectorWitnessArithmetic.exponential_sum_tail χ V D hD hV hVzero ρ Y h.summable,
    h.tsum_eq]

theorem pairExponential_summable_norm (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O => ‖pairExponential χ V D ρ Y p‖) :=
  (detector_hasSum_pairs χ V hD hY hV hρ).summable.norm

def pairTail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairExponential χ V D ρ Y p * (1-V (2*pairNorm p/D))

theorem pairTail_summable (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (pairTail χ V D ρ Y) := by
  apply Summable.of_norm
  apply ((pairExponential_summable_norm χ V hD hY hVzero hρ).mul_right 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  rw [pairTail, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hn := norm_sub_le (1 : ℂ) (V (2*pairNorm p/D))
  rw [norm_one] at hn
  linarith [hV (2*pairNorm p/D)]

theorem pairTail_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairTail χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J *
        (1-V (2*(J.absNorm : ℝ)/D)) := by
  have hn (p : CompletedGauss.MulFiber J) : pairNorm p.val = (J.absNorm : ℝ) := by
    rw [pairNorm, p.property]
  simp_rw [pairTail, hn]
  rw [tsum_mul_right, pairExponential_fiber]

theorem detector_eq_pair_tail (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hVone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairTail χ V D ρ Y)
      (detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ))) := by
  have hs := pairTail_summable χ V (by linarith : 0 < D) hY hVzero hV hρ
  have hf := hs.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairTail χ V D ρ Y p.val) _ at hf
  simp_rw [pairTail_fiber] at hf
  have he := hf.tsum_eq
  rw [detector_large_product_tail χ V hD hY hVone hVzero hρ] at he
  exact he.symm ▸ hs.hasSum

end SevenEighths.GammaDetectorExpansion

end

end OAI
end OAIOriginalModule2024

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorLower
Source SHA256: 1107f7f6ad56b42a2627e97ad555c1971d19ff4f486033c401083586817662eb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2025



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorLower
open HeckeFamily HeckeDetectorTail HeckeDetectorFinite HeckeDetectorPartition
open GammaZeroDetector
local notation "O" => HeckeFamily.O

lemma unit_term_lower (U : ℝ) (hU : 2 ≤ U) :
    (3/4 : ℝ) ≤ ‖Complex.exp (-1/((U^20 : ℝ) : ℂ))‖ := by
  have hUp : 0 < U := by linarith
  have hp : 4 ≤ U^20 := by
    calc
      4 ≤ U^2 := by nlinarith
      _ ≤ U^20 := pow_le_pow_right₀ (by linarith : 1 ≤ U) (by norm_num : 2 ≤ 20)
  have hi : 1/(U^20) ≤ (1/4 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  rw [Complex.norm_exp]
  have he : (-1/((U^20 : ℝ) : ℂ)).re = -1/(U^20) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,←Complex.ofReal_div,Complex.ofReal_re]
  rw [he]
  have hh := Real.add_one_le_exp (-1/(U^20))
  simp only [neg_div] at hh ⊢
  linarith

theorem terminal_uniform_lower (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      (1/2 : ℝ) ≤ ‖∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I‖ := by
  obtain ⟨UG,hUG⟩ := detector_uniform_small R θ (1/8) hR hθ hθ' (by norm_num)
  obtain ⟨UT,hUT⟩ := terminalRemainder_uniform_small 1 1 (1/8) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max 2 (max UG UT),?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hg := hUG U ((le_max_left UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ hχ V hVb D (by linarith) hDU hQ ρ hρ hzero hheight
  have ht := hUT U ((le_max_right UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ V T hVb hTb hTone D ρ (by linarith)
  have hi := terminal_sum_identity χ V T 1 1 D (U^20) (U^21) (by norm_num)
    hVb hTb hD (by positivity) hVone hVzero ρ (by linarith)
  rw [(GammaDetectorExpansion.detector_hasSum_convolution χ V
    (by linarith : 0 < D) (by positivity : 0 < U^20) hVzero (by linarith : -1 < ρ.re)).tsum_eq] at hi
  have he : Complex.exp (-1/((U^20 : ℝ) : ℂ)) =
      detectorIntegral χ V D (U^20) ρ -
        (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I) -
        (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I) := by
    rw [hi]
    ring
  have hn := norm_sub_le
    (detectorIntegral χ V D (U^20) ρ - ∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
    (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I)
  rw [←he] at hn
  have hn' := norm_sub_le (detectorIntegral χ V D (U^20) ρ)
    (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
  have hu := unit_term_lower U hU2
  linarith

theorem exists_dyadic_zero_witness (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          (1/2 : ℝ) ≤ 625*(Real.logb 2 U)^2*‖dyadicBlock χ V T D (U^20) (U^21) ρ j k‖ ∧
          (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
          (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨U₁,hU₁⟩ := terminal_uniform_lower R θ hR hθ hθ'
  refine ⟨max 2 U₁,?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone hTzero D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hUpos : 0 < U := by linarith
  have ht := hU₁ U ((le_max_right _ _).trans hU) χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,hb⟩ := exists_dyadic_block χ V T D (U^20) (U^21)
    (by positivity) hTzero hVone hVzero ρ (1/2) ht
  have hbn : dyadicBlock χ V T D (U^20) (U^21) ρ j k ≠ 0 := by
    intro hz
    rw [hz,norm_zero,mul_zero] at hb
    norm_num at hb
  refine ⟨j,hj,k,hk,?_,nonzero_block_scale_bounds χ V T D (U^20) (U^21)
    (by linarith) (by positivity) hTzero hVone hVzero ρ j k hbn⟩
  exact hb.trans (mul_le_mul_of_nonneg_right
    (HeckeDetectorBudget.source_pair_count_bound U hU2) (norm_nonneg _))

end SevenEighths.HeckeDetectorLower

end

end OAI
end OAIOriginalModule2025

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Logarithmic
Source SHA256: 4e1a1a62c738c401b60aeeab30153debb383e156fc0afdfd08757ed1e7f2dd66
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2026



namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmic
open HeckeFamily HeckeLogarithmicInput

def complexity (η : Character) (t : ℝ) : ℝ :=
  2*(η.modulus.absNorm : ℝ)*(3+|t|)^2

theorem complexity_ge_exp (η : Character) (t : ℝ) : Real.exp 1 ≤ complexity η t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (modulus_norm_ge_one η)

theorem regular_disk_differentiable (η : Character) {a e t : ℝ}
    (ha : (1/2 : ℝ) ≤ a) (he : 0 < e) :
    DifferentiableOn ℂ (regular η) (ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) := by
  intro z hz
  exact (regular_differentiableAt η (by
    have hr := LogarithmicControl.disk_re_gt hz
    linarith)).differentiableWithinAt

theorem exists_uniform_polynomial_exponent :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ a e t : ℝ, 1/2 ≤ a → 0 < e → ∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-3*e),
        ‖regular η z‖ ≤ (complexity η t)^M := by
  obtain ⟨M, hM, hb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := 2*uniformConstant) (p := 1) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro η hp a e t ha he z hz
  have hz2 : z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz
  have h := regular_disk_growth η hp a e t ha he.le hz2
  have hQ : (η.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ (η.modulus.absNorm : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (modulus_norm_ge_one η)
      (show (3/5 : ℝ)≤1 by norm_num)
  apply h.trans
  calc
    _ ≤ (4*uniformConstant)*(η.modulus.absNorm : ℝ)*(3+|t|)^2 := by
      gcongr
      exact mul_nonneg (by norm_num) uniformConstant_nonneg
    _ = (2*uniformConstant)*complexity η t := by unfold complexity; ring
    _ ≤ (complexity η t)^M := by simpa only [Real.rpow_one] using hb _ (complexity_ge_exp η t)

theorem disk_control_of_euler_log (e A ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ (a t : ℝ) (E : ℂ → ℂ),
      1/2 ≤ a → a ≤ 1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      DifferentiableOn ℂ E (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      EqOn (Complex.exp ∘ E) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨M,hM,hpoly⟩ := exists_uniform_polynomial_exponent
  obtain ⟨D,hD,hb⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, LogarithmicControl.outerConstant e A M/(2*e), hD, ?_, ?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he' hA hM
    positivity
  · intro η hp a t E ha ha' hzero hE hEL hEb
    exact hb a (complexity η t) (regular η) E ((2 : ℂ)+t*Complex.I) ha ha'
      (complexity_ge_exp η t) (regular_disk_differentiable η ha he) hzero
      (hpoly η hp a e t ha he) hE hEL hEb

end SevenEighths.HeckeLogarithmic

end

end OAI
end OAIOriginalModule2026

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.LogarithmicActual
Source SHA256: 0de1032bf421966bd89b1f5da862315adfb6a45e78f4af937dcedf0698ac87b1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2027




namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmicActual
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic

def eulerLog (η : Character) : ℂ → ℂ :=
  if η.residue = 1 then HeckeEulerLog.principalEulerLog (idealCoeff η)
  else HeckeEulerLog.eulerLog (idealCoeff η)

def innerBound : ℝ := 3+HeckeEulerLog.eulerLogBound

theorem innerBound_ge_one : 1 ≤ innerBound := by
  unfold innerBound
  linarith [HeckeEulerLog.eulerLogBound_ge_one]

theorem actual_inner_log (η : Character) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    EqOn (Complex.exp ∘ eulerLog η) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) ∧
    ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖eulerLog η z‖ ≤ innerBound := by
  by_cases hη : η.residue = 1
  · have hright (s : ℂ) (hs : 1<s.re) : regular η s =
        ((s-1)/(s+1))*IdealEuler.series (idealCoeff η) s := by
      have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
      have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
      simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized]
      rw [HeckeOrigin.poleRemoved_eq η h0 h1, LFunction_eq_series η hs]
      ring
    simpa only [eulerLog, ite_eq_left hη, innerBound] using
      HeckeEulerLog.principal_continued_inner_disk (idealCoeff η) (idealCoeff_norm_le_one η)
        (regular η) hright t
  · have hright (s : ℂ) (hs : 1<s.re) : regular η s = IdealEuler.series (idealCoeff η) s := by
      rw [regular_eq_nonprincipal η hη]
      exact LFunction_eq_series η hs
    obtain ⟨hd,he,hb⟩ := HeckeEulerLog.continued_inner_disk (idealCoeff η)
      (idealCoeff_norm_le_one η) (regular η) hright t
    simp only [eulerLog, ite_eq_right hη]
    refine ⟨hd,he,?_⟩
    intro z hz
    have h := hb z hz
    unfold innerBound
    linarith

theorem disk_control (e ε : ℝ) (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D B : ℝ, 0<D ∧ 0≤B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨D,B,hD,hB,hb⟩ := disk_control_of_euler_log e innerBound ε he he' innerBound_ge_one hε
  refine ⟨D,B,hD,hB,?_⟩
  intro η hp a t ha ha' hzero
  obtain ⟨hE,hEL,hEb⟩ := actual_inner_log η t
  exact hb η hp a t (eulerLog η) ha ha' hzero hE hEL hEb

theorem primitive_reciprocal_subpower (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ s : ℂ, HeckeZeroSupremum.beta+8*e ≤ s.re →
        ‖HeckeReciprocal.reciprocal η s‖ ≤ D*(complexity η s.im)^ε := by
  obtain ⟨D,B,hD,_,hb⟩ := disk_control e ε he he' hε
  have hEuler : 0 ≤ HeckeReciprocalBound.bound 2 := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨D+HeckeReciprocalBound.bound 2, by linarith, ?_⟩
  intro η hp s hs
  have hcomp : 1 ≤ (complexity η s.im)^ε := Real.one_le_rpow
    ((Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp η s.im)) hε.le
  by_cases hs2 : s.re ≤ 2
  · have hbound := (hb η hp HeckeZeroSupremum.beta s.im HeckeZeroSupremum.half_le_beta
      HeckeZeroSupremum.beta_le_one (fun z hz => regular_ne_zero_on_disk η HeckeZeroSupremum.beta e s.im le_rfl he hz)).1
    have hmem : s ∈ closedBall ((2 : ℂ)+s.im*Complex.I) (2-HeckeZeroSupremum.beta-6*e) := by
      have h := LogarithmicControl.same_height_mem_disk (a := HeckeZeroSupremum.beta)
        (e := e) (t := s.im) (v := 8*e) le_rfl hs hs2
      rw [Complex.re_add_im] at h
      exact closedBall_subset_closedBall (by linarith) h
    have hz := hbound s hmem
    have hr := reciprocal_norm_le_regular_inverse η (by linarith : HeckeZeroSupremum.beta<s.re)
    have hcp : 0 ≤ (complexity η s.im)^ε := by linarith
    nlinarith [norm_nonneg (regular η s)]
  · have hr := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<2)
      (le_of_not_ge hs2)
    have hp0 : 0 ≤ D+HeckeReciprocalBound.bound 2 := by linarith
    exact hr.trans ((by linarith : HeckeReciprocalBound.bound 2 ≤ D+HeckeReciprocalBound.bound 2).trans
      (le_mul_of_one_le_right hp0 hcomp))

end SevenEighths.HeckeLogarithmicActual

end

end OAI
end OAIOriginalModule2027

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
Source SHA256: daaecdb8cc03b9067c3c82928f46ca8a6e01da05483df526a1048775e4384b8c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2028


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeReciprocalGrowth
open HeckeFamily HeckeLogarithmic HeckeDeletionBounds

def presentationComplexity (χ : Character) (t : ℝ) : ℝ :=
  ((radical χ.modulus).absNorm : ℝ)*complexity χ t

theorem reciprocal_subpower (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ D : ℝ, 0<D ∧ ∀ (χ : Character) (s : ℂ),
      HeckeZeroSupremum.beta+8*e ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ D*(presentationComplexity χ s.im)^ε := by
  obtain ⟨Dp,hDp,hpbound⟩ := HeckeLogarithmicActual.primitive_reciprocal_subpower e ε he he' hε
  obtain ⟨Cd,hCd,hreduce⟩ := HeckeDeletionReciprocal.exists_primitive_reciprocal_reduction
    (HeckeZeroSupremum.beta+8*e) ε (by linarith [HeckeZeroSupremum.half_le_beta]) hε
  refine ⟨Cd*Dp, mul_pos hCd hDp, ?_⟩
  intro χ s hs
  obtain ⟨ψ,hp,hn,_,hr⟩ := hreduce χ
  have hc : complexity ψ s.im ≤ complexity χ s.im := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ s.im :=
    (Real.exp_pos 1).le.trans (complexity_ge_exp ψ s.im)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  apply (hr s hs).trans
  calc
    _ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε * (Dp*(complexity ψ s.im)^ε) :=
      mul_le_mul_of_nonneg_left (hpbound ψ hp s hs) (by positivity)
    _ = (Cd*Dp)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ s.im)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hc hr0) hε.le)
      (mul_pos hCd hDp).le

theorem polynomial_reciprocal_bound (χ : Character) (a : ℝ)
    (hβ : HeckeZeroSupremum.beta < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2) := by
  let e : ℝ := min (1/2000) ((a-HeckeZeroSupremum.beta)/16)
  have he : 0<e := lt_min (by norm_num) (by linarith)
  have he' : e<1/1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hmargin : HeckeZeroSupremum.beta+8*e ≤ a := by
    have hh := min_le_right (1/2000 : ℝ) ((a-HeckeZeroSupremum.beta)/16)
    change e ≤ (a-HeckeZeroSupremum.beta)/16 at hh
    linarith
  obtain ⟨C,hC,hbound⟩ := reciprocal_subpower e 1 he he' (by norm_num)
  let K : ℝ := C*((radical χ.modulus).absNorm : ℝ)*(2*(χ.modulus.absNorm : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨18*K, by positivity, ?_⟩
  intro s hs
  have h := hbound χ s (hmargin.trans hs)
  have hheight : (3+|s.im|)^2 ≤ 18*(1+|s.im|^2) := by
    nlinarith [sq_nonneg (|s.im|-1), sq_nonneg |s.im|]
  rw [Real.rpow_one] at h
  calc
    _ ≤ K*(3+|s.im|)^2 := by
      convert h using 1 ; unfold K presentationComplexity complexity ; ring
    _ ≤ K*(18*(1+|s.im|^2)) := mul_le_mul_of_nonneg_left hheight hK
    _ = _ := by ring

end SevenEighths.HeckeReciprocalGrowth

end

end OAI
end OAIOriginalModule2028

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicControl
Source SHA256: 7b052b188a242174544251848e99ead459104f79134c9c9e0c36cdc684192f32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2029




namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem original_disk_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := HeckeLogarithmicActual.disk_control e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
  intro χ hχ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).1 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : LFunction χ z = LFunction ψ z*factors χ.modulus ψ z :=
    LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      (LFunction ψ z)⁻¹*(factors χ.modulus ψ z)⁻¹ := by
    rw [HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos]
    simp only [HeckeReciprocal.reciprocal, ite_eq_right hψ]
  have hdel1 : ‖factors χ.modulus ψ z‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ.modulus ψ z)⁻¹)]
  have hdel2 : ‖(factors χ.modulus ψ z)⁻¹‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖LFunction ψ z‖+‖(LFunction ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (LFunction ψ z))
      have h2 := mul_le_mul_of_nonneg_left hdel2 (norm_nonneg ((LFunction ψ z)⁻¹))
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_original_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖ ≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

end SevenEighths.HeckeDyadicControl

end

end OAI
end OAIOriginalModule2029

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicBuffered
Source SHA256: 508090ebf0750c0910207745e020c6de3f258598c5fb66529798cb288cb38672
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2030



namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeLogarithmic HeckeReciprocalGrowth

theorem presentationComplexity_mono_height (χ : Character) {t H : ℝ}
    (ht : |t|≤H) : presentationComplexity χ t≤presentationComplexity χ H := by
  unfold presentationComplexity complexity
  have hH : 0≤H := (abs_nonneg t).trans ht
  rw [abs_of_nonneg hH]
  gcongr

theorem buffered_rectangle_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+6*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
        C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDyadicControl.buffered_original_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2 : ℂ)+z.im*I)=((z.re-2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-2≤0)]
    linarith
  have hz2 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-2*e) :=
    closedBall_subset_closedBall (by linarith) hz6
  refine ⟨HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
    hmax j z.im hzi hz2, ?_⟩
  apply (hbound χ hχ T a i hT ha ha' hmax j z.im hzi z hz6).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow
  · unfold presentationComplexity complexity
    positivity
  · exact presentationComplexity_mono_height _ hzi
  · exact hε.le

theorem translated_rectangle_mem {a e σ freq l r H T : ℝ}
    (hl : a+6*e≤l+σ) (hr : r+σ≤2) (hlr : l≤r) (hT : 0≤T)
    (hfreq : |freq|+T≤H) {s : ℂ} (hs : s ∈ (uIcc l r ×ℂ uIcc (-T) T)) :
    a+6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧
      |(s+shift σ freq).im|≤H := by
  have hs' : s.re ∈ Icc l r ∧ s.im ∈ Icc (-T) T := by
    change s.re ∈ uIcc l r ∧ s.im ∈ uIcc (-T) T at hs
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using hs
  have hsi : |s.im|≤T := abs_le.mpr hs'.2
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.1]
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.2]
  · have hi : (s+shift σ freq).im=s.im-freq := by simp [shift,sub_eq_add_neg]
    rw [hi]
    exact (abs_sub _ _).trans (by linarith)

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2030

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicPointwise
Source SHA256: c59a840dc3c2a74b862306eb443e5d9cfff4a62d58139890684a27922f34ec22
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2031


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_four_sides (A B C D : ℂ) :
    ‖A+I*(B-C)+D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
  have h₁ := norm_add_le (A+I*(B-C)) D
  have h₂ := norm_add_le A (I*(B-C))
  have h₃ := norm_sub_le B C
  simp only [norm_mul,norm_I,one_mul] at h₂
  linarith

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

theorem polynomial_bound_of_rectangle_split (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K Kc : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K) (hKc : 0≤Kc)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hcentralSeries : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤Kc)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*Kc*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ Kc T hDp hC₂ hKc hT
    hm₂ hcentralSeries
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2031

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicBounded
Source SHA256: 737524365d6749c9238a946557df14270b4dd36eecbd58a0608a9c560fd2dcc6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2032


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem buffered_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
      ‖polynomial (χ j) inverse W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(a+6*e-1/2)*K*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*K/(1+V)^n)*|2-a-6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨C,hC,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
  have hK : 0≤K := mul_nonneg hC.le (Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _)
  have hlr : a+6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    translated_rectangle_mem (a:=a) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : a+6*e≤a+6*e-σ+σ) (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
  have hz {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    hrect χ hχ T a i hT ha ha' hmax j (s+shift σ freq) (hmem hs).1 (hmem hs).2.1 (hmem hs).2.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) inverse (s+shift σ freq)‖≤K := by
    have hb := (hz hs).2
    cases inverse
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans hb
  have hbound := polynomial_bound_of_rectangle (χ j) (hχ j) inverse W A B hA hWs hW
    D σ freq (a+6*e-σ) (2-σ) V C₂ Cn K n hD hlr (by linarith) hV hC₂ hCn hK hm₂ hmn
    (fun _ hs _ => (hz hs).1) hseries
  dsimp only [K] at hbound
  convert hbound using 1 ; congr 2 <;> ring_nf

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2032

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicReflection
Source SHA256: 8932f905bd7b3fb05b915fa08e8aea2e42289e82298b8246b1a9ed81df78a188
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2033



namespace OAI

noncomputable section
open scoped Classical Topology
open Set Complex
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePrimitive HeckeStripActual

variable (c : O) [NeZero c]

theorem functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    {s : ℂ} (hs : s.re<1) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s)/Complex.Gamma s) *
      LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  by_cases h0 : s=0
  · subst s
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    simp
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s≠0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s≠1 := by intro h; apply h0; linear_combination -h
  have hΓ : Complex.Gamma (1-s)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [LFunction_eq_uncompleted c χ hu hp hχ,he,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓ]
  have ha : ((HeckeStrip.completionScale (conductor c)) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have hpow : (HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)=
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) := by
    rw [←Complex.cpow_add _ _ ha]
    congr 1
    ring
  rw [div_eq_mul_inv]
  calc
    _ = TraceCharacter.normalizedGauss c χ *
        ((HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
          (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)) *
        (Complex.Gamma (1-s)*(Complex.Gamma s)⁻¹) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by ring
    _ = _ := by rw [hpow]

theorem gamma_real_ratio_bound : ∃ C : ℝ, 0<C ∧
    ∀ x ∈ Icc (-(1/10 : ℝ)) (1/2), Real.Gamma (1-x)/Real.Gamma (x+2)≤C := by
  have hcont : ContinuousOn (fun x : ℝ => Real.Gamma (1-x)/Real.Gamma (x+2))
      (Icc (-(1/10 : ℝ)) (1/2)) := by
    intro x hx
    have hnum : DifferentiableAt ℝ Real.Gamma (1-x) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.2])
    have hden : DifferentiableAt ℝ Real.Gamma (x+2) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.1])
    exact ((hnum.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => 1-y) (show ContinuousAt (fun y : ℝ => 1-y) x by fun_prop)).div
      (hden.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => y+2) (show ContinuousAt (fun y : ℝ => y+2) x by fun_prop))
      (Real.Gamma_pos_of_pos (show 0<x+2 by linarith [hx.1])).ne').continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))

theorem gamma_ratio_strip_bound : ∃ C : ℝ, 0<C ∧ ∀ s : ℂ,
    -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖Complex.Gamma (1-s)/Complex.Gamma s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hreal⟩ := gamma_real_ratio_bound
  refine ⟨C,hC,?_⟩
  intro s hl hr
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1/2) (1/2-s.re) (-s.im) 2 (by linarith) (by norm_num; linarith)
  have hnum : ((1/2 : ℝ) : ℂ)+((1/2-s.re : ℝ)+(-s.im)*I)=1-s := by
    apply Complex.ext <;> simp; ring
  have hden : ((1/2 : ℝ) : ℂ)-((1/2-s.re : ℝ)+(-s.im)*I)+(2 : ℕ)=s+2 := by
    apply Complex.ext <;> simp
  simp only [ofReal_neg] at hb
  rw [hnum,hden] at hb
  have hreal' := hreal s.re ⟨hl,hr⟩
  have hb' : ‖Complex.Gamma (1-s)/Complex.Gamma (s+2)‖≤C := by
    apply hb.trans
    convert hreal' using 1; congr 1 <;> ring_nf
  have heq : Complex.Gamma (1-s)/Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s+k))*(Complex.Gamma (1-s)/Complex.Gamma (s+2)) := by
    rw [div_eq_mul_inv,CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat,div_eq_mul_inv]
    ring
  have hs : ‖s‖≤1+|s.im| := by
    have hsr : |s.re|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hn := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  norm_num only [Nat.cast_ofNat] at hf
  have hf' : ‖∏ k ∈ Finset.range 2,(s+k)‖≤(3+|s.im|)^2 :=
    hf.trans (pow_le_pow_left₀ (by positivity) (show ‖s‖+2≤3+|s.im| by linarith) 2)
  rw [heq,norm_mul]
  exact (mul_le_mul hf' hb' (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem completionScale_rpow_le {Q x : ℝ} (hQ : 0<Q) (hx : 0≤x) :
    HeckeStrip.completionScale Q ^ x≤Q^(x/2) := by
  have hs3 : Real.sqrt 3≤2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hscale : HeckeStrip.completionScale Q≤Real.sqrt Q := by
    unfold HeckeStrip.completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤3)]
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    nlinarith [Real.sqrt_nonneg Q,Real.pi_gt_three]
  calc
    _ ≤ (Real.sqrt Q)^x := Real.rpow_le_rpow
      (HeckeStrip.completionScale_pos Q hQ).le hscale hx
    _ = _ := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hQ.le]
      congr 1
      ring

theorem primitive_reflected_bound : ∃ C : ℝ, 0<C ∧
    ∀ (c : O) [NeZero c] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
      (_hp : FiniteFourier.IsPrimitiveOnIdeals χ), χ≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction (character c χ hu) s‖≤
      C*(conductor c)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ := by
  obtain ⟨C,hC,hgamma⟩ := gamma_ratio_strip_bound
  refine ⟨C,hC,?_⟩
  intro c _ χ hu hp hχ s hl hr
  rw [functional_equation c χ hu hp hχ (by linarith),norm_mul,norm_mul,norm_mul,
    TraceCharacter.normalizedGauss_norm c χ hp,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)))]
  have hscale := completionScale_rpow_le
    (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)) (show 0≤1-2*s.re by linarith)
  have he : (1-2*s).re=1-2*s.re := by simp
  rw [he]
  have he' : (1-2*s.re)/2=1/2-s.re := by ring
  rw [he'] at hscale
  calc
    _ ≤ ((conductor c)^(1/2-s.re)*(C*(3+|s.im|)^2))*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hscale (hgamma s hl hr)
        (norm_nonneg _) (Real.rpow_nonneg (by exact_mod_cast (conductor_ge_one c).trans' zero_le_one) _))
        (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI
end OAIOriginalModule2033

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedFamily
Source SHA256: e65009fce75c354379fe7d939628b5d7e8744d39112d2f939a13b7ebbfc6f15f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2034




namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePresentation HeckeFiniteDeletion

theorem family_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ η : Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue → η.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction η s‖≤C*(η.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction η (1-conj s)‖ := by
  obtain ⟨C,hC,hbound⟩ := primitive_reflected_bound
  refine ⟨C,hC,?_⟩
  intro η hp hη s hl hr
  have h := hbound (generator η) (principalResidue η) (principalResidue_unit η)
    (principalResidue_primitive η hp) (principalResidue_ne_one η hη) s hl hr
  have hi : HeckePrimitive.character (generator η) (principalResidue η)⁻¹
      (HeckePrimitive.inverse_unit_trivial (generator η) (principalResidue η) (principalResidue_unit η)) =
      (principalCharacter η).inverse := rfl
  rw [hi,LFunction_inverse_conj (principalCharacter η) (principalResidue_ne_one η hη),
    norm_conj,map_sub,map_one] at h
  change ‖LFunction (principalCharacter η) s‖≤_ at h
  rw [LFunction_principalCharacter η hη,LFunction_principalCharacter η hη] at h
  simpa only [HeckeStripActual.conductor,span_generator] using h

theorem LFunction_eq_of_mask_entire (χ ψ : Character) (hχ : χ.residue≠1)
    (hmask : ∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) (s : ℂ) :
    LFunction χ s=LFunction ψ s*factors χ.modulus ψ s := by
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha := LFunction_entire_nonprincipal χ hχ
  have hb : Differentiable ℂ (fun z => LFunction ψ z*factors χ.modulus ψ z) :=
    (LFunction_entire_nonprincipal ψ hψ).mul (factors_differentiable _ _)
  have he : LFunction χ=(fun z => LFunction ψ z*factors χ.modulus ψ z) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    exact LFunction_eq_of_mask_right χ ψ hmask hz
  exact congr_fun he s

theorem original_reflected_bound : ∃ C : ℝ, 0<C ∧ ∀ χ ψ : Character,
    FiniteFourier.IsPrimitiveOnIdeals ψ.residue → χ.residue≠1 →
    (∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction χ (1-conj s)‖*
      (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) := by
  obtain ⟨C,hC,hbound⟩ := family_reflected_bound
  refine ⟨C,hC,?_⟩
  intro χ ψ hp hχ hmask s hl hr
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have h := hbound ψ hp hψ s hl hr
  have hd : factors χ.modulus ψ (1-conj s)≠0 := factors_ne_zero _ _ (by simp; linarith)
  have he : LFunction ψ (1-conj s)=LFunction χ (1-conj s)*(factors χ.modulus ψ (1-conj s))⁻¹ := by
    rw [LFunction_eq_of_mask_entire χ ψ hχ hmask]
    field_simp
  rw [he,norm_mul] at h
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        (‖LFunction χ (1-conj s)‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖))*
          ‖factors χ.modulus ψ s‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem original_reflected_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_bound
  obtain ⟨Cl,hCl,hleft⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound ε hε
  obtain ⟨Cr,hCr,hright⟩ := HeckeDeletionBounds.factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cg*Cl*Cr,by positivity,?_⟩
  intro χ hχ s hl hr
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hR : 0<((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hd₁ := hleft χ.modulus ψ s
  have hd₂ : ‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    have h := hright χ.modulus ψ (1-conj s) (by simp; linarith)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hd : ‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      (Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
    calc
      _ ≤ (Cl*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε))*
          (Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) :=
        mul_le_mul hd₁ hd₂ (norm_nonneg _) (mul_nonneg hCl.le (Real.rpow_nonneg hR.le _))
      _ = _ := by
        have he : ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε =
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
          rw [←Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (Cl*Cr)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
              ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) := by ring
          _ = _ := by rw [he]
  have hQ' : (ψ.modulus.absNorm : ℝ)^(1/2-s.re)≤(χ.modulus.absNorm : ℝ)^(1/2-s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by linarith)
  calc
    _ ≤ Cg*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) :=
      hreflect χ ψ hp hχ hmask s hl hr
    _ ≤ Cg*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        ((Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)) := by
      apply mul_le_mul _ hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI
end OAIOriginalModule2034

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedControl
Source SHA256: 03f9e40ed1b004dd5aca0419ab6e73369a6186d3234b0d52aa5eb1c2b9f08d42
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2035


namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds HeckeDyadicReflection

theorem radical_norm_ge_one (M : Ideal O) : 1≤((radical M).absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))

theorem buffered_reflected_line_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (s : ℂ), s.re=1-a-6*e → |s.im|≤(3*i+2 : ℕ)*T →
      ‖LFunction (χ j) s‖≤C*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_subpower ε hε
  obtain ⟨Cb,hCb,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨Cg*Cb,mul_pos hCg hCb,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j s hs him
  have hwre : (1-conj s).re=a+6*e := by simp; linarith
  have hwim : (1-conj s).im=s.im := by simp
  have hw := hrect χ hχ T a i hT ha ha' hmax j (1-conj s)
    (by rw [hwre]) (by rw [hwre]; linarith) (by rwa [hwim])
  have hL : ‖LFunction (χ j) (1-conj s)‖≤
      Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hw.2
  have href := hreflect (χ j) (hχ j) s (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : 1/2-s.re=a-1/2+6*e := by rw [hs]; ring
  rw [hexp] at href
  have hR : ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)≤
      ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤6*e := max_le (by rw [hs]; linarith) (by positivity)
    linarith
  calc
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
        (3+|s.im|)^2*‖LFunction (χ j) (1-conj s)‖ := href
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε) := by
      gcongr
    _ = _ := by ring

theorem original_upper_strip (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ χ : Character, χ.residue≠1 → ∀ s : ℂ,
      -(1/10 : ℝ)≤s.re →
      ‖LFunction χ s‖≤C*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
        ((radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := factors_any_re_subpower_bound ε hε
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h => hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp hs
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤
      Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε) := by
    apply (hdel χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤1/10 := max_le (by linarith) (by norm_num)
    linarith
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε)) :=
      mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^(1/10+ε)) := by
      gcongr
      linarith
    _ = _ := by ring

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2035

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedPointwise
Source SHA256: 4252086123f81faa3692095e5a3f83b1d0af84d2577c6989a3bc217ae5ba912b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2036


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds

theorem reflected_polynomial_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ Cg Cr : ℝ, 0<Cg ∧ 0<Cr ∧
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤D → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      let H := (3*i+2 : ℕ)*T
      let Q := ((χ j).modulus.absNorm : ℝ)
      let R := ((radical (χ j).modulus).absNorm : ℝ)
      let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
      let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
        (presentationComplexity (χ j) H)^ε
      ‖polynomial (χ j) false W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(1/2-a-6*e)*Kr*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*Kg/(1+V)^n)*|1+a+6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨Cg,hCg,hglobal⟩ := original_upper_strip ε hε
  obtain ⟨Cr,hCr,hreflect⟩ := buffered_reflected_line_control e ε he he' hε
  refine ⟨Cg,Cr,hCg,hCr,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let H : ℝ := (3*i+2 : ℕ)*T
  let Q : ℝ := (χ j).modulus.absNorm
  let R : ℝ := (radical (χ j).modulus).absNorm
  let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
  let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
    (presentationComplexity (χ j) H)^ε
  have hKg : 0≤Kg := by dsimp [Kg,Q,R]; positivity
  have hKr : 0≤Kr := by dsimp [Kr,Q,R,presentationComplexity,HeckeLogarithmic.complexity]; positivity
  have hlr : 1-a-6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      1-a-6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧ |(s+shift σ freq).im|≤H := by
    have h := translated_rectangle_mem (a:=1-a-12*e) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : 1-a-12*e+6*e≤1-a-6*e-σ+σ)
      (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
    constructor
    · linarith [h.1]
    · exact h.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) false (s+shift σ freq)‖≤Kg := by
    have h := hglobal (χ j) (hχ j) (s+shift σ freq) (by linarith [(hmem hs).1])
    apply h.trans
    dsimp [Kg,Q,R]
    gcongr
    exact (hmem hs).2.2
  have hcentral (t : ℝ) (ht : t∈Icc (-V) V) :
      ‖series (χ j) false (((1-a-6*e-σ : ℝ) : ℂ)+t*I+shift σ freq)‖≤Kr := by
    have him : |t-freq|≤H := (abs_sub _ _).trans (by
      have ht' := abs_le.mpr ht
      change |t|+|freq|≤H
      linarith)
    apply hreflect χ hχ T a i hT ha ha' hmax j
    · simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero,shift_re]
      ring
    · simpa [shift,sub_eq_add_neg,H] using him
  have hb := polynomial_bound_of_rectangle_split (χ j) (hχ j) false W A B hA hWs hW
    D σ freq (1-a-6*e-σ) (2-σ) V C₂ Cn Kg Kr n hD hlr (by linarith)
    hV hC₂ hCn hKg hKr hm₂ hmn hcentral (fun _ _ h => Bool.false_ne_true h |>.elim) hseries
  dsimp only [Kg,Kr,Q,R,H] at hb
  convert hb using 1 ; congr 2 <;> ring_nf

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2036

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicScale
Source SHA256: ac9c335a1ed84aa17ecc893157c92165fe7d5dcf10c29f9c9eb386c6be48e73e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2037


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem radical_dvd (M : Ideal O) (hM : M≠0) : radical M∣M := by
  unfold radical SmoothMobiusCorrection.primeProduct
  rw [SmoothMobiusCorrection.prod_primeSet M (fun J : Ideal O => J)]
  exact IdealMobiusDivisorSum.support_product_dvd hM (Finset.Subset.refl _)

theorem radical_norm_le_modulus (χ : Character) :
    ((radical χ.modulus).absNorm : ℝ)≤χ.modulus.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
    (map_dvd Ideal.absNorm (radical_dvd χ.modulus χ.modulus_ne_bot))

theorem presentationComplexity_le_of_modulus_le (χ : Character) (U H : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) :
    presentationComplexity χ H≤2*U^2*(3+|H|)^2 := by
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hU : 0≤U := (Nat.cast_nonneg χ.modulus.absNorm).trans hQ
  unfold presentationComplexity complexity
  calc
    _ ≤ U*(2*U*(3+|H|)^2) := by gcongr
    _ = _ := by ring

theorem reflected_conductor_cost (χ : Character) (U a e ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (ha : 1/2≤a) (he : 0≤e) (hε : 0≤ε) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)≤U^(a-1/2+12*e+2*ε) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one
    ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hR := (radical_norm_le_modulus χ).trans hQ
  calc
    _ ≤ U^(a-1/2+6*e)*U^(6*e+2*ε) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hQ (by linarith))
        (Real.rpow_le_rpow (by positivity) hR (by positivity))
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hU.le _)
    _ = _ := by
      rw [←Real.rpow_add hU]
      congr 1
      ring

theorem positive_scale_exponent (U a e r : ℝ) (hU : 0<U) :
    (U^r)^(a+6*e-1/2)=U^((a-1/2+6*e)*r) := by
  rw [←Real.rpow_mul hU.le]
  congr 1
  ring

theorem reflected_scale_exponent (U a e ε m : ℝ) (hU : 0<U) :
    U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e)=
      U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε) := by
  rw [←Real.rpow_mul hU.le,←Real.rpow_add hU]
  congr 1
  ring

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2037

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
Source SHA256: f58fdd3249b3e9022fc5185928ac778b9daf5bfab923d98abd18464709017fe8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2038


namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem exists_external_tail_order (τ B p : ℝ) (hτ : 0<τ) :
    ∃ n : ℕ, ∀ Z : ℝ, 1≤Z → Z^B/(1+Z^τ)^n≤Z^p := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((B-p)/τ)
  refine ⟨n,?_⟩
  intro Z hZ
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hn' : B≤p+τ*(n : ℝ) := by
    have h := (div_lt_iff₀ hτ).mp hn
    nlinarith
  have hden : 0<(1+Z^τ)^n := by positivity
  apply (div_le_iff₀ hden).mpr
  calc
    Z^B ≤ Z^(p+τ*(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _ = Z^p*(Z^τ)^n := by
      rw [Real.rpow_add hZp,Real.rpow_mul hZp.le,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hZp.le _) (by linarith) n)
      (Real.rpow_nonneg hZp.le _)

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

theorem uniform_external_tail_order (τ dmax B R : ℝ)
    (hτ : 0<τ) (_hdmax : 0≤dmax) (hB : 0≤B) (hR : 0≤R) :
    ∃ n : ℕ, ∀ Z d p : ℝ, 1≤Z → 0≤d → d≤dmax → -R≤p →
      (Z^d)^B/(1+Z^τ/2)^n≤(2 : ℝ)^n*(Z^d)^p := by
  obtain ⟨n,hn⟩ := exists_external_tail_order τ (dmax*B) (-dmax*R) hτ
  refine ⟨n,?_⟩
  intro Z d p hZ hd hd' hp
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hnum : (Z^d)^B≤Z^(dmax*B) := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd' hB)
  have htarget : Z^(-dmax*R)≤(Z^d)^p := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith [mul_nonneg hd (show 0≤p+R by linarith),
      mul_nonneg (show 0≤dmax-d by linarith) hR]
  have hden : ((1+Z^τ)/2)^n≤(1+Z^τ/2)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ (Z^(dmax*B))/((1+Z^τ)/2)^n :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (2 : ℝ)^n*(Z^(dmax*B)/(1+Z^τ)^n) := by
      rw [div_pow]
      field_simp
    _ ≤ (2 : ℝ)^n*Z^(-dmax*R) := mul_le_mul_of_nonneg_left (hn Z hZ) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left htarget (by positivity)

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2038

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicCentralBudget
Source SHA256: ea70a0f2b24ba698ca30d97f55383a796b377cc434de9e506adc5d750f1d88e6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2039



namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem presentation_cost (χ : Character) (U H ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hε : 0≤ε) (hε' : ε≤1) :
    (presentationComplexity χ H)^ε≤2*U^(2*ε)*(3+H)^2 := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hbase : 1≤3+H := by linarith
  have hc := presentationComplexity_le_of_modulus_le χ U H hQ
  rw [abs_of_nonneg hH] at hc
  have hp : (presentationComplexity χ H)^ε≤(2*U^2*(3+H)^2)^ε :=
    Real.rpow_le_rpow (by unfold presentationComplexity complexity; positivity) hc hε
  have he : (2*U^2*(3+H)^2)^ε=(2 : ℝ)^ε*U^(2*ε)*(3+H)^(2*ε) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) (by positivity)]
    simp only [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤U),
      ←Real.rpow_mul (by linarith : 0≤3+H),Nat.cast_ofNat]
  rw [he] at hp
  have h2 : (2 : ℝ)^ε≤2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hε'
  have hh : (3+H)^(2*ε)≤(3+H)^2 := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
  exact hp.trans (mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _))
    hh (Real.rpow_nonneg (by linarith) _) (by positivity))

theorem positive_central_cost (χ : Character) (U H a e ε η r : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hε : 0≤ε) (hε' : ε≤1)
    (hheight : (3+H)^4≤U^η) :
    (U^r)^(a+6*e-1/2)*(presentationComplexity χ H)^ε≤
      2*U^((a-1/2+6*e)*r+2*ε+η) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hh : (3+H)^2≤U^η := by
    apply le_trans _ hheight
    exact pow_le_pow_right₀ (by linarith) (by decide : 2≤4)
  calc
    _ ≤ (U^r)^(a+6*e-1/2)*(2*U^(2*ε)*U^η) :=
      mul_le_mul_of_nonneg_left ((presentation_cost χ U H ε hQ hH hε hε').trans
        (mul_le_mul_of_nonneg_left hh (by positivity))) (by positivity)
    _ = _ := by
      rw [positive_scale_exponent U a e r hU]
      rw [Real.rpow_add hU,Real.rpow_add hU]
      ring

theorem reflected_central_cost (χ : Character) (U H a e ε η m : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (ha : 1/2≤a)
    (he : 0≤e) (hε : 0≤ε) (hε' : ε≤1) (hheight : (3+H)^4≤U^η) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)*(3+H)^2*
      (presentationComplexity χ H)^ε*(U^m)^(1/2-a-6*e)≤
      2*U^((a-1/2)*(1-m)+6*e*(2-m)+4*ε+η) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hcost := reflected_conductor_cost χ U a e ε hQ ha he hε
  have hcomplex := presentation_cost χ U H ε hQ hH hε hε'
  have hcomplex0 : 0≤(presentationComplexity χ H)^ε := Real.rpow_nonneg (by
    unfold presentationComplexity complexity
    positivity) _
  calc
    _ ≤ U^(a-1/2+12*e+2*ε)*(3+H)^2*(2*U^(2*ε)*(3+H)^2)*(U^m)^(1/2-a-6*e) := by
      gcongr
    _ = 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*(3+H)^4 := by ring
    _ ≤ 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*U^η :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by
      rw [reflected_scale_exponent U a e ε m hU]
      calc
        _ = 2*(U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε)*U^(2*ε)*U^η) := by ring
        _ = 2*U^(((a-1/2)*(1-m)+6*e*(2-m)+2*ε)+2*ε+η) := by
          rw [←Real.rpow_add hU,←Real.rpow_add hU]
        _ = _ := by congr 2; ring

theorem direct_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤r) (hrR : r≤R) (hheight : (3+H)^4≤U^η) :
    (U^r)^(3/2 : ℝ)*(presentationComplexity χ H)^κ≤2*U^(2*R+2+η) := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have h := positive_central_cost χ U H 2 0 κ η r hQ hH hκ hκ' hheight
  norm_num only [mul_zero,add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hU
  nlinarith

theorem reflected_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (hH : 0≤H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤r) (hrR : r≤R) (hheight : (3+H)^4≤U^η) :
    (U^r)^(3/2 : ℝ)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
      ((radical χ.modulus).absNorm : ℝ)^(1/10+κ)*(3+H)^2≤U^(2*R+2+η) := by
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hh : (3+H)^2≤U^η :=
    (pow_le_pow_right₀ (by linarith) (by decide : 2≤4)).trans hheight
  calc
    _ ≤ (U^r)^(3/2 : ℝ)*U^(3/5 : ℝ)*U^(1/10+κ)*U^η := by
      gcongr
    _ = U^(r*(3/2)+(3/5)+(1/10+κ)+η) := by
      rw [←Real.rpow_mul hUp.le,←Real.rpow_add hUp,←Real.rpow_add hUp,←Real.rpow_add hUp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2039

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicLossBudget
Source SHA256: 9488cc14894c68cd9a014d4de033f35ca8da14a796998a2be4b5f811a2c6b1e0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2040


namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem central_squared_exponents (R a e κ η ε r m : ℝ)
    (hR : 0≤R) (he : 0≤e) (hκ : 0≤κ) (_hη : 0≤η)
    (hr : r≤R) (hm : 0≤m)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    2*((a-1/2+6*e)*r+2*κ+η)≤(2*a-1)*r+ε ∧
    2*((a-1/2)*(1-m)+6*e*(2-m)+4*κ+η)≤(2*a-1)*(1-m)+ε := by
  have hEr : e*r≤e*R := mul_le_mul_of_nonneg_left hr he
  have hEm : 0≤e*m := mul_nonneg he hm
  have hER : 0≤e*R := mul_nonneg he hR
  constructor <;> nlinarith

theorem exists_central_loss_parameters (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ e₀ κ η : ℝ, 0<e₀ ∧ e₀≤1/1000 ∧ 0<κ ∧ κ≤1 ∧ 0<η ∧
      ∀ e : ℝ, 0<e → e<e₀ → 12*e*(R+2)+8*κ+2*η≤ε/2 := by
  let e₀ : ℝ := min (1/1000) (ε/(96*(R+2)))
  let κ : ℝ := min (1/2) (ε/64)
  let η : ℝ := ε/16
  have hRp : 0<R+2 := by linarith
  have he₀ : 0<e₀ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hκ : 0<κ := lt_min (by norm_num) (div_pos hε (by norm_num))
  refine ⟨e₀,κ,η,he₀,min_le_left _ _,hκ,(min_le_left _ _).trans (by norm_num),
    div_pos hε (by norm_num),?_⟩
  intro e he he'
  have heb : e≤ε/(96*(R+2)) := he'.le.trans (min_le_right _ _)
  have heb' := (le_div_iff₀ (by positivity : 0<96*(R+2))).mp heb
  have hκb : κ≤ε/64 := min_le_right _ _
  dsimp only [η]
  nlinarith

theorem indexed_height_bound (i I : ℕ) (hi : i≤I) (T : ℝ) (hT : 0≤T) :
    (3+(3*i+2 : ℕ)*T)^4≤(3*(I : ℝ)+5)^4*(1+T)^4 := by
  have hi' : (i : ℝ)≤I := by exact_mod_cast hi
  have hlin : 3+(3*i+2 : ℕ)*T≤(3*(I : ℝ)+5)*(1+T) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hi' hT,Nat.cast_nonneg (α:=ℝ) I]
  calc
    _ ≤ ((3*(I : ℝ)+5)*(1+T))^4 := pow_le_pow_left₀ (by positivity) hlin 4
    _ = _ := mul_pow _ _ _

theorem min_plain_bound (X C U δ m ε : ℝ)
    (h₁ : X≤C*U^(δ*m+ε)) (h₂ : X≤C*U^(δ*(1-m)+ε)) :
    X≤C*U^(δ*min m (1-m)+ε) := by
  rcases le_total m (1-m) with h | h
  · simpa only [min_eq_left h] using h₁
  · simpa only [min_eq_right h] using h₂

theorem squared_bound_of_central_and_error (z : ℂ) (U C E p b ε : ℝ)
    (hU : 1≤U) (hC : 0≤C) (hE : 0≤E) (hε : 0≤ε)
    (hb : 2*b≤ε)
    (hz : ‖z‖≤C*U^(p+b)+E*U^p) :
    ‖z‖^2≤(C+E)^2*U^(2*p+ε) := by
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hp₁ : U^(p+b)≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hp₂ : U^p≤U^(p+ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hn : ‖z‖≤(C+E)*U^(p+ε/2) := by
    calc
      _ ≤ C*U^(p+b)+E*U^p := hz
      _ ≤ C*U^(p+ε/2)+E*U^(p+ε/2) := add_le_add
        (mul_le_mul_of_nonneg_left hp₁ hC) (mul_le_mul_of_nonneg_left hp₂ hE)
      _ = _ := by ring
  calc
    _ ≤ ((C+E)*U^(p+ε/2))^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
      have hp : (U^(p+ε/2))^2=U^(2*p+ε) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
        congr 1
        norm_num
        ring
      rw [mul_pow,hp]

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2040

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicScaled
Source SHA256: e1576b4de60dd2ad77d5caf81c7ad870e21cf3c7f25c3713842e9fa3b8a7eeeb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2041


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_direct_bound (e κ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤η → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) inverse W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+6*e)*r+2*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cb,hCb,hbound⟩ := buffered_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cb*Real.pi+8*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := positive_central_cost (χ j) U H a e κ η r hQ hH hκ.le hκ' hheight
  have hexternal := direct_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-6*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+6*e-1/2)*(Cb*(presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η) := by
    calc
      _ = (C₂*Cb*Real.pi)*((U^r)^(a+6*e-1/2)*(presentationComplexity (χ j) H)^κ) := by ring
      _ ≤ (C₂*Cb*Real.pi)*(2*U^((a-1/2+6*e)*r+2*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cb*(presentationComplexity (χ j) H)^κ)/(1+V)^n)*|2-a-6*e|≤
      (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cb*((U^r)^(3/2 : ℝ)*(presentationComplexity (χ j) H)^κ)/(1+V)^n*|2-a-6*e| := by ring
      _ ≤ 2*Cn*Cb*(2*U^(2*R+2+η))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cb*Real.pi≤C := by dsimp [C]; nlinarith [mul_nonneg hE Real.pi_pos.le]
  have heC : 8*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith [Real.pi_pos]
  calc
    _ ≤ (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2041

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicScaledReflection
Source SHA256: 98ff7c446d1d1209dcbbf786e5d7e36150c4d9b727bed7a51a0db9caae64eb9e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2042


namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_reflected_bound (e κ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤η → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) false W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cg,Cr,hCg,hCr,hbound⟩ := reflected_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cr*Real.pi+6*Cg+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := reflected_central_cost (χ j) U H a e κ η r hQ hH (by linarith) he.le hκ.le hκ' hheight
  have hexternal := reflected_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |1+a+6*e|≤3 := abs_le.mpr ⟨by linarith,by linarith⟩
  let Q : ℝ := (χ j).modulus.absNorm
  let Rad : ℝ := (HeckeDeletionBounds.radical (χ j).modulus).absNorm
  have hc : C₂*(U^r)^(1/2-a-6*e)*(Cr*Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
      (presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η) := by
    calc
      _ = (C₂*Cr*Real.pi)*(Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
        (presentationComplexity (χ j) H)^κ*(U^r)^(1/2-a-6*e)) := by ring
      _ ≤ (C₂*Cr*Real.pi)*(2*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cg*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)/(1+V)^n)*|1+a+6*e|≤
      (6*Cg)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cg*((U^r)^(3/2 : ℝ)*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)/(1+V)^n*|1+a+6*e| := by ring
      _ ≤ 2*Cn*Cg*U^(2*R+2+η)/(1+V)^n*3 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cr*Real.pi≤C := by dsimp [C]; nlinarith only [hCg,mul_nonneg hE Real.pi_pos.le]
  have heC : 6*Cg+E*Real.pi≤C := by dsimp [C]; nlinarith only [mul_pos hCr Real.pi_pos]
  calc
    _ ≤ (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+
        (6*Cg)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+
        (6*Cg+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2042

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicSource
Source SHA256: 16c4e2b0da614f6532f026074cd804282f39808866c56d2fd40456fb497e2f70
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2043


namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem source_dyadic_bounds (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0≤profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0<C ∧
    ∀ (Z d : ℝ), 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ r σ freq : ℝ, (χ j).modulus.absNorm≤Z^d → 0≤r → r≤R →
      |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
      (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^2*‖mellin W ((x : ℂ)+t*I)‖≤profileBound 2) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤profileBound (n+2)) →
      ‖polynomial (χ j) inverse W ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
      ‖polynomial (χ j) false W ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*min r (1-r)+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ he he' hκ hκ'
  obtain ⟨Cr,hCr,hreflect⟩ := scaled_reflected_bound e κ he he' hκ hκ'
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+2+η) (R+1)
    hτ hdmax (by positivity) (by positivity)
  let K := Cd+Cr
  have hK : 0<K := add_pos hCd hCr
  let M := K*profileBound 2
  let E := K*profileBound (n+2)*(2 : ℝ)^n
  let C := (M+E)^2+1
  have hM : 0≤M := mul_nonneg hK.le (hprofile 2)
  have hE : 0≤E := mul_nonneg (mul_nonneg hK.le (hprofile (n+2))) (by positivity)
  refine ⟨n,C,by dsimp [C]; positivity,?_⟩
  intro Z d hZ hd hd' hT ι _ χ hχ a i ha ha' hmax j inverse W A B hA hWs hW
    r σ freq hQ hr hrR hfreq hheight hm₂ hmn
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hV : 0≤Z^τ/2 := by positivity
  have hleft : a+6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨by linarith,by linarith⟩
  have hleft' : 1-a-6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨le_rfl,by linarith⟩
  have hsub : Icc (a+6*e-σ) (2-σ)⊆Icc (1-a-6*e-σ) (2-σ) := by
    intro x hx
    exact ⟨hleft.1.trans hx.1,hx.2⟩
  have hD (inv : Bool) := hdirect χ hχ (Z^τ) a i hT ha ha' hmax j inv W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2))
    (hm₂ _ hleft) (fun x hx => hmn x (hsub hx))
  have hP := hreflect χ hχ (Z^τ) a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2)) (hm₂ _ hleft') hmn
  have hCdK : Cd≤K := le_add_of_nonneg_right hCr.le
  have hCrK : Cr≤K := le_add_of_nonneg_left hCd.le
  have hnormD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖≤
        M*U^((a-1/2)*r+(6*e*r+2*κ+η))+
          K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply (hD inv).trans
    dsimp only [M]
    have hexp : (a-1/2+6*e)*r+2*κ+η=(a-1/2)*r+(6*e*r+2*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hnormP : ‖polynomial (χ j) false W (U^r) σ freq‖≤
      M*U^((a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η))+
        K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply hP.trans
    dsimp only [M]
    have hexp : (a-1/2)*(1-r)+6*e*(2-r)+4*κ+η=
        (a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hfinish (z : ℂ) (p b : ℝ) (hp : -(R+1)≤p) (hb : 2*b≤ε)
      (hz : ‖z‖≤M*U^(p+b)+K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n) :
      ‖z‖^2≤C*U^(2*p+ε) := by
    have ht := htail Z d p hZ hd hd' hp
    have herror : K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n≤E*U^p := by
      calc
        _ = (K*profileBound (n+2))*(U^(2*R+2+η)/(1+Z^τ/2)^n) := by ring
        _ ≤ (K*profileBound (n+2))*((2 : ℝ)^n*U^p) :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg hK.le (hprofile _))
        _ = _ := by dsimp [E]; ring
    have hn := hz.trans (add_le_add (le_refl _) herror)
    have hs := squared_bound_of_central_and_error z U M E p b ε hU hM hE hε.le hb hn
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    dsimp [C]
    linarith
  have hpos : 0≤(a-1/2)*r := mul_nonneg (by linarith) hr
  have href : -(R+1)≤(a-1/2)*(1-r) := by
    have hp : (a-1/2)*r≤(1/2)*R := mul_le_mul (by linarith) hrR hr (by norm_num)
    nlinarith
  have hbud := central_squared_exponents R a e κ η ε r r hR he.le hκ.le hη hrR hr hbudget
  have hbD : 2*(6*e*r+2*κ+η)≤ε := by nlinarith [hbud.1]
  have hbP : 2*(6*e*(2-r)+4*κ+η)≤ε := by nlinarith [hbud.2]
  have hfinalD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖^2≤C*U^((2*a-1)*r+ε) := by
    convert hfinish _ ((a-1/2)*r) (6*e*r+2*κ+η) (by linarith) hbD (hnormD inv) using 1 ;
      congr 2 ; ring
  have hfinalP : ‖polynomial (χ j) false W (U^r) σ freq‖^2≤C*U^((2*a-1)*(1-r)+ε) := by
    convert hfinish _ ((a-1/2)*(1-r)) (6*e*(2-r)+4*κ+η) href hbP hnormP using 1 ;
      congr 2 ; ring
  exact ⟨hfinalD inverse,min_plain_bound _ C U (2*a-1) r ε (hfinalD false) hfinalP⟩

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2043

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
Source SHA256: bcd6a1684cde46e6198037c05268ea4f9b4fe7e2db89eba9682adb8577b6d880
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2044



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma norm_phase (x D : ℝ) (hx : 0<x) (hD : 0<D) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-s)*FourierBridge.logPhase t (Real.log (x/D)) =
      (D : ℂ)^(-s)*((x/D : ℝ) : ℂ)^(-HeckeDyadic.shift s.re (2*Real.pi*t-s.im)) := by
  have hxD : 0<x/D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold FourierBridge.logPhase HeckeDyadic.shift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s=(s.re : ℂ)+(s.im : ℂ)*I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring

lemma normalization (D : ℝ) (hD : 0<D) (s : ℂ) :
    (D : ℂ)^((1/2 : ℂ)-s)*(D : ℂ)^(-(1/2 : ℂ))=(D : ℂ)^(-s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 1
  ring

lemma polynomial_eq_finite (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

theorem phase_sum_eq_polynomial (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (s : ℂ) (t : ℝ) (S : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    (∑ J∈S, coefficient χ inverse J*(J.absNorm : ℂ)^(-s)*
      W ((J.absNorm : ℝ)/D)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ inverse W D s.re (2*Real.pi*t-s.im) := by
  rw [polynomial_eq_finite χ inverse W D s.re (2*Real.pi*t-s.im) S hcover,
    ← mul_assoc, normalization D hD s, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hnorm : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS J hJ))
  have hp := norm_phase (J.absNorm : ℝ) D hnorm hD s t
  simp only [Complex.ofReal_natCast] at hp
  calc
    _ = coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
        ((J.absNorm : ℂ)^(-s)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) := by ring
    _ = _ := by rw [hp]; ring

def inverseProfile (V W : ℝ→ℂ) (Dstar D : ℝ) (x : ℝ) : ℂ :=
  V (D*x/Dstar)*W x

lemma inverseProfile_at_norm (V W : ℝ→ℂ) (Dstar D x : ℝ) (hD : 0<D) :
    inverseProfile V W Dstar D (x/D)=V (x/Dstar)*W (x/D) := by
  unfold inverseProfile
  congr 2
  field_simp

lemma weighted_eq (χ : Character) (s : ℂ) (J : Ideal O) (hJ : J≠0) :
    IdealEuler.weighted (idealCoeff χ) s J=idealCoeff χ J*(J.absNorm : ℂ)^(-s) := by
  simp only [IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]

theorem plain_phase_eq (χ : Character) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (plainCoefficient χ W D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ false W D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ false W D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [plainCoefficient, weighted_eq χ s J (hS J hJ)]
  rfl

theorem inverse_phase_eq (χ : Character) (V W : ℝ→ℂ) (Dstar D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (inverseCoefficient χ V W Dstar D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*
        polynomial χ true (inverseProfile V W Dstar D) D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ true (inverseProfile V W Dstar D) D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [inverseCoefficient, weighted_eq χ s J (hS J hJ), inverseProfile_at_norm V W Dstar D _ hD]
  simp only [coefficient, ite_true]
  ring

lemma normalization_norm (D : ℝ) (hD : 0<D) (s : ℂ) :
    ‖(D : ℂ)^((1/2 : ℂ)-s)‖=D^(1/2-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  congr 1
  simp

theorem pair_phase_norm (χ : Character) (V W₁ W₂ : ℝ→ℂ) (Dstar D N : ℝ)
    (hD : 0<D) (hN : 0<N) (s : ℂ) (t : ℝ) (S R : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0) (hR : ∀ J∈R, J≠0)
    (hcoverS : ∀ J : Ideal O, J≠0 → inverseProfile V W₁ Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (hcoverR : ∀ J : Ideal O, J≠0 → W₂ ((J.absNorm : ℝ)/N)≠0 → J∈R) :
    ‖phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
        (fun J => Real.log ((J.absNorm : ℝ)/D)) t‖ *
      ‖phasePolynomial R (plainCoefficient χ W₂ N s)
        (fun J => Real.log ((J.absNorm : ℝ)/N)) t‖ =
      D^(1/2-s.re)*N^(1/2-s.re)*
        (‖polynomial χ true (inverseProfile V W₁ Dstar D) D s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false W₂ N s.re (2*Real.pi*t-s.im)‖) := by
  rw [inverse_phase_eq χ V W₁ Dstar D hD s t S hS hcoverS,
    plain_phase_eq χ W₂ N hN s t R hR hcoverR,
    norm_mul, norm_mul, normalization_norm D hD s, normalization_norm N hN s]
  ring

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end OAIOriginalModule2044

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicSupport
Source SHA256: 467a4c3d414ff91b1411e18eff8955a42978291a301c777e1318a0bd9292c3b2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2045



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDetectorFinite HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def fourierSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U⌉₊

lemma fourierSet_nonzero (U : ℝ) (J : Ideal O) (hJ : J∈fourierSet U) : J≠0 := by
  have hn := (mem_idealsUpTo.mp hJ).1
  exact Ideal.absNorm_eq_zero_iff.not.mp (by omega)

lemma pairSet_subset_fourier (U : ℝ) (hU : 0≤U) :
    pairSet U ⊆ fourierSet U ×ˢ fourierSet U := by
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  have hb : ⌈2*U⌉₊ ≤ ⌈16*U⌉₊ := Nat.ceil_mono (by linarith)
  exact Finset.mem_product.mpr
    ⟨mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h1).1,(mem_idealsUpTo.mp h1).2.trans hb⟩,
     mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h2).1,(mem_idealsUpTo.mp h2).2.trans hb⟩⟩

lemma annular_covered (U D : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : W ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hr : (J.absNorm : ℝ)/D<2 := lt_of_not_ge (fun hn => hw (hW _ hn))
  have hn : (J.absNorm : ℝ)≤16*U := by
    have hh := (div_lt_iff₀ hD).mp hr
    linarith
  exact_mod_cast hn.trans (Nat.le_ceil (16*U))

lemma inverse_annular_covered (U D Dstar : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (V W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply annular_covered U D hD hDU W hW J hJ
  exact (mul_ne_zero_iff.mp hw).2

lemma scales_le_eight_terminal (U : ℝ) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U) :
    (2 : ℝ)^j≤8*U ∧ (2 : ℝ)^k≤8*U := by
  have hj : 1≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hk : 1≤(2 : ℝ)^k := one_le_pow₀ (by norm_num)
  constructor
  · exact (le_mul_of_one_le_right (by positivity) hk).trans hprod.le
  · exact (le_mul_of_one_le_left (by positivity) hj).trans hprod.le

theorem dyadicBlock_eq_fourier_rectangle (χ : Character) (V T : ℝ→ℂ)
    (D Y U : ℝ) (hU : 0<U) (hT : ∀ x : ℝ, 2≤x → T x=0)
    (s : ℂ) (j k : ℕ) :
    dyadicBlock χ V T D Y U s j k =
      ∑ J∈fourierSet U, ∑ K∈fourierSet U,
        pairCoefficient χ V T D Y U s (J,K)*
          DyadicTransfer.annularCutoff V ((J.absNorm : ℝ)/(2 : ℝ)^j)*
          DyadicTransfer.annularCutoff V ((K.absNorm : ℝ)/(2 : ℝ)^k) := by
  unfold dyadicBlock
  calc
    _ = ∑ p∈fourierSet U ×ˢ fourierSet U,
        pairCoefficient χ V T D Y U s p *
          DyadicTransfer.annularCutoff V ((p.1.absNorm : ℝ)/(2 : ℝ)^j) *
          DyadicTransfer.annularCutoff V ((p.2.absNorm : ℝ)/(2 : ℝ)^k) := by
      apply Finset.sum_subset (pairSet_subset_fourier U hU.le)
      intro p hp hn
      rw [pairCoefficient_support χ V T D Y U hU hT s p hn, zero_mul, zero_mul]
    _ = _ := Finset.sum_product _ _ _

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end OAIOriginalModule2045

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicProfiles
Source SHA256: a14db8091860078d6e4af081528e578df153cd74140c712dba99186c4ee5b278
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2046


namespace OAI

noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open CubicReflectionKernel
theorem section_deriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem compact_family_deriv_integrable (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ × ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def ratioProfile (V W : ℝ→ℂ) (R x : ℝ) : ℂ := V (R*x)*W x

def logFamily (V W : ℝ→ℂ) (p : ℝ×ℝ) (y : ℝ) : ℂ :=
  Real.exp (-p.2*y) • ratioProfile V W p.1 (Real.exp (-y))

lemma logFamily_smooth (V W : ℝ→ℂ) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily V W)) := by
  unfold Function.uncurry logFamily ratioProfile
  have he : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => Real.exp (-p.1.2*p.2)) := by fun_prop
  have hv : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => V (p.1.1*Real.exp (-p.2))) :=
    hV.comp (by fun_prop)
  have hw : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => W (Real.exp (-p.2))) :=
    hW.comp (by fun_prop)
  exact he.smul (hv.mul hw)

lemma ratioProfile_support (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (ratioProfile V W R)⊆Function.support W := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).2

lemma logFamily_support (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily V W p)⊆Icc (-Real.log b) (-Real.log a) := by
  exact mellinLogFamily_support (ratioProfile V W p.1) a b ha
    ((ratioProfile_support V W p.1).trans hW) p.2

theorem ratioProfile_mellin_bound (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (Rmax lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R∈Icc 0 Rmax, ∀ σ∈Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (ratioProfile V W R) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := compact_family_fourier_weighted_bound
    (logFamily V W) (logFamily_smooth V W hV hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support V W a b ha hWs)
    (Icc 0 Rmax ×ˢ Icc lo hi) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro R hR σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (mellinLogFamily (ratioProfile V W R) σ) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j * ((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily V W (R,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow, mul_assoc]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (R,σ) ⟨hR,hσ⟩ _) (by positivity)

lemma inverseProfile_eq_ratio (V W : ℝ→ℂ) (Dstar D : ℝ) :
    HeckeDetectorDyadicBridge.inverseProfile V W Dstar D=ratioProfile V W (D/Dstar) := by
  funext x
  unfold HeckeDetectorDyadicBridge.inverseProfile ratioProfile
  congr 2
  ring

theorem exists_profile_bounds (V W : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (lo hi : ℝ) :
    ∃ C : ℕ→ℝ, (∀ j, 0<C j) ∧
      (∀ j : ℕ, ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin W ((σ : ℂ)+t*Complex.I)‖≤C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0<Dstar → 0≤D → D≤4*Dstar →
        ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile V W Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤C j) := by
  choose Cp hCp hbP using fun j => compact_source_mellin_strip_decay W a b ha hWs hW lo hi j
  choose Ci hCi hbI using fun j => ratioProfile_mellin_bound V W hV hW a b ha hWs 4 lo hi j
  refine ⟨fun j => Cp j+Ci j,fun j => add_pos (hCp j) (hCi j),?_,?_⟩
  · intro j σ hσ t
    exact (hbP j σ hσ t).trans (le_add_of_nonneg_right (hCi j).le)
  · intro j Dstar D hDs hD hratio σ hσ t
    rw [inverseProfile_eq_ratio]
    exact (hbI j (D/Dstar) ⟨div_nonneg hD hDs.le,(div_le_iff₀ hDs).mpr hratio⟩ σ hσ t).trans
      (le_add_of_nonneg_left (hCp j).le)

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end OAIOriginalModule2046

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicCutoff
Source SHA256: a51edeb1cffd8f4ca88f35e5bacf69eda2738c722546fd2392fa705516d300a7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2047



namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

lemma exists_positive_annular : ∃ W : ℝ→ℂ,
    ContDiff ℝ ∞ W ∧ Function.support W⊆Icc (1/4) (9/4) ∧
    ∀ x : ℝ, 0≤x → W x=DyadicTransfer.annularCutoff cutoff x := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 3 (by norm_num)
  let W : ℝ→ℂ := fun x => g (4*x-5)*DyadicTransfer.annularCutoff cutoff x
  have hs : ContDiff ℝ ∞ (DyadicTransfer.annularCutoff cutoff) :=
    (cutoff.smooth ⊤).sub ((cutoff.smooth ⊤).comp (by fun_prop))
  refine ⟨W,(hgs.comp (by fun_prop)).mul hs,?_,?_⟩
  · intro x hx
    have hg : g (4*x-5)≠0 := (mul_ne_zero_iff.mp hx).1
    have hh := hgsupp (subset_tsupport g hg)
    constructor <;> norm_num at hh <;> linarith [hh.1,hh.2]
  · intro x hx
    by_cases hh : DyadicTransfer.annularCutoff cutoff x=0
    · simp [W,hh]
    have ha := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
      (by simpa using hh)
    norm_num at ha
    have hg : g (4*x-5)=1 := hgone _ (abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩)
    simp only [W,hg,one_mul]

def positiveAnnular : ℝ→ℂ := Classical.choose exists_positive_annular

lemma positiveAnnular_smooth : ContDiff ℝ ∞ positiveAnnular :=
  (Classical.choose_spec exists_positive_annular).1

lemma positiveAnnular_support : Function.support positiveAnnular⊆Icc (1/4) (9/4) :=
  (Classical.choose_spec exists_positive_annular).2.1

lemma positiveAnnular_eq (x : ℝ) (hx : 0≤x) :
    positiveAnnular x=DyadicTransfer.annularCutoff cutoff x :=
  (Classical.choose_spec exists_positive_annular).2.2 x hx

lemma positiveAnnular_zero (x : ℝ) (hx : 2≤x) : positiveAnnular x=0 := by
  rw [positiveAnnular_eq x (by linarith)]
  exact DyadicTransfer.annularCutoff_eq_zero_of_two_le cutoff cutoff_zero hx

theorem actual_profile_bounds :
    ∃ C : ℕ→ℝ, (∀ j, 0<C j) ∧
      (∀ j : ℕ, ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin positiveAnnular ((σ : ℂ)+t*Complex.I)‖≤C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0<Dstar → 0≤D → D≤4*Dstar →
        ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤C j) :=
  exists_profile_bounds cutoff positiveAnnular (cutoff.smooth ⊤) positiveAnnular_smooth
    (1/4) (9/4) (by norm_num) positiveAnnular_support (-2) 2

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end OAIOriginalModule2047

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicActual
Source SHA256: e3ba1b9c5a860f607d8c42476312a1551d72e99f72eb43ff79877b0742ea91dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2048


namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

lemma inverse_profile_smooth (Dstar D : ℝ) :
    ContDiff ℝ ∞ (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) := by
  unfold HeckeDetectorDyadicBridge.inverseProfile
  have hv : ContDiff ℝ ∞ (fun x : ℝ => cutoff (D*x/Dstar)) := (cutoff.smooth ⊤).comp (by fun_prop)
  exact hv.mul positiveAnnular_smooth

lemma inverse_profile_support (Dstar D : ℝ) :
    Function.support (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)⊆Icc (1/4) (9/4) := by
  intro x hx
  exact positiveAnnular_support ((mul_ne_zero_iff.mp hx).2)

theorem simultaneous_upper (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        51/100≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        ‖polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
        ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq‖^2≤
          C*(Z^d)^((2*a-1)*min m (1-m)+ε) := by
  obtain ⟨Cp,hCp,hplain,hinverse⟩ := actual_profile_bounds
  obtain ⟨n,C,hC,hbound⟩ := source_dyadic_bounds R dmax τ ε e κ η
    hR hdmax hτ hε he he' hκ hκ' hη hbudget Cp (fun k => (hCp k).le)
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hdmax' hT ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight
  have hU : 1≤Z^d := Real.one_le_rpow hZ hd
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (by linarith) _
  have hstrip : Icc (1-a-6*e-σ) (2-σ)⊆Icc (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hInv := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j true
    (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
    (1/4) (9/4) (by norm_num) (inverse_profile_support Dstar ((Z^d)^r))
    (inverse_profile_smooth Dstar ((Z^d)^r)) r σ freq hQ hr hrR hfreq hheight
    (fun x hx t => hinverse 2 Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
    (fun x hx t => hinverse (n+2) Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
  have hPlain := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j false
    positiveAnnular (1/4) (9/4) (by norm_num) positiveAnnular_support positiveAnnular_smooth
    m σ freq hQ hm hmR hfreq hheight
    (fun x hx t => hplain 2 x (hstrip hx) t)
    (fun x hx t => hplain (n+2) x (hstrip hx) t)
  exact ⟨hInv.1,hPlain.2⟩

end SevenEighths.HeckeDetectorDyadicActual

end

end OAI
end OAIOriginalModule2048

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFrequency
Source SHA256: 747c68ae236e9f8431be90600b8ba9649e62a2f54a57a7ca20a63fd331c6409f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2049





namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorDyadicBridge
local notation "O" => HeckeFamily.O

theorem dyadic_frequency_bound (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L)
    (hΩone : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      DyadicTransfer.annularCutoff cutoff x ≠ 0 →
      DyadicTransfer.annularCutoff cutoff y ≠ 0 → Ω (Real.log x+Real.log y)=1)
    (n : ℕ) :
    ∃ C₀ Cn : ℝ, 1 ≤ C₀ ∧ 0 ≤ Cn ∧ ∀ (U Dstar F : ℝ),
      1 ≤ U → 0 < Dstar → 0 < F → ∀ (χ : Character) (s : ℂ), 0 ≤ s.re →
      ∀ j k : ℕ, ∃ t : ℝ, ‖t‖ ≤ F ∧
        ‖dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k‖ ≤
          (67108864*U^42)*Cn/F^n + C₀*
            ‖phasePolynomial (expandedSet U)
                (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar ((2 : ℝ)^j) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
              phasePolynomial (expandedSet U)
                (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t‖ := by
  obtain ⟨C₀,hC₀,hb₀⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow 0
  obtain ⟨Cn,hCn,hbn⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow n
  refine ⟨1+C₀,Cn,by linarith,hCn,?_⟩
  intro U Dstar F hU hDstar hF χ s hs j k
  let D : ℝ := (2 : ℝ)^j
  let N : ℝ := (2 : ℝ)^k
  let a := inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s
  let b := plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) N s
  let x := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/D)
  let y := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/N)
  let g := logSource Ω cutoff cutoff hΩc hΩ (cutoff.smooth ⊤) (cutoff.smooth ⊤)
    (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
  have hUpos : 0 < U := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have heq : dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k =
      ∑ I ∈ expandedSet U, ∑ J ∈ expandedSet U, a I*b J*g (x I+y J) := by
    rw [dyadicBlock_eq_fourier_rectangle χ cutoff cutoff Dstar (U^20) (U^21)
      (by positivity) cutoff_zero s j k]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact actual_pair_profile χ Ω cutoff cutoff (DyadicTransfer.annularCutoff cutoff)
      (DyadicTransfer.annularCutoff cutoff) Dstar D N (U^20) (U^21) hD hN s I J
      (fourierSet_nonzero _ I hI) (fourierSet_nonzero _ J hJ)
      (hΩone _ _ (by positivity) (by positivity))
  obtain ⟨t,ht,hb⟩ := exists_bounded_frequency (expandedSet U) (expandedSet U) a b x y g F hF n
  refine ⟨t,ht,?_⟩
  rw [heq]
  have hg₀ : (∫ t : ℝ, ‖(𝓕 g) t‖) ≤ C₀ := by
    simpa only [pow_zero,one_mul] using hb₀ (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
      (by positivity) (by positivity) (by positivity)
  have hgn : (∫ t : ℝ, (1+‖t‖)^n*‖(𝓕 g) t‖) ≤ Cn :=
    hbn (2*D*N/Dstar) (D*N/U^20) (D*N/U^21) (by positivity) (by positivity) (by positivity)
  have hmass := coefficient_mass χ cutoff cutoff_norm_le U Dstar D N hU s hs
  apply hb.trans
  apply add_le_add
  · calc
      _ ≤ ((67108864*U^42)/F^n)*Cn := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmass (by positivity)
        · exact hgn
        · exact integral_nonneg (fun t => by positivity)
        · positivity
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (hg₀.trans (by linarith)) (norm_nonneg _)

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end OAIOriginalModule2049

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFrequencyTail
Source SHA256: 3b0c035a218d31b8aacba0106d2e9d8c726b895046c391494ec87c3311fa98dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2050


namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.HeckeDetectorFrequency

lemma logb_square_div_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun U : ℝ => (Real.logb 2 U)^2/U^a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have h' := h.const_mul ((Real.log 2)^2)⁻¹
  convert h' using 1
  · ext U
    rw [Real.rpow_two,Real.logb]
    ring
  · ring_nf

theorem exists_frequency_tail_order (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ C : ℝ, ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n) ≤ 1/4 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (43/τ)
  have he : 0 < τ*(n : ℝ)-42 := by
    have hh := (div_lt_iff₀ hτ).mp hn
    nlinarith
  refine ⟨n,?_⟩
  intro C
  have ht := (logb_square_div_rpow_tendsto (τ*(n : ℝ)-42) he).const_mul (625*67108864*C)
  have ht' : Tendsto
      (fun U : ℝ => (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n))
      atTop (𝓝 0) := by
    apply (show Tendsto (fun U : ℝ => (625*67108864*C)*
      ((Real.logb 2 U)^2/U^(τ*(n : ℝ)-42))) atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    rw [Real.rpow_sub hU,Real.rpow_mul_natCast hU.le,
      show (42 : ℝ)=((42 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    field_simp
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht').2 (1/4) (by norm_num))
  exact ⟨U₀,fun U hU hU1 => (hU₀ U hU).le⟩

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end OAIOriginalModule2050

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorCommonFrequency
Source SHA256: 31e30e6678eb204a8172f6a5b847eefce471a55a4a7ee2ba6cc7458b70925807
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2051



namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier HeckeDetectorLower
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorPartition
local notation "O" => HeckeFamily.O

def phaseProduct (χ : Character) (D U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ) : ℂ :=
  phasePolynomial (expandedSet U)
    (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) D ((2 : ℝ)^j) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
  phasePolynomial (expandedSet U)
    (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t

theorem exists_common_frequency_witness (R θ τ : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hτ : 0 < τ) :
    ∃ C U₀ : ℝ, 0 < C ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ χ : Character, χ.residue ≠ 1 → ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖ ≤ U^τ ∧
            1 ≤ C*(Real.logb 2 U)^2*‖phaseProduct χ D U ρ j k t‖ ∧
            (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨Ω,hΩc,hΩ,hwindow,hΩone⟩ := exists_product_log_cutoff
  obtain ⟨n,hn⟩ := exists_frequency_tail_order τ hτ
  have hL : 0 ≤ 2*Real.log 2+1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  obtain ⟨C₀,Cn,hC₀,hCn,hfreq⟩ := dyadic_frequency_bound Ω hΩc hΩ
    (2*Real.log 2+1) hL hwindow hΩone n
  obtain ⟨UF,hUF⟩ := hn Cn
  obtain ⟨UL,hUL⟩ := exists_dyadic_zero_witness R θ hR hθ hθ'
  refine ⟨2500*C₀,max 2 (max UF UL),by positivity,?_⟩
  intro U hU χ hχ D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  obtain ⟨j,hj,k,hk,hblock,hsupport⟩ :=
    hUL U ((le_max_right UF UL).trans ((le_max_right 2 _).trans hU))
      χ hχ cutoff cutoff cutoff_norm_le cutoff_norm_le cutoff_one cutoff_zero cutoff_one cutoff_zero
      D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨t,ht,hb⟩ := hfreq U D (U^τ) hU1 (by linarith) (by positivity) χ ρ (by linarith) j k
  have htail := hUF U ((le_max_left UF UL).trans ((le_max_right 2 _).trans hU)) hU1
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 625*(Real.logb 2 U)^2 by positivity)
  refine ⟨j,hj,k,hk,t,ht,?_,hsupport⟩
  change ‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖ at hb
  change (625*(Real.logb 2 U)^2)*‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (625*(Real.logb 2 U)^2)*((67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖) at hb'
  nlinarith

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end OAIOriginalModule2051

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorNormalized
Source SHA256: 3bad55d4115e7264eff96fba13f8b3dc28823efd5376c7951eb2417eb96bf37b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2052



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNormalized
open HeckeFamily HeckeDyadic HeckeDetectorFourier HeckeDetectorProfiles
open HeckeDetectorDyadicBridge HeckeDetectorDyadicProfiles HeckeDetectorFrequency

lemma plainCoefficient_positive (χ : Character) (D : ℝ) (hD : 0<D) (s : ℂ) :
    plainCoefficient χ positiveAnnular D s=
      plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) D s := by
  funext J
  unfold plainCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

lemma inverseCoefficient_positive (χ : Character) (Dstar D : ℝ) (hD : 0<D) (s : ℂ) :
    inverseCoefficient χ cutoff positiveAnnular Dstar D s=
      inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s := by
  funext J
  unfold inverseCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

theorem phaseProduct_norm (χ : Character) (Dstar U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    ‖phaseProduct χ Dstar U s j k t‖ =
      ((2 : ℝ)^j)^(1/2-s.re)*((2 : ℝ)^k)^(1/2-s.re)*
        (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
            ((2 : ℝ)^j) s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) s.re (2*Real.pi*t-s.im)‖) := by
  obtain ⟨hj,hk⟩ := scales_le_eight_terminal (U^21) j k hprod
  have hDj : 0<(2 : ℝ)^j := by positivity
  have hNk : 0<(2 : ℝ)^k := by positivity
  unfold phaseProduct
  rw [norm_mul, ← inverseCoefficient_positive χ Dstar ((2 : ℝ)^j) hDj s,
    ← plainCoefficient_positive χ ((2 : ℝ)^k) hNk s]
  exact pair_phase_norm χ cutoff positiveAnnular positiveAnnular Dstar ((2 : ℝ)^j) ((2 : ℝ)^k)
    hDj hNk s t (fourierSet (U^21)) (fourierSet (U^21))
    (fourierSet_nonzero (U^21)) (fourierSet_nonzero (U^21))
    (inverse_annular_covered (U^21) ((2 : ℝ)^j) Dstar hDj hj cutoff positiveAnnular positiveAnnular_zero)
    (annular_covered (U^21) ((2 : ℝ)^k) hNk hk positiveAnnular positiveAnnular_zero)

theorem exists_normalized_product (R θ τ : ℝ) (hR : 0≤R)
    (hθ : 0≤θ) (hθ' : θ<3/4) (hτ : 0<τ) :
    ∃ C U₀ : ℝ, 0<C ∧ ∀ U : ℝ, U₀≤U →
      ∀ χ : Character, χ.residue≠1 → ∀ Dstar : ℝ, 2≤Dstar → Dstar≤U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ)≤R*U → ∀ ρ : ℂ,
      (51/100 : ℝ)≤ρ.re → LFunction χ ρ=0 → |ρ.im|≤U^θ →
      ∃ j∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖≤U^τ ∧
            1≤C*(Real.logb 2 U)^2*((2 : ℝ)^j)^(1/2-ρ.re)*((2 : ℝ)^k)^(1/2-ρ.re)*
              (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
                  ((2 : ℝ)^j) ρ.re (2*Real.pi*t-ρ.im)‖ *
               ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) ρ.re (2*Real.pi*t-ρ.im)‖) ∧
            (2 : ℝ)^j<4*Dstar ∧ Dstar/8<(2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k<8*U^21 := by
  obtain ⟨C,U₀,hC,hbound⟩ := exists_common_frequency_witness R θ τ hR hθ hθ' hτ
  refine ⟨C,U₀,hC,?_⟩
  intro U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,t,ht,hb,hd,hn,hprod⟩ := hbound U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  refine ⟨j,hj,k,hk,t,ht,?_,hd,hn,hprod⟩
  rw [phaseProduct_norm χ Dstar U ρ j k t hprod] at hb
  convert hb using 1; ring

end SevenEighths.HeckeDetectorNormalized

end

end OAI
end OAIOriginalModule2052

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorSaturation
Source SHA256: 483523e4b40337a39c66bbef06a8e2bc719dd5af4e4b533186010ea2ef75a8de
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2053



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSaturation
open HeckeDetectorFrequency

lemma logarithmic_cost_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ U : ℝ in atTop, (C*(Real.logb 2 U)^2)^2≤U^ε := by
  have ht := (logb_square_div_rpow_tendsto (ε/2) (by linarith)).pow 2
  have ht' := ht.const_mul (C^2)
  have hbound : ∀ᶠ U : ℝ in atTop,
      C^2*((Real.logb 2 U)^2/U^(ε/2))^2≤1 := by
    have hh : Tendsto (fun U : ℝ => C^2*((Real.logb 2 U)^2/U^(ε/2))^2)
        atTop (𝓝 0) := by simpa using ht'
    exact (tendsto_order.mp hh).2 1 (by norm_num) |>.mono (fun _ h => h.le)
  filter_upwards [hbound,eventually_gt_atTop (0 : ℝ)] with U hb hU
  have he : (U^(ε/2))^2=U^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hU.le]
    congr 1
    norm_num
  rw [div_pow, he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU ε)).mp
    (show C^2*((Real.logb 2 U)^2)^2/U^ε≤1 by simpa only [mul_div_assoc] using hb)
  simpa only [one_mul,mul_one,mul_pow] using hh

lemma normalized_product_lower (U r m σ a ε K A B : ℝ)
    (hU : 1<U) (hr : 0≤r) (hm : 0≤m) (hσ : a≤σ)
    (_hK : 0≤K) (_hA : 0≤A) (_hB : 0≤B)
    (hcost : K^2≤U^ε)
    (hprod : 1≤K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B)) :
    U^((2*a-1)*(r+m)-ε)≤A^2*B^2 := by
  have hUp : 0<U := by linarith
  have hcentral : (U^r)^(1/2-σ)*(U^m)^(1/2-σ)=U^((1/2-σ)*(r+m)) := by
    rw [← Real.rpow_mul hUp.le,← Real.rpow_mul hUp.le,← Real.rpow_add hUp]
    congr 1
    ring
  have hp : 1≤K*U^((1/2-σ)*(r+m))*(A*B) := by
    calc
      1 ≤ K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B) := hprod
      _ = _ := by rw [←hcentral]; ring
  have hsq : 1≤(K*U^((1/2-σ)*(r+m))*(A*B))^2 := by nlinarith
  have he : (U^((1/2-σ)*(r+m)))^2=U^((1-2*σ)*(r+m)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,he,mul_pow] at hsq
  let q := (2*a-1)*(r+m)-ε
  let L := K^2*U^((1-2*σ)*(r+m))
  have hLq : L*U^q≤1 := by
    calc
      _ ≤ U^ε*U^((1-2*σ)*(r+m))*U^q := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
        exact mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hUp.le _)
      _ = U^(ε+(1-2*σ)*(r+m)+q) := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]
      _ ≤ U^0 := Real.rpow_le_rpow_of_exponent_le hU.le (by
        dsimp [q]
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (add_nonneg hr hm)])
      _ = 1 := Real.rpow_zero _
  calc
    U^q = U^q*1 := by ring
    _ ≤ U^q*(L*(A^2*B^2)) := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hUp.le _)
    _ = (L*U^q)*(A^2*B^2) := by ring
    _ ≤ 1*(A^2*B^2) := mul_le_mul_of_nonneg_right hLq (by positivity)
    _ = _ := by ring

open HeckeFamily HeckeDyadic HeckeDetectorDyadicActual HeckeDetectorDyadicProfiles HeckeDetectorProfiles

theorem actual_saturation (R dmax τ ε e κ η Clower : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε/2) (hClower : 0≤Clower) :
    ∃ U₀ : ℝ, ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      U₀≤Z^d → 1<Z^d →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        a≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        let M := polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq
        let S := polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq
        1≤Clower*(Real.logb 2 (Z^d))^2*((Z^d)^r)^(1/2-σ)*((Z^d)^m)^(1/2-σ)*(‖M‖*‖S‖) →
        m≤1/2+75*ε ∧ (Z^d)^((2*a-1)*r-2*ε)≤‖M‖^2 ∧
          (Z^d)^((2*a-1)*m-2*ε)≤‖S‖^2 := by
  obtain ⟨Cu,hCu,hupper⟩ := simultaneous_upper R dmax τ (ε/2) e κ η
    hR hdmax hτ (by linarith) he he' hκ hκ' hη hbudget
  have hev := (logarithmic_cost_eventually Clower ε hε).and
    (constant_absorbed_eventually Cu (ε/2) (by linarith))
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨U₀,?_⟩
  intro Z d hZ hd hd' hT hlarge hU ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight M S hprod
  have hσlo : 51/100≤σ := ha.trans hσ
  obtain ⟨hcost,hconst⟩ := hU₀ (Z^d) hlarge
  obtain ⟨hMu,hSu⟩ := hupper Z d hZ hd hd' hT χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσlo hσ' hfreq hheight
  have hp := normalized_product_lower (Z^d) r m σ a ε
    (Clower*(Real.logb 2 (Z^d))^2) ‖M‖ ‖S‖ hU hr hm hσ
    (mul_nonneg hClower (sq_nonneg _)) (norm_nonneg _) (norm_nonneg _) hcost hprod
  have hbound (x : ℝ) : Cu*(Z^d)^(x+ε/2)≤(Z^d)^(x+ε) := by
    calc
      _ ≤ (Z^d)^(ε/2)*(Z^d)^(x+ε/2) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z^d)]; congr 1; ring
  exact Detector.simultaneous_saturation hU (by linarith) hε.le (sq_nonneg _) (sq_nonneg _)
    hp (hMu.trans (hbound _)) (hSu.trans (hbound _))

end SevenEighths.HeckeDetectorSaturation

end

end OAI
end OAIOriginalModule2053

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
Source SHA256: d95f006e9e029c6be4fbf46aa7775d41c94e2f6f51ff36e203f871834c8a2df0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2054


namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_power_allowance (C p dmin α : ℝ) (hα : 0≤α) (hgap : p<dmin*α) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → C*Z^p≤(Z^d)^α := by
  have hh := constant_absorbed_eventually C (dmin*α-p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd
  have hZp : 0<Z := by linarith
  calc
    _ ≤ Z^(dmin*α-p)*Z^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*α) := by rw [←Real.rpow_add hZp]; congr 1; ring
    _ ≤ Z^(d*α) := Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hα)
    _ = _ := Real.rpow_mul hZp.le _ _

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

lemma uniform_zero_height (dmin τ : ℝ) (I : ℕ) (hgap : τ<dmin/2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3*i : ℕ)*Z^τ≤(Z^d)^(1/2 : ℝ) := by
  have hh := uniform_power_allowance (3*I : ℕ) τ dmin (1/2) (by norm_num) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hn : (3*i : ℕ)≤3*I := by omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.rpow_nonneg (by linarith) _)).trans (hZ d hd)

lemma uniform_height_budget (dmin τ η : ℝ) (I : ℕ) (hτ : 0≤τ)
    (hη : 0≤η) (hgap : 4*τ<dmin*η) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η := by
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^4*16) (4*τ) dmin η hη hgap
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hT : 1≤Z^τ := Real.one_le_rpow hZ1 hτ
  have hp : (1+Z^τ)^4≤16*Z^(4*τ) := by
    calc
      _ ≤ (2*Z^τ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        have he : (Z^τ)^4=Z^(4*τ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤Z)]
          congr 1
          norm_num
          ring
        rw [mul_pow,he]
        norm_num
  calc
    _ ≤ (3*(I : ℝ)+5)^4*(1+Z^τ)^4 := indexed_height_bound i I hi (Z^τ) (by linarith)
    _ ≤ (3*(I : ℝ)+5)^4*(16*Z^(4*τ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((3*(I : ℝ)+5)^4*16)*Z^(4*τ) := by ring
    _ ≤ _ := hZ d hd

lemma uniform_fourier_allowance (dmax τ : ℝ) (hdmax : 0<dmax) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, 0≤d → d≤dmax →
      2*Real.pi*(Z^d)^(τ/(2*dmax))≤Z^τ/2 := by
  have hh := constant_absorbed_eventually (4*Real.pi) (τ/2) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd hd'
  have hZp : 0<Z := by linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^(τ/2) := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hm := mul_le_mul_of_nonneg_right hd' (show 0≤τ/(2*dmax) by positivity)
    have he : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rwa [he] at hm
  have he : Z^(τ/2)*Z^(τ/2)=Z^τ := by rw [←Real.rpow_add hZp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le (τ/2))
  rw [he] at hh
  have hpi := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  nlinarith

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end OAIOriginalModule2054

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicLengths
Source SHA256: a6983512af1c788015607a605ee25599eef56de27b32ca8bac8055c53c9230bc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2055


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDyadicGeometry

lemma log_scale_bounds (U x : ℝ) (hU : 8≤U) (hx : 1≤x) (hxU : x≤8*U^21) :
    0≤Real.logb U x ∧ Real.logb U x≤22 ∧ U^(Real.logb U x)=x := by
  have hUp : 0<U := by linarith
  have hU1 : 1<U := by linarith
  have hxp : 0<x := by linarith
  have he := Real.rpow_logb hUp hU1.ne' hxp
  refine ⟨Real.logb_nonneg hU1 hx,?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hU1).mp
  rw [he,show (22 : ℝ)=((22 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  calc
    x ≤ 8*U^21 := hxU
    _ ≤ U*U^21 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = U^22 := by ring

lemma dyadic_scale_bounds (U : ℝ) (hU : 8≤U) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    0≤Real.logb U ((2 : ℝ)^j) ∧ Real.logb U ((2 : ℝ)^j)≤22 ∧
      0≤Real.logb U ((2 : ℝ)^k) ∧ Real.logb U ((2 : ℝ)^k)≤22 ∧
      U^(Real.logb U ((2 : ℝ)^j))=(2 : ℝ)^j ∧
      U^(Real.logb U ((2 : ℝ)^k))=(2 : ℝ)^k := by
  obtain ⟨hj,hk⟩ := HeckeDetectorDyadicBridge.scales_le_eight_terminal (U^21) j k hprod
  obtain ⟨hr,hr',he⟩ := log_scale_bounds U ((2 : ℝ)^j) hU (one_le_pow₀ (by norm_num)) hj
  obtain ⟨hm,hm',he'⟩ := log_scale_bounds U ((2 : ℝ)^k) hU (one_le_pow₀ (by norm_num)) hk
  exact ⟨hr,hr',hm,hm',he,he'⟩

lemma support_exponents (U t r m ε : ℝ) (hU : 1<U) (hcost : 8≤U^ε)
    (hleft : U^r<4*U^t) (hright : U^t/8<U^r*U^m) :
    r≤t+ε ∧ t-ε≤r+m := by
  have hUp : 0<U := by linarith
  constructor
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^r ≤ 4*U^t := hleft.le
      _ ≤ U^ε*U^t := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hUp.le _)
      _ = U^(t+ε) := by rw [←Real.rpow_add hUp]; congr 1; ring
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^(t-ε) = U^t/U^ε := Real.rpow_sub hUp _ _
      _ ≤ U^t/8 := div_le_div_of_nonneg_left (Real.rpow_nonneg hUp.le _) (by norm_num) hcost
      _ ≤ U^r*U^m := hright.le
      _ = U^(r+m) := (Real.rpow_add hUp _ _).symm

lemma truncation_scale (U t : ℝ) (hU : 2≤U) (ht : 1≤t) (ht' : t≤3/2) :
    2≤U^t ∧ U^t≤U^(3/2 : ℝ) := by
  have hU1 : 1≤U := by linarith
  constructor
  · apply hU.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1 ht
  · exact Real.rpow_le_rpow_of_exponent_le hU1 ht'

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end OAIOriginalModule2055

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneous
Source SHA256: 047c424f89d6daba8327d96fd6882ef2d92a1ae137b147bd71eff11f04a1beab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2056



namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneous
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneous

end

end OAI
end OAIOriginalModule2056

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount
Source SHA256: e9a384fe36df1591d34836022a452c23d79cc6918fbaa45363403b46efde5634
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2057


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

theorem inverse_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (D : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ r q z εw εp εm C : ℝ) (hU : 0<U)
    (hM : ∀ u∈rows, U^(δ*r-εw)≤‖polynomial (χ u) true W D (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-δ*r-2*q*z+εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*r-εw)+(2*q*z-εp))≤‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,norm_mul,mul_pow]
    exact mul_le_mul (hM u hu) (hP u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _)
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem plain_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (N : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ m q z εw εp εm C : ℝ) (hU : 0<U)
    (hS : ∀ u∈rows, U^(δ*m-εw)≤‖polynomial (χ u) false W N (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) false W N (σ u) (freq u)*
        polynomial (χ u) false W N (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-2*δ*m-2*q*z+2*εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*m-εw)+(δ*m-εw)+(2*q*z-εp))≤
        ‖polynomial (χ u) false W N (σ u) (freq u)*
          polynomial (χ u) false W N (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,Real.rpow_add hU,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _))
      (hP u hu) (Real.rpow_nonneg hU.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem classified_card_bound {α Label : Type*} [Fintype Label]
    (rows : Finset α) (presentation : α→Label) (left right : α→ℕ)
    (B : ℕ) (hleft : ∀ u∈rows, left u<B) (hright : ∀ u∈rows, right u<B)
    (K : ℝ)
    (hfiber : ∀ p : Label, ∀ j∈Finset.range B, ∀ k∈Finset.range B,
      ((rows.filter (fun u => presentation u=p ∧ left u=j ∧ right u=k)).card : ℝ)≤K) :
    (rows.card : ℝ)≤(Fintype.card Label : ℝ)*(B : ℝ)^2*K := by
  let labels : Finset (Label×ℕ×ℕ) := Finset.univ ×ˢ (Finset.range B ×ˢ Finset.range B)
  let label : α→Label×ℕ×ℕ := fun u => (presentation u,left u,right u)
  have hmaps : (rows : Set α).MapsTo label labels := by
    intro u hu
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hleft u hu),Finset.mem_range.mpr (hright u hu)⟩⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have he' : (rows.card : ℝ)=∑ l∈labels,
      ((rows.filter (fun u => label u=l)).card : ℝ) := by exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ l∈labels, K := by
      apply Finset.sum_le_sum
      intro l hl
      rcases l with ⟨p,j,k⟩
      obtain ⟨hp,hjk⟩ := Finset.mem_product.mp hl
      obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
      have hh := hfiber p j hj k hk
      simpa only [label,Prod.mk.injEq] using hh
    _ = _ := by simp [labels,Finset.card_product,pow_two,mul_assoc]

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end OAIOriginalModule2057

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing
Source SHA256: 1bc53cfbcc67251c35614694e55336e0e3ec3d872c7668ed7585a8ccff6864a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2058


namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

def denominator (x : ℝ) : ℝ := 3-17*x/9

def primeWeight (x : ℝ) : ℝ := (2-8*x/9)*(1-x)

def crossing (x t : ℝ) : ℝ := ((2-8*x/9)*t-5*x/9)/denominator x

def inverseExponent (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)

def plainExponent (δ x t r : ℝ) : ℝ := 1-δ*(4*x/9+(2-8*x/9)*(t-r))

def shortExponent (δ x t : ℝ) : ℝ := 1-δ+δ*primeWeight x/denominator x*(3/2-t)

def longExponent (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)

lemma denominator_lower {x : ℝ} (hx : x≤1/2) : 37/18≤denominator x := by
  unfold denominator
  linarith

theorem crossing_bounds {x t : ℝ} (hx : 0≤x) (hx' : x≤1/2)
    (ht : 1≤t) (ht' : t≤3/2) :
    23/37≤crossing x t ∧ crossing x t≤1 ∧
      1/3≤t-crossing x t ∧ t-crossing x t≤1/2 := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤2-8*x/9 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0≤1-x := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t-crossing x t=((1-x)*t+5*x/9)/denominator x := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

theorem crossing_average (δ x t r : ℝ) (hd : denominator x≠0) :
    ((2-8*x/9)*inverseExponent δ x r+(1-x)*plainExponent δ x t r)/denominator x =
      shortExponent δ x t := by
  unfold inverseExponent plainExponent shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma inverse_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    inverseExponent δ x (crossing x t)=shortExponent δ x t := by
  unfold inverseExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma plain_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    plainExponent δ x t (crossing x t)=shortExponent δ x t := by
  unfold plainExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {δ x t r : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2) :
    (r≤crossing x t → plainExponent δ x t r≤shortExponent δ x t) ∧
      (crossing x t≤r → inverseExponent δ x r≤shortExponent δ x t) := by
  have hd : denominator x≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hx'))
  constructor
  · intro hr
    rw [←plain_at_crossing δ x t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤2-8*x/9 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [←inverse_at_crossing δ x t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1-x by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

theorem strict_inverse_capacity {r ν : ℝ} (hr : 23/37≤r) (hν : 0<ν) :
    r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 ∧
      (1-r)/2≤7/37 ∧ 9/37≤3-2*r-8*((1-r)/2-ν) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma plain_capacity_bound {m κ : ℝ} (hm : 1/3≤m) (hm' : m≤1/2) (hκ : 3/4≤κ) :
    0≤(1-2*m)/(6*κ) ∧ (1-2*m)/(6*κ)≤2/27 := by
  have hkp : 0<6*κ := by linarith
  constructor
  · exact div_nonneg (by linarith) hkp.le
  · apply (div_le_iff₀ hkp).mpr
    nlinarith

lemma prime_supply_margin : (8/39 : ℝ)-7/37=23/1443 := by norm_num

lemma short_ge_base {δ x t : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2)
    (ht : t≤3/2) : 1-δ≤shortExponent δ x t := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤primeWeight x := mul_nonneg (by linarith) (by linarith)
  unfold shortExponent
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (mul_nonneg hδ hp) hd.le) (by linarith))

lemma inverse_capacity_exponent (δ x r : ℝ) :
    1-δ*r-2*(δ*x)*((1-r)/2)=inverseExponent δ x r := by unfold inverseExponent; ring

theorem capacity_loss {q m Δ γ : ℝ} (_hq : 0≤q) (hq' : q≤1/2)
    (hm : 1/3-γ≤m) (hm' : m≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hγ : 0≤γ) :
    2*q*(1-2*m)*(2/9-1/(9/2+12*Δ))≤Δ/4+2*γ := by
  have hd : 0<9/2+12*Δ := by linarith
  have hden : (16 : ℝ)≤(9/2)*(9/2+12*Δ) := by nlinarith
  have hqmul : q*(1-2*m)≤(1/2)*(1/3+2*γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0≤24*Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔ' (show 0≤24*γ by positivity)
  have he : 2*q*(1-2*m)*(2/9-1/(9/2+12*Δ)) =
      24*q*(1-2*m)*Δ/((9/2)*(9/2+12*Δ)) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ (show 0<(9/2)*(9/2+12*Δ) by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_left hden (show 0≤Δ/4+2*γ by positivity)
  nlinarith

theorem plain_capacity_comparison {δ x Δ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤1) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hm : 1/3-γ≤m) (hm' : m≤1/2)
    (hγ : 0≤γ) (hlength : t-r-γ≤m) :
    1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)≤plainExponent δ x t r+Δ/4+4*γ := by
  have hq : 0≤δ*x := mul_nonneg hδ hx
  have hq' : δ*x≤1/2 := (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss hq hq' hm hm' hΔ hΔ' hγ
  have hc : 0≤δ*(2-8*x/9) := mul_nonneg hδ (by linarith)
  have hc' : δ*(2-8*x/9)≤2 := by
    have hh := mul_le_mul_of_nonneg_right hδ' (show 0≤2-8*x/9 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  have hid : (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9))-plainExponent δ x t r =
      δ*(2-8*x/9)*(t-r-m) := by unfold plainExponent; ring
  have hid' : 1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ) =
      (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9)) +
      2*(δ*x)*(1-2*m)*(2/9-1/(9/2+12*Δ)) := by ring
  rw [hid']
  linarith

lemma inverse_zero_capacity {δ r ν : ℝ} (hδ : 0≤δ)
    (hcap : (1-r)/2≤ν) : 1-δ*r≤1-δ+2*δ*ν := by
  have hh := mul_le_mul_of_nonneg_left hcap hδ
  nlinarith

lemma plain_zero_capacity {δ m κ ν : ℝ} (hδ : 0≤δ) (hκ : 0<κ)
    (hκ' : κ≤1) (hν : 0≤ν) (hcap : (1-2*m)/(6*κ)≤ν) :
    1-2*δ*m≤1-δ+6*δ*ν := by
  have hh := (div_le_iff₀ (show 0<6*κ by positivity)).mp hcap
  have hk := mul_le_mul_of_nonneg_right hκ' hν
  have hm : 1-2*m≤6*ν := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hm hδ
  nlinarith

lemma long_count_bound {δ r t γ : ℝ} (hδ : δ≤5/6) (_hγ : 0≤γ)
    (hr : r≤t+γ) :
    1-5/6+(5/6-δ)*r≤longExponent δ t+(5/6-δ)*γ := by
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤5/6-δ by linarith)
  unfold longExponent
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end OAIOriginalModule2058

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountOptimization
Source SHA256: db2977184a11c1ee832e6805fffa897c34d8910cd798a31123c9b5dacf5f0c20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2059



namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

theorem count_bound_of_source_branches (B C U δ x Δ t r m ε ν γ : ℝ)
    (hC : 0≤C) (hU : 1≤U) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (ht : 1≤t) (ht' : t≤3/2) (hν : 0≤ν) (hγ : 0≤γ)
    (hleft : t-r-γ≤m) (hright : r≤t+γ)
    (hI0 : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B≤C*U^(1-2*δ*m+ε))
    (hI : 23/37≤r → r<1 → ν<(1-r)/2 → B≤C*U^(inverseExponent δ x r+ε))
    (hP : r≤crossing x t → m<1/2 → ν<(1-2*m)/(9/2+12*Δ) →
      B≤C*U^(1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+ε)) :
    B≤C*U^(max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ) := by
  let target := max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ
  have hshort : shortExponent δ x t≤max (shortExponent δ x t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t≤max (shortExponent δ x t) (longExponent δ t) := le_max_right _ _
  have hbase := short_ge_base hδ hx hx' ht'
  have hcross := crossing_bounds hx hx' ht ht'
  have hchoose := selected_short_bound (t:=t) (r:=r) hδ hx hx'
  have promote (p : ℝ) (hp : B≤C*U^p) (hpt : p≤target) : B≤C*U^target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1≤r
  · have hmax : max 1 ((1+5*r)/6)=(1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5/6-δ)*γ≤γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r<1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6)=1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing x t≤r
  · by_cases hcap : (1-r)/2≤ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r≤crossing x t := (lt_of_not_ge hrc).le
  by_cases hm : 1/2≤m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m<1/2 := lt_of_not_ge hm
  by_cases hcap : (1-2*m)/(9/2+12*Δ)≤ν
  · apply promote _ hP0
    have hk0 : 0<3/4+2*Δ := by linarith
    have hk1 : 3/4+2*Δ≤1 := by linarith
    have hz := plain_zero_capacity hδ hk0 hk1 hν
      (show (1-2*m)/(6*(3/4+2*Δ))≤ν by convert hcap using 1; ring)
    have hv : 6*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1/3-γ≤m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ≤1 by linarith) hx hx' hΔ hΔ'
      hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end OAIOriginalModule2059

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget
Source SHA256: 10491ef291665f80ff61771bce01c4aa5fed4fe168b92de67427d683c6fc77a7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2060


namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBranchBudget
open HeckeDetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x Δ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)=
      2*(δ*x)*(1-2*m)/(9/2+12*Δ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (Δ x t r m ε ν : ℝ)
    (hΔ : 0≤Δ) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤crossing x t) (hleft : t-r-ε≤m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(9/2+12*Δ)) :
    0≤(1-2*m)/(9/2+12*Δ)-ν ∧ (1-2*m)/(9/2+12*Δ)-ν≤7/37 ∧
      2*m+6*(3/4+2*Δ)*((1-2*m)/(9/2+12*Δ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 ht ht1
  have hm : 1/4≤m := by linarith [hcross.2.2.1]
  have hd : 0<9/2+12*Δ := by linarith
  have hc : (1-2*m)/(9/2+12*Δ)≤7/37 := (div_le_iff₀ hd).mpr (by nlinarith)
