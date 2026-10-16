    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 1)) hm
  have h0 : Measurable (fun s : ℂ => if s=0 then LFunction χ 0 else
      if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (0:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 0)) h1
  convert h0 using 1
  funext s
  split_ifs with hs0 hs1
  · subst s; rfl
  · subst s; rfl
  · exact perturbed_LFunction_eq_pole_quotient χ hs0 hs1

lemma perturbed_arithmetic_onLines_measurable_all {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := perturbed_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := perturbed_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (perturbed_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (perturbed_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => (υ:ℂ)+p.2*I))
  have hZL := (perturbed_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => 6*((ξ:ℂ)+p.1.2*I)))
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma perturbed_joinWGap_pos (axis : SliceAxis) (υ : ℝ) (hυ : axis≠.w→υ≠1) : 0< joinWGap axis υ := by
  unfold joinWGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hυ h))
lemma perturbed_joinZGap_pos (axis : SliceAxis) (ξ : ℝ) (hξ : axis≠.z→6*ξ≠1) : 0< joinZGap axis ξ := by
  unfold joinZGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hξ h))

lemma perturbed_slice_w_gap (axis : SliceAxis) (R υ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinWGap axis υ≤‖((υ:ℂ)+(sliceMap axis R q).2*I)-1‖ := by
  cases axis
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using hR.trans (pole_distance_horizontal 1 υ R)
lemma perturbed_slice_z_gap (axis : SliceAxis) (R ξ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinZGap axis ξ≤‖6*((ξ:ℂ)+(sliceMap axis R q).1.2*I)-1‖ := by
  cases axis
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.1*I)-1)
  · have hi : 6*|R|≤‖6*((ξ:ℂ)+R*I)-1‖ := by
      simpa [abs_mul] using Complex.abs_im_le_norm (6*((ξ:ℂ)+R*I)-1)
    simpa [joinZGap,sliceMap] using (by linarith : (6:ℝ)≤6*|R|).trans hi
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.2*I)-1)

theorem perturbed_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := perturbed_arithmetic_onLines_measurable_all η S hS.prime J T b X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ×ℝ) := perturbed_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C
    hX hY hZ ha hσ hξ hcw hυ (joinWGap axis υ) (joinZGap axis ξ)
    (perturbed_joinWGap_pos axis υ hυ1) (perturbed_joinZGap_pos axis ξ hξ1) hC hR (sliceMap axis R q)
    (perturbed_slice_w_gap axis R υ hR0 q) (perturbed_slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ))
    (perturbed_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
      (perturbed_joinWGap_pos axis υ hυ1).le (perturbed_joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ×ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ:ℂ)+(sliceMap axis R q).1.1*I) ((υ:ℂ)+(sliceMap axis R q).2*I)
      ((ξ:ℂ)+(sliceMap axis R q).1.2*I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines,perturbed_arithmetic_profile_eq_source] using hh

theorem perturbed_residue_uniform_moments {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ residueAmplitude S J T b X Z a ξ C*K := by
  obtain ⟨K,hK,hk⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5+N) 0
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0≤ A := perturbed_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ×ℝ → ℂ := fun q => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := perturbed_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) := hm.aestronglyMeasurable.mul
    (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1 (by linarith)).comp
      (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := perturbed_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hmom := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
  have hdom (q : ℝ×ℝ) : jointHeight q.1 q.2 0^N*‖F q‖≤
      A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ jointHeight q.1 q.2 0^N * ((A*jointHeight q.1 q.2 0^5)*
          ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _))
          (pow_nonneg (jointHeight_pos _ _ _).le _)
      _ = _ := by rw [pow_add]; ring
  have hi : Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) := by
    apply (hmom.1.const_mul A).mono'
    · exact (by unfold jointHeight; fun_prop : Continuous (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)).aestronglyMeasurable.mul hFc.norm
    · apply Eventually.of_forall
      intro q
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)),sliceMap] using hdom q
  have hn : (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ A*K := by
    calc
      _ ≤ ∫q : ℝ×ℝ,A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖)
          ∂volume.prod volume := integral_mono hi (hmom.1.const_mul A) hdom
      _ = A*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖
          ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A*K := mul_le_mul_of_nonneg_left (by simpa only [sliceMap,pow_zero,div_one] using hmom.2) hA
  have heq : F =ᵐ[volume.prod volume] (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    dsimp only [F,onLines,sliceMap]
    simp only [ofReal_one,ofReal_zero,zero_mul,add_zero]
    rw [perturbed_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      perturbed_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
  have hweight : (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)=ᵐ[volume.prod volume]
      (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N) := Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

lemma perturbed_residueOutside_measurable (R : ℝ) : MeasurableSet (residueOutside R) := by
  unfold residueOutside
  measurability

theorem perturbed_residue_uniform_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,0≤ R→
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤
        residueAmplitude S J T b X Z a ξ C*K/(1+R)^N := by
  obtain ⟨K,hK,hk⟩ := perturbed_residue_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hi,hb⟩ := hk η S hS J T b hT X Y Z hX hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  let F := fun q : ℝ×ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
      (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
  have hF := perturbed_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ×ℝ) (hq : q∈residueOutside R) :
      ‖F q‖≤ jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N := by
    have hh : 1+R≤ jointHeight q.1 q.2 0 := by
      rcases hq with h|h <;> unfold jointHeight <;> simp only [abs_zero,add_zero] <;>
        linarith [abs_nonneg q.1,abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0≤1+R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+R) N)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤_
  calc
    _ ≤ ∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N
        ∂volume.prod volume := setIntegral_mono_on hF.norm.integrableOn (hi.div_const _).integrableOn
          (perturbed_residueOutside_measurable R) hdom
    _ = (∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := integral_div _ _
    _ ≤ (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi (Eventually.of_forall (fun q =>
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

lemma perturbed_continued_high_slice_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ ξ υ : ℝ)
    (axis : SliceAxis) (R : ℝ) (hR : R≠0) :
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) := by
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,(sliceMap axis R q).1.1≠0 := by
    cases axis
    · exact Eventually.of_forall (fun _ => hR)
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠0 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠1 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  dsimp only
  rw [perturbed_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma perturbed_source_axis_gaps {e : ℝ} (he : 0< e) :
    |(19/20:ℝ)-1|=1/20 ∧ |6*(1/6+e)-1|=6*e ∧ |6*(33/200:ℝ)-1|=1/100 := by
  constructor
  · norm_num
  constructor
  · rw [show 6*(1/6+e)-1=6*e by ring,abs_of_pos (by positivity)]
  · norm_num

theorem perturbed_raw_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((σ:ℂ)+p.1.1*I) (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I))
        (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  obtain ⟨K,hK,hk⟩ := perturbed_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs Bz cw ha hβ hcw N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := perturbed_continued_high_slice_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule19
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalContours -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalTransport -/
section LocalModule20

set_option linter.unusedVariables false

/-! Actual ordered principal transport at the perturbed endpoint. The source
functions and positive Gaussian/tail measures are unchanged. Domain inputs
are supplied by freshly proved Euler and contour bounds; this file assumes
no improved transport theorem or physical high bound.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours ProbePrincipalTransport
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma perturbed_gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hb (t : ℝ) : gaussianMoment n t ≤ (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _ ≤ ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma perturbed_gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  simp [gaussianMoment,height]

lemma perturbed_gaussianMoment_tendsto_bot (n : ℕ) : Tendsto (gaussianMoment n) atBot (𝓝 0) := by
  have h := (perturbed_gaussianMoment_tendsto n).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,perturbed_gaussianMoment_even] using h

lemma perturbed_shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma perturbed_shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (perturbed_gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma perturbed_shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert perturbed_shifted_gaussian_top n (-v) using 1
  funext t
  rw [←perturbed_gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem perturbed_verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a≤ c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a≤ s.re ∧ s.re≤ c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖≤ A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((perturbed_shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖≤ A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((perturbed_shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((perturbed_shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem perturbed_principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0≤ A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖≤ A*jointEnvelope 8 p := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0≤ A := perturbed_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [hξ.1],hξ.2⟩
  have hw : (2:ℝ)≤‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1≤‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0≤6*ξ-1 := by linarith [hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [hξ.1]) h
  have hb := perturbed_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←perturbed_arithmetic_profile_eq_source,norm_mul]
  calc
    _ ≤ (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _ ≤ A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem perturbed_continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := perturbed_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := perturbed_continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ)≤ξ by linarith)) ha hβ
    (c:=3)
  apply perturbed_verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma perturbed_continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : 34999/40000≤ s.re) (hw : 9/10≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25< z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25< z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0< z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (perturbed_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma perturbed_continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : 34999/40000≤ s.re) (hw : 9/10≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6< z.re} := by
  have hK := perturbed_continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)< z.re; change (1/6:ℝ)< z.re at hz; linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem perturbed_continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := perturbed_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := perturbed_continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply perturbed_verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)< z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _ ≤ A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _ ≤ A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma perturbed_verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma perturbed_verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma perturbed_verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem perturbed_continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := perturbed_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hi3 := perturbed_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [perturbed_verticalIntegral_triple_reverse F a ξ 3 hiA,perturbed_verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply perturbed_verticalIntegral_congr_line
  intro u
  apply perturbed_verticalIntegral_congr_line
  intro v
  exact perturbed_continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem perturbed_continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := perturbed_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := perturbed_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply perturbed_verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [perturbed_verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    perturbed_verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply perturbed_verticalIntegral_congr_line
  intro u
  exact perturbed_continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma perturbed_continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [perturbed_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem perturbed_source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  dsimp only
  rw [←perturbed_continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←perturbed_continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := perturbed_continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := perturbed_continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem perturbed_source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  exact (perturbed_source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (perturbed_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

lemma perturbed_continued_principal_measurable (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    {ι : Type*} (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (x w z : ℝ×(ℝ×ℝ) → ℂ) (hx : Continuous x) (hw : Continuous w) (hz : Continuous z)
    (hβ : ∀p,HeckeZeroSupremum.beta<(x p).re) (hz0 : ∀p,0<(z p).re) :
    Measurable (fun p => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z (x p) (w p) (z p)*
      LFunction (fixedSourcePrincipal S hS) (6*z p)*LFunction (fixedSourcePrincipal S hS) (w p)) := by
  have hH := perturbed_global_correction_measurable η S x w z hx.measurable hw.measurable hz.measurable
  have hB := perturbed_slot_multiplier_measurable η J T b x w z hx.measurable hw.measurable hz.measurable
  have hR : Continuous (fun p => HeckeReciprocal.reciprocal (η.excludePrimes S hS) (x p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (HeckeReciprocal.reciprocal_differentiableAt _ (hβ p)).continuousAt.comp hx.continuousAt
  have hM0 : Continuous (fun p => mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (ProbeRadialMellin.radial_mellin_analytic W0 _ (hz0 p)).continuousAt.comp hz.continuousAt
  have hM1 := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous.comp hw
  have hL6 := (perturbed_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p => 6*z p))
  have hLw := (perturbed_LFunction_measurable (fixedSourcePrincipal S hS)).comp hw.measurable
  have hm0 := hM0.measurable
  have hm1 := hM1.measurable
  have hmr := hR.measurable
  have hmx := hx.measurable
  have hmw := hw.measurable
  have hmz := hz.measurable
  unfold continuedSourceMultiplier
  fun_prop (disch := aesop)

lemma perturbed_strip_integrable_of_uniform_slices (F : ℝ×(ℝ×ℝ) → ℂ) (l r D : ℝ)
    (hlr : l≤ r) (hm : AEStronglyMeasurable F ((volume.restrict (Icc l r)).prod (volume.prod volume)))
    (hs : ∀σ∈Icc l r,Integrable (fun q => F (σ,q)) (volume.prod volume))
    (hb : ∀σ∈Icc l r,(∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤ D) :
    Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc l r)).prod (volume.prod volume))≤(r-l)*D := by
  have hm' := hm.norm.integral_prod_right'
  have hb' : ∀ᵐσ : ℝ ∂volume.restrict (Icc l r),
      ‖∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume‖≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb σ hσ
  have hi' : Integrable (fun σ : ℝ => ∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)
      (volume.restrict (Icc l r)) :=
    (integrableOn_const (s:=Icc l r) (C:=D) (hs:=by simp [Real.volume_Icc])).mono' hm' hb'
  have hi : Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨?_,hi'⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    exact hs σ hσ
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi.norm]
  calc
    _ ≤ ∫σ : ℝ in Icc l r,D := integral_mono_ae hi' (integrableOn_const (hs:=by simp [Real.volume_Icc])) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      exact hb σ hσ)
    _ = _ := by simp [sub_nonneg.mpr hlr,mul_comm]

theorem perturbed_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 34999/40000≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := perturbed_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a 3 2 3 ha hβ (by norm_num) N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  dsimp only
  let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
    ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
    LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
  have hcut := perturbed_continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => ((max a p.1:ℝ):ℂ)+R*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => (ξ:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ.trans_le (le_max_left a p.1))
    (by intro p; simpa using (show (0:ℝ)<ξ by linarith [hξ.1]))
  have hm : AEStronglyMeasurable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) := by
    apply hcut.aestronglyMeasurable.congr
    have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc a 3)).prod (volume.prod volume),p.1∈Icc a 3 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hh] with p hp
    dsimp [F]
    rw [max_eq_right hp.1]
  have hh (σ : ℝ) (hσ : σ∈Icc a 3) := hc σ hσ ξ ⟨by linarith [hξ.1],hξ.2⟩
    3 (by norm_num) .s (by intro _; norm_num) (by intro _; linarith [hξ.1]) R hR
  have hs (σ : ℝ) (hσ : σ∈Icc a 3) : Integrable (fun q => F (σ,q)) (volume.prod volume) := by
    simpa only [F,sliceMap,ofReal_ofNat] using (hh σ hσ).1
  have hb (σ : ℝ) (hσ : σ∈Icc a 3) : (∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤
      arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N := by
    have ht := (hh σ hσ).2
    norm_num [joinWGap,joinZGap,sliceMap] at ht
    simpa only [F,norm_mul] using ht
  exact perturbed_strip_integrable_of_uniform_slices F a 3 _ ha3 hm hs hb

theorem perturbed_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 34999/40000≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := perturbed_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a 3 2 3 ha hβ (by norm_num) N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  dsimp only
  let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
    ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
    LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
  have hcut := perturbed_continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => (a:ℂ)+p.2.1*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => ((max ξlo p.1:ℝ):ℂ)+R*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ)
    (by intro p; simpa using (show (0:ℝ)< max ξlo p.1 by linarith [le_max_left ξlo p.1]))
  have hm : AEStronglyMeasurable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) := by
    apply hcut.aestronglyMeasurable.congr
    have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.1∈Icc ξlo 2 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hh] with p hp
    dsimp [F]
    rw [max_eq_right hp.1]
  have hh (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) := hc a ⟨le_rfl,ha3⟩ ξ ⟨by linarith [hξ.1],hξ.2⟩
    3 (by norm_num) .z (by intro _; norm_num) (by simp) R hR
  have hs (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) : Integrable (fun q => F (ξ,q)) (volume.prod volume) := by
    simpa only [F,sliceMap,ofReal_ofNat] using (hh ξ hξ).1
  have hb (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) : (∫q : ℝ×ℝ,‖F (ξ,q)‖ ∂volume.prod volume)≤
      arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N := by
    have ht := (hh ξ hξ).2
    norm_num [joinWGap,joinZGap,sliceMap] at ht
    simpa only [F,norm_mul] using ht
  exact perturbed_strip_integrable_of_uniform_slices F ξlo 2 _ hξ2 hm hs hb

lemma perturbed_high_x_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ R : ℝ) (hR : R≠0) :
    (fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.2.1*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I))
      =ᵐ[(volume.restrict (Icc a 3)).prod (volume.prod volume)]
    (fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((p.1:ℂ)+R*I)
      (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I))
      ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.2.1*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I)) := by
  apply Eventually.of_forall
  intro p
  have h0 : (p.1:ℂ)+R*I≠0 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  have h1 : (p.1:ℂ)+R*I≠1 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  dsimp only
  rw [perturbed_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma perturbed_high_z_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξlo R : ℝ) :
    (fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((p.1:ℂ)+R*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I))
      =ᵐ[(volume.restrict (Icc ξlo 2)).prod (volume.prod volume)]
    (fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((a:ℂ)+p.2.1*I)
      (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I))
      ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((p.1:ℂ)+R*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I)) := by
  have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.2.1≠0 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ)))
  filter_upwards [hh] with p hp
  have h0 : (a:ℂ)+p.2.1*I≠0 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+p.2.1*I≠1 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  rw [perturbed_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem perturbed_raw_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 34999/40000≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((p.1:ℂ)+R*I)
        (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I)) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := perturbed_uniform_high_x_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  have hh := hc ξ hξ R hR
  have heq := perturbed_high_x_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem perturbed_raw_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 34999/40000≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.2.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I)) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := perturbed_uniform_high_z_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo hξ2 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := hc R hR
  have heq := perturbed_high_z_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξlo R
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem perturbed_source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := perturbed_source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (perturbed_source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
    dsimp [K,π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral,integral_const_mul,ofReal_ofNat]
    ring
  exact hi.trans hh

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule20
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalTransport -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalPhysical -/
section LocalModule21
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open Complex MeasureTheory
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours ProbePrincipalPhysical
local notation "Id" => Ideal HeckeFamily.O
theorem perturbed_principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=> primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact perturbed_source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=> hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule21
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalPhysical -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalSlot -/
section LocalModule22

set_option linter.unusedVariables false

/-! Sharp actual principal and region slot estimates on the new domain.
The unit cancellation and compensated local identity are unchanged. Bounds
are proved with the new coordinate corner, not supplied as assumptions.
All slot/scalar functions are the original upstream mathematical objects.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open Complex
open OAI OAI.SevenEighths
open ProbeEuler ProbeLocal PrincipalSlotEstimate

theorem perturbed_principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := perturbed_unramifiedClosed_second_region_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) hs (by norm_num) (by norm_num)
  calc
    _ ≤ 240 * Q ^ (-(72599 / 40000 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem perturbed_principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have h := perturbed_principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem perturbed_principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (perturbed_principal_correction_lower_bound hQ hA hη hs)

theorem perturbed_principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hl := perturbed_principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem perturbed_unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

theorem perturbed_principal_coord_cancellation {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    (star η * (Q : ℂ) ^ s) * coordD Q η 1 s = 1 := by
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordD
  simp only [star_one, mul_one]
  calc
    _ = (star η * η) * ((Q : ℂ) ^ s * (Q : ℂ) ^ (-s)) := by ring
    _ = 1 := by rw [perturbed_unit_phase_inverse η hη, ← Complex.cpow_add _ _ hQ0]; simp

theorem perturbed_principal_V {Q : ℝ} : coordV Q (1 / 6) = (Q : ℂ)⁻¹ := by
  norm_num [coordV, Complex.cpow_neg_one]

theorem perturbed_principal_W {Q : ℝ} : coordW Q 1 1 = (Q : ℂ)⁻¹ := by
  simp [coordW, Complex.cpow_neg_one]

theorem perturbed_principal_B_norm {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    ‖star η * (Q : ℂ) ^ s‖ = Q ^ s.re := by
  rw [norm_mul, norm_star, hη, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]

theorem perturbed_compensated_unit_error_bound (V W D P B q : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hBD : B * D = 1) (hWq : W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖1 - q‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) q
    simp only [norm_one] at this
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(1 - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖1 - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + 1 - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + 1 - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (1 - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖1 - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + 1 - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q 1
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD (by simpa using hWq)
  simp only [mul_one] at hid
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(1 - q) * (V / (1 - V) - D)‖ + ‖(B + 1 - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

theorem perturbed_principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(34999 / 40000 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by norm_num))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := perturbed_principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← perturbed_principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-(34999 / 40000 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-(34999 / 40000 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by norm_num)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem perturbed_principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← perturbed_principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := perturbed_principal_marked_error_bounds hQ hA hη hs
  exact perturbed_compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (perturbed_principal_coord_cancellation hQ0 η s hη) hWq

theorem perturbed_principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have hn := perturbed_principal_correction_ne_zero hQ hA hη.le hs
  have he := perturbed_principal_replacement_error hQ hA hη hs
  have hi := perturbed_principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(34999 / 40000 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem perturbed_actual_target_norm (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) :
    ‖HeckeFamily.elementCoeff η p‖ = 1 := by
  let : Finite (HeckeFamily.O ⧸ η.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ η.modulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hp
  unfold HeckeFamily.elementCoeff
  rw [← hu]
  exact FiniteRayExpansion.norm_char_unit η.residue u

theorem perturbed_actual_principal_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : 34999 / 40000 ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(34999 / 40000 : ℝ)) :=
  perturbed_principal_slot_error hQ (actualAPhase_norm_le_one η p) (perturbed_actual_target_norm η p hp) hs

theorem perturbed_weighted_slot_error {ι : Type*} (S : Finset ι) (w : ι → ℝ) (B : ι → ℂ)
    (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)‖ ≤
      δ * ∑ i ∈ S, w i := by
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ) =
      ∑ i ∈ S, (w i : ℂ) * (B i + 1) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Complex.ofReal_sum]
  rw [hid]
  calc
    _ ≤ ∑ i ∈ S, ‖(w i : ℂ) * (B i + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, δ * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB i hi) (hw i hi)
    _ = _ := by rw [Finset.mul_sum]

theorem perturbed_weighted_slot_relative_error {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (B : ι → ℂ) (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) (hS : 0 < ∑ i ∈ S, w i) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1‖ ≤ δ := by
  have hSc : ((∑ i ∈ S, w i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1 =
      -((∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)) /
        (∑ i ∈ S, w i : ℝ) := by field_simp; ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  exact (div_le_iff₀ hS).mpr (perturbed_weighted_slot_error S w B δ hw hB)

theorem perturbed_weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 34999 / 40000 ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-(34999 / 40000 : ℝ))) * ∑ i ∈ S, w i := by
  apply perturbed_weighted_slot_error S w _ _ hw
  intro i hi
  apply (perturbed_principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)

theorem perturbed_product_error {κ : Type*} (S : Finset κ) (F : κ → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ) :
    ‖(∏ i ∈ S, F i) - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haF := hF a (Finset.mem_insert_self a S)
    have hSF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hprod := ih hSF
    have haN : ‖F a‖ ≤ 1 + δ := by
      have h := norm_sub_norm_le (F a) (1 : ℂ)
      simp only [norm_one] at h
      linarith
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖F a * ((∏ i ∈ S, F i) - 1) + (F a - 1)‖ := by congr 1; ring
      _ ≤ ‖F a * ((∏ i ∈ S, F i) - 1)‖ + ‖F a - 1‖ := norm_add_le _ _
      _ ≤ (1 + δ) * ((1 + δ) ^ S.card - 1) + δ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul haN hprod (norm_nonneg _) (by linarith)) haF
      _ = _ := by rw [pow_succ]; ring

theorem perturbed_product_error_linear (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) ^ n - 1 ≤ n * 2 ^ n * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hbase : 0 ≤ (1 + δ) ^ n - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith))
    calc
      _ = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by rw [pow_succ]; ring
      _ ≤ 2 * ((n : ℝ) * 2 ^ n * δ) + δ := by
        gcongr
        linarith
      _ ≤ _ := by rw [Nat.cast_succ, pow_succ]; nlinarith

theorem perturbed_principalScalar_eq {κ : Type*} (S : Finset κ) (M : κ → ℝ) :
    principalScalar S M = ∏ i ∈ S, (-(M i : ℂ)) := by
  unfold principalScalar
  rw [Complex.ofReal_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem perturbed_principalScalar_ne_zero {κ : Type*} (S : Finset κ) (M : κ → ℝ)
    (hM : ∀ i ∈ S, 0 < M i) : principalScalar S M ≠ 0 := by
  rw [perturbed_principalScalar_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hM i hi).ne')

theorem perturbed_fixed_product_relative_error {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  rw [perturbed_principalScalar_eq, ← Finset.prod_div_distrib]
  apply perturbed_product_error S _ δ hδ
  intro i hi
  have hMi : (M i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM i hi).ne'
  have hid : W i / (-(M i : ℂ)) - 1 = -(W i + (M i : ℂ)) / (M i : ℂ) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hM i hi)]
  exact (div_le_iff₀ (hM i hi)).mpr (hW i hi)

theorem perturbed_fixed_product_relative_error_linear {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ S.card * 2 ^ S.card * δ :=
  (perturbed_fixed_product_relative_error S M W δ hδ hM hW).trans
    (perturbed_product_error_linear S.card hδ hδ1)

theorem perturbed_weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 34999 / 40000 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-(34999 / 40000 : ℝ))) ^ S.card - 1 := by
  apply perturbed_fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact perturbed_weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem perturbed_principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by norm_num)
  refine ⟨hV, ?_, ?_⟩
  · rw [perturbed_principal_W, ← perturbed_principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem perturbed_principal_correction_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) =
      localCorrection (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
        (principalMarked Q A η s) := by
  have h := perturbed_principal_geometric_bounds hQ hη hs
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem perturbed_principal_raw_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    1 / 16 ≤ ‖principalRawFactor Q A η s‖ := by
  have hl := perturbed_principal_correction_lower_bound hQ hA hη hs
  have hg := perturbed_principal_geometric_bounds hQ hη hs
  have hV : ‖1 - coordV Q (1 / 6)‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q (1 / 6))
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 1‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 1)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      8 * ‖principalRawFactor Q A η s‖ := by
    rw [perturbed_principal_correction_eq_raw hQ hη hs]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖principalRawFactor Q A η s‖ *
      (‖1 - coordV Q (1 / 6)‖ * ‖1 - coordW Q 1 1‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖principalRawFactor Q A η s‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem perturbed_principal_raw_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    principalRawFactor Q A η s ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (perturbed_principal_raw_lower_bound hQ hA hη hs)

theorem perturbed_principal_slot_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re) :
    principalSlot Q A η s =
      (star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) := by
  have hg := perturbed_principal_geometric_bounds hQ hη hs
  have hn := perturbed_principal_correction_ne_zero hQ hA hη hs
  have hp := perturbed_principal_raw_ne_zero hQ hA hη hs
  have hr := compensatedReplacement_eq_raw (coordV Q (1 / 6)) (coordW Q 1 1)
    (coordD Q η 1 s) (principalMarked Q A η s) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-1 : ℂ))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← perturbed_principal_correction_eq_raw hQ hη hs] at hr
  unfold principalSlot principalReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem perturbed_principal_raw_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re) :
    ‖(star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) + 1‖ ≤ 1440 * Q ^ (-(34999 / 40000 : ℝ)) := by
  rw [← perturbed_principal_slot_eq_raw hQ hA hη.le hs]
  exact perturbed_principal_slot_error hQ hA hη hs

theorem perturbed_weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 34999 / 40000 ≤ s.re)
    (hsmall : 1440 * P ^ (-(34999 / 40000 : ℝ)) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-(34999 / 40000 : ℝ))) :=
  (perturbed_weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (perturbed_product_error_linear S.card (by positivity) hsmall)

theorem perturbed_region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(72599 / 40000 : ℝ)) :=
      perturbed_unramifiedClosed_second_region_bound Q A η 1 s w z (by linarith) hA hη (by simp) hs hw hz
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem perturbed_region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have h := perturbed_region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem perturbed_region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (perturbed_region_correction_lower_bound hQ hA hη hs hw hz)

theorem perturbed_region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hl := perturbed_region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem perturbed_region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem perturbed_region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(34999 / 40000 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := perturbed_principal_B_norm hQ0 η s hη
  have hg := perturbed_region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(34999 / 40000 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem perturbed_region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := perturbed_region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(34999 / 40000 : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := perturbed_region_marked_error_bounds hQ hA hη hs hw hz
  exact perturbed_compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (perturbed_principal_coord_cancellation hQ0 η s hη) hWq

theorem perturbed_region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have hn := perturbed_region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := perturbed_region_replacement_error hQ hA hη hs hw hz
  have hi := perturbed_region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(34999 / 40000 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

@[simp] theorem region_slot_at_residue (Q : ℝ) (A η s : ℂ) :
    regionSlot Q A η s 1 (1 / 6) = principalSlot Q A η s := rfl

theorem perturbed_region_correction_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z =
      localCorrection (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
        (regionMarked Q A η s w z) := by
  have h := perturbed_region_geometric_bounds hQ hη hs hw hz
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem perturbed_region_raw_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 16 ≤ ‖regionRawFactor Q A η s w z‖ := by
  have hl := perturbed_region_correction_lower_bound hQ hA hη hs hw hz
  have hg := perturbed_region_geometric_bounds hQ hη hs hw hz
  have hV : ‖1 - coordV Q z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q z)
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 w‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 w)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s w z‖ ≤
      8 * ‖regionRawFactor Q A η s w z‖ := by
    rw [perturbed_region_correction_eq_raw hQ hη hs hw hz]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖regionRawFactor Q A η s w z‖ *
      (‖1 - coordV Q z‖ * ‖1 - coordW Q 1 w‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖regionRawFactor Q A η s w z‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem perturbed_region_raw_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionRawFactor Q A η s w z ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (perturbed_region_raw_lower_bound hQ hA hη hs hw hz)

theorem perturbed_region_slot_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionSlot Q A η s w z =
      (star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) := by
  have hg := perturbed_region_geometric_bounds hQ hη hs hw hz
  have hn := perturbed_region_correction_ne_zero hQ hA hη hs hw hz
  have hp := perturbed_region_raw_ne_zero hQ hA hη hs hw hz
  have hr := compensatedReplacement_eq_raw (coordV Q z) (coordW Q 1 w)
    (coordD Q η 1 s) (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-w))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← perturbed_region_correction_eq_raw hQ hη hs hw hz] at hr
  unfold regionSlot regionReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem perturbed_region_raw_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) + 1‖ ≤ 1440 * Q ^ (-(34999 / 40000 : ℝ)) := by
  rw [← perturbed_region_slot_eq_raw hQ hA hη.le hs hw hz]
  exact perturbed_region_slot_error hQ hA hη hs hw hz

theorem perturbed_region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-(34999 / 40000 : ℝ)) := by
  have he := perturbed_region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem perturbed_weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 34999 / 40000 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-(34999 / 40000 : ℝ))) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-(34999 / 40000 : ℝ))) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := perturbed_region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-(34999 / 40000 : ℝ)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem perturbed_actual_region_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s w z : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : 34999 / 40000 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s w z + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(34999 / 40000 : ℝ)) :=
  perturbed_region_slot_error hQ (actualAPhase_norm_le_one η p) (perturbed_actual_target_norm η p hp) hs hw hz

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule22
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalSlot -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedSharpProduct -/
section LocalModule23

set_option linter.unusedVariables false

/-! Sharp fixed positive slot bounds for the genuine finite Euler product.
This derives the new exponent in the small-prime error from proved local
unit cancellation; no sharp product estimate is an input.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss HeckeFamily ProbePhysical ProbeEuler ProbeLocal ProbeFiniteProductBounds
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

theorem perturbed_slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 34999/40000≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(34999/40000 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using perturbed_weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem perturbed_combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 34999/40000≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(34999/40000 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (perturbed_global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (perturbed_slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)


end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule23
/- END RHZeroFreeExtension.analytic_high.PerturbedSharpProduct -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedRemainderBounds -/
section LocalModule24


noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open ProbePrincipalRemainderBounds
namespace RHZeroFreeExtension.AnalyticHigh
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma perturbed_remainder_active_prime_sum_bound (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hP : 0< P)
    (hthreshold : 480≤ c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤ W x ∧ W x≤ B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=> W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A) :
      c*P≤(Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ)≤ d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ)≤128*(d*P) := by
    have h := DescentFiberCost.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤ c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith)
  rw [he]
  calc
    _≤∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _≤(128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

def perturbed_remainder_slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(34999/40000:ℝ)))*(128*d*B*c^(ξ-1))

lemma perturbed_remainder_slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) : 0≤ perturbed_remainder_slotConstant J c d B ξ := by
  have hd0 : 0≤ d := hc.le.trans hd
  unfold perturbed_remainder_slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=> by positivity)

theorem perturbed_remainder_window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0< P j)
    (hthreshold : ∀j∈J,480≤ c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j)
    (T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (s w z : ℂ)
    (hs : 34999/40000≤ s.re) (hw : 19/20≤ w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      perturbed_remainder_slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=> W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := perturbed_combined_slot_bound_sharp η S hS J A
    (fun j p=> W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=> PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(34999/40000:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=> by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (perturbed_remainder_active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [perturbed_remainder_slotConstant,←mul_assoc,Finset.prod_mul_distrib]

lemma perturbed_remainder_scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0≤ X) (hY : 0≤ Y) (hZ : 0≤ Z) :
    0≤ scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0< P j) (hthreshold : ∀j∈J,480≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) (T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
  (ha : 34999/40000≤ a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤ C)
  (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma perturbed_remainder_continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*perturbed_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := perturbed_remainder_window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := perturbed_height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX];congr 1;simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ];congr 1;simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];congr 1;simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile;ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _≤ X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (perturbed_remainder_slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma perturbed_remainder_full_sharp_pointwise (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*perturbed_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := perturbed_remainder_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := perturbed_fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := perturbed_fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (perturbed_zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := perturbed_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := perturbed_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*perturbed_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*perturbed_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := perturbed_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact perturbed_height_le_joint_z _ _ _ | exact perturbed_height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma perturbed_remainder_residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*perturbed_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := perturbed_remainder_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := perturbed_fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (perturbed_zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := perturbed_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := perturbed_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*perturbed_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*perturbed_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact perturbed_height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma perturbed_remainder_vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=> F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ (fun w=> F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma perturbed_remainder_vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=> F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma perturbed_remainder_normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (34999/40000:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem perturbed_remainder_full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    Integrable F heightMeasure ∧
      (∫p,‖F p‖ ∂heightMeasure)≤ K/(|6*ξ-1| *|υ-1|)*
        (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (34999/40000) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*perturbed_remainder_slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := perturbed_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := perturbed_zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := perturbed_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := perturbed_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=> LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*perturbed_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0≤ A := by dsimp [A];positivity
  have hE : 0≤ E := mul_nonneg (perturbed_remainder_scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _≤∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact perturbed_remainder_full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _≤(K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith

theorem perturbed_remainder_residue_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume)≤ K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (34999/40000) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*perturbed_remainder_slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := perturbed_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := perturbed_zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := perturbed_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I)) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    rw [perturbed_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*perturbed_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0≤ A := by dsimp [A];positivity
  have hE : 0≤ E := mul_nonneg (perturbed_remainder_scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _≤∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact perturbed_remainder_residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _≤(K+1)/|6*ξ-1| *E := by gcongr;linarith

theorem perturbed_remainder_full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := perturbed_remainder_full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0< k := pow_pos perturbed_remainder_normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [perturbed_remainder_vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _≤ k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _≤ k*(K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem perturbed_remainder_residue_vertical_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral ξ
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := perturbed_remainder_residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0< k := pow_pos perturbed_remainder_normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [perturbed_remainder_vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _≤(1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _≤(1+‖R‖)*(k*(K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
      gcongr;exact hh.2
    _=_ := by ring
end Uniform

theorem perturbed_remainder_ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (34999/40000:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e≤5/6) :
    ∃C : ℝ,0< C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := perturbed_remainder_full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith,by linarith⟩ (by linarith)
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := perturbed_remainder_residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith)];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (perturbed_remainder_scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (perturbed_remainder_scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith

lemma perturbed_remainder_source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=5003/30000) (Z a ξ υ : ℝ) (hZ : 0< Z) :
    scalePower (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(ell j))^ξ) =
    Z^(a-11/16+(16253/20000)*(ξ-1/6)+(28747/60000)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(ell j))^ξ)=Z^((5003/30000)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma perturbed_remainder_source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=5003/30000) (Z a e : ℝ) (hZ : 0< Z) :
    scalePower (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(ell j))^(1/6+e)) = Z^(a-11/16+(16253/20000)*e-28747/1200000) := by
  rw [perturbed_remainder_source_scale_identity J ell hell Z a (1/6+e) (19/20) hZ]
  congr 1;ring

lemma perturbed_remainder_source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=5003/30000) (Z a : ℝ) (hZ : 0< Z) :
    scalePower (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(ell j))^(33/200:ℝ)) = Z^(a-11/16-16253/12000000) := by
  rw [perturbed_remainder_source_scale_identity J ell hell Z a (33/200) 1 hZ]
  congr 1;ring

lemma perturbed_remainder_eventual_annulus_threshold {ι : Type*} (η : Character) (J : Finset ι)
    (c : ℝ) (hc : 0< c) (ell : ι→ℝ) (hell : ∀j∈J,0< ell j) :
    ∃Z0 : ℝ,1≤ Z0 ∧ ∀Z : ℝ,Z0≤ Z→∀j∈J,
      480≤ c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j) := by
  have hh : ∀ᶠZ : ℝ in atTop,∀j∈J,
      480≤ c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j) := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    have ht := (tendsto_rpow_atTop (hell j hj)).const_mul_atTop hc
    exact (ht.eventually (eventually_ge_atTop 480)).and
      (ht.eventually (eventually_gt_atTop (Ideal.absNorm η.modulus:ℝ)))
  obtain ⟨Z0,hZ0⟩ := eventually_atTop.mp hh
  refine ⟨max 1 Z0,le_max_left _ _,?_⟩
  intro Z hZ
  exact hZ0 Z ((le_max_right _ _).trans hZ)

theorem perturbed_remainder_source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (34999/40000:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e≤5/6) :
    ∃C : ℝ,0< C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=5003/30000) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0< Z→
    (∀j∈J,480≤ c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-11/16+(16253/20000)*e-28747/1200000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤ C*Z^(a-11/16-16253/12000000)) := by
  obtain ⟨C,hC,hbound⟩ := perturbed_remainder_ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=> Z^(ell j)) (fun _ _=> Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [perturbed_remainder_source_w_scale_identity J ell hell Z a e hZ,perturbed_remainder_source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

lemma perturbed_remainder_source_w_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16+(16253/20000)*e-28747/1200000≤β-11/16-17/48000 := by linarith

lemma perturbed_remainder_source_z_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16-16253/12000000≤β-11/16-17/48000 := by linarith

theorem perturbed_remainder_source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (34999/40000:ℝ) 2) :
    ∃C : ℝ,0< C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=5003/30000) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤ Z→
    (∀j∈J,480≤ c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> verticalIntegral (1/6+e)
      (fun z=> verticalIntegral (19/20) (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=> verticalIntegral (33/200) (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) := by
  obtain ⟨C,hC,hbound⟩ := perturbed_remainder_source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (perturbed_remainder_source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (perturbed_remainder_source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end RHZeroFreeExtension.AnalyticHigh

end

end LocalModule24
/- END RHZeroFreeExtension.analytic_high.PerturbedRemainderBounds -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalPhysicalRemainder -/
section LocalModule25
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
open OAI OAI.SevenEighths
open ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem perturbed_physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e≤1/1000)
    (ha : 34999/40000< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=5003/30000 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤ W j x ∧ W j x≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤ Z → (∀j,480≤ c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryGenerator (P j).val.val)
          W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := perturbed_remainder_source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0< Z := by linarith
  have hb := hbound ell hell W (fun j _=> hW j) (fun j _=> hsupp j) T (fun j _ p hp=> hT j p hp)
    Z hZ (fun j _=> hthreshold j) (fun j _=> hmod j)
  dsimp only at hb
  have heq := perturbed_principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)
  apply hn.trans
  have hCe : C≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤ Z^(HeckeZeroSupremum.beta-11/16-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule25
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalPhysicalRemainder -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedSignalShift -/
section LocalModule26
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI OAI.SevenEighths
open HeckeSignalShift
namespace PerturbedHeckeSignalShift
open HeckeFamily HeckeSignal Continuation

theorem perturbed_quotient_holomorphic (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re}) {a : ℝ}
    (ha : (34999/40000 : ℝ)< a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  exact ((hH.differentiableAt ((Complex.isOpen_re_gt (34999/40000)).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem perturbed_quotient_polynomial_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (n : ℕ) (ha : (34999/40000 : ℝ)< a) (_hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ 2) :
    ‖quotient χ H s‖ ≤ ((3/2)*C)*(1+|s.im|^n) := by
  have hnorm : ‖H s‖ ≤ 3/2 := by
    have ht := norm_add_le (H s-1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith [hb s (ha.trans_le hs.1)]
  unfold quotient
  rw [norm_mul]
  calc
    _ ≤ (3/2)*(C*(1+|s.im|^n)) :=
      mul_le_mul hnorm (hR s hs.1 hs.2) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem perturbed_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ n ha2
    (gaussianContourIntegrand_differentiableOn (perturbed_quotient_holomorphic χ H hH ha hβ) c hx0)
    (C := x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*((3/2)*C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x^(b+c) ≤ x^(2+c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have he : Real.exp ((b-5/6)^2) ≤ Real.exp ((2-5/6 : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hb'.1,hb'.2]
  have hq := perturbed_quotient_polynomial_bound χ H hb n ha hC hR
    (s := (b : ℂ)+y*I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)) *
        (((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring

theorem perturbed_signal_bound_at_infinity (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    ‖signal χ H c x‖ ≤ infinityConstant a C n*x^(a+c) := by
  have hx0 : 0 < x := by linarith
  rw [perturbed_contour_shift_left χ H hH hb c a C n ha ha2 hβ hC hR hx, norm_mul]
  have hint := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable n).const_mul
      (x^(a+c)*Real.exp ((a-5/6)^2)*((3/2)*C)))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
      have hq := perturbed_quotient_polynomial_bound χ H hb n ha hC hR
        (s := (a : ℂ)+y*I) (by simpa using And.intro (le_refl a) ha2)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
      calc
        _ ≤ x^(a+c)*Real.exp ((a-5/6)^2)*(((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
        _ = _ := by unfold polynomialGaussian; ring))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 ; unfold infinityConstant ; ring

theorem perturbed_signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n)) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  apply IsBigO.of_bound (infinityConstant a C n)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := perturbed_signal_bound_at_infinity χ H hH hb c a C n ha ha2 hβ hC hR hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ x by linarith) (a+c))] using h

end PerturbedHeckeSignalShift

end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule26
/- END RHZeroFreeExtension.analytic_high.PerturbedSignalShift -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedSignalBounds -/
section LocalModule27
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeSignalBounds
namespace PerturbedHeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem perturbed_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) {x : ℝ} (hx : 1≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact PerturbedHeckeSignalShift.perturbed_contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem perturbed_signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact PerturbedHeckeSignalShift.perturbed_signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end PerturbedHeckeSignalBounds

end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule27
/- END RHZeroFreeExtension.analytic_high.PerturbedSignalBounds -/

/- BEGIN original module geometry.Normalization -/
section LocalModule28

namespace RHNormalization
noncomputable section

theorem physical_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^(21247/60000 : ℝ) : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-(5003/30000 : ℝ)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s-11/16) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (21247/60000) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf

#print axioms physical_power_identity
end
end RHNormalization

end LocalModule28
/- END geometry.Normalization -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPhysicalNormalization -/
section LocalModule29
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
open OAI OAI.SevenEighths
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal ProbePhysical Continuation HeckeSignal
open PrincipalSignalComparison PrincipalMellinResidues
variable {κ ι : Type*}
theorem perturbed_source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^(21247/60000 : ℝ) : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-(5003/30000 : ℝ)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s-11/16) := RHNormalization.physical_power_identity hZ s

theorem perturbed_normalized_source_double_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(21247/60000 : ℝ)) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (5003/30000) (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := perturbed_source_power_identity hZ s
  have hz : (Z : ℂ)^(((-(5003/30000 : ℝ)/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-(5003/30000 : ℝ)/6 : ℝ) : ℂ)) *
          ((Z : ℂ)^(((-(5003/30000 : ℝ)/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem perturbed_sourceResidueIntegral_normalized (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (5003/30000) (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^(21247/60000 : ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (5003/30000) (slotMass T w) : ℂ)) =
        slotResidue χ (fun s => H s 1 (1/6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral slotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact perturbed_normalized_source_double_residue W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem perturbed_source_double_residue_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => kernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(21247/60000 : ℝ)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hiraw := raw_slot_integrable χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := 5003/30000))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (5003/30000) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (perturbed_normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

#print axioms perturbed_source_power_identity
#print axioms perturbed_normalized_source_double_residue
end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule29
/- END RHZeroFreeExtension.analytic_high.PerturbedPhysicalNormalization -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalSignalComparison -/
section LocalModule30
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
open OAI OAI.SevenEighths
open PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

theorem perturbed_raw_inverse_ae_reciprocal (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem perturbed_raw_quotient_integral_eq (χ : Character) (a : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  apply integral_congr_ae
  filter_upwards [perturbed_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [div_eq_mul_inv, ht]

variable {κ ι : Type*}

structure perturbed_SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(34999/40000 : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

theorem perturbed_slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : perturbed_SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem perturbed_slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : perturbed_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 34999/40000 ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(34999/40000 : ℝ)) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    perturbed_weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem perturbed_slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : perturbed_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 34999/40000 ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(34999/40000 : ℝ)) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [perturbed_slotRatio_error S T w Q A η h hs]

theorem perturbed_principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999/40000 ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := perturbed_principal_geometric_bounds hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1-coordR Q A s (1/6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1/6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ)^s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1/6) hR hV hD)
    (perturbed_principal_correction_ne_zero hQ hA hη hs)

theorem perturbed_slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : perturbed_SlotBounds S T w Q A η P) {a : ℝ} (ha : 34999/40000 ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (perturbed_principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

theorem perturbed_slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [perturbed_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

theorem perturbed_kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    {a Z : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (PerturbedHeckeSignalShift.perturbed_quotient_holomorphic χ H hH ha hβ) (-11/16) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem perturbed_kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := PerturbedHeckeSignalShift.perturbed_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-11/16))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem perturbed_kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (perturbed_kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (perturbed_kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem perturbed_slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : perturbed_SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := perturbed_kernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := perturbed_slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := perturbed_slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := perturbed_slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [perturbed_slotResidue_eq_reciprocal,
      PerturbedHeckeSignalBounds.perturbed_contour_shift_left χ H hH hb (-11/16) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H a Z t * _ - kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(34999/40000 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(34999/40000 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(34999/40000 : ℝ))) :=
        mul_le_mul (perturbed_kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(34999/40000 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem perturbed_exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), perturbed_SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
          D * Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact perturbed_slotResidue_bound_of_reciprocal_bound χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem perturbed_raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [perturbed_raw_inverse_ae_reciprocal χ a] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

private instance : IsPrincipalIdealRing HeckeFamily.O := IsCyclotomicExtension.Rat.three_pid K

theorem perturbed_idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  let := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  obtain ⟨u, hu⟩ := hu
  change ‖IdealCharacter.value χ.modulus χ.residue J‖ = 1
  rw [IdealCharacter.value, ite_eq_right hJ, ← hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

open ProbePhysical ActualEisensteinCubic CompletedGauss

theorem perturbed_prime_coprime_of_norm_gt (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

theorem perturbed_annularPrimeWeight_nonneg (W : ℝ → ℝ) (hW : ∀ x, 0 ≤ W x)
    (scale : ℝ) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) : 0 ≤ annularPrimeWeight W scale P :=
  mul_nonneg (hW _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem perturbed_annularPrimeWeight_norm_lower (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : c*scale ≤ (Ideal.absNorm P.val : ℝ) :=
  (le_div_iff₀ hscale).mp (hW _ (left_ne_zero_of_mul hw))

theorem perturbed_annularPrimeWeight_target_unit (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (η : Character)
    (hthreshold : (Ideal.absNorm η.modulus : ℝ) < c*scale) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : ‖idealCoeff η P.val‖ = 1 := by
  have hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val := by
    exact_mod_cast hthreshold.trans_le (perturbed_annularPrimeWeight_norm_lower W c scale hscale hW P hw)
  exact perturbed_idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (perturbed_prime_coprime_of_norm_gt η P hN)

theorem perturbed_sourceCorrection_eq_principal (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) : sourceCorrection η E = principalCorrection η E := by
  funext s
  exact source_globalCorrection_principal E hE η s

theorem perturbed_sourceCorrection_differentiable (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | 34999/40000 < s.re} :=
  (perturbed_globalClosedCorrection_analytic_x η E hE.tail 1 (1/6) (by norm_num) (by norm_num)).differentiableOn

theorem perturbed_sourceCorrection_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : 34999/40000 < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 :=
  perturbed_globalClosedCorrection_bound η E hE.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)

theorem perturbed_actual_principal_slot (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (s : ℂ) :
    compensatedReplacement (coordV (Ideal.absNorm P.val) (1/6))
      (coordW (Ideal.absNorm P.val) 1 1) (coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s)
      (idealMarkedClosed η P s 1 (1/6))
      (star (idealCoeff η P.val) * (Ideal.absNorm P.val : ℂ)^s)
      ((Ideal.absNorm P.val : ℂ)^(-1 : ℂ)) / idealClosedCorrection η P s 1 (1/6) =
      principalSlot (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem perturbed_exists_actualSlotResidue_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (w : κ → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ) (P Z : ℝ),
      480 ≤ P → 1440 * P^(-(34999/40000 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      ‖actualSlotResidue η E hE a Z S T w -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  obtain ⟨D, hD, hb⟩ := perturbed_exists_slotResidue_bound (ι := OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (perturbed_sourceCorrection_differentiable η E hE) (perturbed_sourceCorrection_bound η E hE)
    ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro T w P Z hP hsmall hw hnorm hcop hmass hZ
  exact (hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z
    ⟨hP, hsmall, hw, hnorm, fun j hj p hp => actualAPhase_norm_le_one η _,
      fun j hj p hp => perturbed_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp),
      hmass⟩ hZ).2

open PrincipalMellinResidues

theorem perturbed_slotMass_active (T : κ → Finset ι) (w : κ → ι → ℝ) :
    slotMass (activePools T w) w = slotMass T w := by
  funext j
  simp only [slotMass, activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem perturbed_slotProduct_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotProduct S (activePools T w) w Q A η s = slotProduct S T w Q A η s := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem perturbed_slotRatio_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotRatio S (activePools T w) w Q A η s = slotRatio S T w Q A η s := by
  rw [slotRatio, slotRatio, perturbed_slotProduct_active, perturbed_slotMass_active]

theorem perturbed_slotResidue_active (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S (activePools T w) w Q A η = slotResidue χ H a Z S T w Q A η := by
  simp only [slotResidue, perturbed_slotRatio_active]

theorem perturbed_slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (34999/40000)*ell)
    (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      perturbed_SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H (-11/16) Z) =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) := by
  obtain ⟨D, hD, hd⟩ := perturbed_exists_slotResidue_bound χ H hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(34999/40000 : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [perturbed_slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(34999/40000 : ℝ)) = c0^(-(34999/40000 : ℝ))*Z^(ell*(-(34999/40000 : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a-11/16+ell*(-(34999/40000 : ℝ))) ≤ Z^(a-11/16-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H (-11/16) Z‖ ≤ (D*c0^(-(34999/40000 : ℝ)))*Z^(a-11/16-saving) := by
    calc
      _ ≤ D*Z^(a-11/16)*(c0^(-(34999/40000 : ℝ))*Z^(ell*(-(34999/40000 : ℝ)))) := he
      _ = (D*c0^(-(34999/40000 : ℝ)))*Z^(a-11/16+ell*(-(34999/40000 : ℝ))) := by
        rw [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'

theorem perturbed_actualSlotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (34999/40000)*ell)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (w : ℝ → κ → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      perturbed_SlotBounds S (activePools (T Z) (w Z)) (w Z) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
        (c0*Z^ell)) :
    (fun Z : ℝ => actualSlotResidue η E hE a Z S (T Z) (w Z) -
        signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z)
      =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) :=
  perturbed_slotResidue_isBigO S c0 ell saving hc0 hsaving (η.excludePrimes E hE.prime)
    (sourceCorrection η E) (perturbed_sourceCorrection_differentiable η E hE)
    (perturbed_sourceCorrection_bound η E hE) ha ha2 hβ T w
    (fun _ _ p => Ideal.absNorm p.val)
    (fun _ _ p => actualAPhase η (primaryGenerator p.val)) (fun _ _ p => idealCoeff η p.val) hdata

theorem perturbed_fixedPrincipal_product_eq (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    fixedPrincipal (∏ p ∈ E, p) = fixedSourcePrincipal E hE.prime := rfl

theorem perturbed_exists_normalized_actual_source_bound (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
      (w : κ → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(34999/40000 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (5003/30000) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(21247/60000 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(21247/60000 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := perturbed_exists_slotResidue_bound (ι := OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (perturbed_sourceCorrection_differentiable η E hE) (perturbed_sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := perturbed_sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : perturbed_SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => perturbed_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact perturbed_source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule30
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalSignalComparison -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalResidueActual -/
section LocalModule31
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
open OAI OAI.SevenEighths
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss ProbePrincipalResidueActual
theorem perturbed_normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 34999/40000< a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta< a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0< a0 → 0< a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤ P → 1440*P^(-(34999/40000 : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤ W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0< slotMass T (residueWeights W scale) j) → 1≤ Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (5003/30000) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        sourceMultiplier W0 W1 (Z^(21247/60000 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(21247/60000 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D*Z^(a-11/16)*P^(-(34999/40000 : ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := perturbed_exists_normalized_actual_source_bound E hE η ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏p∈E,p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule31
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalResidueActual -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedRayPoolThresholds -/
section LocalModule32

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
open OAI OAI.SevenEighths
open ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem perturbed_power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0< c) (hd : c≤ d) (hmin : 0< ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤ Z ∧ 480≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(34999/40000:ℝ))≤1 ∧
      (∀j,480≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)< c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(34999/40000:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<34999/40000)).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0< Z := by linarith
  have hmono (j : ι) : c*Z^ellMin≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule32
/- END RHZeroFreeExtension.analytic_high.PerturbedRayPoolThresholds -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalNormalized -/
section LocalModule33
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤ c) (hA : ‖A-R‖≤ c) (hN : ‖N⁻¹‖≤ v)
    (hR : ‖R/N-F‖≤ d) : ‖A/N-F‖≤ c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem perturbed_actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hmin : 0< ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=5003/30000)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0< e) (hehi : e≤1/1000) (hnu : 0< nu)
    (ha : 34999/40000< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (5003/30000)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryGenerator (P j).val.val)
          W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16+e-(34999/40000)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := perturbed_physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := perturbed_normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(34999/40000:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [perturbed_power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=> hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=> c) (fun _=> d) ell (fun _=> hc) (fun _=> hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0< Z := by linarith
  let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (5003/30000)
    (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=> Z^(ell j)) (c*Z^ellMin) (Z^(28747/60000:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=> hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=> Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(34999/40000:ℝ))=c^(-(34999/40000:ℝ))*Z^(-(34999/40000:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-11/16)*(c*Z^ellMin)^(-(34999/40000:ℝ))=
      (D*c^(-(34999/40000:ℝ)))*Z^(HeckeZeroSupremum.beta-11/16+e-(34999/40000)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-11/16+e-(34999/40000)*ellMin=
      (HeckeZeroSupremum.beta+e-11/16)+(-(34999/40000:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤ C := by
    dsimp [C]
    have : 0≤ D*c^(-(34999/40000:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(34999/40000:ℝ))≤ C := by
    dsimp [C]
    have : 0≤ C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        C*Z^(HeckeZeroSupremum.beta-11/16+e-(34999/40000)*ellMin) := by gcongr
    _ = _ := by ring
end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule33
/- END RHZeroFreeExtension.analytic_high.PerturbedPrincipalNormalized -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportCentralErrorSaving -/
section LocalModule34
set_option linter.unusedVariables false

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma perturbed_central_prime_tuple_count {K : ℕ} (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(5003/30000:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(5003/30000:ℝ) := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


lemma perturbed_central_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^(21247/60000:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(28747/60000:ℝ))^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma perturbed_central_prime_product_bound {K : ℕ} (P : Fin K→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(5003/30000:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^(5003/30000:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma perturbed_central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((16253/20000:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(5003/30000:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(65003/10000:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (16253/20000:ℝ)+ζ≤1 by linarith))
  have hp := perturbed_central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=> Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(5003/30000:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((5003/30000:ℝ)*(3:ℕ))=Z^(65003/10000:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


end SevenEighths.ProbeHighRowFamily
end
end OAI

end LocalModule34
/- END RHZeroFreeExtension.analytic_high.PerturbedTransportCentralErrorSaving -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportCubeErrorSaving -/
section LocalModule35
set_option linter.unusedVariables false

namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem perturbed_original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((16253/20000:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(5003/30000:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((85003/10000:ℝ)+saving)/τ)
  have hN' : (85003/10000:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := perturbed_central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := perturbed_central_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(85003/10000:ℝ)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(65003/10000:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(85003/10000:ℝ)/height H^N) := by
      have hh : Z^(65003/10000:ℝ)*Z^(2:ℝ)=Z^(85003/10000:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(85003/10000:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end LocalModule35
/- END RHZeroFreeExtension.analytic_high.PerturbedTransportCubeErrorSaving -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportCubeFiniteError -/
section LocalModule36
set_option linter.unusedVariables false

namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem perturbed_finite_cube_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48) (hA : 0≤ A)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((16253/20000:ℝ)+ζ)) →
      ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(5003/30000:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=> Z^(length j)) W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=> Z^(length j)) W0 W1
          (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := perturbed_original_row_cube_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((16253/20000:ℝ)+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (16253/20000:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (perturbed_central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (5003/30000:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (a u) e (H u)‖≤ E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=> hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=> hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤ A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) (fun j _=> hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end LocalModule36
/- END RHZeroFreeExtension.analytic_high.PerturbedTransportCubeFiniteError -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportTailScales -/
section LocalModule37
set_option linter.unusedVariables false
namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
lemma perturbed_small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(5003/30000:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(21247/60000:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+1/40000+(17/50:ℝ)-1)*
        (Z^(28747/60000:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-49337/500000+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma perturbed_small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤ Z) (hU : 1≤ U)
    (hUsmall : U≤ Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(5003/30000:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(21247/60000:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+1/40000+(17/50:ℝ)-1)*
        (Z^(28747/60000:ℝ))^((1/2:ℝ)-1))≤ Z^(β-11/16-39337/500000+8*e) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤ Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,perturbed_small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-11/16-49337/500000+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;ring

lemma perturbed_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(5003/30000:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(21247/60000:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(28747/60000:ℝ))^((2:ℝ)-1))=
      Z^((66247/40000:ℝ)+(16253/20000:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end LocalModule37
/- END RHZeroFreeExtension.analytic_high.PerturbedTransportTailScales -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportLargeDyad -/
section LocalModule38
set_option linter.unusedVariables false

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem perturbed_large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤ r)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z U : ℝ),1≤ Z → 1≤ U →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(5003/30000:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z 2 2 r
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((66247/40000:ℝ)+(16253/20000:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤ Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=> Z^(length i)) hYp W hWS hWB
    (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(21247/60000:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(28747/60000:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [perturbed_large_source_scale Z hZ0 length hl r];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end LocalModule38
/- END RHZeroFreeExtension.analytic_high.PerturbedTransportLargeDyad -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportGeometricTail -/
section LocalModule39
set_option linter.unusedVariables false

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma perturbed_large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0< Z) (n : ℕ) :
    Z^((66247/40000:ℝ)+(16253/20000:ℝ)*r)*(Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((66247/40000:ℝ)+((16253/20000:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma perturbed_large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0< Z) (hr : 8/5+δ< r) :
    Summable (fun n : ℕ=> Z^((66247/40000:ℝ)+(16253/20000:ℝ)*r)*(Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [perturbed_large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma perturbed_large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0< Z) (hr : 8/5+δ< r) :
    (∑'n : ℕ,Z^((66247/40000:ℝ)+(16253/20000:ℝ)*r)*(Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((66247/40000:ℝ)+((16253/20000:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [perturbed_large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma perturbed_exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤ r ∧ 8/5+δ< r ∧
      (66247/40000:ℝ)+((16253/20000:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((66247/40000:ℝ)+((16253/20000:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end SevenEighths.ProbeHighRowFamily
end

end OAI

end LocalModule39
/- END RHZeroFreeExtension.analytic_high.PerturbedTransportGeometricTail -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedTransportLargeTail -/
section LocalModule40
set_option linter.unusedVariables false

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma perturbed_absolutePhysicalDyadIntegral_nonneg {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) :
    0≤ absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (norm_nonneg _) (physicalDyadNorm_nonneg S hS hmax η R T hT W Yp _ _ _)

theorem perturbed_large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤ r) (hr' : 8/5+δ< r) (hζ : 0<ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(5003/30000:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
