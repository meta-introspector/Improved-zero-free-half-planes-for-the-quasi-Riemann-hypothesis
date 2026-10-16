    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  exact (iv_source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (iv_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

lemma iv_continued_principal_measurable (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    {ι : Type*} (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (x w z : ℝ×(ℝ×ℝ) → ℂ) (hx : Continuous x) (hw : Continuous w) (hz : Continuous z)
    (hβ : ∀p,HeckeZeroSupremum.beta<(x p).re) (hz0 : ∀p,0<(z p).re) :
    Measurable (fun p => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z (x p) (w p) (z p)*
      LFunction (fixedSourcePrincipal S hS) (6*z p)*LFunction (fixedSourcePrincipal S hS) (w p)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hH := iv_global_correction_measurable η S x w z hx.measurable hw.measurable hz.measurable
  have hB := iv_slot_multiplier_measurable η J T b x w z hx.measurable hw.measurable hz.measurable
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
  have hL6 := (iv_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p => 6*z p))
  have hLw := (iv_LFunction_measurable (fixedSourcePrincipal S hS)).comp hw.measurable
  have hm0 := hM0.measurable
  have hm1 := hM1.measurable
  have hmr := hR.measurable
  have hmx := hx.measurable
  have hmw := hw.measurable
  have hmz := hz.measurable
  unfold continuedSourceMultiplier
  fun_prop (disch := aesop)

lemma iv_strip_integrable_of_uniform_slices (F : ℝ×(ℝ×ℝ) → ℂ) (l r D : ℝ)
    (hlr : l≤ r) (hm : AEStronglyMeasurable F ((volume.restrict (Icc l r)).prod (volume.prod volume)))
    (hs : ∀σ∈Icc l r,Integrable (fun q => F (σ,q)) (volume.prod volume))
    (hb : ∀σ∈Icc l r,(∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤ D) :
    Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc l r)).prod (volume.prod volume))≤(r-l)*D := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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

theorem iv_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHIVProbe.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := iv_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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
  have hcut := iv_continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
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
  exact iv_strip_integrable_of_uniform_slices F a 3 _ ha3 hm hs hb

theorem iv_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHIVProbe.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := iv_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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
  have hcut := iv_continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
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
  exact iv_strip_integrable_of_uniform_slices F ξlo 2 _ hξ2 hm hs hb

lemma iv_high_x_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply Eventually.of_forall
  intro p
  have h0 : (p.1:ℂ)+R*I≠0 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  have h1 : (p.1:ℂ)+R*I≠1 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  dsimp only
  rw [iv_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma iv_high_z_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.2.1≠0 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ)))
  filter_upwards [hh] with p hp
  have h0 : (a:ℂ)+p.2.1*I≠0 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+p.2.1*I≠1 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  rw [iv_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem iv_raw_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHIVProbe.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((p.1:ℂ)+R*I)
        (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I)) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := iv_uniform_high_x_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  have hh := hc ξ hξ R hR
  have heq := iv_high_x_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem iv_raw_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHIVProbe.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.2.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I)) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := iv_uniform_high_z_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo hξ2 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := hc R hR
  have heq := iv_high_z_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξlo R
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem iv_source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := iv_source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (iv_source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by iv_high_geometry) (hβ.trans_le ha3) (by norm_num)
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

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_source_initial_joint_ordered_at_a

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_raw_uniform_high_x_joins

-- Parametric high adaptation: V2PrincipalPhysical
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open Complex MeasureTheory
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours ProbePrincipalPhysical
local notation "Id" => Ideal HeckeFamily.O
theorem iv_principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact iv_source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=> hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2EulerRegion

set_option linter.unusedVariables false

/-! Actual local Euler formulas on the perturbed x-half-plane.
The proofs use upstream coordinate norm estimates and rational denominator
bounds; no perturbed local bound is assumed. The broad summable17/10 bound
is retained, and the narrower second rectangle has exact decay72599/40000.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem iv_unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (437/500:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(11/5:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(87/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(77/100:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith


lemma iv_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 437/500≤ x.re) (hz : 4/25≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem iv_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|437/500< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := iv_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem iv_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 437/500≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) {w : ℂ|9/10< w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := iv_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem iv_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 437/500≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|4/25< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := iv_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2PrincipalSlot

set_option linter.unusedVariables false

/-! Sharp actual principal and region slot estimates on the new domain.
The unit cancellation and compensated local identity are unchanged. Bounds
use the exact v2 boundary, with a proved rational bracket for local arithmetic.
Correction inverses use the actual broad summable Euler estimate.
All slot/scalar functions are the original upstream mathematical objects.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open Complex
open OAI OAI.SevenEighths
open ProbeEuler ProbeLocal PrincipalSlotEstimate

theorem iv_principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := iv_unramifiedClosed_open_region_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) (hBlo.trans hs) (by iv_high_geometry) (by iv_high_geometry)
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by iv_high_geometry)) (by iv_high_geometry)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem iv_principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h := iv_principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem iv_principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (iv_principal_correction_lower_bound hQ hA hη hs)

theorem iv_principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hl := iv_principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem iv_unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

theorem iv_principal_coord_cancellation {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    (star η * (Q : ℂ) ^ s) * coordD Q η 1 s = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordD
  simp only [star_one, mul_one]
  calc
    _ = (star η * η) * ((Q : ℂ) ^ s * (Q : ℂ) ^ (-s)) := by ring
    _ = 1 := by rw [iv_unit_phase_inverse η hη, ← Complex.cpow_add _ _ hQ0]; simp

theorem iv_principal_V {Q : ℝ} : coordV Q (1 / 6) = (Q : ℂ)⁻¹ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  norm_num [coordV, Complex.cpow_neg_one]

theorem iv_principal_W {Q : ℝ} : coordW Q 1 1 = (Q : ℂ)⁻¹ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp [coordW, Complex.cpow_neg_one]

theorem iv_principal_B_norm {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    ‖star η * (Q : ℂ) ^ s‖ = Q ^ s.re := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [norm_mul, norm_star, hη, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]

theorem iv_compensated_unit_error_bound (V W D P B q : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hBD : B * D = 1) (hWq : W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P‖ ≤ 720 * T := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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

theorem iv_principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(RHIVProbe.boundary : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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
    exact h.trans (by simpa using hpow (-1) 0 (by iv_high_geometry))
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
  have hB := iv_principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by iv_high_geometry)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← iv_principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by iv_high_geometry)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem iv_principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by iv_high_geometry)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← iv_principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by iv_high_geometry)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := iv_principal_marked_error_bounds hQ hA hη hs
  exact iv_compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (iv_principal_coord_cancellation hQ0 η s hη) hWq

theorem iv_principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hn := iv_principal_correction_ne_zero hQ hA hη.le hs
  have he := iv_principal_replacement_error hQ hA hη hs
  have hi := iv_principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(RHIVProbe.boundary : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem iv_actual_target_norm (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) :
    ‖HeckeFamily.elementCoeff η p‖ = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : Finite (HeckeFamily.O ⧸ η.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ η.modulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hp
  unfold HeckeFamily.elementCoeff
  rw [← hu]
  exact FiniteRayExpansion.norm_char_unit η.residue u

theorem iv_actual_principal_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(RHIVProbe.boundary : ℝ)) :=
  iv_principal_slot_error hQ (actualAPhase_norm_le_one η p) (iv_actual_target_norm η p hp) hs

theorem iv_weighted_slot_error {ι : Type*} (S : Finset ι) (w : ι → ℝ) (B : ι → ℂ)
    (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)‖ ≤
      δ * ∑ i ∈ S, w i := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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

theorem iv_weighted_slot_relative_error {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (B : ι → ℂ) (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) (hS : 0 < ∑ i ∈ S, w i) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1‖ ≤ δ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hSc : ((∑ i ∈ S, w i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1 =
      -((∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)) /
        (∑ i ∈ S, w i : ℝ) := by field_simp; ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  exact (div_le_iff₀ hS).mpr (iv_weighted_slot_error S w B δ hw hB)

theorem iv_weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : RHIVProbe.boundary ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-(RHIVProbe.boundary : ℝ))) * ∑ i ∈ S, w i := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply iv_weighted_slot_error S w _ _ hw
  intro i hi
  apply (iv_principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by iv_high_geometry)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by iv_high_geometry)

theorem iv_product_error {κ : Type*} (S : Finset κ) (F : κ → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ) :
    ‖(∏ i ∈ S, F i) - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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

theorem iv_product_error_linear (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) ^ n - 1 ≤ n * 2 ^ n * δ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by iv_high_geometry)
    have hbase : 0 ≤ (1 + δ) ^ n - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith))
    calc
      _ = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by rw [pow_succ]; ring
      _ ≤ 2 * ((n : ℝ) * 2 ^ n * δ) + δ := by
        gcongr
        linarith
      _ ≤ _ := by rw [Nat.cast_succ, pow_succ]; nlinarith

theorem iv_principalScalar_eq {κ : Type*} (S : Finset κ) (M : κ → ℝ) :
    principalScalar S M = ∏ i ∈ S, (-(M i : ℂ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold principalScalar
  rw [Complex.ofReal_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem iv_principalScalar_ne_zero {κ : Type*} (S : Finset κ) (M : κ → ℝ)
    (hM : ∀ i ∈ S, 0 < M i) : principalScalar S M ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [iv_principalScalar_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hM i hi).ne')

theorem iv_fixed_product_relative_error {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [iv_principalScalar_eq, ← Finset.prod_div_distrib]
  apply iv_product_error S _ δ hδ
  intro i hi
  have hMi : (M i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM i hi).ne'
  have hid : W i / (-(M i : ℂ)) - 1 = -(W i + (M i : ℂ)) / (M i : ℂ) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hM i hi)]
  exact (div_le_iff₀ (hM i hi)).mpr (hW i hi)

theorem iv_fixed_product_relative_error_linear {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ S.card * 2 ^ S.card * δ :=
  (iv_fixed_product_relative_error S M W δ hδ hM hW).trans
    (iv_product_error_linear S.card hδ hδ1)

theorem iv_weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-(RHIVProbe.boundary : ℝ))) ^ S.card - 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply iv_fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact iv_weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem iv_principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by iv_high_geometry)
  refine ⟨hV, ?_, ?_⟩
  · rw [iv_principal_W, ← iv_principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem iv_principal_correction_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) =
      localCorrection (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
        (principalMarked Q A η s) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h := iv_principal_geometric_bounds hQ hη hs
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem iv_principal_raw_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    1 / 16 ≤ ‖principalRawFactor Q A η s‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hl := iv_principal_correction_lower_bound hQ hA hη hs
  have hg := iv_principal_geometric_bounds hQ hη hs
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
    rw [iv_principal_correction_eq_raw hQ hη hs]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖principalRawFactor Q A η s‖ *
      (‖1 - coordV Q (1 / 6)‖ * ‖1 - coordW Q 1 1‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖principalRawFactor Q A η s‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem iv_principal_raw_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    principalRawFactor Q A η s ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (iv_principal_raw_lower_bound hQ hA hη hs)

theorem iv_principal_slot_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    principalSlot Q A η s =
      (star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hg := iv_principal_geometric_bounds hQ hη hs
  have hn := iv_principal_correction_ne_zero hQ hA hη hs
  have hp := iv_principal_raw_ne_zero hQ hA hη hs
  have hr := compensatedReplacement_eq_raw (coordV Q (1 / 6)) (coordW Q 1 1)
    (coordD Q η 1 s) (principalMarked Q A η s) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-1 : ℂ))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← iv_principal_correction_eq_raw hQ hη hs] at hr
  unfold principalSlot principalReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem iv_principal_raw_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re) :
    ‖(star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) + 1‖ ≤ 1440 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [← iv_principal_slot_eq_raw hQ hA hη.le hs]
  exact iv_principal_slot_error hQ hA hη hs

theorem iv_weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : RHIVProbe.boundary ≤ s.re)
    (hsmall : 1440 * P ^ (-(RHIVProbe.boundary : ℝ)) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-(RHIVProbe.boundary : ℝ))) :=
  (iv_weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (iv_product_error_linear S.card (by positivity) hsmall)

theorem iv_region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) :=
      iv_unramifiedClosed_open_region_bound Q A η 1 s w z (by linarith) hA hη (by simp) (hBlo.trans hs) (by linarith) (by linarith)
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by iv_high_geometry)) (by iv_high_geometry)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem iv_region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h := iv_region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem iv_region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (iv_region_correction_lower_bound hQ hA hη hs hw hz)

theorem iv_region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hl := iv_region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem iv_region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem iv_region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(RHIVProbe.boundary : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := iv_principal_B_norm hQ0 η s hη
  have hg := iv_region_geometric_bounds hQ hη.le hs hw hz
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
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(RHIVProbe.boundary : ℝ)) := by
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

theorem iv_region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := iv_region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(RHIVProbe.boundary : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := iv_region_marked_error_bounds hQ hA hη hs hw hz
  exact iv_compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (iv_principal_coord_cancellation hQ0 η s hη) hWq

theorem iv_region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hn := iv_region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := iv_region_replacement_error hQ hA hη hs hw hz
  have hi := iv_region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(RHIVProbe.boundary : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

@[simp] theorem iv_region_slot_at_residue (Q : ℝ) (A η s : ℂ) :
    regionSlot Q A η s 1 (1 / 6) = principalSlot Q A η s := rfl

theorem iv_region_correction_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z =
      localCorrection (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
        (regionMarked Q A η s w z) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h := iv_region_geometric_bounds hQ hη hs hw hz
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem iv_region_raw_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 16 ≤ ‖regionRawFactor Q A η s w z‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hl := iv_region_correction_lower_bound hQ hA hη hs hw hz
  have hg := iv_region_geometric_bounds hQ hη hs hw hz
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
    rw [iv_region_correction_eq_raw hQ hη hs hw hz]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖regionRawFactor Q A η s w z‖ *
      (‖1 - coordV Q z‖ * ‖1 - coordW Q 1 w‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖regionRawFactor Q A η s w z‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem iv_region_raw_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionRawFactor Q A η s w z ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (iv_region_raw_lower_bound hQ hA hη hs hw hz)

theorem iv_region_slot_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionSlot Q A η s w z =
      (star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hg := iv_region_geometric_bounds hQ hη hs hw hz
  have hn := iv_region_correction_ne_zero hQ hA hη hs hw hz
  have hp := iv_region_raw_ne_zero hQ hA hη hs hw hz
  have hr := compensatedReplacement_eq_raw (coordV Q z) (coordW Q 1 w)
    (coordD Q η 1 s) (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-w))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← iv_region_correction_eq_raw hQ hη hs hw hz] at hr
  unfold regionSlot regionReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem iv_region_raw_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) + 1‖ ≤ 1440 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [← iv_region_slot_eq_raw hQ hA hη.le hs hw hz]
  exact iv_region_slot_error hQ hA hη hs hw hz

theorem iv_region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have he := iv_region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem iv_weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : RHIVProbe.boundary ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-(RHIVProbe.boundary : ℝ))) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-(RHIVProbe.boundary : ℝ))) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := iv_region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-(RHIVProbe.boundary : ℝ)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by iv_high_geometry)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by iv_high_geometry)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem iv_actual_region_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s w z : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : RHIVProbe.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s w z + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(RHIVProbe.boundary : ℝ)) :=
  iv_region_slot_error hQ (actualAPhase_norm_le_one η p) (iv_actual_target_norm η p hp) hs hw hz

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actual_principal_slot_error
#print axioms RHZeroFreeExtension.AnalyticHigh.iv_weighted_principal_product_error_linear
#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actual_region_slot_error

-- Parametric high adaptation: V2SharpProduct

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

theorem iv_slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : RHIVProbe.boundary≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(RHIVProbe.boundary : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using iv_weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem iv_combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : RHIVProbe.boundary≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(RHIVProbe.boundary : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [norm_mul]
  exact mul_le_mul (iv_global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (iv_slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)


end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2RemainderBounds


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

lemma iv_remainder_active_prime_sum_bound (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hP : 0< P)
    (hthreshold : 480≤ c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤ W x ∧ W x≤ B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let A := T.filter (fun p=> W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A) :
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
  have hp (p : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤ c^(ξ-1)*P^(ξ-1) := by
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

def iv_remainder_slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(RHIVProbe.boundary:ℝ)))*(128*d*B*c^(ξ-1))

lemma iv_remainder_slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) : 0≤ iv_remainder_slotConstant J c d B ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hd0 : 0≤ d := hc.le.trans hd
  unfold iv_remainder_slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=> by positivity)

theorem iv_remainder_window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0< P j)
    (hthreshold : ∀j∈J,480≤ c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j)
    (T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s w z : ℂ)
    (hs : RHIVProbe.boundary≤ s.re) (hw : 19/20≤ w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      iv_remainder_slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let A (j : ι) := (T j).filter (fun p=> W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
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
  have h := iv_combined_slot_bound_sharp η S hS J A
    (fun j p=> W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=> PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(RHIVProbe.boundary:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=> by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (iv_remainder_active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [iv_remainder_slotConstant,←mul_assoc,Finset.prod_mul_distrib]

lemma iv_remainder_scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0≤ X) (hY : 0≤ Y) (hZ : 0≤ Z) :
    0≤ scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0< P j) (hthreshold : ∀j∈J,480≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) (T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
  (ha : RHIVProbe.boundary≤ a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤ C)
  (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma iv_remainder_continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*iv_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hslot := iv_remainder_window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := iv_height_le_joint_s t v u
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
      (iv_remainder_slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma iv_remainder_full_sharp_pointwise (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*iv_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := iv_remainder_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := iv_fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := iv_fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (iv_zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := iv_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := iv_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*iv_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*iv_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := iv_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact iv_height_le_joint_z _ _ _ | exact iv_height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma iv_remainder_residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*iv_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := iv_remainder_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := iv_fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (iv_zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := iv_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := iv_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*iv_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*iv_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact iv_height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma iv_remainder_vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=> F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ (fun w=> F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma iv_remainder_vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=> F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma iv_remainder_normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (RHIVProbe.boundary:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem iv_remainder_full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (RHIVProbe.boundary) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*iv_remainder_slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := iv_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := iv_zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := iv_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := iv_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=> LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*iv_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0≤ A := by dsimp [A];positivity
  have hE : 0≤ E := mul_nonneg (iv_remainder_scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _≤∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact iv_remainder_full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _≤(K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith

theorem iv_remainder_residue_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume)≤ K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (RHIVProbe.boundary) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*iv_remainder_slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := iv_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := iv_zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := iv_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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
    rw [iv_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*iv_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0≤ A := by dsimp [A];positivity
  have hE : 0≤ E := mul_nonneg (iv_remainder_scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _≤∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact iv_remainder_residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _≤(K+1)/|6*ξ-1| *E := by gcongr;linarith

theorem iv_remainder_full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hbound⟩ := iv_remainder_full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0< k := pow_pos iv_remainder_normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [iv_remainder_vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
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

theorem iv_remainder_residue_vertical_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral ξ
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hbound⟩ := iv_remainder_residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0< k := pow_pos iv_remainder_normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [iv_remainder_vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
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

theorem iv_remainder_ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (RHIVProbe.boundary:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e≤5/6) :
    ∃C : ℝ,0< C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
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
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨A,hA,hfirst⟩ := iv_remainder_full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith,by linarith⟩ (by linarith)
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := iv_remainder_residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
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
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (iv_remainder_scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (iv_remainder_scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith

lemma iv_remainder_source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=RHIVProbe.ell) (Z a ξ υ : ℝ) (hZ : 0< Z) :
    scalePower (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(ell j))^ξ) =
    Z^(a-((4+RHIVProbe.b)/6)+(RHIVProbe.h)*(ξ-1/6)+(RHIVProbe.y)*(υ-1)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hp : (∏j∈J,(Z^(ell j))^ξ)=Z^((RHIVProbe.ell)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  iv_ring

lemma iv_remainder_source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=RHIVProbe.ell) (Z a e : ℝ) (hZ : 0< Z) :
    scalePower (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(ell j))^(1/6+e)) = Z^(a-((4+RHIVProbe.b)/6)+(RHIVProbe.h)*e-(RHIVProbe.y/20)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [iv_remainder_source_scale_identity J ell hell Z a (1/6+e) (19/20) hZ]
  congr 1;ring

lemma iv_remainder_source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=RHIVProbe.ell) (Z a : ℝ) (hZ : 0< Z) :
    scalePower (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(ell j))^(33/200:ℝ)) = Z^(a-((4+RHIVProbe.b)/6)-(RHIVProbe.h/600)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [iv_remainder_source_scale_identity J ell hell Z a (33/200) 1 hZ]
  congr 1;ring

lemma iv_remainder_eventual_annulus_threshold {ι : Type*} (η : Character) (J : Finset ι)
    (c : ℝ) (hc : 0< c) (ell : ι→ℝ) (hell : ∀j∈J,0< ell j) :
    ∃Z0 : ℝ,1≤ Z0 ∧ ∀Z : ℝ,Z0≤ Z→∀j∈J,
      480≤ c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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

theorem iv_remainder_source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (RHIVProbe.boundary:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e≤5/6) :
    ∃C : ℝ,0< C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=RHIVProbe.ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0< Z→
    (∀j∈J,480≤ c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-((4+RHIVProbe.b)/6)+(RHIVProbe.h)*e-(RHIVProbe.y/20))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤ C*Z^(a-((4+RHIVProbe.b)/6)-(RHIVProbe.h/600))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hbound⟩ := iv_remainder_ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=> Z^(ell j)) (fun _ _=> Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [iv_remainder_source_w_scale_identity J ell hell Z a e hZ,iv_remainder_source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

lemma iv_remainder_source_w_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-((4+RHIVProbe.b)/6)+(RHIVProbe.h)*e-(RHIVProbe.y/20)≤β-((4+RHIVProbe.b)/6)-1/3000 := by
  have hh : RHIVProbe.h ≤ 1 := by iv_high_geometry
  have hy : (2/5 : ℝ) ≤ RHIVProbe.y := by iv_high_geometry
  have hl : 0 ≤ RHIVProbe.h := by iv_high_geometry
  have hp : RHIVProbe.h*e ≤ RHIVProbe.h*(1/1000) := mul_le_mul_of_nonneg_left he hl
  linarith

lemma iv_remainder_source_z_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-((4+RHIVProbe.b)/6)-(RHIVProbe.h/600)≤β-((4+RHIVProbe.b)/6)-1/3000 := by
  have hh : (4/5 : ℝ) ≤ RHIVProbe.h := by iv_high_geometry
  linarith

theorem iv_remainder_source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (RHIVProbe.boundary:ℝ) 2) :
    ∃C : ℝ,0< C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=RHIVProbe.ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤ Z→
    (∀j∈J,480≤ c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> verticalIntegral (1/6+e)
      (fun z=> verticalIntegral (19/20) (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=> verticalIntegral (33/200) (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hbound⟩ := iv_remainder_source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (iv_remainder_source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (iv_remainder_source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end RHZeroFreeExtension.AnalyticHigh

end

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_remainder_source_remainders_strict_saving

-- Parametric high adaptation: V2PrincipalPhysicalRemainder
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

theorem iv_physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e≤1/1000)
    (ha : RHIVProbe.boundary< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=RHIVProbe.ell → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤ W j x ∧ W j x≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤ Z → (∀j,480≤ c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryGenerator (P j).val.val)
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := iv_remainder_source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0< Z := by linarith
  have hb := hbound ell hell W (fun j _=> hW j) (fun j _=> hsupp j) T (fun j _ p hp=> hT j p hp)
    Z hZ (fun j _=> hthreshold j) (fun j _=> hmod j)
  dsimp only at hb
  have heq := iv_principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (HeckeZeroSupremum.beta+e) e
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
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000)
  apply hn.trans
  have hCe : C≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤ Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_physical_principal_residue_remainder

-- Parametric high adaptation: V2SignalShift
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI OAI.SevenEighths
open HeckeSignalShift
namespace IVHeckeSignalShift
open HeckeFamily HeckeSignal Continuation

theorem iv_quotient_holomorphic (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary < s.re}) {a : ℝ}
    (ha : (RHIVProbe.boundary : ℝ)< a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  exact ((hH.differentiableAt ((Complex.isOpen_re_gt (RHIVProbe.boundary)).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem iv_quotient_polynomial_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, RHIVProbe.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (n : ℕ) (ha : (RHIVProbe.boundary : ℝ)< a) (_hC : 0 ≤ C)
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

theorem iv_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary< s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (RHIVProbe.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hboundary : 5/6< RHIVProbe.boundary := by iv_high_geometry
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ n ha2
    (gaussianContourIntegrand_differentiableOn (iv_quotient_holomorphic χ H hH ha hβ) c hx0)
    (C := x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*((3/2)*C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x^(b+c) ≤ x^(2+c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have he : Real.exp ((b-5/6)^2) ≤ Real.exp ((2-5/6 : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hb'.1,hb'.2]
  have hq := iv_quotient_polynomial_bound χ H hb n ha hC hR
    (s := (b : ℂ)+y*I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)) *
        (((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring

theorem iv_signal_bound_at_infinity (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary< s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (RHIVProbe.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    ‖signal χ H c x‖ ≤ infinityConstant a C n*x^(a+c) := by
  have hboundary : 5/6< RHIVProbe.boundary := by iv_high_geometry
  have hx0 : 0 < x := by linarith
  rw [iv_contour_shift_left χ H hH hb c a C n ha ha2 hβ hC hR hx, norm_mul]
  have hint := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable n).const_mul
      (x^(a+c)*Real.exp ((a-5/6)^2)*((3/2)*C)))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
      have hq := iv_quotient_polynomial_bound χ H hb n ha hC hR
        (s := (a : ℂ)+y*I) (by simpa using And.intro (le_refl a) ha2)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
      calc
        _ ≤ x^(a+c)*Real.exp ((a-5/6)^2)*(((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
        _ = _ := by unfold polynomialGaussian; ring))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 ; unfold infinityConstant ; ring

theorem iv_signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary< s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : (RHIVProbe.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n)) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  apply IsBigO.of_bound (infinityConstant a C n)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := iv_signal_bound_at_infinity χ H hH hb c a C n ha ha2 hβ hC hR hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ x by linarith) (a+c))] using h

#print axioms iv_contour_shift_left
#print axioms iv_signal_bound_at_infinity

end IVHeckeSignalShift

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2SignalBounds
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeSignalBounds
namespace IVHeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem iv_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary< s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (RHIVProbe.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) {x : ℝ} (hx : 1≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact IVHeckeSignalShift.iv_contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem iv_signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary< s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (RHIVProbe.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact IVHeckeSignalShift.iv_signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end IVHeckeSignalBounds

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2PhysicalNormalization

/-! Actual double-residue normalization for the v2 physical probe. The pole
is still 1/6. Changing b changes the signal intercept to -(4+b)/6. -/
namespace RHIVProbe
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Complex
open OAI OAI.SevenEighths
open HeckeFamily PrincipalSlotEstimate ProbePhysical HeckeSignal
open PrincipalSignalComparison PrincipalMellinResidues
variable {kappa iota : Type*}

def slotResidue (chi : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset kappa) (T : kappa → Finset iota) (w Q : kappa → iota → ℝ)
    (A eta : kappa → iota → ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)-(((4+b)/6 : ℝ) : ℂ))*
      Complex.exp ((((a : ℂ)+t*I)-5/6)^2)*H ((a : ℂ)+t*I)/
      LFunction chi ((a : ℂ)+t*I)*slotRatio S T w Q A eta ((a : ℂ)+t*I)

theorem source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^x : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*
        (Z : ℂ)^(s-(((4+b)/6 : ℝ) : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le x (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  simp only [x]
  push_cast
  ring

theorem normalized_source_double_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (chi : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset kappa) (T : kappa → Finset iota) (w Q : kappa → iota → ℝ)
    (A eta : kappa → iota → ℂ) (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A eta s) :
    (fixedPrincipalResidue M^2/6*
      sourceMultiplier W0 W1 (Z^x) Y Z chi s H B 1 (1/6))/
      (sourceResidueConstant W0 W1 M*
        (Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s-(((4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*
        H 1 (1/6)/LFunction chi s*slotRatio S T w Q A eta s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity hZ s
  have hz : (Z : ℂ)^(((-ell/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M*(sourceResidueConstant W0 W1 M)⁻¹)*
      ((Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*((Z : ℂ)^(((-ell/6 : ℝ) : ℂ)))⁻¹)*
      ((Z : ℂ)^(s-(((4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*
        H 1 (1/6)*(LFunction chi s)⁻¹*
        (slotProduct S T w Q A eta s*(PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem sourceResidueIntegral_normalized (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (chi : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset kappa) (T : kappa → Finset iota)
    (w Q : kappa → iota → ℝ) (A eta : kappa → iota → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0) (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A eta ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M chi a (Z^x) Y Z H B/
      (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
        slotResidue chi (fun s => H s 1 (1/6)) a Z S T w Q A eta := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral RHIVProbe.slotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat] using
    normalized_source_double_residue W0 W1 M chi Y Z hZ ((a : ℂ)+t*I)
      (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) S T w Q A eta hc (hB t)

#print axioms source_power_identity
#print axioms normalized_source_double_residue
#print axioms sourceResidueIntegral_normalized
end
end RHIVProbe

-- Parametric high adaptation: V2GlobalCorrection

set_option linter.unusedVariables false

/-! The genuine upstream idealClosedCorrection and globalClosedCorrection
on the new half-plane. The original summable prime majorant and original
cutoff are reused because the new local theorem retains the same17/10 decay.
No product bound, analyticity, or perturbed contraction is assumed.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma iv_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply iv_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem iv_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=> iv_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma iv_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z
  let B := fun P : {P : OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    iv_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem iv_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> globalClosedCorrection η S x w z) {x : ℂ|437/500< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply iv_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact iv_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem iv_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 437/500≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply iv_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact iv_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem iv_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=> globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply iv_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact iv_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2SourceAnalytic

/-! Genuine source Euler correction at the radical v2 boundary. The wider
rational half-plane Re(s)>437/500 retains the original summable prime bound
and source exclusion tail. No analyticity or product contraction is assumed. -/
namespace RHIVProbe
noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler PrincipalSignalComparison
open RHZeroFreeExtension.AnalyticHigh
lemma correction_boundary_lower : (437/500 : ℝ) < boundary := by iv_high_geometry

theorem source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) :
    AnalyticOnNhd ℂ (sourceCorrection eta S) {z : ℂ | boundary < z.re} := by
  apply (iv_globalClosedCorrection_analytic_x eta S hS.tail 1 (1/6)
    (by norm_num) (by norm_num)).mono
  intro z hz
  exact lt_trans correction_boundary_lower hz

theorem source_contraction (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) (z : ℂ) (hz : boundary < z.re) :
    ‖sourceCorrection eta S z-1‖ ≤ (1/2 : ℝ) :=
  iv_globalClosedCorrection_bound eta S hS.tail z 1 (1/6)
    (by linarith [correction_boundary_lower]) (by norm_num) (by norm_num)

theorem source_nonzero (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) (z : ℂ) (hz : boundary < z.re) :
    sourceCorrection eta S z ≠ 0 := by
  have hb := source_contraction S hS eta z hz
  intro hn
  rw [hn, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

#print axioms source_analytic
#print axioms source_contraction
#print axioms source_nonzero
end
end RHIVProbe

-- Parametric high adaptation: V2Kernel

namespace RHIVProbe
noncomputable section
open MeasureTheory Complex
open OAI OAI.SevenEighths
open HeckeFamily HeckeSignal HeckeSignalShift Continuation
open RHZeroFreeExtension.AnalyticHigh.IVHeckeSignalShift
def kernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-((4+b)/6)) Z ((a : ℂ)+t*I)

def kernelEnvelope (a C Z : ℝ) : ℝ :=
  Z^(a-(4+b)/6) * Real.exp ((a-5/6)^2) * ((3/2)*C)

theorem kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | boundary < s.re})
    {a Z : ℝ} (ha : boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (iv_quotient_holomorphic χ H hH ha hβ) (-((4+b)/6)) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : boundary < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := iv_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-((4+b)/6)))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | boundary < s.re})
    (hb : ∀ s : ℂ, boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound χ H hb ha ha2 hC hZ hR))


theorem source_kernel_integrable (S : Finset (Ideal HeckeFamily.O))
    (hS : ProbePhysical.SourceExclusions S) (chi : Character)
    {a Z : ℝ} (ha : boundary< a) (ha2 : a≤2)
    (hbeta : HeckeZeroSupremum.beta< a) (hZ : 0< Z) :
    Integrable (kernel chi (PrincipalSignalComparison.sourceCorrection chi S) a Z) := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound chi a hbeta
  exact kernel_integrable chi (PrincipalSignalComparison.sourceCorrection chi S)
    (source_analytic S hS chi).differentiableOn (source_contraction S hS chi)
    ha ha2 hbeta hC hZ hR

#print axioms source_kernel_integrable
#print axioms kernel_continuous
#print axioms kernel_norm_bound
#print axioms kernel_integrable
end
end RHIVProbe

-- Parametric high adaptation: V2PrincipalSignalComparison
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
open OAI OAI.SevenEighths
open PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open ProbePhysical ActualEisensteinCubic CompletedGauss PrincipalMellinResidues

variable {κ ι : Type*}

def iv_actualSlotResidue (eta : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (a Z : ℝ) (S : Finset κ)
    (T : κ → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (w : κ → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) : ℂ :=
  RHIVProbe.slotResidue (eta.excludePrimes E hE.prime) (sourceCorrection eta E) a Z S T w
    (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase eta (primaryGenerator p.val)) (fun _ p => idealCoeff eta p.val)

theorem iv_raw_inverse_ae_reciprocal (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem iv_raw_quotient_integral_eq (χ : Character) (a : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply integral_congr_ae
  filter_upwards [iv_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [div_eq_mul_inv, ht]


structure iv_SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(RHIVProbe.boundary : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

theorem iv_slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : iv_SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem iv_slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : iv_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : RHIVProbe.boundary ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    iv_weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem iv_slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : iv_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : RHIVProbe.boundary ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [iv_slotRatio_error S T w Q A η h hs]

theorem iv_principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHIVProbe.boundary ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := iv_principal_geometric_bounds hQ hη hs
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
    (iv_principal_correction_ne_zero hQ hA hη hs)

theorem iv_slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : iv_SlotBounds S T w Q A η P) {a : ℝ} (ha : RHIVProbe.boundary ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (iv_principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio PrincipalSignalComparison.slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

theorem iv_slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    RHIVProbe.slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-((4+RHIVProbe.b)/6)) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold RHIVProbe.slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [iv_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

theorem iv_kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary < s.re})
    {a Z : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (RHIVProbe.kernel χ H a Z) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hh := gaussianContourIntegrand_differentiableOn
    (IVHeckeSignalShift.iv_quotient_holomorphic χ H hH ha hβ) (-((4+RHIVProbe.b)/6)) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem iv_kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, RHIVProbe.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖RHIVProbe.kernel χ H a Z t‖ ≤ RHIVProbe.kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hq := IVHeckeSignalShift.iv_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold RHIVProbe.kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-((4+RHIVProbe.b)/6)))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold RHIVProbe.kernelEnvelope polynomialGaussian; ring_nf

theorem iv_kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary < s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (RHIVProbe.kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (RHIVProbe.kernelEnvelope a C Z)).mono'
    (iv_kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (iv_kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem iv_slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary < s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : iv_SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => RHIVProbe.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖RHIVProbe.slotResidue χ H a Z S T w Q A η - signal χ H (-((4+RHIVProbe.b)/6)) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-((4+RHIVProbe.b)/6)) * P^(-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := iv_kernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := iv_slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := iv_slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := iv_slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : RHIVProbe.slotResidue χ H a Z S T w Q A η - signal χ H (-((4+RHIVProbe.b)/6)) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        RHIVProbe.kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [iv_slotResidue_eq_reciprocal,
      IVHeckeSignalBounds.iv_contour_shift_left χ H hH hb (-((4+RHIVProbe.b)/6)) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, RHIVProbe.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, RHIVProbe.kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change RHIVProbe.kernel χ H a Z t * _ - RHIVProbe.kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(RHIVProbe.boundary : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖RHIVProbe.kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (RHIVProbe.kernelEnvelope a C Z * (slotErrorConstant S * P^(-(RHIVProbe.boundary : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (RHIVProbe.kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(RHIVProbe.boundary : ℝ))) :=
        mul_le_mul (iv_kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold RHIVProbe.kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (RHIVProbe.kernelEnvelope a C Z * (slotErrorConstant S * P^(-(RHIVProbe.boundary : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold RHIVProbe.kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem iv_exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary < s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), iv_SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => RHIVProbe.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖RHIVProbe.slotResidue χ H a Z S T w Q A η - signal χ H (-((4+RHIVProbe.b)/6)) Z‖ ≤
          D * Z^(a-((4+RHIVProbe.b)/6)) * P^(-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact iv_slotResidue_bound_of_reciprocal_bound χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem iv_raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => RHIVProbe.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-(((4+RHIVProbe.b)/6 : ℝ) : ℂ)) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply hi.congr
  filter_upwards [iv_raw_inverse_ae_reciprocal χ a] with t ht
  unfold RHIVProbe.kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

theorem iv_source_double_residue_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      PrincipalSignalComparison.slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => RHIVProbe.kernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(RHIVProbe.x : ℝ)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hiraw := iv_raw_slot_integrable χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := RHIVProbe.ell))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (RHIVProbe.ell) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (RHIVProbe.normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

private instance : IsPrincipalIdealRing HeckeFamily.O := IsCyclotomicExtension.Rat.three_pid HeckeFamily.K

theorem iv_idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
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

theorem iv_prime_coprime_of_norm_gt (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

theorem iv_annularPrimeWeight_nonneg (W : ℝ → ℝ) (hW : ∀ x, 0 ≤ W x)
    (scale : ℝ) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 0 ≤ annularPrimeWeight W scale P :=
  mul_nonneg (hW _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem iv_annularPrimeWeight_norm_lower (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : c*scale ≤ (Ideal.absNorm P.val : ℝ) :=
  (le_div_iff₀ hscale).mp (hW _ (left_ne_zero_of_mul hw))

theorem iv_annularPrimeWeight_target_unit (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (η : Character)
    (hthreshold : (Ideal.absNorm η.modulus : ℝ) < c*scale) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : ‖idealCoeff η P.val‖ = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val := by
    exact_mod_cast hthreshold.trans_le (iv_annularPrimeWeight_norm_lower W c scale hscale hW P hw)
  exact iv_idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (iv_prime_coprime_of_norm_gt η P hN)

theorem iv_sourceCorrection_eq_principal (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) : sourceCorrection η E = principalCorrection η E := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  funext s
  exact source_globalCorrection_principal E hE η s

theorem iv_sourceCorrection_differentiable (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | RHIVProbe.boundary < s.re} :=
  (iv_principalDomain_globalClosedCorrection_analytic_x η E hE.tail 1 (1/6) (by norm_num) (by norm_num)).differentiableOn

theorem iv_sourceCorrection_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : RHIVProbe.boundary < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 :=
  iv_principalDomain_globalClosedCorrection_bound η E hE.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)

theorem iv_actual_principal_slot (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s : ℂ) :
    compensatedReplacement (coordV (Ideal.absNorm P.val) (1/6))
      (coordW (Ideal.absNorm P.val) 1 1) (coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s)
      (idealMarkedClosed η P s 1 (1/6))
      (star (idealCoeff η P.val) * (Ideal.absNorm P.val : ℂ)^s)
      ((Ideal.absNorm P.val : ℂ)^(-1 : ℂ)) / idealClosedCorrection η P s 1 (1/6) =
      principalSlot (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem iv_exists_actualSlotResidue_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) {a : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (w : κ → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (P Z : ℝ),
      480 ≤ P → 1440 * P^(-(RHIVProbe.boundary : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      ‖iv_actualSlotResidue η E hE a Z S T w -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHIVProbe.b)/6)) Z‖ ≤
        D * Z^(a-((4+RHIVProbe.b)/6)) * P^(-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨D, hD, hb⟩ := iv_exists_slotResidue_bound (ι := OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (iv_sourceCorrection_differentiable η E hE) (iv_sourceCorrection_bound η E hE)
    ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro T w P Z hP hsmall hw hnorm hcop hmass hZ
  exact (hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z
    ⟨hP, hsmall, hw, hnorm, fun j hj p hp => actualAPhase_norm_le_one η _,
      fun j hj p hp => iv_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp),
      hmass⟩ hZ).2

open PrincipalMellinResidues

theorem iv_slotMass_active (T : κ → Finset ι) (w : κ → ι → ℝ) :
    slotMass (activePools T w) w = slotMass T w := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  funext j
  simp only [slotMass, activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem iv_slotProduct_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    PrincipalSignalComparison.slotProduct S (activePools T w) w Q A η s = PrincipalSignalComparison.slotProduct S T w Q A η s := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply Finset.prod_congr rfl
  intro j hj
  simp only [activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem iv_slotRatio_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotRatio S (activePools T w) w Q A η s = slotRatio S T w Q A η s := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [slotRatio, slotRatio, iv_slotProduct_active, iv_slotMass_active]

theorem iv_slotResidue_active (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    RHIVProbe.slotResidue χ H a Z S (activePools T w) w Q A η = RHIVProbe.slotResidue χ H a Z S T w Q A η := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [RHIVProbe.slotResidue, iv_slotRatio_active]

theorem iv_slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (RHIVProbe.boundary)*ell)
    (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHIVProbe.boundary < s.re})
    (hb : ∀ s : ℂ, RHIVProbe.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      iv_SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => RHIVProbe.slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H (-((4+RHIVProbe.b)/6)) Z) =O[atTop] (fun Z : ℝ => Z^(a-((4+RHIVProbe.b)/6)-saving)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨D, hD, hd⟩ := iv_exists_slotResidue_bound χ H hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(RHIVProbe.boundary : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [iv_slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(RHIVProbe.boundary : ℝ)) = c0^(-(RHIVProbe.boundary : ℝ))*Z^(ell*(-(RHIVProbe.boundary : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a-((4+RHIVProbe.b)/6)+ell*(-(RHIVProbe.boundary : ℝ))) ≤ Z^(a-((4+RHIVProbe.b)/6)-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖RHIVProbe.slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H (-((4+RHIVProbe.b)/6)) Z‖ ≤ (D*c0^(-(RHIVProbe.boundary : ℝ)))*Z^(a-((4+RHIVProbe.b)/6)-saving) := by
    calc
      _ ≤ D*Z^(a-((4+RHIVProbe.b)/6))*(c0^(-(RHIVProbe.boundary : ℝ))*Z^(ell*(-(RHIVProbe.boundary : ℝ)))) := he
      _ = (D*c0^(-(RHIVProbe.boundary : ℝ)))*Z^(a-((4+RHIVProbe.b)/6)+ell*(-(RHIVProbe.boundary : ℝ))) := by
        rw [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'

theorem iv_actualSlotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (RHIVProbe.boundary)*ell)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (w : ℝ → κ → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      iv_SlotBounds S (activePools (T Z) (w Z)) (w Z) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
        (c0*Z^ell)) :
    (fun Z : ℝ => iv_actualSlotResidue η E hE a Z S (T Z) (w Z) -
        signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHIVProbe.b)/6)) Z)
      =O[atTop] (fun Z : ℝ => Z^(a-((4+RHIVProbe.b)/6)-saving)) :=
  iv_slotResidue_isBigO S c0 ell saving hc0 hsaving (η.excludePrimes E hE.prime)
    (sourceCorrection η E) (iv_sourceCorrection_differentiable η E hE)
    (iv_sourceCorrection_bound η E hE) ha ha2 hβ T w
    (fun _ _ p => Ideal.absNorm p.val)
    (fun _ _ p => actualAPhase η (primaryGenerator p.val)) (fun _ _ p => idealCoeff η p.val) hdata

theorem iv_fixedPrincipal_product_eq (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    fixedPrincipal (∏ p ∈ E, p) = fixedSourcePrincipal E hE.prime := rfl

theorem iv_exists_normalized_actual_source_bound (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : RHIVProbe.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
      (w : κ → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(RHIVProbe.boundary : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = PrincipalSignalComparison.slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (RHIVProbe.ell) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(RHIVProbe.x : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(RHIVProbe.x : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHIVProbe.b)/6)) Z‖ ≤
        D * Z^(a-((4+RHIVProbe.b)/6)) * P^(-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := iv_exists_slotResidue_bound (ι := OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (iv_sourceCorrection_differentiable η E hE) (iv_sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := RHIVProbe.sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : iv_SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => iv_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact iv_source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_exists_normalized_actual_source_bound
#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actualSlotResidue_isBigO

-- Parametric high adaptation: V2PrincipalResidueActual
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
open OAI OAI.SevenEighths
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss ProbePrincipalResidueActual
theorem iv_normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : RHIVProbe.boundary< a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta< a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0< a0 → 0< a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤ P → 1440*P^(-(RHIVProbe.boundary : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤ W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0< slotMass T (residueWeights W scale) j) → 1≤ Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (RHIVProbe.ell) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        sourceMultiplier W0 W1 (Z^(RHIVProbe.x : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(RHIVProbe.x : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHIVProbe.b)/6)) Z‖ ≤
        D*Z^(a-((4+RHIVProbe.b)/6))*P^(-(RHIVProbe.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := iv_exists_normalized_actual_source_bound E hE η ha ha2 hβ S
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

-- Parametric high adaptation: V2RayPoolThresholds

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
open OAI OAI.SevenEighths
open ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem iv_power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0< c) (hd : c≤ d) (hmin : 0< ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤ Z ∧ 480≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(RHIVProbe.boundary:ℝ))≤1 ∧
      (∀j,480≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)< c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(RHIVProbe.boundary:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by iv_high_geometry : (0:ℝ)< RHIVProbe.boundary)).comp ht).const_mul (1440:ℝ)
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

-- Parametric high adaptation: V2PrincipalNormalized
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma iv_normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤ c) (hA : ‖A-R‖≤ c) (hN : ‖N⁻¹‖≤ v)
    (hR : ‖R/N-F‖≤ d) : ‖A/N-F‖≤ c*v+d := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem iv_actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hmin : 0< ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=RHIVProbe.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0< e) (hehi : e≤1/1000) (hnu : 0< nu)
    (ha : RHIVProbe.boundary< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryGenerator (P j).val.val)
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-((4+RHIVProbe.b)/6)) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000+nu)+
        Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := iv_physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := iv_normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(RHIVProbe.boundary:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [iv_power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=> hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=> c) (fun _=> d) ell (fun _=> hc) (fun _=> hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0< Z := by linarith
  let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
    (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=> Z^(ell j)) (c*Z^ellMin) (Z^(RHIVProbe.y:ℝ)) Z h480 hsmall
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
  have hh := iv_normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(RHIVProbe.boundary:ℝ))=c^(-(RHIVProbe.boundary:ℝ))*Z^(-(RHIVProbe.boundary:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-((4+RHIVProbe.b)/6))*(c*Z^ellMin)^(-(RHIVProbe.boundary:ℝ))=
      (D*c^(-(RHIVProbe.boundary:ℝ)))*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin=
      (HeckeZeroSupremum.beta+e-((4+RHIVProbe.b)/6))+(-(RHIVProbe.boundary:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤ C := by
    dsimp [C]
    have : 0≤ D*c^(-(RHIVProbe.boundary:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(RHIVProbe.boundary:ℝ))≤ C := by
    dsimp [C]
    have : 0≤ C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)-1/3000+nu)+
        C*Z^(HeckeZeroSupremum.beta-((4+RHIVProbe.b)/6)+e-(RHIVProbe.boundary)*ellMin) := by gcongr
    _ = _ := by ring
end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_actual_ray_principal_comparison

-- Parametric high adaptation: V2TransportCentralErrorSaving
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma iv_central_prime_tuple_count {K : ℕ} (T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(RHIVProbe.ell:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(RHIVProbe.ell:ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
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


lemma iv_central_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^(RHIVProbe.x:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(RHIVProbe.y:ℝ))^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by
    have haY := mul_nonneg hYpos.le ha
    have heY := mul_nonneg hYpos.le he
    nlinarith only [hXhi, haY, heY])

lemma iv_central_prime_product_bound {K : ℕ} (P : Fin K→OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(RHIVProbe.ell:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^(RHIVProbe.ell:ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma iv_central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((RHIVProbe.h:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(RHIVProbe.ell:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^((6+3*RHIVProbe.ell):ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (RHIVProbe.h:ℝ)+ζ≤1 by linarith))
  have hp := iv_central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=> Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(RHIVProbe.ell:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((RHIVProbe.ell:ℝ)*(3:ℕ))=Z^((6+3*RHIVProbe.ell):ℝ) := by rw [←Real.rpow_add hZ0]; congr 1; ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCubeErrorSaving
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem iv_original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((RHIVProbe.h:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(RHIVProbe.ell:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨N,hN⟩ := exists_nat_gt ((((8+3*RHIVProbe.ell):ℝ)+saving)/τ)
  have hN' : ((8+3*RHIVProbe.ell):ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := iv_central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := iv_central_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^((8+3*RHIVProbe.ell):ℝ)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^((6+3*RHIVProbe.ell):ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^((8+3*RHIVProbe.ell):ℝ)/height H^N) := by
      have hh : Z^((6+3*RHIVProbe.ell):ℝ)*Z^(2:ℝ)=Z^((8+3*RHIVProbe.ell):ℝ) := by rw [←Real.rpow_add hZ0]; congr 1; ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^((8+3*RHIVProbe.ell):ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportCubeFiniteError
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem iv_finite_cube_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48) (hA : 0≤ A)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((RHIVProbe.h:ℝ)+ζ)) →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(RHIVProbe.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=> Z^(length j)) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=> Z^(length j)) W0 W1
          (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hrow⟩ := iv_original_row_cube_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((RHIVProbe.h:ℝ)+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (RHIVProbe.h:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (iv_central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (RHIVProbe.ell:ℝ)≤1 by linarith)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (a u) e (H u)‖≤ E := by
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
        rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
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


end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportTailScales
set_option linter.unusedVariables false
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily
lemma iv_small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(RHIVProbe.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(RHIVProbe.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+RHIVProbe.canonicalOffset+(17/50:ℝ)-1)*
        (Z^(RHIVProbe.y:ℝ))^((1/2:ℝ)-1))=Z^(β-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  dsimp only [RHIVProbe.sourceSaving, RHIVProbe.smallSaving, RHIVProbe.canonicalOffset, RHIVProbe.largeConstant]
  iv_ring

lemma iv_small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤ Z) (hU : 1≤ U)
    (hUsmall : U≤ Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(RHIVProbe.ell:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(RHIVProbe.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+RHIVProbe.canonicalOffset+(17/50:ℝ)-1)*
        (Z^(RHIVProbe.y:ℝ))^((1/2:ℝ)-1))≤ Z^(β-((4+RHIVProbe.b)/6)-RHIVProbe.smallSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤ Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,iv_small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-((4+RHIVProbe.b)/6)-RHIVProbe.sourceSaving+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1; dsimp only [RHIVProbe.smallSaving]; ring

lemma iv_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(RHIVProbe.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(RHIVProbe.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(RHIVProbe.y:ℝ))^((2:ℝ)-1))=
      Z^((RHIVProbe.largeConstant:ℝ)+(RHIVProbe.h:ℝ)*b) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  dsimp only [RHIVProbe.sourceSaving, RHIVProbe.smallSaving, RHIVProbe.canonicalOffset, RHIVProbe.largeConstant]
  iv_ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportLargeDyad
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem iv_large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
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
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((RHIVProbe.largeConstant:ℝ)+(RHIVProbe.h:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤ Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=> Z^(length i)) hYp W hWS hWB
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(RHIVProbe.x:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(RHIVProbe.y:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [iv_large_source_scale Z hZ0 length hl r];ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportGeometricTail
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily

lemma iv_large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0< Z) (n : ℕ) :
    Z^((RHIVProbe.largeConstant:ℝ)+(RHIVProbe.h:ℝ)*r)*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((RHIVProbe.largeConstant:ℝ)+((RHIVProbe.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma iv_large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0< Z) (hr : 8/5+δ< r) :
    Summable (fun n : ℕ=> Z^((RHIVProbe.largeConstant:ℝ)+(RHIVProbe.h:ℝ)*r)*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  simp_rw [iv_large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma iv_large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0< Z) (hr : 8/5+δ< r) :
    (∑'n : ℕ,Z^((RHIVProbe.largeConstant:ℝ)+(RHIVProbe.h:ℝ)*r)*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((RHIVProbe.largeConstant:ℝ)+((RHIVProbe.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  simp_rw [iv_large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma iv_exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤ r ∧ 8/5+δ< r ∧
      (RHIVProbe.largeConstant:ℝ)+((RHIVProbe.h:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((RHIVProbe.largeConstant:ℝ)+((RHIVProbe.h:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportLargeTail
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma iv_absolutePhysicalDyadIntegral_nonneg {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) :
    0≤ absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  apply integral_nonneg
  intro p
  exact mul_nonneg (norm_nonneg _) (physicalDyadNorm_nonneg S hS hmax η R T hT W Yp _ _ _)

theorem iv_large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤ r) (hr' : 8/5+δ< r) (hζ : 0<ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((RHIVProbe.largeConstant:ℝ)+((RHIVProbe.h:ℝ)+ζ)*(8/5+δ)-ζ*r) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨C,hC,hmain⟩ := iv_large_physical_dyad_bound K δ a b B r hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℝ := fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
    (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r
  let g : ℕ→ℝ := fun n=> Z^((RHIVProbe.largeConstant:ℝ)+(RHIVProbe.h:ℝ)*r)*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤ f n := iv_absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤ A*g n := by
    have hUn : 1≤ Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    simpa only [A,g,mul_assoc] using hh
  have hg : Summable g := iv_large_geometric_summable Z ζ δ r hZ0 hr'
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^((RHIVProbe.largeConstant:ℝ)+((RHIVProbe.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      rw [show (∑'n,g n)=_ from iv_large_geometric_sum Z ζ δ r hZ0 hr']
    _ = _ := by dsimp [A];ring

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportLargeSaving
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem iv_large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤ r ∧ 0< C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((RHIVProbe.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(RHIVProbe.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(RHIVProbe.x:ℝ)) (Z^(RHIVProbe.y:ℝ)) Z 2 2 r)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHIVProbe.transport_geometry
  have hCanonical : RHIVProbe.boundary+RHIVProbe.canonicalOffset = 7/8 := by dsimp [RHIVProbe.canonicalOffset]; ring
  obtain ⟨r,hr,hr',hpower⟩ := iv_exists_large_tail_line ζ δ saving hζ
  obtain ⟨C,hC,hmain⟩ := iv_large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2TransportPhysicalLargeTail
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem iv_large_original_physical_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B)
