    (((whittaker_bound_integrable b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ => (whittakerIntegrand_hasDerivAt freq w p).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma weightedWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := weightedWhittakerIntegrand_integrable ρ freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        rw [whittakerIntegrand_eq freq s v hv.1 z]
        ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerAverage_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (weightedWhittakerProduct_eq_average ρ freq w hw).symm
  exact (weightedWhittakerProduct_differentiableAt ρ freq s hs).congr_of_eventuallyEq he

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

theorem kernelCompact_projection_measure_bound (K : Set HyperbolicSpace) (hK : IsCompact K) :
    ∃N : ℕ,Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (N:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel := by
  choose e he heq using kernelQuotient_localHomeomorph
  have hcover : K⊆⋃w : HyperbolicSpace,(e w).source := by
    intro w _
    exact Set.mem_iUnion.mpr ⟨w,he w⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun w => (e w).source) (fun w => (e w).open_source) hcover
  have hinj (w : HyperbolicSpace) :
      Set.InjOn (integralOrbitProjection globalKubotaKernel) (e w).source := by
    rw [heq w]
    exact (e w).injOn
  refine ⟨t.card,Measure.le_iff.mpr ?_⟩
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.smul_apply]
  change hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ K)≤
    (t.card:ℝ≥0∞)*integralQuotientVolume globalKubotaKernel B
  calc
    _ ≤ hyperbolicVolume (⋃w∈t,(integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) := by
      apply measure_mono
      rintro w ⟨hw,hK⟩
      obtain ⟨v,hv,hwv⟩ := Set.mem_iUnion₂.mp (ht hK)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,hw,hwv⟩
    _ ≤ ∑w∈t,hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑_w∈t,integralQuotientVolume globalKubotaKernel B := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := kernelProjection_measurePreserving_on (e w).source (e w).open_source.measurableSet (hinj w)
      rw [←Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),
        ←Measure.map_apply (measurable_integralOrbitProjection _) hB,hm.map_eq]
      exact Measure.restrict_le_self B
    _ = _ := by simp [nsmul_eq_mul]

section DominatedComplexL2
variable {α : Type*} [MeasurableSpace α] {«μ» ν : Measure α} {c : ℝ≥0∞}

def dominatedComplexL2 (hc : c≠⊤) (h : ν≤c•«μ») : Lp ℂ 2 «μ»→L[ℂ]Lp ℂ 2 ν where
  toFun := Lp.LpToLpOfMeasureLeSMul hc h
  map_add' := map_add (Lp.LpToLpOfMeasureLeSMul hc h)
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z•f),
      Lp.coeFn_LpToLpOfMeasureLeSMul hc h f,
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul hc h f),
      (Measure.absolutelyContinuous_of_le_smul h).ae_eq (Lp.coeFn_smul z f)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,Pi.smul_apply] at *
    rw [h1,h3,h2,h4]
  cont := (Lp.LpToLpOfMeasureLeSMul hc h).continuous

lemma dominatedComplexL2_ae (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    dominatedComplexL2 hc h f=ᵐ[ν]f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hc h f

lemma dominatedComplexL2_norm_le (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    ‖dominatedComplexL2 hc h f‖≤c.toReal^((1:ℝ)/2)*‖f‖ := by
  have hb := (Lp.LpToLpOfMeasureLeSMul hc h : Lp ℂ 2 «μ»→L[ℝ]Lp ℂ 2 ν).le_opNorm f
  have hn := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hc h
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hn

end DominatedComplexL2

def kernelCompactMultiplicity (K : Set HyperbolicSpace) (hK : IsCompact K) : ℕ :=
  (kernelCompact_projection_measure_bound K hK).choose

lemma kernelCompactMultiplicity_spec (K : Set HyperbolicSpace) (hK : IsCompact K) :
    Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (kernelCompactMultiplicity K hK:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel :=
  (kernelCompact_projection_measure_bound K hK).choose_spec

def kernelCompactPullbackCLM (K : Set HyperbolicSpace) (hK : IsCompact K) :
    KernelQuotientL2→L[ℂ]Lp ℂ 2 (hyperbolicVolume.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    ⟨measurable_integralOrbitProjection _,rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤)
        (kernelCompactMultiplicity_spec K hK))

theorem kernelCompactPullbackCLM_ae (K : Set HyperbolicSpace) (hK : IsCompact K)
    (F : KernelQuotientL2) :
    kernelCompactPullbackCLM K hK F=ᵐ[hyperbolicVolume.restrict K]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm : MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict K)
      (Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)) :=
    ⟨measurable_integralOrbitProjection _,rfl⟩
  have he := dominatedComplexL2_ae
    (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤) (kernelCompactMultiplicity_spec K hK) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp he)

lemma whittaker_bound_integrable_finite («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) («μ».prod volume) := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) «μ» := integrable_const _
  simpa only [one_mul] using hv.mul_prod hk

lemma scaledWhittakerIntegrand_integrable («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s (c*p.1,p.2)) («μ».prod volume) := by
  apply ((whittaker_bound_integrable_finite «μ» s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrand_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s (c*p.1,p.2) s.re (by linarith) le_rfl)
        (norm_nonneg _) (norm_nonneg _))

lemma scaledWhittakerProduct_differentiableAt («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w (c*p.1,p.2)∂«μ».prod volume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := «μ».prod volume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w (c*p.1,p.2))
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w (c*p.1,p.2))
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul
        ((whittakerIntegrand_continuous freq w).comp (by fun_prop))).aestronglyMeasurable))
    (scaledWhittakerIntegrand_integrable «μ» ρ c freq s hs)
    ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrandDeriv_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w (c*p.1,p.2) b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable_finite «μ» b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ =>
      (whittakerIntegrand_hasDerivAt freq w (c*p.1,p.2)).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma whittakerIntegrand_scale (c v : ℝ) (hc : 0<c) (hv : 0<v) (hcv : 5≤c*v)
    (freq s : ℂ) (z : ℂ) :
    (c:ℂ)^(s+1)*whittakerIntegrand (freq/c) s (c*v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hcn : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  rw [whittakerIntegrand_eq (freq/c) s (c*v) hcv z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hv.le]
  have he : -(freq/(c:ℂ)*((c:ℂ)*v))*z=-(freq*v)*z := by field_simp
  rw [he]
  have hp : (c:ℂ)^(s+1)*(c:ℂ)^(-s-1)=1 := by
    rw [←Complex.cpow_add _ _ hcn,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _ = ((c:ℂ)^(s+1)*(c:ℂ)^(-s-1))*
      ((v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z))) := by ring
    _ = _ := by rw [hp,one_mul]

lemma scaledWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    ((5/a:ℝ):ℂ)^(s+1)*
      (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*p.1,p.2)
        ∂(volume.restrict (Set.Icc a b)).prod volume)=
      ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := scaledWhittakerIntegrand_integrable (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs
  rw [integral_prod _ hi,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hvp : 0<v := ha.trans_le hv.1
  have hcv : 5≤(5/a)*v := by
    calc
      5=(5/a)*a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  rw [←integral_const_mul]
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*
        (hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        calc
          _ = ρ v*(((5/a:ℝ):ℂ)^(s+1)*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*v,z)) := by ring
          _ = _ := by rw [whittakerIntegrand_scale (5/a) v (by positivity) hvp hcv freq s z]; ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerInterval_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have hc : ((5/a:ℝ):ℂ)≠0 := by exact_mod_cast (show (5/a:ℝ)≠0 by positivity)
  have hd := ((differentiableAt_id.add_const (1:ℂ)).const_cpow (Or.inl hc)).mul
    (scaledWhittakerProduct_differentiableAt (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact (scaledWhittakerProduct_eq_average ρ a b ha freq w hw).symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cuspWeightedFourierPhase (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*cuspFourierPhase h w

lemma cuspWeightedFourierPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Continuous (cuspWeightedFourierPhase ρ h) :=
  (ρ.continuous.comp hyperbolicHeight_continuous).mul (cuspFourierPhase_continuous h)

lemma cuspWeightedFourierPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) :
    ‖cuspWeightedFourierPhase ρ h w‖≤‖ρ‖ := by
  rw [cuspWeightedFourierPhase,norm_mul,cuspFourierPhase_norm,mul_one]
  exact ρ.norm_coe_le_norm _

lemma cuspWeightedFourierTest_memLp (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

def cuspWeightedFourierTestL2 (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspWeightedFourierTest_memLp ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))

def kernelCuspWeightedFourier (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspWeightedFourierTestL2 ρ h)).comp kernelCuspPullback

lemma kernelCuspWeightedFourier_integral (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspWeightedFourierTestL2 ρ h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspWeightedFourierTest_memLp ρ h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspWeightedFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspWeightedFourier_restrict (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspWeightedFourier ρ h F := by
  rw [kernelCuspWeightedFourier_integral,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspWeightedFourierFamily (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspWeightedFourier ρ h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspWeightedFourierFamily_meromorphicAt (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MeromorphicAt (kernelCuspWeightedFourierFamily ρ h) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspWeightedFourier ρ h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num))

lemma kernelCuspWeightedFourierFamily_analyticAt_nonreal (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspWeightedFourierFamily ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspWeightedFourier ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact 2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma kernelCuspWeightedFourierFamily_residue_limit (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspWeightedFourierFamily ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspWeightedFourier ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspWeightedFourier ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspWeightedFourier_restrict,
    kernelCuspWeightedFourierFamily] using hh

lemma kernelCuspWeightedFourierFamily_initial (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspWeightedFourierFamily,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (cubicEisensteinLocalFamily_initial_ae kernelCuspAverageCompact kernelCuspAverageCompact_isCompact s hs hi)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]

def cuspWeightedWhittakerHeightFactor (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))

lemma hyperbolicEisenstein_cusp_weighted_fourier_nonzero (ρ : BoundedContinuousFunction ℝ ℂ)
    (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  have hexp : ∀v∈Set.Icc (5:ℝ) 6,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,ite_eq_right hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc (5:ℝ) 6,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _

lemma kernelCuspWeightedFourierFamily_initial_factor (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  rw [kernelCuspWeightedFourierFamily_initial ρ h s hs hi,
    hyperbolicEisenstein_cusp_weighted_fourier_nonzero ρ s (by linarith) h hh]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0260

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.GaussFactorization
Source SHA256: 3d94eb6d99032833643c849cd4596281cabb3ed5a035c9f8e667e17011fd9bad
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0261


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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicBesselNormalizer (h : ActualEisensteinCubic.O) : ℂ :=
  (2*Real.pi:ℂ)/Complex.Gamma (4/3)*(2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)

def cubicResidualFourierCoefficient (h : ActualEisensteinCubic.O) : ℂ :=
  cubicBesselNormalizer h*nonzeroScatteringResidue h

lemma sourceFourierKernel_cubic_height (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) :
    (v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [sourceFourierKernel_four_thirds _ (mul_ne_zero (cuspFrequency_ne_zero h hh) hv0)]
  have hnorm : ‖cuspFrequency h*(v:ℂ)‖=‖cuspFrequency h‖*v := by
    rw [norm_mul,Complex.norm_of_nonneg hv.le]
  rw [hnorm]
  simp only [Complex.ofReal_mul]
  have hbase : (2*Real.pi*(‖cuspFrequency h‖*v):ℂ)=
      (2*Real.pi*‖cuspFrequency h‖:ℂ)*(v:ℂ) := by ring
  have hpow : (2*Real.pi*(‖cuspFrequency h‖*v):ℂ)^(1/3:ℂ)=
      (2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)*(v:ℂ)^(1/3:ℂ) := by
    rw [hbase]
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      (Complex.mul_cpow_ofReal_nonneg (a := 2*Real.pi*‖cuspFrequency h‖) (b := v)
        (by positivity) hv.le (1/3:ℂ))
  have hvpow : (v:ℂ)^(-(4/3:ℂ)-1)*(v:ℂ)^(1/3:ℂ)=1/(v:ℂ)^2 := by
    rw [←Complex.cpow_add _ _ hv0,show -(4/3:ℂ)-1+1/3=-(2:ℂ) by ring,
      Complex.cpow_neg,Complex.cpow_ofNat]
    simp only [one_div]
  have harg : 4*Real.pi*(‖cuspFrequency h‖*v)=4*Real.pi*‖cuspFrequency h‖*v := by ring
  rw [hpow,harg]
  unfold cubicBesselNormalizer
  calc
    _ = ((2*Real.pi:ℂ)/Complex.Gamma (4/3)*(2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ))*
        ((v:ℂ)^(-(4/3:ℂ)-1)*(v:ℂ)^(1/3:ℂ))*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by ring
    _ = _ := by rw [hvpow]; ring

end

section
open Filter MeasureTheory
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspWhittakerHeightFactor_punctured_ne_zero (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    ∀ᶠw : ℂ in 𝓝[≠] s,cuspWhittakerHeightFactor w h≠0 := by
  rcases (cuspWhittakerHeightFactor_analyticAt h s hs).eventually_eq_zero_or_eventually_ne_zero with hz|hne
  · have han : AnalyticOnNhd ℂ (fun w => cuspWhittakerHeightFactor w h) {w : ℂ | 1<w.re} :=
      fun w hw => cuspWhittakerHeightFactor_analyticAt h w hw
    have hcon : Convex ℝ {w : ℂ | 1<w.re} :=
      (convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap
    have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon.isPreconnected hs hz
    have hval : cuspWhittakerHeightFactor (5:ℂ) h=0 := heq (by norm_num)
    have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [hval,Complex.zero_re] at hpos
    exact (lt_irrefl 0 hpos).elim
  · exact hne

lemma continuedNonzeroScattering_eq_arithmetic_germ (h : ActualEisensteinCubic.O) (hh : h≠0)
    (s : ℂ) (hs : 2<s.re) (hi : 0<s.im) :
    continuedNonzeroScattering h =ᶠ[𝓝[≠] s] (fun w => scatteringCoefficient w h) := by
  have hopen : IsOpen {w : ℂ | 2<w.re ∧ 0<w.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hfull : ∀ᶠw : ℂ in 𝓝 s,2<w.re ∧ 0<w.im := hopen.mem_nhds ⟨hs,hi⟩
  have hdomain : ∀ᶠw : ℂ in 𝓝[≠] s,2<w.re ∧ 0<w.im :=
    hfull.filter_mono nhdsWithin_le_nhds
  filter_upwards [hdomain,cuspWhittakerHeightFactor_punctured_ne_zero h s (by linarith)] with w hw hH
  exact continuedNonzeroScattering_eq_upper h hh w hw.1 hw.2 hH

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspWeightedWhittakerHeightFactor_differentiableAt
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ (fun w => cuspWeightedWhittakerHeightFactor ρ w h) s := by
  have heq : (fun w => cuspWeightedWhittakerHeightFactor ρ w h)=
      (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (cuspFrequency h*v)) := by
    funext w
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (mul_assoc _ _ _).symm)
  rw [heq]
  exact cuspWeightedWhittakerAverage_differentiableAt ρ (cuspFrequency h) s hs

lemma cuspWeightedWhittakerHeightFactor_analyticAt
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWeightedWhittakerHeightFactor ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWeightedWhittakerHeightFactor_differentiableAt ρ h w hw

lemma kernelCuspWeightedFourierFamily_cross_identity
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (fun s => kernelCuspWeightedFourierFamily ρ h s*cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspWeightedWhittakerHeightFactor ρ s h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => kernelCuspWeightedFourierFamily ρ h s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (kernelCuspWeightedFourierFamily_analyticAt_nonreal ρ h s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspWeightedWhittakerHeightFactor ρ s h) domain := by
    intro s hs
    exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspWeightedWhittakerHeightFactor_analyticAt ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelCuspWeightedFourierFamily ρ h s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
          cuspWeightedWhittakerHeightFactor ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [kernelCuspWeightedFourierFamily_initial_factor ρ h hh s hs.1 hs.2,
      kernelCuspFourierFamily_eq_upper h hh ⟨by linarith [hs.1],hs.2⟩]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma upperVertical_tendsto_cubic_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,zero_mul,add_zero] at hh
    exact ht.ne' (by linarith [hh])

lemma kernelCuspWeightedFourier_residue_factor
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspWeightedFourier ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*nonzeroScatteringResidue h*
        cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h := by
  have hbase : Tendsto (fun s : ℂ => cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) h)) :=
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => cuspWeightedWhittakerHeightFactor ρ s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h)) :=
    (cuspWeightedWhittakerHeightFactor_analyticAt ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((kernelCuspWeightedFourierFamily_residue_limit ρ h).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspWeightedFourierFamily ρ h ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
        ((4/3:ℂ)+(t:ℂ)*Complex.I))*cuspWeightedWhittakerHeightFactor ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := kernelCuspWeightedFourierFamily_cross_identity ρ h hh hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspWeightedFourier ρ h cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      kernelCuspFourier h cubicEisensteinResidue*cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hH := cuspWhittakerHeightFactor_center_ne_zero h
  calc
    _ = (kernelCuspFourier h cubicEisensteinResidue*cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h)/
        cuspWhittakerHeightFactor (4/3:ℂ) h := (eq_div_iff hH).mpr heq
    _ = _ := by
      unfold nonzeroScatteringResidue
      field_simp [cusp_volume_ne_zero,hH]

lemma cuspWeightedWhittakerHeightFactor_center_bessel
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspWeightedWhittakerHeightFactor ρ (4/3:ℂ) h=
      cubicBesselNormalizer h*(∫v in Set.Icc (5:ℝ) 6,
        ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cuspWeightedWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_cubic_height h hh v hpos]
  ring

lemma kernelCuspWeightedFourier_residue_bessel
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspWeightedFourier ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFourierCoefficient h*
        (∫v in Set.Icc (5:ℝ) 6,ρ v*
          (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [kernelCuspWeightedFourier_residue_factor ρ h hh,
    cuspWeightedWhittakerHeightFactor_center_bessel ρ h hh,cubicResidualFourierCoefficient]
  ring

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma denominatorRep_mk_congr (c d : Eis) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact denominatorRep_spec c _

lemma isCoprime_right_congr_of_dvd (c d e : Eis) (h : c ∣ d-e) :
    IsCoprime c d ↔ IsCoprime c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+c*n := by linear_combination hn
  rw [hd,IsCoprime.add_mul_left_right_iff]

abbrev CubicUnitResidue (b : Eis) :=
  {r : Eis ⧸ Ideal.span {b} // IsUnit r}

def denominatorCRTMap (a b : Eis) (r : AdmissibleResidue (a*b)) :
    AdmissibleResidue a × CubicUnitResidue b :=
  let d:=denominatorRep (a*b) r.1
  (⟨Ideal.Quotient.mk (Ideal.span {3*a}) d,
      (denominatorCondition_congr a _ d (denominatorRep_mk_congr a d)).mpr
        ⟨r.2.1.of_mul_left_left,r.2.2⟩⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr r.2.1.of_mul_left_right⟩)

lemma denominatorCRTMap_injective (a b : Eis) (hab : IsCoprime (3*a) b) :
    Function.Injective (denominatorCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.1.1) he
  have h2:=congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) t.1) at h2
  have hdiv : 3*(a*b) ∣ denominatorRep (a*b) r.1-denominatorRep (a*b) t.1 := by
    simpa only [mul_assoc] using hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←denominatorRep_spec (a*b) r.1,←denominatorRep_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

lemma denominatorCRTMap_surjective (a b : Eis) (hab : IsCoprime (3*a) b) :
    Function.Surjective (denominatorCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩ := hab
  let delta:=denominatorRep a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*(3*a)*xi
  have hda : 3*a ∣ d-delta := by
    refine ⟨u*(xi-delta),?_⟩
    dsimp [d]
    linear_combination delta*huv
  have hdb : b ∣ d-xi := by
    refine ⟨v*(delta-xi),?_⟩
    dsimp [d]
    linear_combination xi*huv
  have hxi : IsCoprime b xi := by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have had : denominatorCondition a d := (denominatorCondition_congr a d delta hda).mpr r.2
  have hbd : IsCoprime b d := (isCoprime_right_congr_of_dvd b d xi hdb).mpr hxi
  have hd : denominatorCondition (a*b) d := ⟨had.1.mul_left hbd,had.2⟩
  let q : AdmissibleResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {3*(a*b)}) d,
    (denominatorCondition_congr (a*b) _ d (denominatorRep_mk_congr (a*b) d)).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) q.1)=r.1
    rw [←denominatorRep_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : 3*a ∣ denominatorRep (a*b) q.1-d := by
      exact (show 3*a ∣ 3*(a*b) from ⟨b,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : b ∣ denominatorRep (a*b) q.1-d := by
      exact (show b ∣ 3*(a*b) from ⟨3*a,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def denominatorCRTEquiv (a b : Eis) (hab : IsCoprime (3*a) b) :
    AdmissibleResidue (a*b) ≃ AdmissibleResidue a × CubicUnitResidue b :=
  Equiv.ofBijective (denominatorCRTMap a b)
    ⟨denominatorCRTMap_injective a b hab,denominatorCRTMap_surjective a b hab⟩

def residueAdditive (h c d : Eis) : ℂ :=
  ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding d/eisEmbedding c)

lemma residueAdditive_congr (h c d e : Eis) (hc : c≠0) (hde : 3*c ∣ d-e) :
    residueAdditive h c d=residueAdditive h c e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+3*c*n:=by linear_combination hn
  have he:eisEmbedding c≠0:=eisEmbedding_ne_zero hc
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency h*eisEmbedding (e+3*c*n)/eisEmbedding c=
      cuspFrequency h*eisEmbedding e/eisEmbedding c+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def cubicUnitGaussSum (h b : Eis) : ℂ :=
  ∑' r : CubicUnitResidue b,
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1)

lemma residueAdditive_three_congr (h b d e : Eis) (hb : b≠0) (hde : b ∣ d-e) :
    residueAdditive (3*h) b d=residueAdditive (3*h) b e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+b*n:=by linear_combination hn
  have he:eisEmbedding b≠0:=eisEmbedding_ne_zero hb
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency (3*h)*eisEmbedding (e+b*n)/eisEmbedding b=
      cuspFrequency (3*h)*eisEmbedding e/eisEmbedding b+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [cuspFrequency,map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

lemma residueAdditive_crt (h a b alpha beta d : Eis) (ha : a≠0) (hb : b≠0)
    (hbez : alpha*b+beta*(3*a)=1) :
    residueAdditive h (a*b) d=
      residueAdditive (h*alpha) a d*residueAdditive (3*(h*beta)) b d := by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one,map_ofNat] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  field_simp [hae,hbe,eisLam_ne_zero]
  linear_combination -(eisEmbedding h*eisEmbedding d)*hbeq

lemma arithmetic_crt_summand (h a b alpha beta : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1)
    (r : AdmissibleResidue (a*b)) :
    eisEmbedding (symbol (a*b) (denominatorRep (a*b) r.1))*
      residueAdditive h (a*b) (denominatorRep (a*b) r.1)=
    (eisEmbedding (symbol a (denominatorRep a (denominatorCRTMap a b r).1.1))*
      residueAdditive (h*alpha) a (denominatorRep a (denominatorCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1)) := by
  let d:=denominatorRep (a*b) r.1
  let delta:=denominatorRep a (denominatorCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1
  have hdprimary : lambda^2∣d-1:=lambda_sq_dvd_three.trans r.2.2
  have hdelta : 3*a∣delta-d:=denominatorRep_mk_congr a d
  have hxi : b∣xi-d:=by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact GaussianShiftedPartition.representative_spec b _
  have hchar : symbol (a*b) d=symbol a delta*symbol xi b := by
    rw [symbol_mul_numerator a b d hdprimary,
      symbol_reciprocity b d hb (primary_ne_zero d hdprimary) hbprimary hdprimary,
      ←symbol_congr hxi]
    rw [←row_symbol_congr_modulus a delta d halevel r.2.2 hdelta]
  change eisEmbedding (symbol (a*b) d)*residueAdditive h (a*b) d=
    (eisEmbedding (symbol a delta)*residueAdditive (h*alpha) a delta)*
      (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [hchar,map_mul,residueAdditive_crt h a b alpha beta d ha hb hbez,
    residueAdditive_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

theorem arithmeticResidueSum_crt (h a b alpha beta : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1) :
    arithmeticResidueSum h (a*b)=
      arithmeticResidueSum (h*alpha) a*cubicUnitGaussSum (h*beta) b := by
  have hab : IsCoprime (3*a) b:=⟨beta,alpha,by linear_combination hbez⟩
  let f : AdmissibleResidue a→ℂ:=fun r=>
    eisEmbedding (symbol a (denominatorRep a r.1))*residueAdditive (h*alpha) a (denominatorRep a r.1)
  let g : CubicUnitResidue b→ℂ:=fun r=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have heq: arithmeticResidueSum h (a*b)=∑' r : AdmissibleResidue (a*b),
      f (denominatorCRTEquiv a b hab r).1*g (denominatorCRTEquiv a b hab r).2 := by
    unfold arithmeticResidueSum
    apply tsum_congr
    intro r
    exact arithmetic_crt_summand h a b alpha beta ha hb halevel hbprimary hbez r
  rw [heq,(denominatorCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let : Finite (AdmissibleResidue a):=finite_admissibleResidue a ha
  let : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  let : Fintype (AdmissibleResidue a):=Fintype.ofFinite _
  let : Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑' r : AdmissibleResidue a × CubicUnitResidue b,f r.1*g r.2)=
    (∑' r : AdmissibleResidue a,f r)*(∑' t : CubicUnitResidue b,g t)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

end

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma residueAdditive_mul (h c t d : Eis) :
    residueAdditive h c (t*d)=residueAdditive (h*t) c d := by
  unfold residueAdditive cuspFrequency
  simp only [map_mul]
  congr 1
  ring

lemma residueAdditive_swap (h c d : Eis) :
    residueAdditive h c d=residueAdditive d c h := by
  unfold residueAdditive cuspFrequency
  congr 1
  ring

lemma arithmeticResidueSum_frequency_congr (h k c : Eis) (hc : c≠0)
    (hh : 3*c∣h-k) : arithmeticResidueSum h c=arithmeticResidueSum k c := by
  unfold arithmeticResidueSum
  apply tsum_congr
  intro r
  congr 1
  change residueAdditive h c (denominatorRep c r.1)=residueAdditive k c (denominatorRep c r.1)
  rw [residueAdditive_swap h,residueAdditive_swap k]
  exact residueAdditive_congr _ c h k hc hh

theorem arithmeticResidueSum_frequency_twist (h c t : Eis) (hc : c≠0)
    (hlevel : (3:Eis)∣c) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum (h*t) c=arithmeticResidueSum h c := by
  have heq:=(residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c=>eisEmbedding (symbol c (denominatorRep c r.1))*
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t)*
      (eisEmbedding (symbol c (denominatorRep c r.1))*residueAdditive (h*t) c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1))*
        residueAdditive h c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1) := by
      apply tsum_congr
      intro r
      change _=eisEmbedding (symbol c (denominatorRep c (residueMultiplication c t ht r).1))*
        residueAdditive h c (denominatorRep c (residueMultiplication c t ht r).1)
      rw [residueMultiplication_phase c hlevel t ht r,map_mul]
      dsimp only [residueMultiplication]
      rw [residueAdditive_congr h c _ (t*denominatorRep c r.1) hc
        (denominatorRep_product_congr c t r.1),residueAdditive_mul]
      ring
    _ = _ := heq

lemma cubicUnitGaussSum_frequency_congr (h k b : Eis) (hb : b≠0)
    (hh : b∣h-k) : cubicUnitGaussSum h b=cubicUnitGaussSum k b := by
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro r
  congr 1
  have he (u : Eis) : residueAdditive (3*u) b (GaussianShiftedPartition.representative b r.1)=
      residueAdditive (3*GaussianShiftedPartition.representative b r.1) b u := by
    unfold residueAdditive cuspFrequency
    simp only [map_mul,map_ofNat]
    congr 1
    ring
  rw [he h,he k]
  exact residueAdditive_three_congr _ b h k hb hh

def cubicUnitResidueMul (b t : Eis) (ht : IsCoprime b t) (r : CubicUnitResidue b) :
    CubicUnitResidue b :=
  ⟨Ideal.Quotient.mk (Ideal.span {b}) t*r.1,
    ((isUnit_quotient_span_iff b t).mpr ht).mul r.2⟩

lemma cubicUnitResidueMul_injective (b t : Eis) (ht : IsCoprime b t) :
    Function.Injective (cubicUnitResidueMul b t ht) := by
  intro r q heq
  apply Subtype.ext
  exact ((isUnit_quotient_span_iff b t).mpr ht).mul_left_cancel (congrArg Subtype.val heq)

def cubicUnitResidueMulEquiv (b t : Eis) (hb : b≠0) (ht : IsCoprime b t) :
    CubicUnitResidue b ≃ CubicUnitResidue b := by
  letI : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  exact Equiv.ofBijective (cubicUnitResidueMul b t ht)
    ⟨cubicUnitResidueMul_injective b t ht,
      Finite.surjective_of_injective (cubicUnitResidueMul_injective b t ht)⟩

lemma cubicUnitResidueMul_rep_congr (b t : Eis) (ht : IsCoprime b t)
    (r : CubicUnitResidue b) :
    b∣GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1-
      t*GaussianShiftedPartition.representative b r.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec,map_mul,
    GaussianShiftedPartition.representative_spec]
  rfl

theorem cubicUnitGaussSum_frequency_twist (h b t : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (ht : IsCoprime b t) :
    eisEmbedding (symbol t b)*cubicUnitGaussSum (h*t) b=cubicUnitGaussSum h b := by
  have heq:=(cubicUnitResidueMulEquiv b t hb ht).tsum_eq
    (fun r : CubicUnitResidue b=>eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1))
  calc
    _ = ∑' r : CubicUnitResidue b,eisEmbedding (symbol t b)*
      (eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
        residueAdditive (3*(h*t)) b (GaussianShiftedPartition.representative b r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : CubicUnitResidue b,
      eisEmbedding (symbol (GaussianShiftedPartition.representative b
        (cubicUnitResidueMulEquiv b t hb ht r).1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b
        (cubicUnitResidueMulEquiv b t hb ht r).1) := by
      apply tsum_congr
      intro r
      change _=eisEmbedding (symbol (GaussianShiftedPartition.representative b
        (cubicUnitResidueMul b t ht r).1) b)*
        residueAdditive (3*h) b (GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1)
      rw [symbol_congr (cubicUnitResidueMul_rep_congr b t ht r),
        symbol_mul_numerator t _ b hbprimary,map_mul]
      rw [residueAdditive_three_congr h b _ (t*GaussianShiftedPartition.representative b r.1)
        hb (cubicUnitResidueMul_rep_congr b t ht r),residueAdditive_mul]
      rw [show (3*h)*t=3*(h*t) by ring]
      ring
    _ = _ := heq

theorem arithmeticResidueSum_coprime_product (h a b : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hab : IsCoprime (3*a) b) :
    arithmeticResidueSum h (a*b)=
      eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        arithmeticResidueSum h a*cubicUnitGaussSum h b := by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez' : alpha*b+beta*(3*a)=1:=by linear_combination hbez
  have hab' : IsCoprime (3*a) b:=⟨beta,alpha,hbez⟩
  have hb3 : (3:Eis)∣b-1:=three_dvd_lambda_sq.trans hbprimary
  have hbt : denominatorCondition a b:=⟨hab'.of_mul_left_right,hb3⟩
  have hA := arithmeticResidueSum_frequency_twist (h*alpha) a b ha halevel hbt
  have hAf : 3*a∣(h*alpha)*b-h:=⟨-h*beta,by linear_combination h*hbez'⟩
  rw [arithmeticResidueSum_frequency_congr _ h a ha hAf] at hA
  have hB := cubicUnitGaussSum_frequency_twist (h*beta) b (3*a) hb hbprimary hab'.symm
  have hBf : b∣(h*beta)*(3*a)-h:=⟨-h*alpha,by linear_combination h*hbez'⟩
  rw [cubicUnitGaussSum_frequency_congr _ h b hb hBf] at hB
  rw [arithmeticResidueSum_crt h a b alpha beta ha hb halevel hbprimary hbez',←hA,←hB]
  ring

end CubicEisenstein

end

end OAI
end OAIOriginalModule0261

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.RamifiedGaussSeries
Source SHA256: 99b25e640f6ec4a22162fc054fb04b86846448af69499fe28b44046a859b7d0f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0262


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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedElement_ne_zero (u : Eisˣ) (n : ℕ) : u.val*lambda^n≠0 := by
  have hl : lambda≠0:=by
    intro hh
    apply CompletedGauss.embedding_lambda_ne_zero
    rw [hh,map_zero]
  exact mul_ne_zero u.ne_zero (pow_ne_zero _ hl)

lemma ramifiedElement_level (u : Eisˣ) (n : ℕ) (hn : 2≤n) :
    (3:Eis)∣u.val*lambda^n :=
  dvd_mul_of_dvd_right (three_dvd_lambda_sq.trans (pow_dvd_pow lambda hn)) _

lemma ramified_denominator_condition (u : Eisˣ) (n : ℕ) (d : Eis)
    (hd : (3:Eis)∣d-1) : denominatorCondition (u.val*lambda^n) d := by
  have hu : IsCoprime u.val d:=⟨u.inv,0,by simp⟩
  have hl3 : lambda∣(3:Eis):=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  have hld : IsCoprime lambda d:=coprime_of_dvd_sub_one lambda d (hl3.trans hd)
  exact ⟨hu.mul_left hld.pow_left,hd⟩

lemma ramified_symbol_congr_mod_nine (u : Eisˣ) (n : ℕ) (d e : Eis)
    (hd : (3:Eis)∣d-1) (he : (3:Eis)∣e-1) (hde : (9:Eis)∣d-e) :
    symbol (u.val*lambda^n) d=symbol (u.val*lambda^n) e := by
  have hdp:=lambda_sq_dvd_three.trans hd
  have hep:=lambda_sq_dvd_three.trans he
  rw [symbol_mul_numerator _ _ d hdp,symbol_mul_numerator _ _ e hep,
    symbol_pow_numerator _ d hdp,symbol_pow_numerator _ e hep,
    symbol_unit_congr_mod_nine u.val d e u.isUnit hdp hep hde,
    CubicRamified.symbol_lambda_congr_mod_nine d e hdp hep hde]

lemma primary_add_nine (d w : Eis) (hd : (3:Eis)∣d-1) :
    (3:Eis)∣d+9*w-1 := by
  convert dvd_add hd (show (3:Eis)∣9*w from ⟨3*w,by ring⟩) using 1 ; ring

def ramifiedResidueAdd (u : Eisˣ) (n : ℕ) (w : Eis)
    (r : AdmissibleResidue (u.val*lambda^n)) : AdmissibleResidue (u.val*lambda^n) :=
  let c:=u.val*lambda^n
  let d:=denominatorRep c r.1+9*w
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) d,
    (denominatorCondition_congr c _ d (denominatorRep_mk_congr c d)).mpr
      (ramified_denominator_condition u n d (primary_add_nine _ _ r.2.2))⟩

lemma ramifiedResidueAdd_injective (u : Eisˣ) (n : ℕ) (w : Eis) :
    Function.Injective (ramifiedResidueAdd u n w) := by
  intro r q heq
  have hh:=congrArg Subtype.val heq
  change Ideal.Quotient.mk (Ideal.span {3*(u.val*lambda^n)}) (denominatorRep _ r.1+9*w)=
    Ideal.Quotient.mk (Ideal.span {3*(u.val*lambda^n)}) (denominatorRep _ q.1+9*w) at hh
  simp only [map_add,denominatorRep_spec] at hh
  exact Subtype.ext (add_right_cancel hh)

def ramifiedResidueAddEquiv (u : Eisˣ) (n : ℕ) (w : Eis) :
    AdmissibleResidue (u.val*lambda^n) ≃ AdmissibleResidue (u.val*lambda^n) := by
  letI : Finite (AdmissibleResidue (u.val*lambda^n)):=
    finite_admissibleResidue _ (ramifiedElement_ne_zero u n)
  exact Equiv.ofBijective (ramifiedResidueAdd u n w)
    ⟨ramifiedResidueAdd_injective u n w,
      Finite.surjective_of_injective (ramifiedResidueAdd_injective u n w)⟩

lemma residueAdditive_add (h c d e : Eis) :
    residueAdditive h c (d+e)=residueAdditive h c d*residueAdditive h c e := by
  unfold residueAdditive
  rw [map_add,mul_add,add_div,AddChar.map_add_eq_mul]

theorem ramified_arithmetic_additive_eigen (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (w : Eis) :
    residueAdditive h (u.val*lambda^n) (9*w)*arithmeticResidueSum h (u.val*lambda^n)=
      arithmeticResidueSum h (u.val*lambda^n) := by
  let c:=u.val*lambda^n
  have hc:c≠0:=ramifiedElement_ne_zero u n
  have hlevel:(3:Eis)∣c:=ramifiedElement_level u n hn
  have heq:=(ramifiedResidueAddEquiv u n w).tsum_eq
    (fun r : AdmissibleResidue c=>eisEmbedding (symbol c (denominatorRep c r.1))*
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c,residueAdditive h c (9*w)*
      (eisEmbedding (symbol c (denominatorRep c r.1))*residueAdditive h c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c (ramifiedResidueAddEquiv u n w r).1))*
        residueAdditive h c (denominatorRep c (ramifiedResidueAddEquiv u n w r).1) := by
      apply tsum_congr
      intro r
      let d:=denominatorRep c r.1
      have hrep : 3*c∣denominatorRep c (ramifiedResidueAdd u n w r).1-(d+9*w):=
        denominatorRep_mk_congr c (d+9*w)
      have hdp:(3:Eis)∣d+9*w-1:=primary_add_nine d w r.2.2
      have hchar : symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1)=symbol c d := by
        rw [row_symbol_congr_modulus c _ (d+9*w) hlevel hdp hrep]
        exact ramified_symbol_congr_mod_nine u n (d+9*w) d hdp r.2.2 ⟨w,by ring⟩
      change _=eisEmbedding (symbol c (denominatorRep c (ramifiedResidueAdd u n w r).1))*
        residueAdditive h c (denominatorRep c (ramifiedResidueAdd u n w r).1)
      rw [hchar,residueAdditive_congr h c _ (d+9*w) hc hrep,residueAdditive_add]
      dsimp only [d]
      ring
    _ = _ := heq

theorem ramified_arithmetic_support (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    u.val*lambda^n∣3*h := by
  let c:=u.val*lambda^n
  have hc:c≠0:=ramifiedElement_ne_zero u n
  have hp : ∀w:Eis,residueAdditive h c (9*w)=1:=by
    intro w
    apply mul_right_cancel₀ hA
    rw [ramified_arithmetic_additive_eigen h u n hn w,one_mul]
  let psi:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc
  have hprimitive:psi.IsPrimitive:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  by_contra hdiv
  have hne:Ideal.Quotient.mk (Ideal.span {c}) (3*h)≠0:=by
    intro hh
    exact hdiv (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  apply hprimitive hne
  ext x
  obtain ⟨w,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [AddChar.mulShift_apply,←map_mul,psi,eisTraceModChar,
    IdealGaussCRT.traceModChar_mk,AddChar.one_apply]
  convert hp w using 1
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp
  ; ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_primary_coprime (u : Eisˣ) (n : ℕ) (b : Eis)
    (hb : lambda^2∣b-1) : IsCoprime (3*(u.val*lambda^n)) b := by
  have h3:IsCoprime (3:Eis) b:=(primary_coprime_three b hb).symm
  have hl:IsCoprime lambda b:=coprime_of_dvd_sub_one lambda b
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hb)
  have hu:IsCoprime u.val b:=⟨u.inv,0,by simp⟩
  exact h3.mul_left (hu.mul_left hl.pow_left)

theorem arithmeticResidueSum_ramified_split (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1) :
    arithmeticResidueSum h ((u.val*lambda^n)*b)=
      eisEmbedding (symbol (u.val*lambda^n) b)*
      eisEmbedding (symbol (3*(u.val*lambda^n)) b)*
      arithmeticResidueSum h (u.val*lambda^n)*cubicUnitGaussSum h b :=
  arithmeticResidueSum_coprime_product h _ b (ramifiedElement_ne_zero u n)
    (primary_ne_zero b hb) (ramifiedElement_level u n hn) hb (ramified_primary_coprime u n b hb)

lemma ramifiedElement_absNorm (u : Eisˣ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {u.val*lambda^n})=3^n := by
  have hu:Ideal.span {u.val}=(1:Ideal Eis):=by
    rw [Ideal.one_eq_top]
    exact Ideal.span_singleton_eq_top.mpr u.isUnit
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,hu,map_one,one_mul,
    ←Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

lemma three_absNorm : Ideal.absNorm (Ideal.span {(3:Eis)})=9 := by
  rw [←qNat_eq_absNorm_span]
  have he:(3:Eis)=ActualEisensteinCoordinates.eval 3 0:=by
    simp [ActualEisensteinCoordinates.eval]
  rw [he,ShortDraftLatticeCount.qNat,ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem ramified_arithmetic_norm_bound (h : Eis) (hh : h≠0) (u : Eisˣ)
    (n : ℕ) (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    3^n≤9*Ideal.absNorm (Ideal.span {h}) := by
  have hI:(Ideal.span {h}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hh
  have hN:0<Ideal.absNorm (Ideal.span {h}):=
    Nat.pos_of_ne_zero (fun hz=>hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply Nat.le_of_dvd (by positivity)
  obtain ⟨v,hv⟩:=ramified_arithmetic_support h u n hn hA
  refine ⟨Ideal.absNorm (Ideal.span {v}),?_⟩
  calc
    9*Ideal.absNorm (Ideal.span {h})=Ideal.absNorm (Ideal.span {(3:Eis)*h}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm]
    _=Ideal.absNorm (Ideal.span {(u.val*lambda^n)*v}):=by rw [hv]
    _=3^n*Ideal.absNorm (Ideal.span {v}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,ramifiedElement_absNorm]

def ramifiedFrequencyBound (h : Eis) : ℕ:=Nat.log 3 (9*Ideal.absNorm (Ideal.span {h}))

theorem arithmeticResidueSum_ramified_index_bound (h : Eis) (hh : h≠0)
    (u : Eisˣ) (n : ℕ) (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1)
    (hA : arithmeticResidueSum h ((u.val*lambda^n)*b)≠0) :
    n≤ramifiedFrequencyBound h := by
  have ha:arithmeticResidueSum h (u.val*lambda^n)≠0:=by
    intro hz
    apply hA
    rw [arithmeticResidueSum_ramified_split h u n hn b hb,hz,mul_zero,zero_mul]
  exact Nat.le_log_of_pow_le (by decide) (ramified_arithmetic_norm_bound h hh u n hn ha)

theorem arithmeticDirichletTerm_ramified_vanish (s : ℂ) (h : Eis) (hh : h≠0)
    (u : Eisˣ) (n : ℕ) (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1)
    (hout : ramifiedFrequencyBound h<n) :
    arithmeticDirichletTerm s h
      ⟨(u.val*lambda^n)*b,dvd_mul_of_dvd_left (ramifiedElement_level u n hn) b⟩=0 := by
  have hA:arithmeticResidueSum h ((u.val*lambda^n)*b)=0:=by
    by_contra hA
    exact (not_le_of_gt hout) (arithmeticResidueSum_ramified_index_bound h hh u n hn b hb hA)
  simp only [arithmeticDirichletTerm,hA,mul_zero,ite_self]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev NonzeroLevelLower := {c : LevelLower // c.1≠0}

def ramifiedLower (u : Eisˣ) (n : ℕ) (I : GoodIdeal) : Eis :=
  (u.val*lambda^(n+2))*primaryGenerator I.1

lemma ramifiedLower_ne_zero (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    ramifiedLower u n I≠0:=mul_ne_zero (ramifiedElement_ne_zero u (n+2)) I.2

lemma ramifiedLower_level (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    (3:Eis)∣ramifiedLower u n I:=
  dvd_mul_of_dvd_left (ramifiedElement_level u (n+2) (by omega)) _

lemma ramifiedLower_span (u : Eisˣ) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {ramifiedLower u n I}=ramifiedIdeal^(n+2)*I.1 := by
  unfold ramifiedLower
  rw [mul_assoc,Ideal.span_singleton_mul_left_unit u.isUnit,lambdaFactor_generator_span]

def ramifiedLowerMap (p : Eisˣ × ℕ × GoodIdeal) : NonzeroLevelLower:=
  ⟨⟨ramifiedLower p.1 p.2.1 p.2.2,ramifiedLower_level _ _ _⟩,ramifiedLower_ne_zero _ _ _⟩

lemma ramifiedLowerMap_injective : Function.Injective ramifiedLowerMap := by
  rintro ⟨u,n,I⟩ ⟨v,m,J⟩ h
  have hc : ramifiedLower u n I=ramifiedLower v m J:=congrArg (fun c:NonzeroLevelLower=>c.1.1) h
  have hs:=congrArg (fun x:Eis=>Ideal.span {x}) hc
  rw [ramifiedLower_span,ramifiedLower_span] at hs
  have hh:lambdaFactorMap (n+2,I)=lambdaFactorMap (m+2,J):=Subtype.ext hs
  have he:=lambdaFactorMap_bijective.1 hh
  have hnm:n=m:=by have ht:=congrArg Prod.fst he; omega
  have hIJ:I=J:=congrArg Prod.snd he
  subst m
  subst J
  have huv:u=v:=by
    apply Units.ext
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero) I.2)
    simpa only [ramifiedLower,mul_assoc] using hc
  subst v
  rfl

lemma ramifiedLowerMap_surjective : Function.Surjective ramifiedLowerMap := by
  intro c
  let C:NonzeroIdeal:=⟨Ideal.span {c.1.1},Ideal.span_singleton_eq_bot.not.mpr c.2⟩
  obtain ⟨⟨k,I⟩,hCI⟩:=lambdaFactorMap_bijective.2 C
  have hfact:ramifiedIdeal^k*I.1=Ideal.span {c.1.1}:=congrArg Subtype.val hCI
  have hp2:ramifiedIdeal^2∣ramifiedIdeal^k*I.1:=by
    rw [hfact]
    change (Ideal.span {lambda}:Ideal Eis)^2∣_
    rw [Ideal.span_singleton_pow,Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton]
    exact lambda_sq_dvd_three.trans c.1.2
  have hk:2≤k:=by
    by_contra hh
    have hcases:k=0∨k=1:=by omega
    have hnot:=((goodIdeal_iff_not_ramified I.1).mp I.2)
    rcases hcases with rfl|rfl
    · simp only [pow_zero,one_mul] at hp2
      exact hnot ((dvd_pow_self ramifiedIdeal (by decide : (2:ℕ)≠0)).trans hp2)
    · rw [pow_one,pow_two] at hp2
      exact hnot ((mul_dvd_mul_iff_left ramifiedIdeal_prime.ne_zero).mp hp2)
  obtain ⟨n,hn⟩:=Nat.exists_eq_add_of_le hk
  have hk':k=n+2:=by omega
  subst k
  have hspan : Ideal.span {lambda^(n+2)*primaryGenerator I.1}=Ideal.span {c.1.1}:=
    (lambdaFactor_generator_span (n+2) I).trans (by simpa only [Nat.add_comm] using hfact)
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨(u,n,I),Subtype.ext (Subtype.ext ?_)⟩
  change ramifiedLower u n I=c.1.1
  simpa only [ramifiedLower,mul_assoc,mul_comm,mul_left_comm] using hu

def ramifiedLowerEquiv : Eisˣ × ℕ × GoodIdeal ≃ NonzeroLevelLower:=
  Equiv.ofBijective ramifiedLowerMap ⟨ramifiedLowerMap_injective,ramifiedLowerMap_surjective⟩

lemma arithmeticDirichlet_support_nonzero (s : ℂ) (h : Eis) :
    Function.support (arithmeticDirichletTerm s h)⊆{c : LevelLower | c.1≠0} := by
  intro c hc
  change arithmeticDirichletTerm s h c≠0 at hc
  intro hz
  exact hc (by simp only [arithmeticDirichletTerm,hz,ite_true])

theorem arithmeticDirichletSeries_ramified_reindex (s : ℂ) (hs : 2<s.re) (h : Eis) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑'n:ℕ,∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  have hsum:Summable (arithmeticDirichletTerm s h):=(arithmeticDirichletTerm_summable_norm s hs h).of_norm
  have hsub:Summable (fun c:NonzeroLevelLower=>arithmeticDirichletTerm s h c.1):=hsum.subtype _
  have hp:=ramifiedLowerEquiv.summable_iff.mpr hsub
  change Summable (fun p:Eisˣ×ℕ×GoodIdeal=>arithmeticDirichletTerm s h (ramifiedLowerMap p).1) at hp
  calc
    _=∑'c:NonzeroLevelLower,arithmeticDirichletTerm s h c.1:=
      (tsum_subtype_eq_of_support_subset (arithmeticDirichlet_support_nonzero s h)).symm
    _=∑'p:Eisˣ×ℕ×GoodIdeal,arithmeticDirichletTerm s h (ramifiedLowerMap p).1:=
      (ramifiedLowerEquiv.tsum_eq _).symm
    _=_:=by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro u
      exact (hp.prod_factor u).tsum_prod

theorem arithmeticDirichletSeries_finite_ramified (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs h]
  apply tsum_congr
  intro u
  apply tsum_eq_sum
  intro n hn
  have hout:ramifiedFrequencyBound h<n+2:=by
    have hh':¬n<ramifiedFrequencyBound h+1:=by simpa only [Finset.mem_range] using hn
    omega
  have hzero (I:GoodIdeal) : arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1=0 :=
    arithmeticDirichletTerm_ramified_vanish s h hh u (n+2) (by omega)
      (primaryGenerator I.1) (primaryGenerator_spec I.1 I.2).2 hout
  simp only [hzero,tsum_zero]

theorem arithmeticDirichletSeries_gauss_expansion (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),∑'I:GoodIdeal,
        ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
          (eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
           eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
           arithmeticResidueSum h (u.val*lambda^(n+2))*cubicUnitGaussSum h (primaryGenerator I.1)) := by
  rw [arithmeticDirichletSeries_finite_ramified s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  apply tsum_congr
  intro I
  rw [arithmeticDirichletTerm, ite_eq_right (ramifiedLowerMap (u,n,I)).2]
  dsimp only [ramifiedLowerMap]
  congr 1
  exact arithmeticResidueSum_ramified_split h u (n+2) (by omega)
    (primaryGenerator I.1) (primaryGenerator_spec I.1 I.2).2

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicUnitGaussSum_phase_shift (h a b : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (hab : IsCoprime (3*a) b) :
    eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*cubicUnitGaussSum h b=
      cubicUnitGaussSum (h*(9*a)) b := by
  have hbt : IsCoprime b (9*a):=by
    rw [show (9:Eis)*a=3*(3*a) by ring]
    exact (primary_coprime_three b hbprimary).mul_right hab.symm
  have heig:=cubicUnitGaussSum_frequency_twist h b (9*a) hb hbprimary hbt
  have hs : symbol a b*symbol (3*a) b*symbol (9*a) b=1 := by
    calc
      _=symbol (a*(3*a)*(9*a)) b:=by
        symm
        calc
          _=symbol (a*(3*a)) b*symbol (9*a) b:=
            symbol_mul_numerator _ _ b hbprimary
          _=_:=by rw [symbol_mul_numerator a (3*a) b hbprimary]
      _=symbol ((3*a)^3) b:=by congr 1; ring
      _=(symbol (3*a) b)^3:=symbol_pow_numerator _ _ hbprimary 3
      _=1:=symbol_cube_of_isCoprime _ _ hbprimary hab
  have he : eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
      eisEmbedding (symbol (9*a) b)=1:=by
    simpa only [map_mul,map_one] using congrArg eisEmbedding hs
  calc
    _=(eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b))*
        (eisEmbedding (symbol (9*a) b)*cubicUnitGaussSum (h*(9*a)) b):=by rw [heig]
    _=(eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        eisEmbedding (symbol (9*a) b))*cubicUnitGaussSum (h*(9*a)) b:=by ring
    _=_:=by rw [he,one_mul]

def unramifiedCubicGaussSeries (s : ℂ) (h : Eis) : ℂ:=
  ∑'I:GoodIdeal,(Ideal.absNorm I.1:ℂ)^(-s)*cubicUnitGaussSum h (primaryGenerator I.1)

theorem arithmeticDirichletSeries_unramified_gauss (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*arithmeticResidueSum h (u.val*lambda^(n+2))*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))) := by
  rw [arithmeticDirichletSeries_gauss_expansion s hs h hh]
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,Complex.ofReal_natCast,ramifiedLower_span,
    map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [←cubicUnitGaussSum_phase_shift h (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)]
  ring

theorem scatteringCoefficient_unramified_gauss (s : ℂ) (hs : 2<s.re)
    (h : Eis) (hh : h≠0) :
    scatteringCoefficient s h=
      (∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*arithmeticResidueSum h (u.val*lambda^(n+2))*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient,arithmeticDirichletSeries_unramified_gauss s hs h hh]

end

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicUnitGaussSum_cube_shift (h b t : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (hbt : IsCoprime b t) :
    cubicUnitGaussSum (h*t^3) b=cubicUnitGaussSum h b := by
  have heig:=cubicUnitGaussSum_frequency_twist h b (t^3) hb hbprimary hbt.pow_right
  have hs : symbol (t^3) b=1:=by
    rw [symbol_pow_numerator t b hbprimary 3]
    exact symbol_cube_of_isCoprime t b hbprimary hbt.symm
  simpa only [hs,map_one,one_mul] using heig

theorem unramifiedCubicGaussSeries_neg (s : ℂ) (h : Eis) :
    unramifiedCubicGaussSeries s (-h)=unramifiedCubicGaussSeries s h := by
  apply tsum_congr
  intro I
  congr 1
  have hc : IsCoprime (primaryGenerator I.1) (-1:Eis):=⟨0,-1,by ring⟩
  simpa only [show (-1:Eis)^3=-1 by ring,mul_neg_one] using cubicUnitGaussSum_cube_shift h (primaryGenerator I.1) (-1) I.2
    (primaryGenerator_spec I.1 I.2).2 hc

theorem unramifiedCubicGaussSeries_lambda_pow (s : ℂ) (h : Eis) (n : ℕ) :
    unramifiedCubicGaussSeries s (h*lambda^n)=
      unramifiedCubicGaussSeries s (h*lambda^(n%3)) := by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  have hl:IsCoprime lambda (primaryGenerator I.1):=
    coprime_of_dvd_sub_one lambda _ ((show lambda∣lambda^2 from ⟨lambda,by ring⟩).trans hp)
  have he:lambda^n=lambda^(n%3)*(lambda^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.2 hp hl.symm.pow_right

theorem unramifiedCubicGaussSeries_lambda_cube (s : ℂ) (h : Eis) :
    unramifiedCubicGaussSeries s (h*lambda^3)=unramifiedCubicGaussSeries s h := by
  simpa using unramifiedCubicGaussSeries_lambda_pow s h 3

theorem unit_eq_sign_omega (u : Eisˣ) :
    ∃j:Fin 3,(u:Eis)=omega^j.val ∨ (u:Eis)=-(omega^j.val) := by
  let ζ:=IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η:Eisˣ:=(ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη:(η:Eis)=omega:=rfl
  have hlist:u∈([1,-1,η,-η,η^2,-η^2]:List Eisˣ):=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h|h|h|h|h|h
  · exact ⟨0,Or.inl (by simp [h])⟩
  · exact ⟨0,Or.inr (by simp [h])⟩
  · exact ⟨1,Or.inl (by simp [h,hη])⟩
  · exact ⟨1,Or.inr (by simp [h,hη])⟩
  · exact ⟨2,Or.inl (by simp only [h,Units.val_pow_eq_pow_val,hη];rfl)⟩
  · exact ⟨2,Or.inr (by simp only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη];rfl)⟩

theorem unramifiedCubicGaussSeries_nine_family (h : Eis) (u : Eisˣ) (n : ℕ) :
    ∃j k:Fin 3,∀s:ℂ,
      unramifiedCubicGaussSeries s (h*(9*((u:Eis)*lambda^n)))=
        unramifiedCubicGaussSeries s (h*omega^j.val*lambda^k.val) := by
  have hl:lambda^2=-3*omega:=by
    have hw:omega^2=-omega-1:=by
      have h3:omega^3=1:=omega_primitive.pow_eq_one
      have h1:omega≠1:=omega_primitive.ne_one (by decide)
      have hp:(omega-1)*(omega^2+omega+1)=0:=by linear_combination h3
      have hz:omega^2+omega+1=0:=(mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h1)
      linear_combination hz
    change (omega-1)^2=-3*omega
    linear_combination hw
  have h9:(9:Eis)=omega*lambda^4:=by
    calc
      _=9*omega^3:=by rw [omega_primitive.pow_eq_one];ring
      _=omega*((-3*omega)^2):=by ring
      _=omega*((lambda^2)^2):=by rw [hl]
      _=omega*lambda^4:=by ring
  let ζ:=IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η:Eisˣ:=(ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη:(η:Eis)=omega:=rfl
  obtain ⟨j,hj⟩:=unit_eq_sign_omega (η*u)
  refine ⟨j,⟨(n+4)%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro s
  have he:h*(9*((u:Eis)*lambda^n))=(h*((η*u:Eisˣ):Eis))*lambda^(n+4):=by
    rw [h9,Units.val_mul,hη,pow_add]
    ring
  rw [he,unramifiedCubicGaussSeries_lambda_pow]
  rcases hj with hj|hj
  · rw [hj]
  · rw [hj]
    simpa only [mul_neg,neg_mul] using
      unramifiedCubicGaussSeries_neg s (h*omega^j.val*lambda^((n+4)%3))

end CubicEisenstein

end

end OAI
end OAIOriginalModule0262

/-! Original module: OAI.NumberTheory.DirichletL.Reciprocity.KubotaCharacter
Source SHA256: 71ad7258f9d933640d65295f589f0de47e1a1850a9113b63af78b8a88ea8f0c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0263


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

def rationalEmbedding : SL(2,ℤ)→*SL(2,ActualEisensteinCubic.O) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ActualEisensteinCubic.O)

def levelThreeConjugate (g : SL(2,ActualEisensteinCubic.O)) (M : levelThree) : levelThree :=
  ⟨g*(M:SL(2,ActualEisensteinCubic.O))*g⁻¹,by
    change Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:ActualEisensteinCubic.O)})) _=1
    rw [map_mul,map_mul,map_inv,M.property,mul_one,mul_inv_cancel]⟩

lemma levelThree_bottom_primary (M : levelThree) : lambda^2∣(M:SL(2,ActualEisensteinCubic.O)) 1 1-1 :=
  lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 1 1)

lemma value_inverse_formula (M : levelThree) :
    value M⁻¹=symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  change symbol (((M:SL(2,ActualEisensteinCubic.O))⁻¹) 1 0) (((M:SL(2,ActualEisensteinCubic.O))⁻¹) 0 0)=_
  simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  exact symbol_neg_numerator _ _ hd

lemma value_upper_formula (M : levelThree) :
    value M=symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
  have hd := levelThree_bottom_primary M
  have hdet : (M:SL(2,ActualEisensteinCubic.O)) 0 0*(M:SL(2,ActualEisensteinCubic.O)) 1 1-
      (M:SL(2,ActualEisensteinCubic.O)) 0 1*(M:SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,ActualEisensteinCubic.O)).property
  have hprod : symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)=1 := by
    rw [←symbol_mul_numerator _ _ _ hd]
    calc
      _ = symbol (-1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) := by
        apply symbol_congr
        refine ⟨(M:SL(2,ActualEisensteinCubic.O)) 0 0,?_⟩
        linear_combination -hdet
      _ = 1 := symbol_neg_one _ hd
  have hinv : value M*symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)=1 := by
    rw [←value_inverse_formula,←value_mul,mul_inv_cancel,value_one]
  calc
    value M = value M*1 := by rw [mul_one]
    _ = value M*(symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)) := by rw [hprod]
    _ = symbol ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)*
      (value M*symbol ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 1 1)) := by ring
    _ = _ := by rw [hinv,mul_one]

theorem value_conjugate_S (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=value M := by
  rw [value_upper_formula M]
  change symbol (((rationalEmbedding ModularGroup.S)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.S)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.S)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.S)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_S,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa using symbol_neg_numerator ((M:SL(2,ActualEisensteinCubic.O)) 0 1) ((M:SL(2,ActualEisensteinCubic.O)) 1 1) (levelThree_bottom_primary M)

theorem complexCharacter_conjugate_S (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding ModularGroup.S) M)=complexCharacter M :=
  congrArg ConcreteTraceCRT.eisEmbedding (value_conjugate_S M)

end CubicKubota

namespace CubicJacobiGlobal
open ActualEisensteinCubic

theorem symbol_shift_by_self (c a : ActualEisensteinCubic.O) (ha : lambda^2∣a-1) (hc : (3:ActualEisensteinCubic.O)∣c) :
    symbol c (a+c)=symbol c a := by
  have hA : lambda^2∣a+c-1 := by
    convert dvd_add ha (lambda_sq_dvd_three.trans hc) using 1 ; ring
  calc
    symbol c (a+c)=symbol (-a) (a+c) := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
    _ = symbol a (a+c) := symbol_neg_numerator a (a+c) hA
    _ = symbol (a+c) a := symbol_reciprocity a (a+c) (primary_ne_zero a ha)
      (primary_ne_zero (a+c) hA) ha hA
    _ = symbol c a := by
      apply symbol_congr
      refine ⟨1,?_⟩
      ring
end CubicJacobiGlobal

namespace CubicKubota
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

theorem value_conjugate_T (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding ModularGroup.T) M)=value M := by
  change symbol (((rationalEmbedding ModularGroup.T)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.T)⁻¹) 1 0)
    (((rationalEmbedding ModularGroup.T)*(M:SL(2,ActualEisensteinCubic.O))*(rationalEmbedding ModularGroup.T)⁻¹) 0 0)=_
  simp only [rationalEmbedding,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_inv,ModularGroup.coe_T,Matrix.adjugate_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]
  simpa [value] using symbol_shift_by_self ((M:SL(2,ActualEisensteinCubic.O)) 1 0) ((M:SL(2,ActualEisensteinCubic.O)) 0 0)
    (levelThree_primary M) (levelThree_lower M)

lemma levelThreeConjugate_one (M : levelThree) : levelThreeConjugate 1 M=M := by
  apply Subtype.ext
  simp [levelThreeConjugate]

lemma levelThreeConjugate_mul (g h : SL(2,ActualEisensteinCubic.O)) (M : levelThree) :
    levelThreeConjugate (g*h) M=levelThreeConjugate g (levelThreeConjugate h M) := by
  apply Subtype.ext
  simp [levelThreeConjugate,mul_assoc]

def characterConjugationStabilizer : Subgroup (SL(2,ActualEisensteinCubic.O)) where
  carrier g := ∀M : levelThree,value (levelThreeConjugate g M)=value M
  one_mem' M := by rw [levelThreeConjugate_one]
  mul_mem' hg hh M := by rw [levelThreeConjugate_mul,hg,hh]
  inv_mem' {g} hg M := by
    have h := hg (levelThreeConjugate g⁻¹ M)
    rw [←levelThreeConjugate_mul,mul_inv_cancel,levelThreeConjugate_one] at h
    exact h.symm

theorem value_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    value (levelThreeConjugate (rationalEmbedding g) M)=value M := by
  have htop : characterConjugationStabilizer.comap rationalEmbedding=⊤ := by
    apply top_unique
    rw [←SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (rfl|rfl)
    · exact value_conjugate_S
    · exact value_conjugate_T
  have hg : g∈characterConjugationStabilizer.comap rationalEmbedding := by rw [htop];trivial
  exact hg M

theorem complexCharacter_conjugate_rational (g : SL(2,ℤ)) (M : levelThree) :
    complexCharacter (levelThreeConjugate (rationalEmbedding g) M)=complexCharacter M :=
  congrArg ConcreteTraceCRT.eisEmbedding (value_conjugate_rational g M)

end CubicKubota
end

open scoped BigOperators Classical
namespace CubicJacobiGlobal
open ActualEisensteinCubic
open CubicRamified
open CompletedGauss hiding O

def rationalPrimary (n : ℕ) : ActualEisensteinCubic.O := if n%3=1 then (n:ActualEisensteinCubic.O) else -(n:ActualEisensteinCubic.O)

lemma rationalPrimary_coord (n : ℕ) (hn : ¬3∣n) : ∃A : ℤ,rationalPrimary n=primaryCoord A 0 := by
  have hm : n%3=1 ∨ n%3=2 := by
    have hl := Nat.mod_lt n (by decide : 0<3)
    have h0 : n%3≠0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    omega
  rcases hm with hm|hm
  · refine ⟨(n/3:ℕ),?_⟩
    have he : n=1+3*(n/3) := by omega
    rw [rationalPrimary,ite_eq_left hm,primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring
  · refine ⟨-((n/3:ℕ):ℤ)-1,?_⟩
    have he : n=2+3*(n/3) := by omega
    rw [rationalPrimary,ite_eq_right (by omega),primaryCoord_eq]
    conv_lhs => rw [he]
    simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,]
    ring

lemma rationalPrimary_primary (n : ℕ) (hn : ¬3∣n) : lambda^2∣rationalPrimary n-1 := by
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  exact primaryCoord_primary A 0

lemma rationalPrimary_denominator (x : ActualEisensteinCubic.O) (n : ℕ) : symbol x (rationalPrimary n)=symbol x (n:ActualEisensteinCubic.O) := by
  unfold rationalPrimary
  split_ifs
  · rfl
  · simp only [symbol,Ideal.span_singleton_neg]

lemma rationalPrimary_numerator (m n : ℕ) (hn : ¬3∣n) :
    symbol (rationalPrimary m) (rationalPrimary n)=symbol (m:ActualEisensteinCubic.O) (rationalPrimary n) := by
  change symbol (if m%3=1 then (m:ActualEisensteinCubic.O) else -(m:ActualEisensteinCubic.O)) (rationalPrimary n)=_
  split_ifs
  · rfl
  · exact symbol_neg_numerator _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_mul (a b n : ℕ) (hn : ¬3∣n) :
    symbol ((a*b:ℕ):ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol (a:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)*symbol (b:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O) := by
  rw [←rationalPrimary_denominator _ n,←rationalPrimary_denominator (a:ActualEisensteinCubic.O) n,
    ←rationalPrimary_denominator (b:ActualEisensteinCubic.O) n,Nat.cast_mul]
  exact symbol_mul_numerator _ _ _ (rationalPrimary_primary n hn)

lemma rational_symbol_three (n : ℕ) (hn : ¬3∣n) : symbol (3:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
  rw [←rationalPrimary_denominator _ n]
  obtain ⟨A,hA⟩ := rationalPrimary_coord n hn
  rw [hA]
  have hprimary := primaryCoord_primary A 0
  have hthree : (3:ActualEisensteinCubic.O)=-((1+2*omega)^2) := by
    have hw : omega^2=-omega-1 := by
      change (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger^2=
        -(IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger-1
      exact IsCyclotomicExtension.Rat.Three.eta_sq (IsCyclotomicExtension.zeta_spec 3 ℚ K)
    linear_combination 4*hw
  have htrace := symbol_traceLambda_eq_linearRay (primaryCoord A 0) hprimary
  change symbol (1+2*omega) (primaryCoord A 0)=_ at htrace
  rw [hthree,symbol_neg_numerator _ _ hprimary,symbol_pow_numerator _ _ hprimary,
    htrace,linearRay_primaryCoord]
  simp

lemma rational_symbol_reciprocity (m n : ℕ) (hm : ¬3∣m) (hn : ¬3∣n) :
    symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol (n:ActualEisensteinCubic.O) (m:ActualEisensteinCubic.O) := by
  calc
    _ = symbol (rationalPrimary m) (rationalPrimary n) := by
      rw [rationalPrimary_numerator m n hn,rationalPrimary_denominator]
    _ = symbol (rationalPrimary n) (rationalPrimary m) :=
      symbol_reciprocity _ _ (primary_ne_zero _ (rationalPrimary_primary m hm))
        (primary_ne_zero _ (rationalPrimary_primary n hn))
        (rationalPrimary_primary m hm) (rationalPrimary_primary n hn)
    _ = _ := by rw [rationalPrimary_numerator n m hm,rationalPrimary_denominator]

lemma rational_symbol_mod (m n : ℕ) : symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=symbol ((m%n:ℕ):ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O) := by
  apply symbol_congr
  refine ⟨(m/n:ℕ),?_⟩
  have he : m=m%n+n*(m/n) := (Nat.mod_add_div m n).symm
  have hh : (m:ActualEisensteinCubic.O)=(m%n:ℕ)+ (n:ActualEisensteinCubic.O)*(m/n:ℕ) := by exact_mod_cast he
  linear_combination hh

theorem rational_symbol_eq_one (n : ℕ) (hn : ¬3∣n) (m : ℕ) (hmn : Nat.Coprime m n) :
    symbol (m:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hn1 : n=1
    · subst n
      simpa only [Nat.cast_one] using symbol_one (m:ActualEisensteinCubic.O)
    have hn0 : 0<n := Nat.pos_of_ne_zero (fun h => hn (by rw [h];exact dvd_zero 3))
    have hsmall : ∀r : ℕ,r<n → Nat.Coprime r n → symbol (r:ActualEisensteinCubic.O) (n:ActualEisensteinCubic.O)=1 := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ihr =>
        intro hrn hcop
        by_cases hr0 : r=0
        · subst r
          have : n=1 := by simpa using hcop
          exact False.elim (hn1 this)
        by_cases hr3 : 3∣r
        · have hquot : r/3<r := Nat.div_lt_self (Nat.pos_of_ne_zero hr0) (by decide)
          have hfactor : r=3*(r/3) := (Nat.mul_div_cancel' hr3).symm
          have hqc : Nat.Coprime (r/3) n := hcop.of_dvd_left (Nat.div_dvd_of_dvd hr3)
          rw [hfactor,rational_symbol_mul _ _ n hn]
          norm_num only [Nat.cast_ofNat]
          rw [rational_symbol_three n hn,one_mul]
          exact ihr (r/3) hquot (lt_trans hquot hrn) hqc
        · rw [rational_symbol_reciprocity r n hr3 hn]
          exact ih r hrn hr3 n hcop.symm
    rw [rational_symbol_mod]
    apply hsmall (m%n) (Nat.mod_lt m hn0)
    change Nat.gcd (m%n) n=1
    rw [←Nat.gcd_rec n m]
    exact hmn.symm

end CubicJacobiGlobal

section

open scoped BigOperators Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic

lemma primary_int_natAbs_not_three (a : ℤ) (ha : lambda^2∣(a:ActualEisensteinCubic.O)-1) : ¬3∣a.natAbs := by
  intro h
  have hInt : (3:ℤ)∣a := Int.natCast_dvd.mpr h
  have hO : (3:ActualEisensteinCubic.O)∣(a:ActualEisensteinCubic.O) := by
    rcases hInt with ⟨b,hb⟩
    refine ⟨(b:ActualEisensteinCubic.O),?_⟩
    simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) hb
  have hL2 : lambda∣lambda^2 := dvd_pow_self _ (by decide : (2:ℕ)≠0)
  have hLa := (hL2.trans lambda_sq_dvd_three).trans hO
  have hLa1 := hL2.trans ha
  have h1 : lambda∣(1:ActualEisensteinCubic.O) := by
    convert dvd_sub hLa hLa1 using 1 ; ring
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h1)

theorem integer_symbol_eq_one (c a : ℤ) (ha : lambda^2∣(a:ActualEisensteinCubic.O)-1)
    (hcop : Nat.Coprime c.natAbs a.natAbs) : symbol (c:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=1 := by
  have hnum : symbol (c:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=symbol (c.natAbs:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O) := by
    rcases Int.natAbs_eq c with h|h
    · have he : (c:ActualEisensteinCubic.O)=(c.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact congrArg (fun z : ActualEisensteinCubic.O => symbol z (a:ActualEisensteinCubic.O)) he
    · have he : (c:ActualEisensteinCubic.O)=-(c.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact (congrArg (fun z : ActualEisensteinCubic.O => symbol z (a:ActualEisensteinCubic.O)) he).trans
        (symbol_neg_numerator _ _ ha)
  rw [hnum]
  have hden : symbol (c.natAbs:ActualEisensteinCubic.O) (a:ActualEisensteinCubic.O)=symbol (c.natAbs:ActualEisensteinCubic.O) (a.natAbs:ActualEisensteinCubic.O) := by
    rcases Int.natAbs_eq a with h|h
    · have he : (a:ActualEisensteinCubic.O)=(a.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      exact congrArg (symbol (c.natAbs:ActualEisensteinCubic.O)) he
    · have he : (a:ActualEisensteinCubic.O)=-(a.natAbs:ActualEisensteinCubic.O) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ActualEisensteinCubic.O)) h
      rw [he]
      simp only [symbol,Ideal.span_singleton_neg]
  rw [hden]
  exact rational_symbol_eq_one a.natAbs (primary_int_natAbs_not_three a ha) c.natAbs hcop
end CubicJacobiGlobal

namespace CubicKubota

section
open ActualEisensteinCubic
open CubicJacobiGlobal hiding O

theorem value_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    value ⟨rationalEmbedding g,hg⟩=1 := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hcop : IsCoprime (g 1 0) (g 0 0) := by
    refine ⟨-(g 0 1),g 1 1,?_⟩
    linear_combination hdet
  have hp := levelThree_primary ⟨rationalEmbedding g,hg⟩
  change lambda^2∣((g 0 0:ℤ):ActualEisensteinCubic.O)-1 at hp
  change symbol ((g 1 0:ℤ):ActualEisensteinCubic.O) ((g 0 0:ℤ):ActualEisensteinCubic.O)=1
  exact integer_symbol_eq_one (g 1 0) (g 0 0) hp (Int.isCoprime_iff_nat_coprime.mp hcop)

theorem complexCharacter_rational_intersection (g : SL(2,ℤ)) (hg : rationalEmbedding g∈levelThree) :
    complexCharacter ⟨rationalEmbedding g,hg⟩=1 := by
  change ConcreteTraceCRT.eisEmbedding (value ⟨rationalEmbedding g,hg⟩)=1
  rw [value_rational_intersection g hg,map_one]

end

open ActualEisensteinCubic

def levelTwo : Subgroup (SL(2,ActualEisensteinCubic.O)) where
  carrier g := ∃n : levelThree,∃r : SL(2,ℤ),(n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=g
  one_mem' := ⟨1,1,by simp⟩
  mul_mem' := by
    rintro g h ⟨n,r,rfl⟩ ⟨m,s,rfl⟩
    refine ⟨n*levelThreeConjugate (rationalEmbedding r) m,r*s,?_⟩
    simp [levelThreeConjugate,map_mul,mul_assoc]
  inv_mem' := by
    rintro g ⟨n,r,rfl⟩
    refine ⟨levelThreeConjugate (rationalEmbedding r⁻¹) n⁻¹,r⁻¹,?_⟩
    simp [levelThreeConjugate,map_inv,mul_assoc]

lemma levelThree_le_levelTwo : levelThree≤levelTwo := by
  intro g hg
  exact ⟨⟨g,hg⟩,1,by simp⟩

lemma rational_mem_levelTwo (r : SL(2,ℤ)) : rationalEmbedding r∈levelTwo :=
  ⟨1,r,by simp⟩

lemma levelTwo_eq_sup : levelTwo=levelThree⊔rationalEmbedding.range := by
  apply le_antisymm
  · rintro g ⟨n,r,rfl⟩
    exact Subgroup.mul_mem _
      ((show levelThree≤levelThree⊔rationalEmbedding.range from le_sup_left) n.property)
      ((show rationalEmbedding.range≤levelThree⊔rationalEmbedding.range from le_sup_right) ⟨r,rfl⟩)
  · apply sup_le levelThree_le_levelTwo
    rintro g ⟨r,rfl⟩
    exact rational_mem_levelTwo r

lemma complexCharacter_product_well_defined (n m : levelThree) (r s : SL(2,ℤ))
    (h : (n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=(m:SL(2,ActualEisensteinCubic.O))*rationalEmbedding s) :
    complexCharacter n=complexCharacter m := by
  have he : ((m⁻¹*n:levelThree):SL(2,ActualEisensteinCubic.O))=rationalEmbedding (s*r⁻¹) := by
    have hh := congrArg (fun g : SL(2,ActualEisensteinCubic.O)=>(m:SL(2,ActualEisensteinCubic.O))⁻¹*g*(rationalEmbedding r)⁻¹) h
    simpa [map_mul,map_inv,mul_assoc] using hh
  have hm : rationalEmbedding (s*r⁻¹)∈levelThree := he ▸ (m⁻¹*n).property
  have hv : complexCharacter (m⁻¹*n)=1 := by
    have he' : (m⁻¹*n:levelThree)=⟨rationalEmbedding (s*r⁻¹),hm⟩ := Subtype.ext he
    rw [he']
    exact complexCharacter_rational_intersection (s*r⁻¹) hm
  calc
    complexCharacter n=complexCharacter (m*(m⁻¹*n)) := by rw [mul_inv_cancel_left]
    _ = complexCharacter m*complexCharacter (m⁻¹*n) := map_mul _ _ _
    _ = complexCharacter m := by rw [hv,mul_one]

def levelTwoLeft (g : levelTwo) : levelThree := g.property.choose

def levelTwoRight (g : levelTwo) : SL(2,ℤ) := g.property.choose_spec.choose

lemma levelTwo_product (g : levelTwo) :
    (levelTwoLeft g:SL(2,ActualEisensteinCubic.O))*rationalEmbedding (levelTwoRight g)=(g:SL(2,ActualEisensteinCubic.O)) :=
  g.property.choose_spec.choose_spec

def levelTwoValue (g : levelTwo) : ℂ := complexCharacter (levelTwoLeft g)

lemma levelTwoValue_of_product (g : levelTwo) (n : levelThree) (r : SL(2,ℤ))
    (h : (n:SL(2,ActualEisensteinCubic.O))*rationalEmbedding r=(g:SL(2,ActualEisensteinCubic.O))) : levelTwoValue g=complexCharacter n :=
  complexCharacter_product_well_defined (levelTwoLeft g) n (levelTwoRight g) r
    ((levelTwo_product g).trans h.symm)

def levelTwoComplexCharacter : levelTwo→*ℂ where
  toFun := levelTwoValue
  map_one' := by
    rw [levelTwoValue_of_product 1 1 1 (by simp),map_one]
  map_mul' g h := by
    have hp :
        ((levelTwoLeft g*levelThreeConjugate (rationalEmbedding (levelTwoRight g)) (levelTwoLeft h):levelThree):SL(2,ActualEisensteinCubic.O))*
          rationalEmbedding (levelTwoRight g*levelTwoRight h)=((g*h:levelTwo):SL(2,ActualEisensteinCubic.O)) := by
      simp only [Subgroup.coe_mul,levelThreeConjugate,map_mul]
      simp only [mul_assoc,inv_mul_cancel_left]
      rw [←levelTwo_product g,←levelTwo_product h]
      group
    rw [levelTwoValue_of_product (g*h) _ _ hp,map_mul,complexCharacter_conjugate_rational]
    rfl

lemma levelTwoComplexCharacter_restrict (n : levelThree) :
    levelTwoComplexCharacter ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩=complexCharacter n := by
  exact levelTwoValue_of_product _ n 1 (by simp)

lemma levelTwoComplexCharacter_rational (r : SL(2,ℤ)) :
    levelTwoComplexCharacter ⟨rationalEmbedding r,rational_mem_levelTwo r⟩=1 := by
  exact (levelTwoValue_of_product _ 1 r (by simp)).trans (map_one _)

lemma levelTwoComplexCharacter_cube (g : levelTwo) : levelTwoComplexCharacter g^3=1 :=
  complexCharacter_cube (levelTwoLeft g)

lemma norm_levelTwoComplexCharacter (g : levelTwo) : ‖levelTwoComplexCharacter g‖=1 :=
  norm_complexCharacter (levelTwoLeft g)

end CubicKubota
end

namespace CubicKubota

open scoped Classical MatrixGroups
open ActualEisensteinCubic
open CubicEisenstein

theorem globalKubotaKernel_conjugate (g : levelTwo) (k : SL(2,ActualEisensteinCubic.O))
    (hk : k∈globalKubotaKernel) :
    (g:SL(2,ActualEisensteinCubic.O))*k*(g:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel := by
  obtain ⟨hk3,hkv⟩ := (globalKubotaKernel_mem k).mp hk
  let n : levelThree := ⟨k,hk3⟩
  let n2 : levelTwo := ⟨k,levelThree_le_levelTwo hk3⟩
  let cn := levelThreeConjugate (g:SL(2,ActualEisensteinCubic.O)) n
  refine (globalKubotaKernel_mem _).mpr ⟨cn.property,?_⟩
  change complexCharacter cn=1
  rw [←levelTwoComplexCharacter_restrict cn]
  have he : (⟨(cn:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo cn.property⟩:levelTwo)=g*n2*g⁻¹ :=
    Subtype.ext rfl
  rw [he,map_mul,map_mul]
  have hn : levelTwoComplexCharacter n2=1 :=
    (levelTwoComplexCharacter_restrict n).trans hkv
  rw [hn,mul_one,←map_mul,mul_inv_cancel,map_one]

def kernelInLevelTwo : Subgroup levelTwo := globalKubotaKernel.comap levelTwo.subtype

instance kernelInLevelTwo_normal : kernelInLevelTwo.Normal where
  conj_mem k hk g := globalKubotaKernel_conjugate g k hk

theorem globalKubotaKernel_rational_conjugate_iff (r : SL(2,ℤ)) (k : SL(2,ActualEisensteinCubic.O)) :
    rationalEmbedding r*k*(rationalEmbedding r)⁻¹∈globalKubotaKernel ↔
      k∈globalKubotaKernel := by
  constructor
  · intro h
    have hh := globalKubotaKernel_conjugate
      (⟨rationalEmbedding r⁻¹,rational_mem_levelTwo r⁻¹⟩:levelTwo) _ h
    simpa [map_inv,mul_assoc] using hh
  · exact globalKubotaKernel_conjugate
      (⟨rationalEmbedding r,rational_mem_levelTwo r⟩:levelTwo) k

end CubicKubota

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein

def cuspHeightCompact (a b : ℝ) : Set HyperbolicSpace :=
  cuspCoordinateLift '' (Set.Icc a b ×ˢ Metric.closedBall (0:ℂ) (∑i,‖periodBasis i‖))

lemma cuspHeightCompact_isCompact (a b : ℝ) (ha : 0<a) : IsCompact (cuspHeightCompact a b) := by
  apply (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
  intro q hq
  exact (cuspCoordinateLift_continuousAt q (ha.trans_le hq.1.1)).continuousWithinAt

lemma cuspPeriodStrip_subset_heightCompact (a b : ℝ) (_ha : 0<a) :
    cuspPeriodStrip a b⊆cuspHeightCompact a b := by
  intro w hw
  refine ⟨(hyperbolicHeight w,hyperbolicHorizontal w),⟨hw.2,?_⟩,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain _ hw.1
  · rw [←spatialComplexSplit_coordinates,cuspCoordinateLift,
      spatialComplexSplit.symm_apply_apply,euclideanToHyperbolic_coordinates]

lemma cuspPeriodStrip_measure_ne_top_of_pos (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume (cuspPeriodStrip a b)≠(⊤:ℝ≥0∞) := by
  apply ne_of_lt
  exact (measure_mono (cuspPeriodStrip_subset_heightCompact a b ha)).trans_lt
    (cuspHeightCompact_isCompact a b ha).measure_lt_top

theorem cuspPeriodStripFiniteVolume (a b : ℝ) (ha : 0<a) :
    IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  isFiniteMeasure_restrict.mpr (cuspPeriodStrip_measure_ne_top_of_pos a b ha)

lemma cuspStrip_restrict_le_compact (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume.restrict (cuspPeriodStrip a b)≤
      (1:ℝ≥0∞) • hyperbolicVolume.restrict (cuspHeightCompact a b) := by
  simpa only [one_smul] using
    (Measure.restrict_mono_set hyperbolicVolume (cuspPeriodStrip_subset_heightCompact a b ha))

abbrev CuspHeightStripL2 (a b : ℝ) := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip a b))

def kernelCuspHeightPullback (a b : ℝ) (ha : 0<a) : KernelQuotientL2→L[ℂ]CuspHeightStripL2 a b :=
  (dominatedComplexL2 (by simp : (1:ℝ≥0∞)≠⊤) (cuspStrip_restrict_le_compact a b ha)).comp
    (kernelCompactPullbackCLM (cuspHeightCompact a b) (cuspHeightCompact_isCompact a b ha))

lemma kernelCuspHeightPullback_ae (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    kernelCuspHeightPullback a b ha F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hfirst := dominatedComplexL2_ae (by simp : (1:ℝ≥0∞)≠⊤) (cuspStrip_restrict_le_compact a b ha)
    (kernelCompactPullbackCLM (cuspHeightCompact a b) (cuspHeightCompact_isCompact a b ha) F)
  have hsecond := (Measure.absolutelyContinuous_of_le_smul (cuspStrip_restrict_le_compact a b ha)).ae_eq
    (kernelCompactPullbackCLM_ae (cuspHeightCompact a b) (cuspHeightCompact_isCompact a b ha) F)
  exact hfirst.trans hsecond

lemma kernelCuspHeight_quasiMeasurePreserving (a b : ℝ) (ha : 0<a) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) (integralQuotientVolume globalKubotaKernel) := by
  have hcompact : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspHeightCompact a b)) (integralQuotientVolume globalKubotaKernel) :=
    ⟨measurable_integralOrbitProjection _,
      Measure.absolutelyContinuous_of_le_smul (kernelCompactMultiplicity_spec _ (cuspHeightCompact_isCompact a b ha))⟩
  exact ⟨hcompact.measurable,
    ((Measure.absolutelyContinuous_of_le_smul (cuspStrip_restrict_le_compact a b ha)).map
      (measurable_integralOrbitProjection _)).trans hcompact.absolutelyContinuous⟩

def cuspHeightQuotientCompact (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspHeightCompact a b

lemma cuspHeightQuotientCompact_isCompact (a b : ℝ) (ha : 0<a) :
    IsCompact (cuspHeightQuotientCompact a b) :=
  (cuspHeightCompact_isCompact a b ha).image (continuous_integralOrbitProjection _)

lemma cuspPeriodStrip_image_subset (a b : ℝ) (ha : 0<a) :
    integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b⊆cuspHeightQuotientCompact a b :=
  Set.image_mono (cuspPeriodStrip_subset_heightCompact a b ha)

def positiveEuclideanStrip (a b : ℝ) : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc a b ×ˢ periodDomain)

lemma positiveEuclideanStrip_measurable (a b : ℝ) : MeasurableSet (positiveEuclideanStrip a b) :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma positiveEuclideanStrip_positive (a b : ℝ) (ha : 0<a) :
    positiveEuclideanStrip a b⊆euclideanUpperHalf := by
  intro p hp
  exact ha.trans_le hp.1.1

lemma positiveEuclideanStrip_preimage (a b : ℝ) :
    hyperbolicEuclideanCoordinates ⁻¹' positiveEuclideanStrip a b=cuspPeriodStrip a b := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc a b ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates_of_pos (a b : ℝ) (ha : 0<a)
    (g : HyperbolicSpace→ℂ) (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
  rw [positiveEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip a b))
  have he : (∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume)=
      ∫p in positiveEuclideanStrip a b,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc a b ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in positiveEuclideanStrip a b,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc a b ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [positiveEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc a b ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma cuspCoordinateLift_weighted_integrable_of_pos (a b : ℝ) (ha : 0<a)
    (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := ha.trans_le hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2

end CubicEisenstein

end

end OAI
end OAIOriginalModule0263

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierBounds
Source SHA256: 3992a53330dc896355f9744e89f09781b055d2a8d0c99c3f87ddc1d2249c020d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0264



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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspHeightFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  let := cuspPeriodStripFiniteVolume a b ha
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

def cuspHeightFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : CuspHeightStripL2 a b :=
  (cuspHeightFourierTest_memLp a b ha ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))

def kernelCuspHeightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspHeightFourierTestL2 a b ha ρ h)).comp (kernelCuspHeightPullback a b ha)

lemma kernelCuspHeightFourier_integral (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h F=∫w in cuspPeriodStrip a b,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h),
    kernelCuspHeightPullback_ae a b ha F] with w hw hp
  rw [RCLike.inner_apply,cuspHeightFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspHeightFourier_restrict (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h (kernelMassRestrictionCLM (cuspHeightQuotientCompact a b)
      (cuspHeightQuotientCompact_isCompact a b ha).measurableSet F)=kernelCuspHeightFourier a b ha ρ h F := by
  rw [kernelCuspHeightFourier_integral,kernelCuspHeightFourier_integral]
  have he := (kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp
    (kernelMassRestriction_coe (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩) _))

def kernelCuspHeightFourierFamily (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspHeightFourier a b ha ρ h
    (kernelLocalCorrectedSeed (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha)
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspHeightFourierFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspHeightFourierFamily a b ha ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspHeightFourier a b ha ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal (cuspHeightQuotientCompact a b)
        (cuspHeightQuotientCompact_isCompact a b ha) 2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma kernelCuspHeightFourierFamily_residue_limit (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspHeightFourierFamily a b ha ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspHeightFourier a b ha ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspHeightFourier_restrict,
    kernelCuspHeightFourierFamily] using hh

lemma kernelCuspHeightFourierFamily_initial (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ h s=∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspHeightFourierFamily,kernelCuspHeightFourier_integral]
  have he := (kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (cuspHeightQuotientCompact a b)
      (cuspHeightQuotientCompact_isCompact a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]

def cuspIntervalWhittakerHeightFactor (a b : ℝ)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc a b,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))

lemma hyperbolicEisenstein_cusp_height_fourier_nonzero (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  have hexp : ∀v∈Set.Icc a b,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := ha.trans_le hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,ite_eq_right hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc a b,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _

lemma kernelCuspHeightFourierFamily_initial_factor (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  rw [kernelCuspHeightFourierFamily_initial a b ha ρ h s hs hi,
    hyperbolicEisenstein_cusp_height_fourier_nonzero a b ha ρ s (by linarith) h hh]

lemma cuspIntervalWhittakerHeightFactor_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspIntervalWhittakerHeightFactor a b ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  have heq : (fun s => cuspIntervalWhittakerHeightFactor a b ρ s h)=
      (fun s => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (mul_assoc _ _ _).symm)
  rw [heq]
  exact cuspWeightedWhittakerInterval_differentiableAt ρ a b ha (cuspFrequency h) w hw

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma kernelCuspHeightFourierFamily_cross_identity (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (kernelCuspHeightFourierFamily_analyticAt_nonreal a b ha ρ h s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) domain := by
    intro s hs
    exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
          cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [kernelCuspHeightFourierFamily_initial_factor a b ha ρ h hh s hs.1 hs.2,
      kernelCuspFourierFamily_eq_upper h hh ⟨by linarith [hs.1],hs.2⟩]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma kernelCuspHeightFourier_residue_factor (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*nonzeroScatteringResidue h*
        cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hbase : Tendsto (fun s : ℂ => cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) h)) :=
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => cuspIntervalWhittakerHeightFactor a b ρ s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h)) :=
    (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((kernelCuspHeightFourierFamily_residue_limit a b ha ρ h).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspHeightFourierFamily a b ha ρ h ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
        ((4/3:ℂ)+(t:ℂ)*Complex.I))*cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := kernelCuspHeightFourierFamily_cross_identity a b ha ρ h hh hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      kernelCuspFourier h cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hH := cuspWhittakerHeightFactor_center_ne_zero h
  calc
    _ = (kernelCuspFourier h cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h)/
        cuspWhittakerHeightFactor (4/3:ℂ) h := (eq_div_iff hH).mpr heq
    _ = _ := by
      unfold nonzeroScatteringResidue
      field_simp [cusp_volume_ne_zero,hH]

lemma cuspIntervalWhittakerHeightFactor_center_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h=
      cubicBesselNormalizer h*(∫v in Set.Icc a b,
        ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  dsimp only
  rw [sourceFourierKernel_cubic_height h hh v hpos]
  ring

lemma kernelCuspHeightFourier_residue_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFourierCoefficient h*
        (∫v in Set.Icc a b,ρ v*
          (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [kernelCuspHeightFourier_residue_factor a b ha ρ h hh,
    cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,cubicResidualFourierCoefficient]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma kernelCuspHeightFourier_uniform_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(ρ : BoundedContinuousFunction ℝ ℂ)(h : ActualEisensteinCubic.O)(F : KernelQuotientL2),
      ‖kernelCuspHeightFourier a b ha ρ h F‖≤C*‖ρ‖*‖F‖ := by
  let := cuspPeriodStripFiniteVolume a b ha
  let mass : ℝ := (measureUnivNNReal (hyperbolicVolume.restrict (cuspPeriodStrip a b)):ℝ)^((2:ℝ≥0∞).toReal)⁻¹
  have hmass : 0≤mass := Real.rpow_nonneg (by positivity) _
  refine ⟨mass*‖kernelCuspHeightPullback a b ha‖,mul_nonneg hmass (norm_nonneg _),?_⟩
  intro ρ h F
  have htest : ‖cuspHeightFourierTestL2 a b ha ρ h‖≤mass*‖ρ‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg ρ)
    filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h)] with w hw
    change ‖cuspHeightFourierTestL2 a b ha ρ h w‖≤‖ρ‖
    rw [cuspHeightFourierTestL2,hw,norm_star]
    exact cuspWeightedFourierPhase_bound ρ h w
  change ‖inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)‖≤_
  calc
    _ ≤ ‖cuspHeightFourierTestL2 a b ha ρ h‖*‖kernelCuspHeightPullback a b ha F‖ := norm_inner_le_norm _ _
    _ ≤ (mass*‖ρ‖)*(‖kernelCuspHeightPullback a b ha‖*‖F‖) :=
      mul_le_mul htest ((kernelCuspHeightPullback a b ha).le_opNorm F) (norm_nonneg _)
        (mul_nonneg hmass (norm_nonneg _))
    _ = _ := by ring

lemma cubicResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖cubicResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖cubicEisensteinResidue‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelCuspHeightFourier_residue_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h cubicEisensteinResidue
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

def cubicBesselDensity (x t : ℝ) : ℝ :=
  t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t))

lemma cubicBesselDensity_integrable (x : ℝ) :
    IntegrableOn (cubicBesselDensity x) (Set.Ioi 0) := by
  have hi := (schlafliIntegral_integrable (1/3:ℂ) x (by norm_num)).re
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
    schlafliIntegrand_real (1/3) x t ht]
  change t^((1/3:ℝ)-1)*Real.exp (-t-x^2/(4*t))=cubicBesselDensity x t
  norm_num [cubicBesselDensity]

lemma cubicBesselDensity_nonneg (x t : ℝ) (ht : 0≤t) : 0≤cubicBesselDensity x t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

lemma schlafliIntegral_cubic_real (x : ℝ) :
    schlafliIntegral (1/3:ℂ) x=((∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t):ℝ) := by
  unfold schlafliIntegral
  calc
    _ = ∫t in Set.Ioi (0:ℝ),((cubicBesselDensity x t:ℝ):ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
        schlafliIntegrand_real (1/3) x t ht]
      norm_num [cubicBesselDensity]
    _ = _ := integral_ofReal

lemma schlafliBesselK_cubic_real (x : ℝ) (hx : 0<x) :
    schlafliBesselK (1/3:ℂ) x=
      (((1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)):ℝ) := by
  rw [schlafliBesselK,schlafliIntegral_cubic_real]
  have hp := Complex.ofReal_cpow (show 0≤x/2 by positivity) (-(1:ℝ)/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat,neg_div] at hp
  rw [←hp]
  push_cast
  ring_nf

lemma schlafliBesselK_cubic_norm_re (x : ℝ) (hx : 0<x) :
    ‖schlafliBesselK (1/3:ℂ) x‖=(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  apply Complex.norm_of_nonneg
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicBesselDensity_nonneg x t ht.le

lemma cubicBesselDensity_upper (x t : ℝ) (ht : 0<t) :
    cubicBesselDensity x t≤Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hq : -t-x^2/(4*t)≤-x/2-t/2 := by
    have hf : x/2-t/2≤x^2/(4*t) :=
      (le_div_iff₀ (show 0<4*t by positivity)).mpr (by
        nlinarith [sq_nonneg (t-x),sq_nonneg t])
    linarith
  have he := Real.exp_le_exp.mpr hq
  unfold cubicBesselDensity
  calc
    _ ≤ t^(-(2:ℝ)/3)*Real.exp (-x/2-t/2) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring_nf

lemma cubicBesselIntegral_upper (x : ℝ) :
    (∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2:ℝ)/3) (p := (1:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,show ∀t : ℝ,-(1/2)*t=-t/2 by intro t;ring] using h
  have hb := setIntegral_mono_on (cubicBesselDensity_integrable x)
    (hi.const_mul (Real.exp (-x/2))) measurableSet_Ioi (fun t ht => cubicBesselDensity_upper x t ht)
  rw [integral_const_mul] at hb
  have he : (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    convert hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf
  rw [he] at hb
  exact hb

def cubicBesselUpperConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperConstant_pos : 0<cubicBesselUpperConstant := by
  unfold cubicBesselUpperConstant
  positivity

theorem schlafliBesselK_cubic_upper (x : ℝ) (hx : 1≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤cubicBesselUpperConstant*Real.exp (-x/2) := by
  have hxp : 0<x := by linarith
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  have hp : (x/2)^(-(1:ℝ)/3)≤(1/2:ℝ)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperConstant;ring

lemma cubicBesselDensity_lower (x t : ℝ) (hx : 0<x) (ht : t∈Set.Icc x (2*x)) :
    (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)≤cubicBesselDensity x t := by
  have htp : 0<t := hx.trans_le ht.1
  have hp : (2*x)^(-(2:ℝ)/3)≤t^(-(2:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos htp ht.2 (by norm_num)
  have hfrac : x^2/(4*t)≤x/4 :=
    (div_le_iff₀ (show 0<4*t by positivity)).mpr (by nlinarith [ht.1])
  have he : Real.exp (-9*x/4)≤Real.exp (-t-x^2/(4*t)) :=
    Real.exp_le_exp.mpr (by linarith [ht.2])
  exact mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg htp.le _)

lemma cubicBesselIntegral_lower (x : ℝ) (hx : 0<x) :
    x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
  have hsub : Set.Icc x (2*x)⊆Set.Ioi (0:ℝ) := fun t ht => hx.trans_le ht.1
  have hi := cubicBesselDensity_integrable x
  have hr := hi.mono_set hsub
  have hconstant : IntegrableOn (fun _ : ℝ => (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))
      (Set.Icc x (2*x)) := integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hmono := setIntegral_mono_on hconstant hr measurableSet_Icc
    (fun t ht => cubicBesselDensity_lower x t hx ht)
  have hextend : (∫t in Set.Icc x (2*x),cubicBesselDensity x t)≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensity_nonneg x t ht.le
    · exact Eventually.of_forall hsub
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith),smul_eq_mul,
    show 2*x-x=x by ring] at hmono
  exact hmono.trans hextend

def cubicBesselLowerConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*(2:ℝ)^(-(2:ℝ)/3)

lemma cubicBesselLowerConstant_pos : 0<cubicBesselLowerConstant := by
  unfold cubicBesselLowerConstant
  positivity

theorem schlafliBesselK_cubic_lower (x : ℝ) (hx : 0<x) :
    cubicBesselLowerConstant*Real.exp (-9*x/4)≤(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  have hp := mul_le_mul_of_nonneg_left (cubicBesselIntegral_lower x hx)
    (show 0≤(1/2:ℝ)*(x/2)^(-(1:ℝ)/3) by positivity)
  have hnorm : (x/2)^(-(1:ℝ)/3)=(1/2:ℝ)^(-(1:ℝ)/3)*x^(-(1:ℝ)/3) := by
    rw [show x/2=(1/2:ℝ)*x by ring,Real.mul_rpow (by norm_num) hx.le]
  have htwo : (2*x)^(-(2:ℝ)/3)=(2:ℝ)^(-(2:ℝ)/3)*x^(-(2:ℝ)/3) :=
    Real.mul_rpow (by norm_num) hx.le
  have hxp : x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3)=1 := by
    calc
      _ = x^(-(1:ℝ)/3)*x^(1:ℝ)*x^(-(2:ℝ)/3) := by rw [Real.rpow_one]
      _ = x^((-(1:ℝ)/3+1)+(-(2:ℝ)/3)) := by rw [←Real.rpow_add hx,←Real.rpow_add hx]
      _ = 1 := by norm_num
  have he : (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)))=
      cubicBesselLowerConstant*Real.exp (-9*x/4) := by
    rw [hnorm,htwo]
    calc
      _ = cubicBesselLowerConstant*(x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3))*Real.exp (-9*x/4) := by
        unfold cubicBesselLowerConstant
        ring
      _ = _ := by rw [hxp,mul_one]
  rwa [he] at hp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma exp_neg_mul_le_inverse_cube (ε r : ℝ) (hε : 0<ε) (hr : 0<r) :
    Real.exp (-ε*r)≤(6/ε^3)*r^(-3:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp (ε*r) (le_of_lt (mul_pos hε hr)) 3
  norm_num only [Nat.factorial] at hp
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(ε*r)^3/6) hp
  rw [one_div,←Real.exp_neg] at hi
  rw [Real.rpow_neg hr.le]
  norm_num only [Real.rpow_ofNat]
  have halg : (6/ε^3)*(r^3)⁻¹=((ε*r)^3/6)⁻¹ := by
    field_simp
  rw [halg]
  simpa only [neg_mul,one_div] using hi

lemma summable_exp_neg_embedding_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖ConcreteTraceCRT.eisEmbedding h‖)) := by
  have hs := (summable_embedding_rpow (-3) (by norm_num)).mul_left (6/ε^3)
  have hz : Summable (fun h : ActualEisensteinCubic.O => if h=0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq 0 (1:ℝ)).summable
  apply Summable.of_nonneg_of_le (fun h => (Real.exp_pos _).le) _ (hz.add hs)
  intro h
  by_cases hh : h=0
  · subst h
    norm_num [Pi.add_apply]
  · have hp : 0<‖ConcreteTraceCRT.eisEmbedding h‖ :=
      norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh)
    simpa only [Pi.add_apply,ite_eq_right hh,zero_add] using exp_neg_mul_le_inverse_cube ε _ hε hp

lemma summable_exp_neg_cuspFrequency_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖cuspFrequency h‖)) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := by
    apply norm_pos_iff.mpr
    exact mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero
  have hs := summable_exp_neg_embedding_norm (ε/‖(3:ℂ)*ConcreteTraceCRT.eisLam‖) (div_pos hε hd)
  apply hs.congr
  intro h
  congr 1
  rw [cuspFrequency,norm_div]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselNormalizer_ne_zero (h : ActualEisensteinCubic.O) (hh : h≠0) : cubicBesselNormalizer h≠0 := by
  unfold cubicBesselNormalizer
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  · apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh)))

lemma cubicBesselHeight_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    IntegrableOn (fun v : ℝ => schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)
      (Set.Icc a b) volume := by
  have hsource : IntegrableOn (fun v : ℝ => (v:ℂ)^(-(4/3:ℂ)-1)*
      sourceFourierKernel (4/3) (cuspFrequency h*v)) (Set.Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    intro v hv
    have hpos := ha.trans_le hv.1
    exact ((Complex.continuousAt_ofReal_cpow_const v (-(4/3:ℂ)-1) (Or.inr hpos.ne')).mul
      ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
        ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt
  apply (hsource.div_const (cubicBesselNormalizer h)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  apply (div_eq_iff (cubicBesselNormalizer_ne_zero h hh)).mpr
  simpa only [mul_comm] using sourceFourierKernel_cubic_height h hh v (ha.trans_le hv.1)

lemma cubicBesselHeight_average_lower (a b : ℝ) (ha : 0<a) (hab : a<b) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ((b-a)*cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
      ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖ := by
  have hb : 0<b := ha.trans hab
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  let lower : ℝ := (cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)
  have hi := cubicBesselHeight_integrable a b ha h hh
  have hpoint (v : ℝ) (hv : v∈Set.Icc a b) : lower≤
      RCLike.re (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
    have hvp := ha.trans_le hv.1
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v := by positivity
    have hK := schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx
    have he : Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        Real.exp (-9*(4*Real.pi*‖cuspFrequency h‖*v)/4) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hv.2
        (show 0≤9*Real.pi*‖cuspFrequency h‖ by positivity)
      nlinarith [hmul]
    have hnum : cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)).re :=
      (mul_le_mul_of_nonneg_left he cubicBesselLowerConstant_pos.le).trans hK
    have hden : v^2≤b^2 := sq_le_sq₀ hvp.le hb.le |>.mpr hv.2
    change lower≤Complex.re (_/(v:ℂ)^2)
    rw [←Complex.ofReal_pow,Complex.div_ofReal_re]
    calc
      lower = (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/b^2 := by dsimp [lower]; ring
      _ ≤ (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/v^2 :=
        div_le_div_of_nonneg_left (mul_nonneg cubicBesselLowerConstant_pos.le (Real.exp_pos _).le)
          (sq_pos_of_pos hvp) hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg v)
  have hmono := setIntegral_mono_on
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top) : IntegrableOn (fun _ : ℝ => lower) (Set.Icc a b))
    hi.re measurableSet_Icc hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le hab.le,smul_eq_mul] at hmono
  have hreal : (∫v in Set.Icc a b,RCLike.re
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2))=
      Complex.re (∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) :=
    integral_re hi
  rw [hreal] at hmono
  have hfinal := hmono.trans (Complex.re_le_norm _)
  convert hfinal using 1 ; dsimp [lower] ; ring

lemma cubicResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖cubicResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := cubicResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (cubicResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp

end CubicEisenstein

end

end OAI
end OAIOriginalModule0264

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierSeries
Source SHA256: 1a7a32d5eb921322d0bbc830308c217b3e791e22f6f41c5a94a4ed1f890b9a25
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0265


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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspFrequency_norm_lower (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹≤‖cuspFrequency h‖ := by
  have hn : 1≤‖ConcreteTraceCRT.eisEmbedding h‖^2 := by
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hh))
  have hnorm : 1≤‖ConcreteTraceCRT.eisEmbedding h‖ := by nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding h)]
  rw [cuspFrequency,norm_div,inv_eq_one_div]
  exact div_le_div_of_nonneg_right hnorm (norm_nonneg _)

def cubicBesselUpperAway (deltaLoss : ℝ) : ℝ :=
  (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperAway_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) : 0<cubicBesselUpperAway deltaLoss := by
  unfold cubicBesselUpperAway
  positivity

lemma schlafliBesselK_cubic_upper_away (deltaLoss x : ℝ) (hδ : 0<deltaLoss) (hx : deltaLoss≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤cubicBesselUpperAway deltaLoss*Real.exp (-x/2) := by
  have hxp := hδ.trans_le hx
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  have hp : (x/2)^(-(1:ℝ)/3)≤(deltaLoss/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperAway;ring

def cubicResidualNonzeroTerm (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else nonzeroScatteringResidue h*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

lemma cubicResidualNonzeroTerm_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicResidualNonzeroTerm h (v,z)=cubicResidualFourierCoefficient h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicResidualNonzeroTerm,ite_eq_right hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^3*(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ) := by
    rw [←Complex.cpow_ofNat (v:ℂ) 3,←Complex.cpow_add _ _ hv0]
    congr 1
    ring
  have hker := sourceFourierKernel_cubic_height h hh v hv
  calc
    _ = nonzeroScatteringResidue h*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [hker,cubicResidualFourierCoefficient]
      field_simp

lemma cubicResidualNonzeroTerm_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (cubicResidualNonzeroTerm h) {p : ℝ × ℂ | 0<p.1} := by
  unfold cubicResidualNonzeroTerm
  by_cases hh : h=0
  · simp only [ite_eq_left hh]
    exact continuousOn_const
  simp only [ite_eq_right hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

lemma cubicResidualNonzeroTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖cubicResidualNonzeroTerm h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let deltaLoss : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hδ : 0<deltaLoss := by dsimp [deltaLoss];positivity
  have hCu : 0<cubicBesselUpperAway deltaLoss := cubicBesselUpperAway_pos deltaLoss hδ
  obtain ⟨C,hC,hcoeff⟩ := cubicResidualFourierCoefficient_subexponential (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway deltaLoss,mul_nonneg (mul_nonneg hC hb.le) (cubicBesselUpperAway_pos deltaLoss hδ).le,?_⟩
  intro h p hp
  have hv : 0<p.1 := ha.trans_le hp.1
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : deltaLoss≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1
      ha.le (norm_nonneg (cuspFrequency h))
    dsimp [deltaLoss]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [show p=(p.1,p.2) from rfl,cubicResidualNonzeroTerm_bessel h hh _ hv,
    norm_mul,norm_mul,norm_mul,breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  have hkb := schlafliBesselK_cubic_upper_away deltaLoss (4*Real.pi*‖cuspFrequency h‖*p.1) hδ hx
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway deltaLoss*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (mul_nonneg hC (Real.exp_pos _).le))
        hkb (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway deltaLoss)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2 =
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le
      nlinarith

lemma cubicResidualNonzeroTerm_summable (p : ℝ × ℂ) (hp : 0<p.1) :
    Summable (fun h : ActualEisensteinCubic.O => cubicResidualNonzeroTerm h p) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def cubicResidualNonzeroSeries (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,cubicResidualNonzeroTerm h p

lemma cubicResidualNonzeroSeries_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound a b ha hab
  apply continuousOn_tsum (u := fun h : ActualEisensteinCubic.O => C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))
  · intro h
    exact (cubicResidualNonzeroTerm_continuousOn h).mono (fun p hp => ha.trans_le hp.1)
  · exact (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma cubicResidualNonzeroSeries_continuousOn :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | 0<p.1} := by
  intro p hp
  change 0<p.1 at hp
  have hclosed := cubicResidualNonzeroSeries_continuousOn_slab (p.1/2) (2*p.1) (by linarith) (by linarith)
  have hnb : {q : ℝ × ℂ | q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma cubicResidualNonzeroSeries_uniform (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑h∈t,cubicResidualNonzeroTerm h p)
      cubicResidualNonzeroSeries atTop {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound a b ha hab
  exact tendstoUniformlyOn_tsum
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C) hbound

lemma cubicResidualNonzeroSeries_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicResidualNonzeroSeries (v,z)=∑'h : ActualEisensteinCubic.O,if h=0 then 0 else
      cubicResidualFourierCoefficient h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*
        ShortDraftTrace.breveE (cuspFrequency h*z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,ite_eq_left hh]
  · rw [ite_eq_right hh,cubicResidualNonzeroTerm_bessel h hh v hv z]

def cubicResidualNonzeroFunction (w : HyperbolicSpace) : ℂ :=
  cubicResidualNonzeroSeries (hyperbolicHeight w,hyperbolicHorizontal w)

lemma cubicResidualNonzeroFunction_continuous : Continuous cubicResidualNonzeroFunction := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  have hp : (hyperbolicHeight w,hyperbolicHorizontal w)∈{p : ℝ × ℂ | 0<p.1} := hyperbolicHeight_pos w
  exact (cubicResidualNonzeroSeries_continuousOn.continuousAt (hopen.mem_nhds hp)).comp
    (f := fun u : HyperbolicSpace => (hyperbolicHeight u,hyperbolicHorizontal u))
    (hyperbolicHeight_continuous.prodMk hyperbolicHorizontal_continuous).continuousAt

lemma cubicResidualNonzeroSeries_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    cubicResidualNonzeroSeries (v,z+3*ConcreteTraceCRT.eisEmbedding n)=cubicResidualNonzeroSeries (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,ite_eq_left hh]
  simp only [cubicResidualNonzeroTerm,ite_eq_right hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicResidualModeAmplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else cubicResidualFourierCoefficient h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma cubicResidualNonzeroTerm_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    cubicResidualNonzeroTerm h (v,z)=cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,cubicResidualModeAmplitude,ite_eq_left hh,zero_mul]
  · rw [cubicResidualNonzeroTerm_bessel h hh v hv z,cubicResidualModeAmplitude,ite_eq_right hh]

lemma integral_cusp_character_product (h k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  have hphase (z : ℂ) : ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z)=ShortDraftTrace.breveE (-cuspFrequency (k-h)*z) := by
    rw [←AddChar.map_add_eq_mul]
    congr 1
    unfold cuspFrequency
    rw [map_sub]
    ring
  simp_rw [hphase]
  simpa only [sub_eq_zero,eq_comm] using integral_cusp_character (k-h)

lemma cubicResidualNonzeroSeries_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v k := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
    ShortDraftTrace.breveE (-cuspFrequency k*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => cubicResidualModeAmplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*z)+starRingEnd ℂ (cuspFrequency h*z)))*
      Complex.exp (2*Real.pi*Complex.I*((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
    change ‖(cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)‖≤_
    rw [←cubicResidualNonzeroTerm_eq_amplitude v hv h z,norm_mul,breveE_norm,mul_one]
    exact hbound h (v,z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=
      if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v h else 0 := by
    change (∫z in periodDomain,cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=_
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑'h : ActualEisensteinCubic.O,cubicResidualNonzeroTerm h (v,z))*ShortDraftTrace.breveE (-cuspFrequency k*z)=_
        rw [←tsum_mul_right]
        apply tsum_congr
        intro h
        rw [cubicResidualNonzeroTerm_eq_amplitude v hv h z])
    _ = ∑'h : ActualEisensteinCubic.O,∫z in periodDomain,f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑'h : ActualEisensteinCubic.O,if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v h else 0 := tsum_congr hterm
    _ = _ := by simp

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualNonzeroFunction_heightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip a b,cubicResidualNonzeroFunction w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,(ρ v*(((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v h))/(v:ℂ)^3 := by
  let g : HyperbolicSpace→ℂ := fun w => cubicResidualNonzeroFunction w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := cubicResidualNonzeroFunction_continuous.mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos := ha.trans_le hv.1
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*(((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v h) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,cubicResidualNonzeroFunction,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    calc
      _ = ρ v*(∫z in periodDomain,cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      _ = _ := by rw [cubicResidualNonzeroSeries_fourier v hpos h]
  dsimp only
  rw [hinner]

lemma cubicResidualNonzeroFunction_zero_heightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,cubicResidualNonzeroFunction w*cuspWeightedFourierPhase ρ 0 w∂hyperbolicVolume)=0 := by
  rw [cubicResidualNonzeroFunction_heightFourier a b ha ρ 0]
  simp only [cubicResidualModeAmplitude,ite_true,mul_zero,zero_div,integral_zero]

lemma cubicResidualNonzeroFunction_nonzero_heightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip a b,cubicResidualNonzeroFunction w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFourierCoefficient h*
        (∫v in Set.Icc a b,ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cubicResidualNonzeroFunction_heightFourier a b ha ρ h,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'
  dsimp only
  rw [cubicResidualModeAmplitude,ite_eq_right hh]
  field_simp

lemma cubicEisensteinResidue_nonzero_height_test_eq (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicResidualNonzeroFunction w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspHeightFourier_residue_bessel a b ha ρ h hh,
    cubicResidualNonzeroFunction_nonzero_heightFourier a b ha ρ h hh]

end

section
open Filter MeasureTheory
open scoped Classical Topology

lemma ae_eq_of_boundedContinuous_height_tests («μ» : Measure ℝ) (f g : ℝ→ℂ)
    (hf : Integrable f «μ») (hg : Integrable g «μ»)
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x,ρ x*f x∂«μ»)=(∫x,ρ x*g x∂«μ»)) : f=ᵐ[«μ»]g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro test htest hsupp
  obtain ⟨C,hC⟩ := hsupp.exists_bound_of_continuous htest.continuous
  let ρ : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (test x:ℂ))
      (Complex.continuous_ofReal.comp htest.continuous) C (fun x => by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using hC x)
  have hh := heq ρ
  change (∫x,(test x:ℂ)*f x∂«μ»)=(∫x,(test x:ℂ)*g x∂«μ») at hh
  simpa only [Complex.real_smul] using hh

lemma interval_ae_eq_of_boundedContinuous_height_tests (a b : ℝ) (f g : ℝ→ℂ)
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b))
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x in Set.Icc a b,ρ x*f x)=(∫x in Set.Icc a b,ρ x*g x)) :
    f=ᵐ[volume.restrict (Set.Icc a b)]g :=
  ae_eq_of_boundedContinuous_height_tests (volume.restrict (Set.Icc a b)) f g hf hg heq

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def compactHeightMellin (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^s

lemma compactHeightMellin_integrable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    IntegrableOn (fun v : ℝ => ρ v*(v:ℂ)^s) (Set.Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  apply ρ.continuous.continuousOn.mul
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s
    (Or.inr (ha.trans_le hv.1).ne')).continuousWithinAt

theorem compactHeightMellin_differentiable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) : Differentiable ℂ (compactHeightMellin a b ρ) := by
  let heightLog : ℝ→ℂ := fun v => (Real.log (max a v):ℂ)
  have hl : Continuous heightLog := Complex.continuous_ofReal.comp
    ((continuous_const.max continuous_id).log (fun v => (ha.trans_le (le_max_left a v)).ne'))
  let F : ℂ→ℝ→ℂ := fun s v => ρ v*Complex.exp (heightLog v*s)
  let F' : ℂ→ℝ→ℂ := fun s v => ρ v*(Complex.exp (heightLog v*s)*heightLog v)
  have hF : ∀s,Continuous (F s) := fun s => ρ.continuous.mul ((hl.mul_const s).cexp)
  have hF' : Continuous (fun p : ℂ×ℝ => F' p.1 p.2) := by
    exact (ρ.continuous.comp continuous_snd).mul
      ((((hl.comp continuous_snd).mul continuous_fst).cexp).mul (hl.comp continuous_snd))
  have hder : ∀s v,HasDerivAt (fun w => F w v) (F' s v) s := by
    intro s v
    simpa only [F,F',id_eq,mul_one] using
      (((hasDerivAt_id s).const_mul (heightLog v)).cexp).const_mul (ρ v)
  have heq : compactHeightMellin a b ρ=(fun s => ∫v in Set.Icc a b,F s v) := by
    funext s
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only [compactHeightMellin,F,heightLog]
    rw [max_eq_right hv.1,Complex.ofReal_log (ha.trans_le hv.1).le,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne')]
  rw [heq]
  intro s
  obtain ⟨C,hC⟩ := ((isCompact_closedBall s (1:ℝ)).prod (isCompact_Icc : IsCompact (Set.Icc a b))).exists_bound_of_continuousOn hF'.continuousOn
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ»:=volume.restrict (Set.Icc a b)) (F:=F) (F':=F')
    (bound:=fun _ => C) (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun w => (hF w).aestronglyMeasurable))
    ((hF s).continuousOn.integrableOn_Icc)
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv w hw
      exact hC (w,v) ⟨Metric.ball_subset_closedBall hw,hv⟩)
    (integrable_const C)
    (Eventually.of_forall (fun v w _ => hder w v))
  exact hd.2.differentiableAt

lemma compactHeightMellin_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    AnalyticAt ℂ (compactHeightMellin a b ρ) s :=
  (compactHeightMellin_differentiable a b ha ρ).analyticAt s

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

def cuspHeightConstantAverage (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(compactHeightMellin a b ρ (s-3)+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*compactHeightMellin a b ρ (-s-1))

lemma hyperbolicEisenstein_cusp_height_fourier_zero (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ 0 w∂hyperbolicVolume)=
      cuspHeightConstantAverage a b ρ s := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ 0 w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ 0)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  have hexp : ∀v∈Set.Icc a b,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*
          (ρ v*(v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
            (ρ v*(v:ℂ)^(-s-1))) := by
    intro v hv
    have hpos : 0<v := ha.trans_le hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency 0*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency 0*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinConstantCoefficient_formula v hpos s hs]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have hm : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp,hm]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hexp,integral_const_mul,
    integral_add (compactHeightMellin_integrable a b ha ρ _)
      ((compactHeightMellin_integrable a b ha ρ _).const_mul _),integral_const_mul]
  rfl

lemma kernelCuspHeightFourierFamily_zero_initial (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ 0 s=cuspHeightConstantAverage a b ρ s := by
  rw [kernelCuspHeightFourierFamily_initial a b ha ρ 0 s hs hi,
    hyperbolicEisenstein_cusp_height_fourier_zero a b ha ρ s (by linarith)]

def weightedOutgoingConstant (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  kernelCuspHeightFourierFamily a b ha ρ 0 s-
    ((9*Real.sqrt 3/2:ℝ):ℂ)*compactHeightMellin a b ρ (s-3)

def baseOutgoingConstant (s : ℂ) : ℂ :=
  kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s-
    ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspMainHeightFactor s

lemma weightedOutgoingConstant_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 1<s.re) (hi : 0<s.im) :
    AnalyticAt ℂ (weightedOutgoingConstant a b ha ρ) s := by
  exact (kernelCuspHeightFourierFamily_analyticAt_nonreal a b ha ρ 0 s hs.ne' hi.ne').sub
    (analyticAt_const.mul ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl))

lemma baseOutgoingConstant_analyticAt (s : ℂ) (hs : 1<s.re) (hi : 0<s.im) :
    AnalyticAt ℂ baseOutgoingConstant s := by
  have hne : s≠2 := by intro he; subst s; norm_num at hi
  have hmain : AnalyticAt ℂ cuspMainHeightFactor s := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [eventually_ne_nhds hne] with z hz
    exact cuspMainHeightFactor_differentiableAt z hz
  exact (kernelCuspAverageFamily_analyticAt_nonreal 2 3 (by norm_num) (by norm_num)
    s hs.ne' hi.ne').sub (analyticAt_const.mul hmain)

lemma cuspScatterHeightFactor_analyticAt (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ cuspScatterHeightFactor s := by
  have hne : s≠0 := by intro he; subst s; norm_num at hs
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds hne] with z hz
  exact cuspScatterHeightFactor_differentiableAt z hz

lemma weightedOutgoingConstant_cross_identity (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Set.EqOn (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1))
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s) domain := by
    intro s hs
    exact (weightedOutgoingConstant_analyticAt a b ha ρ s hs.1 hs.2).mul
      (cuspScatterHeightFactor_analyticAt s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) domain := by
    intro s hs
    exact (baseOutgoingConstant_analyticAt s hs.1 hs.2).mul
      ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
        (analyticAt_id.neg.sub analyticAt_const) rfl)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
      apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
        s (by linarith [hs.1])
        (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)).trans
      exact hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1])
    rw [weightedOutgoingConstant,baseOutgoingConstant,
      kernelCuspHeightFourierFamily_zero_initial a b ha ρ s hs.1 hs.2,hb,
      cuspHeightConstantAverage,cuspConstantAverage]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

end CubicEisenstein

end

end OAI
end OAIOriginalModule0265

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection
Source SHA256: c85a3c9cead0519a990c8036170a1c3ff6600b03a87b76724765bb79cd8ebe7c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0266



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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

private theorem finite_tsum_comp_addHom {R S : Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ) :
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y := by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

lemma ramified_affine_isUnit (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) : IsUnit (1+3*x) := by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hh:denominatorCondition (u.val*lambda^n) (1+3*d):=
    ramified_denominator_condition u n _ ⟨d,by ring⟩
  simpa only [map_add,map_one,map_mul,map_ofNat] using
    (isUnit_quotient_span_iff _ _).mpr hh.1

def ramifiedAffineEquiv (u:Eisˣ) (n:ℕ) :
    (Eis⧸Ideal.span {u.val*lambda^n})≃AdmissibleResidue (u.val*lambda^n):=
  (Equiv.subtypeUnivEquiv (ramified_affine_isUnit u n)).symm.trans (affineResidueEquiv _)

theorem ramified_arithmetic_affine (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ∑'x:Eis⧸Ideal.span {u.val*lambda^n},
        eisEmbedding (symbol (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x))*
        residueAdditive h (u.val*lambda^n)
          (1+3*GaussianShiftedPartition.representative (u.val*lambda^n) x) := by
  rw [arithmeticResidueSum,←(ramifiedAffineEquiv u n).tsum_eq]
  apply tsum_congr
  intro x
  let a:=u.val*lambda^n
  let d:=1+3*GaussianShiftedPartition.representative a x
  have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
  have hrep:3*a∣denominatorRep a ((ramifiedAffineEquiv u n) x).val-d:=
    denominatorRep_mk_congr a d
  change eisEmbedding (symbol a (denominatorRep a ((ramifiedAffineEquiv u n) x).val))*
    residueAdditive h a (denominatorRep a ((ramifiedAffineEquiv u n) x).val)=_
  rw [row_symbol_congr_modulus a _ d (ramifiedElement_level u n hn) hd hrep,
    residueAdditive_congr h a _ d (ramifiedElement_ne_zero u n) hrep]

def ramifiedReduction (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    (Eis⧸Ideal.span {u.val*lambda^n})→+*(Eis⧸Ideal.span {(3:Eis)}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
    (ramifiedElement_level u n hn))

lemma ramifiedReduction_surjective (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Function.Surjective (ramifiedReduction u n hn):=
  Ideal.Quotient.factor_surjective _

lemma ramifiedReduction_rep (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (x:Eis⧸Ideal.span {u.val*lambda^n}) :
    (3:Eis)∣GaussianShiftedPartition.representative (u.val*lambda^n) x-
      GaussianShiftedPartition.representative 3 (ramifiedReduction u n hn x) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec]
  have hh:=congrArg (ramifiedReduction u n hn)
    (GaussianShiftedPartition.representative_spec (u.val*lambda^n) x)
  exact hh

lemma residueAdditive_ramified_scale (h k a d:Eis) (ha:a≠0) (hk:3*h=a*k) :
    residueAdditive h a d=residueAdditive k 3 d := by
  unfold residueAdditive cuspFrequency
  congr 1
  have he:=congrArg eisEmbedding hk
  simp only [map_mul,map_ofNat] at he
  have ha':eisEmbedding a≠0:=eisEmbedding_ne_zero ha
  simp only [map_ofNat]
  field_simp
  linear_combination eisLam⁻¹*eisEmbedding d*he

def ramifiedNineSum (k:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  ∑'x:Eis⧸Ideal.span {(3:Eis)},
    eisEmbedding (symbol (u.val*lambda^n)
      (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)

lemma ramifiedReduction_kernel_card (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker=3^(n-2) := by
  have hc:=card_ring_eq_card_mul_kernel (ramifiedReduction u n hn)
    (ramifiedReduction_surjective u n hn)
  change Ideal.absNorm (Ideal.span {u.val*lambda^n})=
    Ideal.absNorm (Ideal.span {(3:Eis)})*Nat.card (ramifiedReduction u n hn).toAddMonoidHom.ker at hc
  rw [ramifiedElement_absNorm,three_absNorm] at hc
  have hn':n=2+(n-2):=by omega
  have hp:(3:ℕ)^n=9*3^(n-2):=by
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  omega

theorem ramified_arithmetic_nine_sum (h k:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      ((3^(n-2):ℕ):ℂ)*ramifiedNineSum k u n := by
  let a:=u.val*lambda^n
  let f:=ramifiedReduction u n hn
  let F:Eis⧸Ideal.span {(3:Eis)}→ℂ:=fun x=>
    eisEmbedding (symbol a (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (1+3*GaussianShiftedPartition.representative 3 x)
  have hpoint (x:Eis⧸Ideal.span {a}):
      eisEmbedding (symbol a (1+3*GaussianShiftedPartition.representative a x))*
        residueAdditive h a (1+3*GaussianShiftedPartition.representative a x)=F (f x):=by
    let d:=1+3*GaussianShiftedPartition.representative a x
    let e:=1+3*GaussianShiftedPartition.representative 3 (f x)
    have hd:(3:Eis)∣d-1:=⟨_,by dsimp [d];ring⟩
    have he:(3:Eis)∣e-1:=⟨_,by dsimp [e];ring⟩
    have h9:(9:Eis)∣d-e:=by
      obtain ⟨w,hw⟩:=ramifiedReduction_rep u n hn x
      exact ⟨w,by dsimp [d,e,f,a] at *;linear_combination 3*hw⟩
    change eisEmbedding (symbol a d)*residueAdditive h a d=F (f x)
    rw [ramified_symbol_congr_mod_nine u n d e hd he h9,
      residueAdditive_ramified_scale h k a d (ramifiedElement_ne_zero u n) hk,
      residueAdditive_congr k 3 d e (by norm_num) (by convert h9 using 1 ;norm_num)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span (ramifiedElement_ne_zero u n)
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  rw [ramified_arithmetic_affine h u n hn]
  calc
    _=∑'x:Eis⧸Ideal.span {a},F (f x):=tsum_congr hpoint
    _=(Nat.card f.toAddMonoidHom.ker:ℂ)*∑'x,F x:=
      finite_tsum_comp_addHom f.toAddMonoidHom (ramifiedReduction_surjective u n hn) F
    _=_:=by rw [ramifiedReduction_kernel_card u n hn];rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedLinearChar (u:Eisˣ) (n:ℕ):AddChar Eis ℂ where
  toFun x:=eisEmbedding (symbol (u.val*lambda^n) (1+3*x))
  map_zero_eq_one':=by simp
  map_add_eq_mul':=by
    intro x y
    have hp (z:Eis):(3:Eis)∣1+3*z-1:=⟨z,by ring⟩
    have hprod:(3:Eis)∣(1+3*x)*(1+3*y)-1:=⟨x+y+3*x*y,by ring⟩
    rw [ramified_symbol_congr_mod_nine u n (1+3*(x+y))
      ((1+3*x)*(1+3*y)) (hp _) hprod ⟨-x*y,by ring⟩,
      symbol_mul_denominator,map_mul]

lemma ramifiedLinearChar_period (u:Eisˣ) (n:ℕ) (x:Eis)
    (hx:x∈Ideal.span {(3:Eis)}) : ramifiedLinearChar u n x=1 := by
  obtain ⟨w,rfl⟩:=Ideal.mem_span_singleton.mp hx
  change eisEmbedding (symbol (u.val*lambda^n) (1+3*(3*w)))=1
  rw [ramified_symbol_congr_mod_nine u n _ 1 ⟨3*w,by ring⟩ (by simp) ⟨w,by ring⟩]
  simp

def ramifiedQuotientChar (u:Eisˣ) (n:ℕ):AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  IdealGaussCRT.quotientAddChar _ (ramifiedLinearChar u n) (ramifiedLinearChar_period u n)

lemma ramifiedQuotientChar_rep (u:Eisˣ) (n:ℕ) (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedQuotientChar u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x)) := by
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  rfl

def ramifiedFrequencyChar (k:Eis) (u:Eisˣ) (n:ℕ):
    AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ:=
  ramifiedQuotientChar u n *
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num)).mulShift (Ideal.Quotient.mk _ k)

lemma ramifiedFrequencyChar_rep (k:Eis) (u:Eisˣ) (n:ℕ)
    (x:Eis⧸Ideal.span {(3:Eis)}) :
    ramifiedFrequencyChar k u n x=
      eisEmbedding (symbol (u.val*lambda^n)
        (1+3*GaussianShiftedPartition.representative 3 x))*
      residueAdditive k 3 (3*GaussianShiftedPartition.representative 3 x) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar_rep]
  congr 1
  conv_lhs => rw [←GaussianShiftedPartition.representative_spec 3 x]
  simp only [AddChar.mulShift_apply,←map_mul,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat]
  congr 1
  field_simp

theorem ramifiedNineSum_eq_character_test (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedNineSum k u n=
      if ramifiedFrequencyChar k u n=1 then 9*residueAdditive k 3 1 else 0 := by
  let:Finite (Eis⧸Ideal.span {(3:Eis)}):=finite_quotient_span (by norm_num)
  let:Fintype (Eis⧸Ideal.span {(3:Eis)}):=Fintype.ofFinite _
  have hcard:(Fintype.card (Eis⧸Ideal.span {(3:Eis)}):ℂ)=9:=by
    have hh:=three_absNorm
    change Nat.card (Eis⧸Ideal.span {(3:Eis)})=9 at hh
    exact_mod_cast (show Fintype.card (Eis⧸Ideal.span {(3:Eis)})=9 by
      simpa only [Nat.card_eq_fintype_card] using hh)
  have he:ramifiedNineSum k u n=residueAdditive k 3 1*
      ∑'x:Eis⧸Ideal.span {(3:Eis)},ramifiedFrequencyChar k u n x:=by
    rw [ramifiedNineSum,←tsum_mul_left]
    apply tsum_congr
    intro x
    rw [ramifiedFrequencyChar_rep,residueAdditive_add]
    ring
  rw [he,tsum_fintype]
  split_ifs with hchar
  · rw [AddChar.sum_eq_card_of_eq_one hchar,hcard]
    ring
  · rw [AddChar.sum_eq_zero_of_ne_one hchar,mul_zero]

theorem ramified_arithmetic_character_test (h k:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n)
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      if ramifiedFrequencyChar k u n=1 then ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0 := by
  rw [ramified_arithmetic_nine_sum h k u n hn hk,ramifiedNineSum_eq_character_test]
  have hp:(3:ℕ)^n=3^(n-2)*9:=by
    have hn':n=(n-2)+2:=by omega
    conv_lhs => rw [hn']
    rw [pow_add]
    norm_num
  split_ifs
  · rw [hp,Nat.cast_mul]
