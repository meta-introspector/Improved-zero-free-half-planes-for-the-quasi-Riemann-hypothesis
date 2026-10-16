    intro m n
    refine ⟨max m n,Set.Ioc_subset_Ioc_right ?_,Set.Ioc_subset_Ioc_right ?_⟩
    · change a+(m:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (m:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_left m n
      linarith
    · change a+(n:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (n:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_right m n
      linarith
  calc
    _ = ⨆n : ℕ,∫⁻t in Set.Ioc a (a+n),ENNReal.ofReal (‖f t‖^2/t^3) := by
      rw [←hcover]
      exact setLIntegral_iUnion_of_directed _ hdir
    _ ≤ _ := by
      apply iSup_le
      intro n
      exact (cusp_hardy_interval_lintegral f a (a+n) ha (le_add_of_nonneg_right (Nat.cast_nonneg n)) hfa
        (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))).trans
          (lintegral_mono_set Set.Ioc_subset_Ioi_self)

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

abbrev CuspChartCoordinates := (ℝ×ℝ)×ℝ

def cuspBaseArea : Measure (ℝ×ℝ) := volume.restrict cuspRectangle
instance cuspBaseArea_sFinite : SFinite cuspBaseArea := by unfold cuspBaseArea; infer_instance

def cuspChartVolume (a : ℝ) : Measure CuspChartCoordinates :=
  (cuspBaseArea.prod (volume.restrict (Set.Ioi a))).withDensity
    (fun q => ENNReal.ofReal ((q.2^3)⁻¹))

abbrev CuspChartL2 (a : ℝ) := Lp ℂ 2 (cuspChartVolume a)

example (a : ℝ) : InnerProductSpace ℂ (CuspChartL2 a) := inferInstance
example (a : ℝ) : CompleteSpace (CuspChartL2 a) := inferInstance

def cuspVerticalDerivative (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  deriv (fun v => F (q.1,v)) q.2

def cuspVerticalVelocity (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  (q.2:ℂ)*cuspVerticalDerivative F q

lemma cusp_weight_mass_identity (u : ℂ) (v : ℝ) (hv : 0<v) :
    ENNReal.ofReal ((v^3)⁻¹) * ENNReal.ofReal (‖u‖^2)=
      ENNReal.ofReal (‖u‖^2/v^3) := by
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cusp_weight_velocity_identity (u : ℂ) (v : ℝ) (hv : 0<v) :
    ENNReal.ofReal ((v^3)⁻¹) * ENNReal.ofReal (‖(v:ℂ)*u‖^2)=
      ENNReal.ofReal (‖u‖^2/v) := by
  rw [cusp_weight_mass_identity _ _ hv,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg hv.le]
  congr 1
  field_simp

theorem cusp_chart_vertical_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      ∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a := by
  have hw : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal ((q.2^3)⁻¹)) := by
    fun_prop
  have hFm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖F q‖^2)) := by fun_prop
  have hVm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2)) := by
    unfold cuspVerticalVelocity
    fun_prop
  unfold cuspChartVolume
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hFm,
    lintegral_withDensity_eq_lintegral_mul _ hw hVm,
    lintegral_prod _ ((hw.mul hFm).aemeasurable),
    lintegral_prod _ ((hw.mul hVm).aemeasurable)]
  apply lintegral_mono
  intro z
  calc
    _ = ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖F (z,v)‖^2/v^3) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact cusp_weight_mass_identity _ _ (ha.trans hv)
    _ ≤ ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖deriv (fun t => F (z,t)) v‖^2/v) := by
      apply cusp_hardy_halfline_lintegral _ a ha (hFa z) (hDiff z)
      exact (hD.comp (continuous_const.prodMk continuous_id)).continuousOn
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (cusp_weight_velocity_identity _ _ (ha.trans hv)).symm

theorem cusp_chart_normalized_vertical_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (1/2:ℝ≥0∞)*(∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      (1/2:ℝ≥0∞)*(∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a) :=
by
  exact mul_le_mul_of_nonneg_left
    (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff) (by positivity)

theorem cusp_chart_memLp_of_vertical (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : MemLp (cuspVerticalVelocity F) 2 (cuspChartVolume a)) :
    MemLp F 2 (cuspChartVolume a) := by
  have hV : Continuous (cuspVerticalVelocity F) := by
    unfold cuspVerticalVelocity
    fun_prop
  have hEi := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hEnergy
  have hEfin := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun q => sq_nonneg ‖cuspVerticalVelocity F q‖))).mp hEi.2
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans_lt hEfin

def cuspCoordinateVelocity (F : CuspChartCoordinates → ℂ)
    (q : CuspChartCoordinates) : Fin 3 → ℂ :=
  ![(q.2:ℂ)*deriv (fun x => F ((x,q.1.2),q.2)) q.1.1,
    (q.2:ℂ)*deriv (fun y => F ((q.1.1,y),q.2)) q.1.2,
    cuspVerticalVelocity F q]

def cuspDirichletEnergy (F : CuspChartCoordinates → ℂ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻q,∑j : Fin 3,ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2) ∂cuspChartVolume a

lemma cusp_vertical_energy_le (F : CuspChartCoordinates → ℂ) (a : ℝ) :
    (∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a)≤
      cuspDirichletEnergy F a := by
  apply lintegral_mono
  intro q
  change ENNReal.ofReal (‖cuspCoordinateVelocity F q 2‖^2)≤_
  exact Finset.single_le_sum (fun j hj => (zero_le : (0:ℝ≥0∞)≤ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2))) (Finset.mem_univ (2:Fin 3))

theorem cusp_chart_dirichlet_coercivity (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤cuspDirichletEnergy F a :=
  (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans (cusp_vertical_energy_le F a)

theorem cusp_chart_memLp_of_energy (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : cuspDirichletEnergy F a<(∞ : ℝ≥0∞)) : MemLp F 2 (cuspChartVolume a) := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_dirichlet_coercivity F a ha hF hD hFa hDiff).trans_lt hEnergy

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (ha.trans hv).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num [show (-3:ℝ)+1=-2 by norm_num]
  ring

theorem cuspChartVolume_univ (a : ℝ) (ha : 0<a) :
    cuspChartVolume a Set.univ=ENNReal.ofReal (9*Real.sqrt 3/(2*a^2)) := by
  unfold cuspChartVolume
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [lintegral_prod _ (by fun_prop)]
  simp only [cusp_height_volume a ha,lintegral_const]
  rw [cuspBaseArea,Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter,cuspRectangle_volume]
  rw [←ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1/(2*a^2))]
  congr 1
  ring

lemma cuspChartVolume_finite (a : ℝ) (ha : 0<a) : IsFiniteMeasure (cuspChartVolume a) :=
  ⟨by rw [cuspChartVolume_univ a ha]; exact ENNReal.ofReal_lt_top⟩

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff

def cuspCoordinateVector : Fin 3 → CuspChartCoordinates := ![((1,0),0),((0,1),0),((0,0),1)]

lemma cuspCoordinateVelocity_eq_fderiv (F : CuspChartCoordinates → ℂ)
    (hF : Differentiable ℝ F) (q : CuspChartCoordinates) (j : Fin 3) :
    cuspCoordinateVelocity F q j=(q.2:ℂ)*fderiv ℝ F q (cuspCoordinateVector j) := by
  fin_cases j
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.1
      (((hasDerivAt_id q.1.1).prodMk (hasDerivAt_const q.1.1 q.1.2)).prodMk (hasDerivAt_const q.1.1 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.2
      (((hasDerivAt_const q.1.2 q.1.1).prodMk (hasDerivAt_id q.1.2)).prodMk (hasDerivAt_const q.1.2 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv

lemma cuspCoordinateVelocity_continuous_compact (F : CuspChartCoordinates → ℂ)
    (hF : ContDiff ℝ ∞ F) (hC : HasCompactSupport F) (j : Fin 3) :
    Continuous (fun q => cuspCoordinateVelocity F q j) ∧
      HasCompactSupport (fun q => cuspCoordinateVelocity F q j) := by
  simp_rw [cuspCoordinateVelocity_eq_fderiv F (hF.differentiable (by simp))]
  have hc := hC.fderiv_apply ℝ (cuspCoordinateVector j)
  constructor
  · exact (Complex.continuous_ofReal.comp continuous_snd).mul
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
  · exact HasCompactSupport.mul_left hc

lemma cusp_compact_smooth_memLp (F : CuspChartCoordinates → ℂ)
    (hF : ContDiff ℝ ∞ F) (hC : HasCompactSupport F) (a : ℝ) (ha : 0<a) :
    MemLp F 2 (cuspChartVolume a) ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity F q j) 2 (cuspChartVolume a) := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  refine ⟨hF.continuous.memLp_of_hasCompactSupport hC,fun j => ?_⟩
  obtain ⟨hc,hs⟩ := cuspCoordinateVelocity_continuous_compact F hF hC j
  exact hc.memLp_of_hasCompactSupport hs

theorem cuspChartL2_dense_smooth_energy (a : ℝ) (ha : 0<a) :
    Dense {f : CuspChartL2 a | ∃g : CuspChartCoordinates → ℂ,
      f=ᵐ[cuspChartVolume a] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity g q j) 2 (cuspChartVolume a)} := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  apply (Lp.dense_hasCompactSupport_contDiff («μ» := cuspChartVolume a)
    (F := ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)).mono
  rintro f ⟨g,hg,hC,hgD⟩
  exact ⟨g,hg,hC,hgD,(cusp_compact_smooth_memLp g hgD hC a ha).2⟩

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum

theorem commonMaskIdeal_primeSupport (D : Ideal O) :
    IdealMobiusDivisorSum.primeSupport (commonMaskIdeal D) = gcdMaskPrimes D := by
  have hp : ∀ P ∈ (gcdMaskPrimes D).val, Prime P := by
    intro P hP
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hf : UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
    simpa [commonMaskIdeal] using UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  rw [IdealMobiusDivisorSum.primeSupport,hf,Finset.val_toFinset]

theorem commonMask_subset_sum_eq_divisors (D : Ideal O) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      f (∏ P ∈ E, P.val)) = ∑ q ∈ idealDivisors (commonMaskIdeal D), f q := by
  rw [sum_subtype_powerset_products,← commonMaskIdeal_primeSupport D]
  exact (squarefree_divisor_sum_eq_support _ (commonMaskIdeal_squarefree D) f).symm

theorem primaryProduct_norm (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖ =
      Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hs : ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2 =
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ) := by
    rw [map_mul,norm_mul,mul_pow,
      primaryGenerator_norm_sq I (supported_primaryGenerator_ne_zero I (admissible_supported hI)),
      primaryGenerator_norm_sq J (supported_primaryGenerator_ne_zero J (admissible_supported hJ))]
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]

def maskedPairIdealDualKernel (G I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
      ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
        ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))

theorem originalPairIdealDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (W : ℝ → ℂ) (M : ℝ) :
    originalPairIdealDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  let Q := idealQuotient D I
  let T := idealQuotient D J
  have hQ : Admissible Q := admissible_idealQuotient hI hDI
  have hT : Admissible T := admissible_idealQuotient hJ hDJ
  have hn := primaryProduct_norm Q T hQ hT
  have hnonneg : 0 ≤ (Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ) := by positivity
  unfold originalPairIdealDualKernel maskedPairIdealDualKernel
  change ((M:ℂ)/(‖eisEmbedding (primaryGenerator Q*primaryGenerator T)‖:ℂ))*_ =
    ((M:ℂ)/(Real.sqrt ((Ideal.absNorm Q:ℝ)*(Ideal.absNorm T:ℝ)):ℂ))*_
  rw [hn]
  congr 1
  rw [← commonMask_subset_sum_eq_divisors D]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Real.sq_sqrt hnonneg,primeSubsetGenerator,unrestrictedPairCharacter,
    idealGenerator_norm_sq,Complex.ofReal_natCast]
  congr 1
  apply tsum_congr
  intro B
  congr 2
  ring

theorem originalPairDualKernel_eq_divisors
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (hray : columnRay I=columnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    originalPairDualKernel D I J W M =
      maskedPairIdealDualKernel (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M := by
  rw [originalPairDualKernel_eq_ideal D I J hI hJ hDI hDJ hIJ hray W M hM]
  exact originalPairIdealDualKernel_eq_divisors D I J hI hJ hDI hDJ W M

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0169

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
Source SHA256: 3d974dc4aeb9d277ab4be2a3dfe0a9722ce4505ae63eaf2af89afe040e116c0d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0170


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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum

def maskedPairDualTail (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K

def retainedDualPair (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M F K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val*
    (((M/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))*F):ℝ):ℂ)*
      dualPrincipalIdeal I J W
        (Real.sqrt (F*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)))))

theorem maskedPairIdealDualKernel_retained
    (G I J : Ideal O) (hG : G ≠ 0) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I=columnRay J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    maskedPairIdealDualKernel G I J W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
        retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K) +
      maskedPairDualTail G I J W M K := by
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hqpos (q : Ideal O) (hq : q ∈ idealDivisors G) : 0<(Ideal.absNorm q:ℝ) := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hpoint (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
        (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
          ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
            ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))) =
        (UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q*
          retainedDualPair I J (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K +
        ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
          (((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
            dualSquarefreeTail I J W
              (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K) := by
    have hqN := hqpos q hq
    have ht : 0 < M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      positivity
    rw [dual_ideal_low_add_tail I J W _ K ht,dualSquarefreeLow_principal_finite I J hI hJ hray W _ K ht,
      mul_add,mul_add]
    congr 1
    simp only [retainedDualPair,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    have hB : 0<(Ideal.absNorm B.val:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr
        (fun hz => (mem_squarefreeIdealRange.mp B.property).1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    have harg : (1:ℝ)/((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ)) =
        (Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)) := by
      field_simp
    rw [harg]
    push_cast
    ring
  unfold maskedPairIdealDualKernel maskedPairDualTail
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpoint

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem retainedDualPrincipalSum_pair_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M F K : ℝ) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols a M F =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*retainedDualPair (cols j) (cols k) W M F K else 0 := by
  unfold retainedDualPrincipalSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [unrestrictedPairTerm,retainedDualPair,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,Finset.sum_const_zero]

theorem retainedDualPrincipalSum_twist_expansion {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M F K : ℝ) (q : Ideal O)
    (hcols : ∀ j, Admissible (cols j)) :
    retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) M F =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*unrestrictedPairCharacter (cols j) (cols k) q*
          retainedDualPair (cols j) (cols k) W M F K else 0 := by
  rw [retainedDualPrincipalSum_pair_expansion]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),unrestrictedPairCharacter]
    ring
  · simp only [hc,ite_false]

def maskedDualFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0

def maskedDualTailFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0

theorem maskedDualFamily_retained {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G ≠ 0) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k)) :
    maskedDualFamily G cols a W M =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) cols
          (fun j => a j*quadraticRow (cols j) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily G cols a W M K := by
  have hp (j k : n) :
      (if IsCoprime (cols j) (cols k) then
        star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0) =
      (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        (if IsCoprime (cols j) (cols k) then
          star (a j)*a k*unrestrictedPairCharacter (cols j) (cols k) q*
            retainedDualPair (cols j) (cols k) (quadraticTransformedSquareProfile W) M (Ideal.absNorm q:ℝ) K
          else 0)) +
      (if IsCoprime (cols j) (cols k) then
        star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0) := by
    by_cases hc : IsCoprime (cols j) (cols k)
    · simp only [hc,ite_true,maskedPairIdealDualKernel_retained G (cols j) (cols k)
        hG (hcols j) (hcols k) (hray j k) W M K hM,mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      ring
    · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
  simp only [maskedDualFamily,hp,Finset.sum_add_distrib,maskedDualTailFamily]
  congr 1
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [retainedDualPrincipalSum_twist_expansion _ cols a _ _ _ q hcols]
  simp only [Finset.mul_sum]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

theorem normalizedFactors_commonMaskIdeal (D : Ideal O) :
    UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) = (gcdMaskPrimes D).val := by
  have hp (P : Ideal O) (hP : P∈(gcdMaskPrimes D).val) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P,hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hp
  simpa only [commonMaskIdeal,Finset.prod_val,id_eq] using h

theorem idealZeroMask_commonMaskIdeal (D : Ideal O) (z : O) :
    idealZeroMask (commonMaskIdeal D) z =
      rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z := by
  classical
  simp only [idealZeroMask,normalizedFactors_commonMaskIdeal,rowCoprimeMask,
    Finset.mem_univ,true_and,Subtype.exists,exists_prop,Finset.mem_val]

lemma idealZeroMask_idempotent (D : Ideal O) (z : O) :
    idealZeroMask D z*idealZeroMask D z=idealZeroMask D z := by
  classical
  unfold idealZeroMask
  split_ifs <;> norm_num

theorem idealZeroMask_generator_eq_indicator (D B : Ideal O) (hD : D≠0) :
    idealZeroMask D (idealGenerator B) = if IsCoprime B D then 1 else 0 := by
  classical
  by_cases hc : IsCoprime B D
  · rw [ite_eq_left hc,idealZeroMask_generator_eq_one D B hc.symm]
  · rw [ite_eq_right hc]
    apply ite_eq_left
    by_contra hn
    apply hc
    apply IsCoprime.symm
    apply ideals_coprime_of_relprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hD).mpr
    intro P hPD hPB hp
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors D :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hD).mpr ⟨hp,hPD⟩
    have hgen : idealGenerator B∈P := by
      apply (Ideal.span_singleton_le_iff_mem P).mp
      rw [span_idealGenerator]
      exact Ideal.dvd_iff_le.mp hPB
    exact hn ⟨P,hfac,hgen⟩

theorem idealZeroMask_primary_eq_indicator (D B : Ideal O) (hD : D≠0) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {primaryGenerator B}=Ideal.span {idealGenerator B} := by
    rw [(primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)).1,span_idealGenerator]
  rw [idealZeroMask_span_eq D _ _ he,idealZeroMask_generator_eq_indicator D B hD]

theorem commonMask_primary_indicator (D B : Ideal O) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B (commonMaskIdeal D) then 1 else 0 := by
  have he := idealZeroMask_commonMaskIdeal D (primaryGenerator B)
  rw [gcdMaskPrimes_mask,badPrime_mask_primaryGenerator,ite_eq_left hB,one_mul] at he
  rw [←he,idealZeroMask_primary_eq_indicator _ B (commonMaskIdeal_squarefree D).ne_zero hB]

theorem residual_joint_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes (I*J) => P.val) Finset.univ z =
      rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val)
        Finset.univ z := by
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hi : idealZeroMask I z=idealZeroMask D z*idealZeroMask (idealQuotient D I) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D I) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDI).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hIq.1 z
  have hj : idealZeroMask J z=idealZeroMask D z*idealZeroMask (idealQuotient D J) z := by
    calc
      _ = idealZeroMask (D*idealQuotient D J) z := congrArg (fun A => idealZeroMask A z) (idealQuotient_mul hDJ).symm
      _ = _ := idealZeroMask_mul D _ hD.1 hJq.1 z
  rw [gcdMaskPrimes_mask,singleton_rowCoprimeMask_eq_idealZeroMask,
    idealZeroMask_mul I J hI.1 hJ.1,
    idealZeroMask_mul (commonMaskIdeal D) _ (commonMaskIdeal_squarefree D).ne_zero (mul_ne_zero hIq.1 hJq.1),
    idealZeroMask_mul _ _ hIq.1 hJq.1,idealZeroMask_commonMaskIdeal,gcdMaskPrimes_mask,hi,hj]
  calc
    _ = (rowCoprimeMask badPrime Finset.univ z)*(idealZeroMask D z*idealZeroMask D z)*
      (idealZeroMask (idealQuotient D I) z*idealZeroMask (idealQuotient D J) z) := by ring
    _ = _ := by rw [idealZeroMask_idempotent]

theorem lowPrincipalLattice_residual (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (X : ℝ) :
    lowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask
        (fun P : primePool {commonMaskIdeal D*(idealQuotient D I*idealQuotient D J)} => P.val) Finset.univ z *
        (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/X)) := by
  unfold lowPrincipalLattice
  apply tsum_congr
  intro z
  by_cases hz : z=0
  · subst z
    simp only [jointMask_zero,ite_true,mul_zero,zero_mul]
  · rw [ite_eq_right hz,quadraticSquareProfile_apply,residual_joint_mask D I J hI hJ hDI hDJ]

theorem idealRange_filter_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (idealRange K).filter (fun B => IsCoprime B G)=coprimeSquarefreeRange G K := by
  classical
  ext B
  constructor
  · intro h
    obtain ⟨hb,hc⟩ := Finset.mem_filter.mp h
    have hB := mem_idealRange.mp hb
    exact Finset.mem_filter.mpr ⟨mem_squarefreeIdealRange.mpr ⟨hB.1.2.1,hB.2⟩,hc⟩
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp h).2⟩
    exact coprimeSquarefreeRange_subset_idealRange G hbad K h

theorem sum_idealRange_coprime (G : Ideal O) (K : ℝ)
    (hbad : ∀ P∈fixedBadPrimes, P∣G) (f : Ideal O → ℂ) :
    (∑ B : idealRange K, if IsCoprime B.val G then f B.val else 0) =
      ∑ B : coprimeSquarefreeRange G K, f B.val := by
  classical
  rw [Finset.sum_coe_sort (idealRange K) (fun B => if IsCoprime B G then f B else 0),
    ←Finset.sum_filter,idealRange_filter_coprime G K hbad,
    Finset.sum_coe_sort (coprimeSquarefreeRange G K) f]

def pairMaskedSquareSource (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (B : Ideal O) : ℂ :=
  (quadraticRow I (primaryGenerator B)*quadraticRow J (primaryGenerator B))*
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(I*J)} => P.val) Finset.univ z *
      (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B))

theorem originalPairLow_residual_finite (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D∣I) (hDJ : D∣J) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      (6:ℂ)⁻¹*∑ B : coprimeSquarefreeRange (commonMaskIdeal D) K,
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val := by
  classical
  rw [originalPairLow_principal_finite I J hI hJ W M K hM]
  have ht (B : idealRange K) :
      (quadraticRow I (primaryGenerator B.val)*quadraticRow J (primaryGenerator B.val))*
        ((6:ℂ)⁻¹*lowPrincipalLattice I J W (Real.sqrt (M/(Ideal.absNorm B.val:ℝ)))) =
      (6:ℂ)⁻¹*(if IsCoprime B.val (commonMaskIdeal D) then
        pairMaskedSquareSource (commonMaskIdeal D) (idealQuotient D I) (idealQuotient D J) W M B.val else 0) := by
    have hB := admissible_supported (mem_idealRange.mp B.property).1
    have hp := canonical_pair_divisor_mask D I J hI hJ hDI hDJ (primaryGenerator B.val)
    rw [canonical_quadraticRow_star I hI,commonMask_primary_indicator D B.val hB] at hp
    rw [hp,lowPrincipalLattice_residual D I J hI hJ hDI hDJ]
    by_cases hc : IsCoprime B.val (commonMaskIdeal D)
    · simp only [hc,ite_true,one_mul,pairMaskedSquareSource,sourcePrincipalScale]
      ring
    · simp only [hc,ite_false,zero_mul,mul_zero]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_idealRange_coprime (commonMaskIdeal D) K
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)]

theorem originalLow_gcd_aggregate
    {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  classical
  let S := coprimeSquarefreeRange (commonMaskIdeal D) K
  let q := fun j => idealQuotient D (cols j)
  have hq (j : n) : Admissible (q j) := admissible_idealQuotient (hcols j) (hdiv j)
  have ht (j k : n) :
      (if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) =
      (6:ℂ)⁻¹ * ∑ B : S,
        originalTerm (fun B : S => B.val) q q a a 1 1 B j k *
          ∑' z : O, rowCoprimeMask (fun P : primePool {commonMaskIdeal D*(q j*q k)} => P.val) Finset.univ z *
            (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B.val)) := by
    have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
    by_cases hc : IsCoprime (q j) (q k)
    · rw [ite_eq_left (heq.mpr hc),originalPairLow_residual_finite D _ _ (hcols j) (hcols k) (hdiv j) (hdiv k) W M K hM]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      simp only [originalTerm,hc,ite_true,one_dvd,pairMaskedSquareSource,star_mul,
        canonical_quadraticRow_star _ (hq j)]
      dsimp only [q]
      ring
    · have hg : ¬gcd (cols j) (cols k)=D := fun h => hc (heq.mp h)
      simp only [hg,ite_false,originalTerm,hc,Finset.sum_const_zero,zero_mul,mul_zero]
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset n)) (t := (Finset.univ:Finset S))]
  simp only [maskedPrincipalSourceSum,Finset.mul_sum,S,q,sourcePrincipalScale]

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem originalDual_gcd_aggregate {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) =
      maskedDualFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M := by
  unfold maskedDualFamily
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have heq := gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD (hdiv j) (hdiv k)
  by_cases hg : gcd (cols j) (cols k)=D
  · have hneq : cols j≠cols k := by
      intro h
      rw [← h] at hg
      exact hproper j (by simpa using hg)
    rw [ite_eq_left hg,ite_eq_left (heq.mp hg),
      originalPairDualKernel_eq_divisors D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) hneq (hray j k) W M hM]
  · rw [ite_eq_right hg,ite_eq_right (fun hc => hg (heq.mpr hc))]

theorem originalHigh_gcd_principal_assembly {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ q ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) (fun j => idealQuotient D (cols j))
          (fun j => a j*quadraticRow (idealQuotient D (cols j)) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M K -
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by
  have hsplit :
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*originalPairDualKernel D (cols j) (cols k) W M else 0) -
      (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
        star (a j)*a k*(∑' lengthScale : Ideal O, originalPairLow (cols j) (cols k) W M K lengthScale) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hg : gcd (cols j) (cols k)=D
    · rw [ite_eq_left hg,ite_eq_left hg,ite_eq_left hg,
        originalPairHigh_eq_source_sub_low (cols j) (cols k) W M K hM,
        originalPairSource_poisson D (cols j) (cols k) (hcols j) (hcols k) hg (hray j k) W M hM]
      ring
    · simp only [hg,ite_false,sub_self]
  rw [hsplit,originalDual_gcd_aggregate D hD cols hcols hdiv hproper hray a W M hM,
    originalLow_gcd_aggregate D hD cols hcols hdiv a W M K hM,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem residual_commonMask_coprime (D I : Ideal O) (hI : Admissible I) (hDI : D∣I) :
    IsCoprime (commonMaskIdeal D) (idealQuotient D I) := by
  have hD := admissible_of_dvd hI hDI
  have hQ := admissible_idealQuotient hI hDI
  have hs : Squarefree (D*idealQuotient D I) := by rw [idealQuotient_mul hDI]; exact hI.2.1
  have hrel := (squarefree_mul_iff.mp hs).1
  have hG := (commonMaskIdeal_squarefree D).ne_zero
  apply ideals_coprime_of_relprime
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hG).mpr
  intro P hPG hPQ hp
  have hf : P∈UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hG).mpr ⟨hp,hPG⟩
  rw [normalizedFactors_commonMaskIdeal] at hf
  have hmem : P∈fixedBadPrimes ∨ P∈primeSupport D := Finset.mem_union.mp hf
  rcases hmem with hbad | hPD
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors (idealQuotient D I) :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.1).mpr ⟨hp,hPQ⟩
    exact (prime_good_iff_not_bad P).mp (hQ.2.2 P hfac) hbad
  · have hd : P∣D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPD)
    exact hp.not_isUnit (hrel hd hPQ)

theorem idealQuotient_norm_eq (D I : Ideal O) (hD : D≠0) (hDI : D∣I) :
    (Ideal.absNorm (idealQuotient D I):ℝ)=(Ideal.absNorm I:ℝ)/(Ideal.absNorm D:ℝ) := by
  have hn : (Ideal.absNorm D:ℝ)≠0 := by
    exact_mod_cast (show Ideal.absNorm D≠0 from fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (eq_div_iff hn).mpr
  rw [mul_comm,←Nat.cast_mul,←map_mul,idealQuotient_mul hDI]

theorem idealQuotient_shell (D I : Ideal O) (hD : D≠0) (hDI : D∣I) (N : ℝ)
    (hI : N/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤N) :
    (N/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (idealQuotient D I):ℝ) ∧
      (Ideal.absNorm (idealQuotient D I):ℝ)≤N/(Ideal.absNorm D:ℝ) := by
  have hn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  rw [idealQuotient_norm_eq D I hD hDI]
  constructor
  · calc
      _ = (N/2)/(Ideal.absNorm D:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hI.1 hn.le
  · exact div_le_div_of_nonneg_right hI.2 hn.le

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : Finset n :=
  Finset.univ.filter (fun j => D ∣ cols j ∧ columnRay (cols j)=c ∧ a j≠0)

theorem mem_gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (j : n) :
    j∈gcdRaySupport cols a D c ↔ D∣cols j ∧ columnRay (cols j)=c ∧ a j≠0 := by
  simp only [gcdRaySupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem gcd_ray_pair_sum_restrict {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O)
    (c : EisensteinEPrimaryPhase.Coord) (H : n → n → ℂ) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
      then star (a j)*a k*H j k else 0) =
    ∑ j : gcdRaySupport cols a D c, ∑ k : gcdRaySupport cols a D c,
      if gcd (cols j.val) (cols k.val)=D then star (a j.val)*a k.val*H j.val k.val else 0 := by
  classical
  let S := gcdRaySupport cols a D c
  let f := fun j k => if gcd (cols j) (cols k)=D ∧ columnRay (cols j)=c ∧ columnRay (cols k)=c
    then star (a j)*a k*H j k else 0
  have hjzero (j : n) (hj : j∉S) (k : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a j=0 := by
        by_contra hn
        apply hj
        exact (mem_gcdRaySupport cols a D c j).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_left (cols j) (cols k),h.2.1,hn⟩
      simp only [hz,star_zero,zero_mul]
    · rfl
  have hkzero (k : n) (hk : k∉S) (j : n) : f j k=0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a k=0 := by
        by_contra hn
        apply hk
        exact (mem_gcdRaySupport cols a D c k).mpr
          ⟨h.1 ▸ GCDMonoid.gcd_dvd_right (cols j) (cols k),h.2.2,hn⟩
      simp only [hz,mul_zero,zero_mul]
    · rfl
  have hleft : (∑ j∈S, ∑ k, f j k) = ∑ j, ∑ k, f j k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    exact Finset.sum_eq_zero (fun k _ => hjzero j hj k)
  change (∑ j, ∑ k, f j k)=_
  rw [←hleft,←Finset.sum_coe_sort S (fun j => ∑ k, f j k)]
  apply Finset.sum_congr rfl
  intro j _
  have hright : (∑ k∈S, f j.val k) = ∑ k, f j.val k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    exact hkzero k hk j.val
  rw [←hright,←Finset.sum_coe_sort S (fun k => f j.val k)]
  apply Finset.sum_congr rfl
  intro k _
  have hj := (mem_gcdRaySupport cols a D c j.val).mp j.property
  have hk := (mem_gcdRaySupport cols a D c k.val).mp k.property
  simp only [f,hj.2.1,hk.2.1,and_true]

theorem gcdRaySupport_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑ j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤ ∑ j, ‖a j‖^2 := by
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

theorem gcdRaySupport_quotient_properties (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (hD : D≠0)
    (c : EisensteinEPrimaryPhase.Coord) :
    let cols := fun j : gcdRaySupport (fun I : idealRange N => I.val) a D c =>
      idealQuotient D j.val.val
    Function.Injective cols ∧
    (∀ j, Admissible (cols j) ∧
      (X/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (cols j):ℝ) ∧
      (Ideal.absNorm (cols j):ℝ)≤X/(Ideal.absNorm D:ℝ) ∧
      IsCoprime (commonMaskIdeal D) (cols j)) ∧
    (∀ j k, columnRay (cols j)=columnRay (cols k)) := by
  dsimp only
  have hp (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) :=
    (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  refine ⟨?_,?_,?_⟩
  · intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_injective_on D (hp j).1 (hp k).1 hjk
  · intro j
    have hadm := (mem_idealRange.mp j.val.property).1
    have hshell := idealQuotient_shell D j.val.val hD (hp j).1 X
      ⟨(ha j.val (hp j).2.2).1.le,(ha j.val (hp j).2.2).2⟩
    exact ⟨admissible_idealQuotient hadm (hp j).1,hshell.1,hshell.2,
      residual_commonMask_coprime D j.val.val hadm (hp j).1⟩
  · intro j k
    exact columnRay_idealQuotient_eq D j.val.val k.val.val
      (mem_idealRange.mp j.val.property).1 (mem_idealRange.mp k.val.property).1
      (hp j).1 (hp k).1 ((hp j).2.1.trans (hp k).2.1.symm)

theorem gcdRaySupport_proper (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (j : gcdRaySupport (fun I : idealRange N => I.val) a D c) : j.val.val≠D := by
  intro h
  have hp := (mem_gcdRaySupport (fun I : idealRange N => I.val) a D c j.val).mp j.property
  have hs := (ha j.val hp.2.2).1
  rw [h] at hs
  exact (not_lt_of_ge hsmall) hs

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0170

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
Source SHA256: 8a8e12ece220c7da1216b684dc077c9abe70e145a9af3bdc11194c9523a20e58
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0171


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
open ActualEisensteinCubic

theorem finite_inverse_norm_square_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0)
    (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ)^2) ≤ 1024 := by
  have hpos (I : Ideal O) (hI : I ∈ S) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑ I ∈ divisorDyadicBin S H j, 1/(Ideal.absNorm I : ℝ)^2) ≤
        512 * (1/(2:ℝ))^j.val := by
    have hp : 0 < (2:ℝ)^j.val := by positivity
    have hone : 1 ≤ (2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card : ℝ) ≤ 128 * (2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I ∈ divisorDyadicBin S H j) :
        1/(Ideal.absNorm I : ℝ)^2 ≤ 4/((2:ℝ)^j.val)^2 := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      have hni : 0 < (Ideal.absNorm I : ℝ) := lt_of_lt_of_le (by norm_num) (hpos I hIS)
      apply (div_le_div_iff₀ (sq_pos_of_pos hni) (sq_pos_of_pos hp)).mpr
      nlinarith
    calc
      _ ≤ ∑ _I ∈ divisorDyadicBin S H j, 4/((2:ℝ)^j.val)^2 :=
        Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card : ℝ) * (4/((2:ℝ)^j.val)^2) := by simp
      _ ≤ (128 * (2:ℝ)^j.val) * (4/((2:ℝ)^j.val)^2) := by gcongr
      _ = 512 * (1/(2:ℝ))^j.val := by
        rw [div_pow,one_pow]
        field_simp
        ; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength H+1), 512 * (1/(2:ℝ))^j.val :=
      Finset.sum_le_sum (fun j _ => hbin j)
    _ = 512 * ∑ j ∈ Finset.range (columnDyadicLength H+1), (1/(2:ℝ))^j := by
      rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
    _ ≤ 512 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by norm_num)
    _ = 1024 := by norm_num

theorem highSquareParts_card_le (M K : ℝ) (_hM : 0 ≤ M) (hK : 0 < K) :
    ((highSquareParts M K).card : ℝ) ≤ 128 * Real.sqrt (M/K) := by
  by_cases hempty : highSquareParts M K = ∅
  · simp only [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨A,hA⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hb := highSquareParts_bounds M K hK A hA
    apply DescentFiberCost.finite_ideal_count_real _ _ (hb.2.1.trans hb.2.2.1)
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).1.1
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).2.2.1

theorem HasSieveExponent.high_kernel {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ K →
      highKernelNorm M N K ≤ C * (M*N)^ε * (M + Real.sqrt (M/K)*N^α) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := h ε hε
  refine ⟨1024*C,by positivity,?_⟩
  intro M N K hM hN hK
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 < K := by linarith
  let S := highSquareParts M K
  have hrow (A : Ideal O) (hA : A ∈ S) :
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N ≤
        C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2 + N^α) := by
    have hb := highSquareParts_bounds M K hK0 A hA
    have hquot : M/(Ideal.absNorm A : ℝ)^2 ≤ M :=
      div_le_self hM0 (by nlinarith [sq_nonneg ((Ideal.absNorm A : ℝ)-1)])
    apply (hbound _ N hb.2.2.2 hN).trans
    gcongr
  have hsum : (∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2) ≤ 1024 := by
    apply finite_inverse_norm_square_sum S (Real.sqrt (M/K))
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).1.1
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).2.2.1
  have hcard : (S.card : ℝ) ≤ 128*Real.sqrt (M/K) := highSquareParts_card_le M K hM0 hK0
  have hcoeff : 0 ≤ C*(M*N)^ε := by positivity
  have hpow : 0 ≤ N^α := Real.rpow_nonneg hN0 _
  calc
    _ ≤ ∑ A ∈ S, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N :=
      highKernelNorm_le_squarePart_sum M N K
    _ ≤ ∑ A ∈ S, C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2+N^α) :=
      Finset.sum_le_sum hrow
    _ = C*(M*N)^ε*(M*(∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2)+(S.card:ℝ)*N^α) := by
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ C*(M*N)^ε*(M*1024+(128*Real.sqrt (M/K))*N^α) := by gcongr
    _ ≤ (1024*C)*(M*N)^ε*(M+Real.sqrt (M/K)*N^α) := by
      have hroot : 0 ≤ Real.sqrt (M/K)*N^α := mul_nonneg (Real.sqrt_nonneg _) hpow
      nlinarith [mul_nonneg hcoeff hroot]

end CanonicalQuadraticSieve

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

def bottomRowUnitary (c d : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star d/(r:ℂ),-star c/(r:ℂ);c/(r:ℂ),d/(r:ℂ)]

lemma bottomRowUnitary_mem (c d : ℂ) (r : ℝ) (hr : r≠0)
    (hrow : ‖c‖^2+‖d‖^2=r^2) : bottomRowUnitary c d r∈Matrix.unitaryGroup (Fin 2) ℂ := by
  have hC : c*star c+d*star d=(r:ℂ)^2 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_pow,← Complex.mul_conj',Complex.star_def] using
      congrArg (fun x : ℝ => (x:ℂ)) hrow
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  simp only [Complex.star_def] at hC
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bottomRowUnitary,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,
      Complex.conj_ofReal] <;>
    field_simp [hrC] <;> first | exact hC | (simpa only [mul_comm,add_comm] using hC) | ring

lemma iwasawa_z_row_identities (a b c d : ℂ) (q : ℝ)
    (hq : q≠0) (hrow : (q:ℂ)=c*star c+d*star d) (hdet : a*d-b*c=1) :
    star d/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*c=a ∧
    -star c/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*d=b := by
  have hqC : (q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq
  constructor
  · field_simp [hqC]
    rw [hrow]
    linear_combination -(star d)*hdet
  · field_simp [hqC]
    rw [hrow]
    linear_combination (star c)*hdet

def matrixHorizontal (g : SL(2,ℂ)) : ℂ :=
  (g 0 0*star (g 1 0)+g 0 1*star (g 1 1))/(rowEnergy (complexBottomRow g):ℂ)

lemma matrix_iwasawa_factor (g : SL(2,ℂ)) :
    ∃k : SL(2,ℂ), k∈compactSubgroup ∧
      g=upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k := by
  let q : ℝ := rowEnergy (complexBottomRow g)
  let r : ℝ := Real.sqrt q
  have hq : 0<q := rowEnergy_pos _ (complexBottomRow_ne_zero g)
  have hr : 0<r := Real.sqrt_pos.mpr hq
  have hr2 : r^2=q := Real.sq_sqrt hq.le
  have hrow : ‖g 1 0‖^2+‖g 1 1‖^2=r^2 := by
    rw [hr2]
    rfl
  have hqC : (q:ℂ)=g 1 0*star (g 1 0)+g 1 1*star (g 1 1) := by
    simp only [q,rowEnergy,complexBottomRow,Complex.ofReal_add,Complex.ofReal_pow,
      ← Complex.mul_conj',Complex.star_def]
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hz := iwasawa_z_row_identities (g 0 0) (g 0 1) (g 1 0) (g 1 1) q hq.ne' hqC hdet
  let B := upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)
  let U := bottomRowUnitary (g 1 0) (g 1 1) r
  have hroot : Real.sqrt (liftedHeight g)=r⁻¹ := by
    exact Real.sqrt_inv q
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hqrC : (r:ℂ)^2=(q:ℂ) := by exact_mod_cast hr2
  have hB : (B:Matrix (Fin 2) (Fin 2) ℂ)=
      !![(r:ℂ)⁻¹,matrixHorizontal g*(r:ℂ);0,(r:ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,upperSection,hroot,Complex.ofReal_inv,div_eq_mul_inv]
  have hfactor : (B:Matrix (Fin 2) (Fin 2) ℂ)*U=(g:Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two]
    · change (r:ℂ)⁻¹*(star (g 1 1)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 0/(r:ℂ))=g 0 0
      calc
        _ = star (g 1 1)/(q:ℂ)+matrixHorizontal g*g 1 0 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.1
    · change (r:ℂ)⁻¹*(-star (g 1 0)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 1/(r:ℂ))=g 0 1
      calc
        _ = -star (g 1 0)/(q:ℂ)+matrixHorizontal g*g 1 1 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.2
    · change 0*(star (g 1 1)/(r:ℂ))+(r:ℂ)*(g 1 0/(r:ℂ))=g 1 0
      field_simp [hrC] ; ring
    · change 0*(-star (g 1 0)/(r:ℂ))+(r:ℂ)*(g 1 1/(r:ℂ))=g 1 1
      field_simp [hrC] ; ring
  let k : SL(2,ℂ) := B⁻¹*g
  have hk : (k:Matrix (Fin 2) (Fin 2) ℂ)=U := by
    change ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) * (g:Matrix (Fin 2) (Fin 2) ℂ)=U
    rw [← hfactor,← Matrix.mul_assoc]
    have hi : ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(B:Matrix (Fin 2) (Fin 2) ℂ)=1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one] using
        congrArg (fun M : SL(2,ℂ) => (M:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel B)
    rw [hi,Matrix.one_mul]
  refine ⟨k,?_,?_⟩
  · change (k:Matrix (Fin 2) (Fin 2) ℂ)∈Matrix.unitaryGroup (Fin 2) ℂ
    rw [hk]
    exact bottomRowUnitary_mem _ _ r hr.ne' hrow
  · dsimp [k,B]
    group

theorem upperPoint_surjective (w : HyperbolicSpace) :
    ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v, upperPoint z v hv=w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
    refine ⟨matrixHorizontal g,liftedHeight g,liftedHeight_pos g,?_⟩
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
    have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
      calc
        _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
            (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
          congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
        _ = k := inv_mul_cancel_left _ _
    rw [hcancel]
    exact hk

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O

lemma eisEmbedding_range_closed : IsClosed (Set.range eisEmbedding) := by
  let : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
  have hc : IsClosed (periodLattice : Set ℂ) :=
    periodLattice.toAddSubgroup.isClosed_of_discreteTopology
  have heq : Set.range eisEmbedding=(fun z : ℂ => 3*z) ⁻¹' (periodLattice : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨n,rfl⟩
      exact three_embedding_mem n
    · intro hz
      obtain ⟨n,hn⟩ := periodPoint_bijective.2 ⟨3*z,hz⟩
      refine ⟨n,?_⟩
      have h := congrArg Subtype.val hn
      exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) h
  rw [heq]
  exact hc.preimage (by fun_prop)

lemma exists_nearest_eisenstein (z : ℂ) :
    ∃n : O, ∀m : O, ‖z-eisEmbedding n‖≤‖z-eisEmbedding m‖ := by
  obtain ⟨y,hy,heq⟩ := eisEmbedding_range_closed.exists_infDist_eq_dist
    (Set.range_nonempty eisEmbedding) z
  obtain ⟨n,rfl⟩ := hy
  refine ⟨n,fun m => ?_⟩
  rw [← dist_eq_norm,← dist_eq_norm,← heq]
  exact Metric.infDist_le_dist_of_mem ⟨m,rfl⟩

lemma hexagon_norm_sq_bound (x y : ℝ)
    (hx : |x|≤1/2)
    (h₁ : x+Real.sqrt 3*y≤1) (h₂ : x-Real.sqrt 3*y≤1)
    (h₃ : -x+Real.sqrt 3*y≤1) (h₄ : -x-Real.sqrt 3*y≤1) :
    x^2+y^2≤1/3 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have ha : |x|+Real.sqrt 3*|y|≤1 := by
    rcases le_total 0 x with hxx | hxx <;> rcases le_total 0 y with hyy | hyy
    · simpa only [abs_of_nonneg hxx,abs_of_nonneg hyy] using h₁
    · simpa only [abs_of_nonneg hxx,abs_of_nonpos hyy,mul_neg,← sub_eq_add_neg] using h₂
    · simpa only [abs_of_nonpos hxx,abs_of_nonneg hyy] using h₃
    · simpa only [abs_of_nonpos hxx,abs_of_nonpos hyy,mul_neg,← sub_eq_add_neg] using h₄
  have hyprod : 0≤(1-|x|-Real.sqrt 3*|y|)*(1-|x|+Real.sqrt 3*|y|) := by
    apply mul_nonneg
    · linarith
    · have : 0≤Real.sqrt 3*|y| := mul_nonneg (Real.sqrt_nonneg 3) (abs_nonneg y)
      linarith
  have hxprod : |x| * (2*|x|-1)≤0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg x) (by linarith)
  have hxy : (Real.sqrt 3*|y|)^2=3*y^2 := by rw [mul_pow,hs,sq_abs]
  nlinarith [sq_abs x,sq_abs y]

theorem exists_eisenstein_distance_sq_le_third (z : ℂ) :
    ∃n : O, Complex.normSq (z-eisEmbedding n)≤1/3 := by
  obtain ⟨n,hn⟩ := exists_nearest_eisenstein z
  let w := z-eisEmbedding n
  have hmin (u : O) : Complex.normSq w≤Complex.normSq (w-eisEmbedding u) := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h := hn (n+u)
    simpa only [map_add,sub_add_eq_sub_sub] using h
  have hre : omega3.re= -(1/2:ℝ) := by norm_num [omega3]
  have h1 := hmin 1
  have hn1 := hmin (-1)
  have hω := hmin (ActualEisensteinCoordinates.eval 0 1)
  have hnω := hmin (-(ActualEisensteinCoordinates.eval 0 1))
  have hη := hmin (ActualEisensteinCoordinates.eval 1 1)
  have hnη := hmin (-(ActualEisensteinCoordinates.eval 1 1))
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  simp only [map_one,map_neg,eisEmbedding_eval,Int.cast_zero,Int.cast_one,zero_add,one_mul,
    Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,hre,omega3_im] at h1 hn1 hω hnω hη hnη
  refine ⟨n,?_⟩
  change Complex.normSq w≤1/3
  rw [Complex.normSq_apply,← sq,← sq]
  apply hexagon_norm_sq_bound
  · apply abs_le.mpr
    constructor <;> nlinarith
  · nlinarith [hη]
  · nlinarith [hnω]
  · nlinarith [hω]
  · nlinarith [hnη]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def integralBottomRow (M : SL(2,O)) : Fin 2 → O := fun j => M 1 j
def integralRowEnergy (g : SL(2,ℂ)) (v : Fin 2 → O) : ℝ :=
  rowEnergy (rowOperator g (fun j => eisEmbedding (v j)))

lemma integralRowEnergy_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {v : Fin 2 → O | integralRowEnergy g v≤C} := by
  have hb : Set.Finite (Metric.closedBall (0 : (Fin 2×Fin 2)→ℤ) (rowBound g*Real.sqrt C)) :=
    (isCompact_closedBall _ _).finite_of_discrete
  apply (Set.Finite.preimage rowCoordinates_injective.injOn hb).subset
  intro v hv
  change rowCoordinates v∈Metric.closedBall 0 (rowBound g*Real.sqrt C)
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (coordinates_le_transformed_energy g v).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (rowBound_pos g).le)

lemma integral_height_action_matrix (M : SL(2,O)) (g : SL(2,ℂ)) :
    hyperbolicHeight (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))=
      (integralRowEnergy g (integralBottomRow M))⁻¹ := by
  change (rowEnergy (complexBottomRow (integralComplexMatrix M*g)))⁻¹=_
  rw [complexBottomRow_mul]
  rfl

lemma integralRowEnergy_bottom_pos (g : SL(2,ℂ)) (M : SL(2,O)) :
    0 < integralRowEnergy g (integralBottomRow M) := by
  have h := hyperbolicHeight_pos (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))
  rw [integral_height_action_matrix,inv_pos] at h
  exact h

theorem exists_maximal_integral_height (w : HyperbolicSpace) :
    ∃N : SL(2,O), ∀M : SL(2,O),
      hyperbolicHeight (integralComplexMatrix M • w)≤hyperbolicHeight (integralComplexMatrix N • w) := by
  induction w using Quotient.inductionOn with
  | _ g =>
    let P : Set (Fin 2 → O) := Set.range integralBottomRow
    let C := integralRowEnergy g (integralBottomRow 1)
    let S : Set (Fin 2 → O) := {v | integralRowEnergy g v≤C} ∩ P
    have hS : Set.Finite S := (integralRowEnergy_sublevel_finite g C).inter_of_left P
    have hSne : S.Nonempty := by
      refine ⟨integralBottomRow 1,?_⟩
      change C≤C ∧ integralBottomRow 1∈Set.range integralBottomRow
      exact ⟨le_rfl,1,rfl⟩
    obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S (integralRowEnergy g) hS hSne
    obtain ⟨N,hN⟩ := hv.2
    refine ⟨N,fun M => ?_⟩
    have hNM : integralRowEnergy g (integralBottomRow N)≤ integralRowEnergy g (integralBottomRow M) := by
      rw [hN]
      by_cases hM : integralRowEnergy g (integralBottomRow M)≤C
      · exact hmin _ ⟨hM,⟨M,rfl⟩⟩
      · exact hv.1.trans (le_of_not_ge hM)
    rw [integral_height_action_matrix,integral_height_action_matrix]
    exact inv_anti₀ (integralRowEnergy_bottom_pos g N) hNM

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def integralTranslation (n : O) : SL(2,O) :=
  ⟨!![1,n;0,1],by simp [Matrix.det_fin_two]⟩
def integralInversion : SL(2,O) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma integralTranslation_action (n : O) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (integralTranslation n) • upperPoint z v hv=
      upperPoint (z+eisEmbedding n) v hv := by
  change (QuotientGroup.mk (integralComplexMatrix (integralTranslation n)*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+eisEmbedding n) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (integralComplexMatrix (integralTranslation n) : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + eisEmbedding n) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [integralComplexMatrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation,RingHom.mapMatrix_apply,Matrix.map_apply,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma integralInversion_height (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix integralInversion • upperPoint z v hv)=
      v/(‖z‖^2+v^2) := by
  have h10 : integralComplexMatrix integralInversion 1 0 = 1 := by
    change eisEmbedding 1 = 1
    exact map_one eisEmbedding
  have h11 : integralComplexMatrix integralInversion 1 1 = 0 := by
    change eisEmbedding 0 = 0
    exact map_zero eisEmbedding
  rw [hyperbolicHeight_action_upperPoint, h10, h11]
  simp

theorem bianchi_ford_cover (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ 1≤Complex.normSq z+v^2 ∧
      ∀R : SL(2,O),hyperbolicHeight (integralComplexMatrix R • upperPoint z v hv)≤v := by
  obtain ⟨N,hN⟩ := exists_maximal_integral_height w
  obtain ⟨z,v,hv,hpoint⟩ := upperPoint_surjective (integralComplexMatrix N • w)
  obtain ⟨n,hn⟩ := exists_eisenstein_distance_sq_le_third z
  let M : SL(2,O) := integralTranslation (-n)*N
  let z' := z-eisEmbedding n
  have hMw : integralComplexMatrix M • w=upperPoint z' v hv := by
    dsimp [M]
    rw [map_mul,mul_smul,← hpoint,integralTranslation_action,map_neg]
    rfl
  have hNv : hyperbolicHeight (integralComplexMatrix N • w)=v := by
    rw [← hpoint,hyperbolicHeight_upperPoint]
  have hmax (R : SL(2,O)) :
      hyperbolicHeight (integralComplexMatrix R • upperPoint z' v hv)≤v := by
    have h := hN (R*M)
    rwa [map_mul,mul_smul,hMw,hNv] at h
  have hinv := hmax integralInversion
  rw [integralInversion_height] at hinv
  have hden : 0<‖z'‖^2+v^2 := by positivity
  have hunit : 1≤‖z'‖^2+v^2 := by
    have hm := (div_le_iff₀ hden).mp hinv
    by_contra hh
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hv
    linarith
  refine ⟨M,z',v,hv,hMw,hn,?_,hmax⟩
  simpa only [Complex.normSq_eq_norm_sq] using hunit

theorem bianchi_reduction_height_floor (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨M,z,v,hv,hMw,hz,hunit,hmax⟩ := bianchi_ford_cover w
  refine ⟨M,z,v,hv,hMw,hz,?_⟩
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hv.le,by linarith⟩

def truncatedFordBox (T : ℝ) : Set (ℂ×ℝ) :=
  Metric.closedBall 0 1 ×ˢ Set.Icc (Real.sqrt (2/3)) T
lemma truncatedFordBox_isCompact (T : ℝ) : IsCompact (truncatedFordBox T) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

lemma mem_truncatedFordBox (z : ℂ) (v T : ℝ)
    (hz : Complex.normSq z≤1/3) (hv : Real.sqrt (2/3)≤v) (hT : v≤T) :
    (z,v)∈truncatedFordBox T := by
  refine ⟨?_,hv,hT⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma levelThree_finiteIndex : levelThree.FiniteIndex := by
  let : Finite (O ⧸ Ideal.span {(3:O)}) := finite_quotient_span (by norm_num)
  unfold levelThree
  infer_instance

def finiteCubicMultiplier : levelThree →* rootsOfUnity 3 ℂ where
  toFun M := rootsOfUnity.mkOfPowEq (complexCharacter M) (complexCharacter_cube M)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq,map_one,OneMemClass.coe_one,Units.val_one]
  map_mul' M N := by
    apply Subtype.ext
    apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq,map_mul,Subgroup.coe_mul,Units.val_mul]

def globalKubotaKernel : Subgroup (SL(2,O)) := finiteCubicMultiplier.ker.map levelThree.subtype

lemma globalKubotaKernel_finiteIndex : globalKubotaKernel.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  let : finiteCubicMultiplier.ker.FiniteIndex := inferInstance
  constructor
  rw [globalKubotaKernel,Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := finiteCubicMultiplier.ker))
    (Subgroup.FiniteIndex.index_ne_zero (H := levelThree))

@[simp] lemma finiteCubicMultiplier_coe (M : levelThree) :
    ((finiteCubicMultiplier M : ℂˣ) : ℂ)=complexCharacter M := rfl

lemma finiteCubicMultiplier_eq_one (M : levelThree) :
    finiteCubicMultiplier M=1 ↔ complexCharacter M=1 := by
  constructor
  · intro h
    have hc := congrArg (fun x : rootsOfUnity 3 ℂ => ((x:ℂˣ):ℂ)) h
    simpa only [finiteCubicMultiplier_coe,OneMemClass.coe_one,Units.val_one] using hc
  · intro h
    apply Subtype.ext
    apply Units.ext
    simpa only [finiteCubicMultiplier_coe,OneMemClass.coe_one,Units.val_one] using h

lemma globalKubotaKernel_mem (M : SL(2,O)) :
    M∈globalKubotaKernel ↔ ∃hM : M∈levelThree,complexCharacter ⟨M,hM⟩=1 := by
  constructor
  · rintro ⟨N,hN,hNM⟩
    subst M
    exact ⟨N.property,(finiteCubicMultiplier_eq_one N).mp hN⟩
  · rintro ⟨hM,hc⟩
    exact ⟨⟨M,hM⟩,(finiteCubicMultiplier_eq_one ⟨M,hM⟩).mpr hc,rfl⟩

lemma finite_right_representatives {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃S : Finset G, ∀g : G,∃r∈S,r⁻¹*g∈H := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let S : Finset G := Finset.univ.image (fun q : G ⧸ H => Quotient.out q)
  refine ⟨S,fun g => ?_⟩
  let q : G ⧸ H := QuotientGroup.mk g
  refine ⟨Quotient.out q,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  · exact QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' q))

theorem finiteIndex_ford_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : H, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=
          integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨S,hS⟩ := finite_right_representatives H
  refine ⟨S,fun w => ?_⟩
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨r,hr,hh⟩ := hS M
  refine ⟨⟨r⁻¹*M,hh⟩,r,hr,z,v,hv,?_,hz,hfloor⟩
  change integralComplexMatrix (r⁻¹*M) • w=_
  rw [map_mul,mul_smul,hMw]

theorem levelThree_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : levelThree, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        complexMatrix h • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  exact finiteIndex_ford_cover levelThree

theorem globalKubotaKernel_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : globalKubotaKernel, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_ford_cover globalKubotaKernel

end CubicEisenstein

end

end OAI
end OAIOriginalModule0171

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology
Source SHA256: f5678b485ac2676e890b1b6bd20f420e0ae86a130e12506d2f45aba6d94e1f61
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0172


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
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

instance complexSLTopology : TopologicalSpace (SL(2,ℂ)) :=
  inferInstanceAs (TopologicalSpace {A : Matrix (Fin 2) (Fin 2) ℂ // A.det=1})

lemma continuous_complexSL_coe :
    Continuous (fun g : SL(2,ℂ) => (g : Matrix (Fin 2) (Fin 2) ℂ)) :=
  continuous_subtype_val

lemma continuous_complexSL_mul (g : SL(2,ℂ)) :
    Continuous (fun h : SL(2,ℂ) => g*h) := by
  apply Continuous.subtype_mk
  change Continuous (fun h : SL(2,ℂ) =>
    (g : Matrix (Fin 2) (Fin 2) ℂ)*(h : Matrix (Fin 2) (Fin 2) ℂ))
  exact continuous_const.mul continuous_complexSL_coe

lemma continuous_coordinateSection : Continuous coordinateSection := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀w : UpperCoordinates,(Real.sqrt w.1.2 : ℂ)≠0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  fin_cases i <;> fin_cases j
  · exact hroot
  · exact (continuous_fst.comp continuous_subtype_val).div hroot hne
  · exact continuous_const
  · exact hroot.inv₀ hne

lemma continuous_hyperbolicProjection :
    Continuous (fun g : SL(2,ℂ) => (g : HyperbolicSpace)) :=
  continuous_quotient_mk'

lemma continuous_upperCoordinates :
    Continuous (fun w : UpperCoordinates => upperPoint w.1.1 w.1.2 w.2) :=
  continuous_hyperbolicProjection.comp continuous_coordinateSection

lemma continuous_translatedUpperCoordinates (g : SL(2,ℂ)) :
    Continuous (fun w : UpperCoordinates => g • upperPoint w.1.1 w.1.2 w.2) := by
  exact continuous_hyperbolicProjection.comp
    ((continuous_complexSL_mul g).comp continuous_coordinateSection)

def integralOrbitRel (H : Subgroup (SL(2,O))) : Setoid HyperbolicSpace where
  r w w' := ∃h : H, integralComplexMatrix (h:SL(2,O)) • w = w'
  iseqv := ⟨by intro w; exact ⟨1,by simp⟩,
    by
      rintro w w' ⟨h,hh⟩
      refine ⟨h⁻¹,?_⟩
      rw [←hh]
      simp [←mul_smul],
    by
      rintro w w' w'' ⟨h,hh⟩ ⟨k,hk⟩
      refine ⟨k*h,?_⟩
      simpa only [Subgroup.coe_mul,map_mul,mul_smul,hh] using hk⟩

abbrev IntegralOrbitQuotient (H : Subgroup (SL(2,O))) := Quotient (integralOrbitRel H)

def integralOrbitProjection (H : Subgroup (SL(2,O))) :
    HyperbolicSpace → IntegralOrbitQuotient H := Quotient.mk _

lemma continuous_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Continuous (integralOrbitProjection H) := continuous_quotient_mk'

lemma integralOrbitProjection_eq (H : Subgroup (SL(2,O))) (h : H) (w : HyperbolicSpace) :
    integralOrbitProjection H (integralComplexMatrix (h:SL(2,O)) • w)=
      integralOrbitProjection H w := by
  apply Eq.symm
  exact Quotient.sound ⟨h,rfl⟩

end

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

def truncatedFordLift (T : ℝ) (p : truncatedFordBox T) : UpperCoordinates :=
  ⟨p.1,lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/3)) p.2.2.1⟩

lemma continuous_truncatedFordLift (T : ℝ) : Continuous (truncatedFordLift T) :=
  continuous_subtype_val.subtype_mk _

def fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) (p : UpperCoordinates) :
    IntegralOrbitQuotient H := integralOrbitProjection H
      (integralComplexMatrix r⁻¹ • upperPoint p.1.1 p.1.2 p.2)

lemma continuous_fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) :
    Continuous (fordOrbitChart H r) :=
  (continuous_integralOrbitProjection H).comp
    (continuous_translatedUpperCoordinates (integralComplexMatrix r⁻¹))

def compactFordCore (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  ⋃r∈S, Set.range (fun p : truncatedFordBox T => fordOrbitChart H r (truncatedFordLift T p))

lemma compactFordCore_isCompact (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    IsCompact (compactFordCore H S T) := by
  let : CompactSpace (truncatedFordBox T) :=
    isCompact_iff_compactSpace.mp (truncatedFordBox_isCompact T)
  apply S.isCompact_biUnion
  intro r hr
  exact isCompact_range ((continuous_fordOrbitChart H r).comp (continuous_truncatedFordLift T))

def fordCuspTail (H : Subgroup (SL(2,O))) (r : SL(2,O)) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  fordOrbitChart H r '' {p : UpperCoordinates | Complex.normSq p.1.1≤1/3 ∧
    Real.sqrt (2/3)≤p.1.2 ∧ T<p.1.2}

theorem finiteIndex_compact_core_cusp_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore H S T) ∧
      Set.univ=compactFordCore H S T ∪ ⋃r∈S, fordCuspTail H r T := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  refine ⟨S,fun T => ⟨compactFordCore_isCompact H S T,?_⟩⟩
  apply Set.Subset.antisymm
  · intro q hq
    induction q using Quotient.inductionOn with | _ w =>
      obtain ⟨h,r,hr,z,v,hv,heq,hz,hfloor⟩ := hS w
      have hqeq : integralOrbitProjection H w=fordOrbitChart H r ⟨(z,v),hv⟩ := by
        rw [←integralOrbitProjection_eq H h w,heq]
        rfl
      change integralOrbitProjection H w∈_
      rw [hqeq]
      by_cases hT : v≤T
      · apply Or.inl
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),mem_truncatedFordBox z v T hz hfloor hT⟩,rfl⟩
      · apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),hv⟩,⟨hz,hfloor,lt_of_not_ge hT⟩,rfl⟩
  · exact Set.subset_univ _

theorem levelThree_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore levelThree S T) ∧
      Set.univ=compactFordCore levelThree S T ∪ ⋃r∈S, fordCuspTail levelThree r T := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  exact finiteIndex_compact_core_cusp_cover levelThree

theorem globalKubotaKernel_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore globalKubotaKernel S T) ∧
      Set.univ=compactFordCore globalKubotaKernel S T ∪ ⋃r∈S, fordCuspTail globalKubotaKernel r T := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_compact_core_cusp_cover globalKubotaKernel

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)

local instance {ι : Type*} : Nonempty (GlobalSecondData ι) :=
  ⟨⟨⟨0,0,∅,∅⟩,∅,∅,∅,⟨∅,∅,∅,0⟩⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondRecover (s : Finset (GlobalSecondData ι)) : SecondPassFiber.OldTuple → GlobalSecondData ι :=
  Function.invFunOn (globalSecondTuple p) s

theorem globalSecondRecover_apply
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (x : GlobalSecondData ι) (hx : x∈s) :
    globalSecondRecover p s (globalSecondTuple p x)=x := by
  have hi : Set.InjOn (globalSecondTuple p) s := by
    intro x hx y hy h
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs y hy) ((hq x hx).trans (hq y hy).symm) h
  exact hi.leftInvOn_invFunOn hx

def globalSecondSource (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ,ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x∈s,w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem globalSecondSource_eq_tupleSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (w : GlobalSecondData ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) :
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    tupleSourceSum p hp hcop hg (s.image (globalSecondTuple p))
      (w ∘ globalSecondRecover p s) (globalSecondLabel p ∘ globalSecondRecover p s)
      F Ψ₁ Ψ₂ m A₁ A₂ W V (z ∘ globalSecondRecover p s) (ud ∘ globalSecondRecover p s)
      (ue ∘ globalSecondRecover p s) (uv ∘ globalSecondRecover p s) (kap ∘ globalSecondRecover p s) X₁ X₂ R := by
  unfold globalSecondSource tupleSourceSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    simp only [Function.comp_apply,globalSecondRecover_apply p hinj s q hs hq x hx]
  · intro x hx y hy he
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs y hy) ((hq x hx).trans (hq y hy).symm) he

theorem globalSecondSource_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htransfer⟩ := SecondPassIntegration.tupleSource_uniform_transfer p hp hcop hg
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  obtain ⟨b,hb,htrans⟩ := htransfer R hR
  let r := globalSecondRecover p s
  have hr (x : GlobalSecondData ι) (hx : x∈s) : r (globalSecondTuple p x)=x :=
    globalSecondRecover_apply p hinj s q hs hfixed x hx
  have hvalid : ∀ y∈s.image (globalSecondTuple p),
      SecondPassFiber.Valid y (newLabel y) q.1 (newRow y) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hv := globalSecondTuple_valid p x (hs x hx)
    simpa only [hfixed x hx] using hv
  have hmap' : ∀ y∈s.image (globalSecondTuple p),(newLabel y,newRow y)∈T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hmap x hx
  have hw' : ∀ y∈s.image (globalSecondTuple p),
      ‖(w ∘ r) y‖*‖outerWindow V ((z ∘ r) y) ((ud ∘ r) y) ((ue ∘ r) y) ((uv ∘ r) y) ((kap ∘ r) y)‖ ≤ B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using hw x hx
  have hlabel : ∀ y∈s.image (globalSecondTuple p),Ideal.span {(globalSecondLabel p ∘ r) y}=newLabel y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using globalSecondLabel_span p x
  have hh := htrans (s.image (globalSecondTuple p)) T q.1 (w ∘ r) B lengthScale (globalSecondLabel p ∘ r)
    F Ψ₁ Ψ₂ (fixedTripleMask m q) (z ∘ r) (ud ∘ r) (ue ∘ r) (uv ∘ r) (kap ∘ r) X₁ X₂
    hq hB hL hvalid hmap' ht hn hw' hlabel
  rw [← globalSecondSource_eq_tupleSource p hp hcop hg hinj s q hs hfixed] at hh
  apply hh.trans
  have hd := SecondPassIntegration.child_coefficient_density_bound p hp hcop hg F Ψ₁ Ψ₂
    (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b J ((1+R)^A) Cₛ hb
  have hpow : 0 < (1+R)^A := pow_pos (by linarith) _
  have hi := (le_div_iff₀' hpow).mpr hd
  have hnn : 0 ≤ B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε := by positivity
  have hbnd := mul_le_mul_of_nonneg_left hi hnn
  convert hbnd using 1 ; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (outerWindow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondRawPool (F : Finset ι) (x : GlobalSecondData ι) : Finset ι :=
  (F\(x.cube.support∪x.common))\x.firstCommon

def globalSecondRawMask (m : O) (x : GlobalSecondData ι) : O :=
  m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit *
    primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)

def globalSecondRawSource (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ,ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x∈s,w x * postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x) Ψ₁ Ψ₂
    (globalSecondRawMask p m x) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem globalSecondRawSource_eq
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (q : Ideal O × Ideal O × Ideal O) (hfixed : ∀ x∈s,globalSecondFixedTriple p x=q)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) (hR : 0 < R) :
    globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R := by
  obtain ⟨C,hC,hsep⟩ := postCommonSmoothPair_uniform_fixed_tests p hp hcop hg A₁ A₂ W V M hM hV 0 0
  obtain ⟨b,hb,hid⟩ := hsep R hR
  unfold globalSecondRawSource globalSecondSource
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun a : ℂ => w x * a)
  rw [hid (globalSecondRawPool F x) Ψ₁ Ψ₂ (globalSecondRawMask p m x) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂,
    hid F Ψ₁ Ψ₂ (fixedTripleMask m q) (globalSecondLabel p x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
    (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂]
  simp only [separatedPostCommon,globalSecondRawPool,globalSecondRawMask,
    globalSecondRawRow_fixed_pool p hp hcop hg hinj,hfixed x hx]

theorem globalSecondRawSource_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := globalSecondSource_uniform_transfer p hp hcop hg hinj
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  rw [globalSecondRawSource_eq p hp hcop hg hinj A₁ A₂ W V M hM hV s w q hfixed
    F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ R hR]
  exact htrans R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct jLabel b0Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
def sideDivisor {ι : Type*} (x : CubeCoordinates ι) (side : Bool) : Finset ι :=
  if side then x.leftDivisor else x.rightDivisor
end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalCubeJNorm (x : GlobalSecondData ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit)‖^2

def globalCubeActiveRoot (x : GlobalSecondData ι) : ℝ :=
  ‖eisEmbedding (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖

def globalFirstColumnScale (ell : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  ell/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common)

def globalFirstRowScale (K ell B F : ℝ) (x : GlobalSecondData ι) : ℝ :=
  ell^2*B^4*F^2*primeProductNorm p x.firstDivisor/
    (K*(primeProductNorm p x.common)^2*globalCubeJNorm p x)

def globalSecondDelta (B F : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  B*F*primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.firstCommon*
    primeProductNorm p (x.source.sourceCommon\x.source.divisor)

def globalNominalChildRow (K B F : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  K*globalCubeJNorm p x/((globalSecondDelta p B F x side)^2*B^2)

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeJNorm_pos (x : GlobalSecondData ι) : 0 < globalCubeJNorm p x :=
  zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeActiveRoot_pos (x : GlobalSecondData ι) : 0 < globalCubeActiveRoot p x := by
  have hh := element_norm_ge_one (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  change 0 < ‖eisEmbedding _‖
  nlinarith [norm_nonneg (eisEmbedding (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i))]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstColumnScale_pos (ell : ℝ) (hell : 0 < ell) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalFirstColumnScale p ell x side :=
  div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondDelta_ge (B F : ℝ) (hB : 0 ≤ B) (hF : 1 ≤ F) (x : GlobalSecondData ι) (side : Bool) :
    B ≤ globalSecondDelta p B F x side := by
  have hA := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hR := primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  unfold globalSecondDelta
  calc
    B = B*1*1*1*1 := by ring
    _ ≤ _ := by gcongr

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondDelta_pos (B F : ℝ) (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalSecondDelta p B F x side := by
  unfold globalSecondDelta
  exact mul_pos (mul_pos (mul_pos (mul_pos hB hF)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)) (FirstPassCubeLabels.primeProductNorm_pos p hp _)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalBaseLabel_norm (x : GlobalSecondData ι) :
    ‖eisEmbedding (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
      x.cube.leftBit x.cube.rightBit)‖^2 = primeProductNorm p x.common*globalCubeJNorm p x := by
  simp only [secondBaseLabel,map_mul,norm_mul,mul_pow,primeSubsetGenerator_norm_eq_productNorm,globalCubeJNorm]

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_radial_ratio (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex) :
    globalFirstRowScale p K ell B F x*secondLogK j*
      (primeProductNorm p (x.source.sourceCommon\x.source.divisor))^2/
      (primeProductNorm p x.firstDivisor*(globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)^2) =
    secondLogK j/globalNominalChildRow p K B F x side := by
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have hd := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
  have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
  have hJ := (globalCubeJNorm_pos p hp x).ne'
  unfold globalFirstRowScale globalFirstColumnScale globalNominalChildRow globalSecondDelta
  field_simp

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_child_mass (ell B F : ℝ) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex) :
    secondLogX p (x.source.sourceCommon\x.source.divisor)
      (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) j *
      secondLogLabelBound p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit j =
    Real.exp 2*((ell*B^3)*F*globalCubeJNorm p x/(globalSecondDelta p B F x side*B^2)) := by
  rw [secondLogX_label_cost,globalBaseLabel_norm]
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
  have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
  unfold globalFirstColumnScale globalSecondDelta
  field_simp

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_complete_cost (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) :
    (K/(primeProductNorm p x.firstDivisor*ell*B^2*F*globalCubeActiveRoot p x)) *
      (globalFirstRowScale p K ell B F x *
        ‖eisEmbedding (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)‖^2*Real.exp 2/globalFirstColumnScale p ell x side) *
      ((B*globalCubeActiveRoot p x/globalCubeJNorm p x)*primeProductNorm p x.firstCommon*
        primeProductNorm p (x.source.sourceCommon\x.source.divisor)) =
    Real.exp 2*globalSecondDelta p B F x side*B^2/globalCubeJNorm p x := by
  rw [globalBaseLabel_norm]
  have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
  have hd := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).ne'
  have ha := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
  have hJ := (globalCubeJNorm_pos p hp x).ne'
  have hc := (globalCubeActiveRoot_pos p hp x).ne'
  unfold globalFirstRowScale globalFirstColumnScale globalSecondDelta
  field_simp

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalNominalChildRow_pos (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) : 0 < globalNominalChildRow p K B F x side := by
  unfold globalNominalChildRow
  exact div_pos (mul_pos hK (globalCubeJNorm_pos p hp x))
    (mul_pos (sq_pos_of_pos (globalSecondDelta_pos p hp B F hB hF x side)) (sq_pos_of_pos hB))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalNominalChildRow_bound (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalNominalChildRow p K B F x side ≤ K/(globalSecondDelta p B F x side)^2 := by
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).1
  change globalCubeJNorm p x ≤ B^2 at hJ
  unfold globalNominalChildRow
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  calc
    _ ≤ K*B^2/((globalSecondDelta p B F x side)^2*B^2) := by gcongr
    _ = _ := by field_simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalChildMass (ell : ℝ) (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex) : ℝ :=
  secondLogX p (x.source.sourceCommon\x.source.divisor)
    (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) j *
    secondLogLabelBound p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent
      x.cube.leftBit x.cube.rightBit j

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalChildMass_bound (ell B F : ℝ) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalChildMass p ell x side j ≤ Real.exp 2*((ell*B^3)*F)/globalSecondDelta p B F x side := by
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).1
  change globalCubeJNorm p x ≤ B^2 at hJ
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  rw [globalChildMass,globalSecond_child_mass p hp ell B F hell hB hF]
  calc
    _ ≤ Real.exp 2*((ell*B^3)*F*B^2/(globalSecondDelta p B F x side*B^2)) := by gcongr
    _ = _ := by field_simp

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalChildRow_bound (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side) :
    secondLogK j*Real.exp 1 ≤ Real.exp 1*K/globalSecondDelta p B F x side := by
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  have hK' := globalNominalChildRow_pos p hp K B F hK hB hF x side
  have hk := (div_le_iff₀ hK').mp hretained
  have hsmall := globalNominalChildRow_bound p hp K B F hK hB hF x side hb₁ hb₂
  calc
    _ ≤ (globalSecondDelta p B F x side*globalNominalChildRow p K B F x side)*Real.exp 1 := by gcongr
    _ ≤ (globalSecondDelta p B F x side*(K/(globalSecondDelta p B F x side)^2))*Real.exp 1 := by gcongr
    _ = _ := by field_simp

include hp in

theorem globalSecondMask_bound (B F : ℝ) (hB : 0 < B) (hF : 1 ≤ F)
    (x : GlobalSecondData ι) (side : Bool) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 ≤
      ‖eisEmbedding m‖^2*globalSecondDelta p B F x side := by
  have hb0 := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).2.1
  have he : ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 =
      ‖eisEmbedding (globalSecondMask p m x)‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span,globalSecondMask_span]
  rw [he]
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  change ‖eisEmbedding ((m*_*_)*∏ i∈x.firstCommon,p i)‖^2 ≤ _
  rw [SecondPassIntegration.restored_child_mask_norm]
  unfold globalSecondDelta
  calc
    _ ≤ ‖eisEmbedding m‖^2*B*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*primeProductNorm p x.firstCommon := by gcongr
    _ ≤ ‖eisEmbedding m‖^2*(B*F*primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.firstCommon*
      primeProductNorm p (x.source.sourceCommon\x.source.divisor)) := by
      have hf : B ≤ B*F*primeProductNorm p (x.cube.sideDivisor side) := by
        calc
          B = B*1*1 := by ring
          _ ≤ _ := by gcongr
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf ht) hr) (sq_nonneg ‖eisEmbedding m‖)]

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecond_halving (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side)
    (hlarge : 2*Real.exp 2 ≤ globalSecondDelta p B F x side) :
    secondLogK j*Real.exp 1 ≤ K/2 ∧ globalChildMass p ell x side j ≤ ((ell*B^3)*F)/2 := by
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  have he : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hrow := globalChildRow_bound p hp K B F hK hB hF x side j hb₁ hb₂ hretained
  have hmass := globalChildMass_bound p hp ell B F hell hB hF x side j hb₁ hb₂
  constructor
  · apply hrow.trans
    apply (div_le_iff₀ hD).mpr
    nlinarith
  · apply hmass.trans
    apply (div_le_iff₀ hD).mpr
    have hparent : 0 < (ell*B^3)*F := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlarge hparent.le]

end

theorem ceil_strict_of_half {a b : ℝ} (hb : 2 ≤ b) (ha : a ≤ b/2) : ⌈a⌉₊ < ⌈b⌉₊ := by
  have hc : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hn : 2 ≤ ⌈b⌉₊ := by exact_mod_cast (hb.trans hc)
  have hn1 : 1 ≤ ⌈b⌉₊ := by omega
  have hbound : a ≤ ((⌈b⌉₊-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1,Nat.cast_one]
    have hh : (2 : ℝ) ≤ ⌈b⌉₊ := by exact_mod_cast hn
    linarith
  have hf : ⌈a⌉₊ ≤ ⌈b⌉₊-1 := Nat.ceil_le.mpr hbound
  omega

theorem globalSecond_rank_decreases {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side)
    (hlarge : 2*Real.exp 2 ≤ globalSecondDelta p B F x side) :
    ⌈max (secondLogK j*Real.exp 1) (globalChildMass p ell x side j)⌉₊ < ⌈max K ((ell*B^3)*F)⌉₊ := by
  obtain ⟨hrow,hmass⟩ := globalSecond_halving p hp K ell B F hK hell hB hF x side j hb₁ hb₂ hretained hlarge
  have hchild : 1 ≤ secondLogK j*Real.exp 1 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  apply ceil_strict_of_half
  · have h2 : 2 ≤ K := by linarith
    exact h2.trans (le_max_left _ _)
  · apply max_le
    · exact hrow.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num))
    · exact hmass.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by norm_num))

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0172

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ScaleCaps
Source SHA256: 0f162069ac5c2780f65b5ee78669fed62aa16d9e1a9a1ba675315faef1d9d945
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0173



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
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)

variable {ι : Type*} [DecidableEq ι]

def finiteBlockExponent (B : Finset ι) (v : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.onFinset B (fun i => if i∈B then v i else 0) (by
    intro i hi
    by_contra hn
    exact hi (ite_eq_right hn))

def cubeCoordinatesOfBlock (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : CubeCoordinates ι where
  leftExponent := finiteBlockExponent B v₁
  rightExponent := finiteBlockExponent B v₂
  leftDivisor := B.filter (fun i => ε₁ i)
  rightDivisor := B.filter (fun i => ε₂ i)

theorem cubeCoordinatesOfBlock_support (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈B,0 < v₁ i+v₂ i) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).support=B := by
  ext i
  simp only [CubeCoordinates.support,cubeCoordinatesOfBlock,Finset.mem_union,
    Finsupp.mem_support_iff,finiteBlockExponent,Finsupp.onFinset_apply]
  by_cases hi : i∈B
  · simp only [hi,ite_true,iff_true]
    have h := hv i hi
    omega
  · simp [hi]

theorem cubeCoordinatesOfBlock_leftBit (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (i : ι) (hi : i∈B) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftBit i=ε₁ i := by
  cases h : ε₁ i <;> simp [CubeCoordinates.leftBit,cubeCoordinatesOfBlock,hi,h]

theorem cubeCoordinatesOfBlock_rightBit (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (i : ι) (hi : i∈B) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightBit i=ε₂ i := by
  cases h : ε₂ i <;> simp [CubeCoordinates.rightBit,cubeCoordinatesOfBlock,hi,h]

theorem cubeCoordinatesOfBlock_admissible (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈B,0 < v₁ i+v₂ i) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).Admissible := by
  unfold CubeCoordinates.Admissible
  rw [cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv]
  exact ⟨Finset.filter_subset _ _,Finset.filter_subset _ _⟩

theorem cubeCoordinatesOfBlock_primeProduct (p : ι → O)
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i)
    (f : ℕ → ℕ → Bool → Bool → ℕ) :
    let x := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
    primeProduct p x.support (fun i => f (x.leftExponent i) (x.rightExponent i) (x.leftBit i) (x.rightBit i)) =
      primeProduct p B (fun i => f (v₁ i) (v₂ i) (ε₁ i) (ε₂ i)) := by
  dsimp only
  rw [cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv]
  unfold primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [cubeCoordinatesOfBlock_leftBit B v₁ v₂ ε₁ ε₂ i hi,
    cubeCoordinatesOfBlock_rightBit B v₁ v₂ ε₁ ε₂ i hi]
  simp only [cubeCoordinatesOfBlock,finiteBlockExponent,Finsupp.onFinset_apply,ite_eq_left hi]

def globalSecondOfBlock (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) : GlobalSecondData ι where
  cube := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  firstCommon := A₀
  common := C
  firstDivisor := D
  source := x

theorem globalSecondOfBlock_injective (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Function.Injective (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂) := by
  intro x y h
  exact congrArg GlobalSecondData.source h

theorem globalSecondOfBlock_admissible (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i)
    (hCB : Disjoint C B) (hD : D⊆C∪B) (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    GlobalSecondAdmissible (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) := by
  refine ⟨cubeCoordinatesOfBlock_admissible B v₁ v₂ ε₁ ε₂ hv,hE,?_,?_⟩
  · simpa only [globalSecondOfBlock,cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv] using hCB
  · simpa only [globalSecondOfBlock,cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv] using hD

variable (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_tuple (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondTuple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      actualSecondTuple p B C D x.divisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency := by
  have hpoly := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
  have hspan (f : ℕ → ℕ → Bool → Bool → ℕ) := congrArg (fun a : O => (Ideal.span {a} : Ideal O)) (hpoly f)
  let c := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  have hJ : jLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  have hS : squarefreeLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) =
      squarefreeLabel p B (fun i => v₁ i+v₂ i) := hpoly (fun a b _ _ => bit (parity (a+b)))
  have hP₁ : primeProduct p c.support c.leftExponent = primeProduct p B v₁ := hpoly (fun a _ _ _ => a)
  have hP₂ : primeProduct p c.support c.rightExponent = primeProduct p B v₂ := hpoly (fun _ b _ _ => b)
  have hA₁ : aLabel p c.support c.leftBit = aLabel p B ε₁ := hpoly (fun _ _ e₁ _ => bit e₁)
  have hA₂ : aLabel p c.support c.rightBit = aLabel p B ε₂ := hpoly (fun _ _ _ e₂ => bit e₂)
  have hJ₂ : j2Label p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (FirstPassCubeLabels.evenDouble (a+b) e₁ e₂))
  change actualSecondTuple p c.support C D x.divisor x.overlap c.leftExponent c.rightExponent c.leftBit c.rightBit x.frequency = _
  unfold actualSecondTuple
  rw [hJ,hS,hP₁,hA₁,hA₂,hJ₂,hP₂]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_triple (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondFixedTriple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
    (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂},
      ∏ i∈A₀,Ideal.span {p i},∏ i∈x.sourceCommon\x.divisor,Ideal.span {p i}) := by
  have h := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
    (fun a b e₁ e₂ => b0Exponent (a+b) e₁ e₂)
  apply Prod.ext
  · exact congrArg (fun a : O => (Ideal.span {a} : Ideal O)) h
  · rfl

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_label (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondLabel p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      secondSupportLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) := by
  have h := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
    (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  unfold globalSecondLabel globalSecondOfBlock secondSupportLabel
  dsimp only [expansionSupportData]
  rw [show jLabel p (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).support
      (fun i => (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftExponent i+
        (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightExponent i)
      (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftBit (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ from h]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

abbrev GlobalLogIndex := Fin 10 → ℕ

def globalLogRep (j : GlobalLogIndex) (i : Fin 10) : ℝ := normLogScale (j i)

theorem globalLogRep_pos (j : GlobalLogIndex) (i : Fin 10) : 0 < globalLogRep j i := normLogScale_pos _

theorem globalLogRep_ge_one (j : GlobalLogIndex) (i : Fin 10) : 1 ≤ globalLogRep j i := normLogScale_ge_one _

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalScaleVector (side : Bool) (x : GlobalSecondData ι) : Fin 10 → ℝ :=
  ![primeProductNorm p (x.cube.sideDivisor side),primeProductNorm p x.common,
    primeProductNorm p x.firstCommon,primeProductNorm p (x.source.sourceCommon\x.source.divisor),
    globalCubeJNorm p x,primeProductNorm p x.firstDivisor,primeProductNorm p x.source.divisor,
    primeProductNorm p x.source.overlap,‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2,
    (globalCubeActiveRoot p x)^2]

def globalScaleIndex (side : Bool) (x : GlobalSecondData ι) : GlobalLogIndex :=
  fun i => normLogBin (globalScaleVector p side x i)

include hp in
theorem globalScaleVector_ge_one (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    ∀ i,1 ≤ globalScaleVector p side x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  · exact primeProductNorm_ge_one p hp x.common
  · exact primeProductNorm_ge_one p hp x.firstCommon
  · exact primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  · change 1 ≤ globalCubeJNorm p x
    exact element_norm_ge_one _ (primeProduct_ne_zero p hp x.cube.support _)
  · exact primeProductNorm_ge_one p hp x.firstDivisor
  · exact primeProductNorm_ge_one p hp x.source.divisor
  · exact primeProductNorm_ge_one p hp x.source.overlap
  · change 1 ≤ ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2
    exact element_norm_ge_one _ (actualSecondRow_ne_zero p _ _ _ hk)
  · change 1 ≤ (globalCubeActiveRoot p x)^2
    exact element_norm_ge_one _ (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
theorem globalScaleIndex_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    globalLogRep (globalScaleIndex p side x) i ≤ globalScaleVector p side x i ∧
    globalScaleVector p side x i ≤ globalLogRep (globalScaleIndex p side x) i*Real.exp 1 :=
  normLogBin_scale_bounds _ (globalScaleVector_ge_one p hp side x hk i)

include hp in
theorem globalScaleIndex_error (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    0 ≤ Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ∧
    Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ≤ 1 :=
  normLogBin_error _ (globalScaleVector_ge_one p hp side x hk i)

def globalLogSector (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalScaleIndex p side x=j)

end

def globalLogBox (U : Fin 10 → ℝ) : Finset GlobalLogIndex :=
  Fintype.piFinset (fun i => Finset.range (normLogBin (U i)+1))

theorem globalLogBox_card (U : Fin 10 → ℝ) :
    (globalLogBox U).card=∏ i : Fin 10,(normLogBin (U i)+1) := by
  simp only [globalLogBox,Fintype.card_piFinset,Finset.card_range]

theorem globalScaleIndex_mem_box {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (U : Fin 10 → ℝ)
    (hU : ∀ i,globalScaleVector p side x i ≤ U i) :
    globalScaleIndex p side x∈globalLogBox U := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (normLogBin_mono (zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)) (hU i))

theorem sum_globalLogSector {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (U : Fin 10 → ℝ)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hU : ∀ x∈s,∀ i,globalScaleVector p side x i ≤ U i) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x=∑ j∈globalLogBox U,∑ x∈globalLogSector p s side j,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => globalScaleIndex_mem_box p hp side x (hk x hx) U (hU x hx)) f

def globalPooledColumnScale (ell : ℝ) (j : GlobalLogIndex) : ℝ :=
  ell/(globalLogRep j 0*globalLogRep j 1*globalLogRep j 2*globalLogRep j 3*globalLogRep j 6*globalLogRep j 7)

def globalPooledLabelScale (j : GlobalLogIndex) : ℝ :=
  globalLogRep j 1*globalLogRep j 4*globalLogRep j 6*globalLogRep j 7*Real.exp 4

def globalPooledRowScale (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)

def globalPooledDelta (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  B*F*globalLogRep j 0*globalLogRep j 2*globalLogRep j 3

def globalPooledNaturalRow (K B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2)

theorem globalPooledColumnScale_pos (ell : ℝ) (hell : 0 < ell) (j : GlobalLogIndex) :
    0 < globalPooledColumnScale ell j := by
  unfold globalPooledColumnScale
  apply div_pos hell
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (globalLogRep_pos j 0)
    (globalLogRep_pos j 1)) (globalLogRep_pos j 2)) (globalLogRep_pos j 3))
    (globalLogRep_pos j 6)) (globalLogRep_pos j 7)

theorem globalPooledLabelScale_ge_one (j : GlobalLogIndex) : 1 ≤ globalPooledLabelScale j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 1) (globalLogRep_ge_one j 4))
        (globalLogRep_ge_one j 6)) (globalLogRep_ge_one j 7)) (Real.one_le_exp (by norm_num))

theorem globalPooled_mass (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledColumnScale ell j*globalPooledLabelScale j =
      Real.exp 4*((ell*B^3)*F)*globalLogRep j 4/(globalPooledDelta B F j*B^2) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta
  field_simp [h]

theorem globalPooled_radial_ratio (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledRowScale K ell B F j*globalLogRep j 8/
      (globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2) =
    Real.exp 1*(globalLogRep j 8/globalPooledNaturalRow K B F j) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledRowScale globalPooledColumnScale globalPooledNaturalRow globalPooledDelta
  field_simp [h]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem maskedPairDualTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M N K : ℝ),
      G≠0 → I≠0 → J≠0 → 0<M → 1≤N → 0≤K →
      N/2≤(Ideal.absNorm I:ℝ) → (Ideal.absNorm I:ℝ)≤N →
      N/2≤(Ideal.absNorm J:ℝ) → (Ideal.absNorm J:ℝ)≤N →
      ‖maskedPairDualTail G I J W M K‖ ≤
        (2*M/N)*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := dualSquarefreeTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro G I J W M N K hG hI hJ hM hN hK hIl hIu hJl hJu
  have hNG : 0<(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hN0 : 0<N := by linarith
  let t0 := M/((Ideal.absNorm G:ℝ)*N*N)
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 t0)^2*(1+t0*K)^A)
  have ht0 : 0<t0 := by dsimp only [t0]; positivity
  have hT : 0≤T := by dsimp only [T]; positivity
  have hterm (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖ ≤ T := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hqN : (Ideal.absNorm q:ℝ)≤(Ideal.absNorm G:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by exact_mod_cast hNG) (map_dvd Ideal.absNorm hqG)
    have ht : 0<M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by positivity
    have htlo : t0≤M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      gcongr
    have hc : ‖(UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ)‖≤1 := by
      rw [norm_div,norm_mul,Complex.norm_natCast]
      have hp : ‖unrestrictedPairCharacter I J q‖≤1 := by
        rw [unrestrictedPairCharacter,norm_mul]
        exact (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      calc
        _ ≤ (1*1)/(Ideal.absNorm q:ℝ) := by
          gcongr
          exact QuadraticInitialBound.norm_ideal_moebius_le_one q
        _ ≤ 1 := by simpa only [one_mul,div_one] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1)
    have hb : ‖dualSquarefreeTail I J W
        (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖≤T := by
      apply (hbound I J W _ K ht hK).trans
      dsimp only [T]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    rw [norm_mul]
    exact (mul_le_mul hc hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpref : ‖(M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ)‖≤2*M/N := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM.le,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one,one_mul] using
      dual_truncation_prefactor_bound M 1 N (Ideal.absNorm I) (Ideal.absNorm J)
        hM (by norm_num) hN0 ⟨hIl,hIu⟩ ⟨hJl,hJu⟩
  rw [maskedPairDualTail,norm_mul]
  calc
    _ ≤ (2*M/N)*(∑ q ∈ idealDivisors G, T) := mul_le_mul hpref
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T,t0]; ring

theorem coprime_pair_error_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (E : ℝ) (hE : 0≤E)
    (error : n → n → ℂ) (herr : ∀ j k, ‖error j k‖≤E) :
    ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ ≤
      (Fintype.card n:ℝ)*E*∑ j, ‖a j‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖*‖a k‖*E) = (∑ j, ‖a j‖)^2*E := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ ≤ ∑ j, ∑ k, ‖if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, ‖a j‖*‖a k‖*E := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · simp only [norm_mul,norm_star]
        exact mul_le_mul_of_nonneg_left (herr j k) (by positivity)
      · simp only [norm_zero]
        positivity
    _ = (∑ j, ‖a j‖)^2*E := hs
    _ ≤ ((∑ j, ‖a j‖^2)*(Fintype.card n:ℝ))*E := mul_le_mul_of_nonneg_right hcs hE
    _ = _ := by ring

theorem maskedDualTailFamily_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ)
      (W : 𝓢(ℝ,ℂ)) (M N K : ℝ), G≠0 → Function.Injective cols →
      0<M → 1≤N → 0≤K →
      (∀ j, cols j≠0 ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
      ‖maskedDualTailFamily G cols a W M K‖ ≤
        256*M*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) * ∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := maskedPairDualTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro n _ G cols a W M N K hG hinj hM hN hK hcols
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)
  have hT : 0≤T := by dsimp only [T]; positivity
  have hn := finite_ideal_family_card_bound cols hinj N hN
    (fun j => (hcols j).1) (fun j => (hcols j).2.2)
  have herr (j k : n) : ‖maskedPairDualTail G (cols j) (cols k) W M K‖≤
      (2*M/N)*(idealDivisors G).card*T :=
    hbound G (cols j) (cols k) W M N K hG (hcols j).1 (hcols k).1 hM hN hK
      (hcols j).2.1 (hcols j).2.2 (hcols k).2.1 (hcols k).2.2
  calc
    _ ≤ (Fintype.card n:ℝ)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 :=
      coprime_pair_error_energy cols a _ (by positivity) _ herr
    _ ≤ (128*N)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 := by gcongr
    _ = _ := by dsimp only [T]; field_simp; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalActualResidualScale (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℝ :=
  globalFirstColumnScale p ell x side/
    (primeProductNorm p x.firstCommon*primeProductNorm p x.source.divisor*
      primeProductNorm p (x.source.sourceCommon\x.source.divisor))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalActualResidualScale_pos (ell : ℝ) (hell : 0 < ell) (side : Bool) (x : GlobalSecondData ι) :
    0 < globalActualResidualScale p ell side x := by
  exact div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (mul_pos (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
      (FirstPassCubeLabels.primeProductNorm_pos p hp _))

include hp in

theorem globalPooled_log_coordinates (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    let d := expansionSupportData x.common x.firstDivisor x.source
    |secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) d| ≤ 6 ∧
    |secondSectorUd p (globalLogRep j 5) d| ≤ 6 ∧
    |secondSectorUe p (globalLogRep j 6) d| ≤ 6 ∧
    |secondSectorUv p (globalLogRep j 7) d| ≤ 6 ∧
    |secondSectorKap p (globalLogRep j 8) d| ≤ 6 := by
  let j := globalScaleIndex p side x
  let I : Finset (Fin 10) := {0,1,2,3,6,7}
  have hpos (i : Fin 10) : 0 < globalScaleVector p side x i :=
    zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)
  have herr (i : Fin 10) := globalScaleIndex_error p hp side x hk i
  have hn (i : Fin 10) : globalScaleVector p side x i/globalLogRep j i ≠ 0 :=
    div_ne_zero (hpos i).ne' (globalLogRep_pos j i).ne'
  have hprod : primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x =
      ∏ i∈I,globalScaleVector p side x i/globalLogRep j i := by
    have h (i : Fin 10) := (globalLogRep_pos j i).ne'
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
    have he := (FirstPassCubeLabels.primeProductNorm_pos p hp x.source.divisor).ne'
    have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
    norm_num [I,globalScaleVector,globalPooledColumnScale,globalActualResidualScale,globalFirstColumnScale]
    field_simp [h]

  have hlog : 0 ≤ Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x) ∧
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
        globalActualResidualScale p ell side x) ≤ 6 := by
    rw [hprod,Real.log_prod (fun i hi => hn i)]
    constructor
    · exact Finset.sum_nonneg (fun i hi => (herr i).1)
    · calc
        _ ≤ ∑ i∈I,(1 : ℝ) := Finset.sum_le_sum (fun i hi => (herr i).2)
        _ = 6 := by norm_num [I]
  have hsmall (i : Fin 10) : |Real.log (globalScaleVector p side x i/globalLogRep j i)| ≤ 6 := by
    rw [abs_of_nonneg (herr i).1]
    exact (herr i).2.trans (by norm_num)
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · change |Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x)| ≤ 6
    rw [abs_of_nonneg hlog.1]
    exact hlog.2
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖^2 / globalLogRep j 5)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 5
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor)‖^2 / globalLogRep j 6)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 6
  · exact hsmall 7
  · exact hsmall 8

include hp in

theorem globalPooled_target_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) ≤ globalPooledLabelScale j ∧
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤ globalLogRep j 8*Real.exp 1 := by
  let j := globalScaleIndex p side x
  have hb (i : Fin 10) := (globalScaleIndex_bounds p hp side x hk i).2
  refine ⟨?_,hb 8⟩
  have he : (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) =
      globalScaleVector p side x 1*globalScaleVector p side x 4*
        globalScaleVector p side x 6*globalScaleVector p side x 7 := by
    rw [show SecondPassFiber.newLabel (globalSecondTuple p x) =
      secondSupportNewLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
        (expansionSupportData x.common x.firstDivisor x.source) from rfl,
      secondSupportNewLabel_norm,globalBaseLabel_norm]
    rfl
  rw [he]
  calc
    _ ≤ (globalLogRep j 1*Real.exp 1)*(globalLogRep j 4*Real.exp 1)*
        (globalLogRep j 6*Real.exp 1)*(globalLogRep j 7*Real.exp 1) := by
      have hpos (i : Fin 10) := (globalScaleVector_ge_one p hp side x hk i).trans' (by norm_num : (0:ℝ) ≤ 1)
      have hr1 := (globalLogRep_pos j 1).le
      have hr4 := (globalLogRep_pos j 4).le
      have hr6 := (globalLogRep_pos j 6).le
      have hr7 := (globalLogRep_pos j 7).le
      gcongr <;> first | exact hpos _ | exact hb _
    _ = globalPooledLabelScale j := by
      unfold globalPooledLabelScale
      rw [show (4:ℝ)=1+1+1+1 by norm_num,Real.exp_add,Real.exp_add,Real.exp_add]
      ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

private theorem five_factor_bounds (a b c d e : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) :
    a ≤ a*b*c*d*e ∧ b ≤ a*b*c*d*e ∧ c ≤ a*b*c*d*e ∧ d ≤ a*b*c*d*e ∧ e ≤ a*b*c*d*e := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      a = a*1*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      b = 1*b*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      c = 1*1*c*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      d = 1*1*1*d*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      e = 1*1*1*1*e := by ring
      _ ≤ _ := by gcongr

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSupported_small_norms (ell M : ℝ) (_hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    primeProductNorm p (x.cube.sideDivisor side) ≤ ell*Real.exp M ∧
    primeProductNorm p x.common ≤ ell*Real.exp M ∧
    primeProductNorm p x.firstCommon ≤ ell*Real.exp M ∧
    primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.divisor ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hg := primeProductNorm_ge_one p hp x.source.sourceCommon
  have hv := primeProductNorm_ge_one p hp x.source.overlap
  have hden : 0 < primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon := by positivity
  have heq : (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)*Real.exp M =
      (ell*Real.exp M)/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon) := by
    unfold globalFirstColumnScale
    ring
  have hprod := (le_div_iff₀ hden).mp (hs.2.trans_eq heq)
  have hprod' : primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*
      primeProductNorm p x.firstCommon*primeProductNorm p x.source.sourceCommon*primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
    convert hprod using 1 ; ring
  obtain ⟨ha',hc',ht',hg',hv'⟩ := five_factor_bounds _ _ _ _ _ ha hc ht hg hv
  refine ⟨ha'.trans hprod',hc'.trans hprod',ht'.trans hprod',?_,?_,hv'.trans hprod'⟩
  · exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans (hg'.trans hprod')
  · exact (primeProductNorm_mono p hp hx.2.1).trans (hg'.trans hprod')

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCube_radical_bound (B : ℝ) (hB : 0 ≤ B) (x : GlobalSecondData ι)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.cube.support ≤ B^2 := by
  have hd : (∏ i∈x.cube.support,p i) ∣ primeProduct p x.cube.support x.cube.leftExponent *
      primeProduct p x.cube.support x.cube.rightExponent := by
    rw [← primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (x.cube.support_pos i hi)
  have hb0 := mul_ne_zero (primeProduct_ne_zero p hp x.cube.support x.cube.leftExponent)
    (primeProduct_ne_zero p hp x.cube.support x.cube.rightExponent)
  have hn := element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSupported_divisor_bound (ell B M : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.firstDivisor ≤ (ell*Real.exp M)*B^2 := by
  have hC := (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  calc
    _ ≤ primeProductNorm p (x.common∪x.cube.support) := primeProductNorm_mono p hp hx.2.2.2
    _ = primeProductNorm p x.common*primeProductNorm p x.cube.support :=
      FirstPassCubeLabels.primeProductNorm_union p _ _ hx.2.2.1
    _ ≤ _ := mul_le_mul hC hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)

include hp in

theorem globalSupported_cutoff_row_bound (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤
      3*(ell*Real.exp M)^2*B^2*((⌈Z*(ell*Real.exp M)^2/Y⌉₊ : ℝ)+1)^2 := by
  let X := globalFirstColumnScale p ell x side
  let U := (X/primeProductNorm p x.firstCommon)*Real.exp M
  let lengthScale := ell*Real.exp M
  have hsmall := globalSupported_small_norms p hp ell M hell side x hx hs
  have hD := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hX : X ≤ ell := by
    exact div_le_self hell.le (one_le_mul_of_one_le_of_one_le ha hc)
  have hU : U ≤ lengthScale := mul_le_mul_of_nonneg_right
    ((div_le_self (globalFirstColumnScale_pos p hp ell hell x side).le ht).trans hX) (Real.exp_pos M).le
  have hU0 : 0 ≤ U := by
    exact (mul_pos (div_pos (globalFirstColumnScale_pos p hp ell hell x side)
      (FirstPassCubeLabels.primeProductNorm_pos p hp _)) (Real.exp_pos M)).le
  have hden : primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2 ≤ lengthScale^2 := by
    rw [show ((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.source.sourceCommon by dsimp [U];ring]
    exact (supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hx.2.1)
      (primeProductNorm_ge_one p hp _)).trans (pow_le_pow_left₀ hU0 hU 2)
  have hr : Z/(Y/(primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2)) ≤ Z*lengthScale^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z/(Y/(primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*lengthScale^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hr
  have hf := secondFrequencyCutoff_norm_sq_le _ Z x.source.frequency hk
  simp only [primeSubsetGenerator_norm_eq_productNorm] at hf
  have hf' : ‖eisEmbedding x.source.frequency‖^2 ≤ 3*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hf.trans
    gcongr
  change ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2 ≤ _
  simp only [actualSecondRow,map_mul,norm_mul,mul_pow,primeSubsetGenerator_norm_eq_productNorm]
  calc
    _ ≤ (lengthScale*B^2)*lengthScale*(3*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul hD hsmall.2.2.2.2.1 (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity))
        hf' (sq_nonneg _) (by dsimp [lengthScale]; positivity)
    _ = _ := by dsimp [lengthScale];ring_nf

def globalNormCaps (ell B Y M Z : ℝ) : Fin 10 → ℝ :=
  let lengthScale := ell*Real.exp M
  ![lengthScale,lengthScale,lengthScale,lengthScale,B^2,lengthScale*B^2,lengthScale,lengthScale,3*lengthScale^2*B^2*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2,B^2]

include hp in
theorem globalScaleVector_le_caps (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ∀ i,globalScaleVector p side x i ≤ globalNormCaps ell B Y M Z i := by
  obtain ⟨ha,hc,ht,hr,he,hv⟩ := globalSupported_small_norms p hp ell M hell side x hx hs
  have hd := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have hrow := globalSupported_cutoff_row_bound p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB hb₁ hb₂).1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  have hactive : (globalCubeActiveRoot p x)^2 ≤ B^2 :=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hrad
  intro i
  fin_cases i
  · exact ha
  · exact hc
  · exact ht
  · exact hr
  · exact hJ
  · exact hd
  · exact he
  · exact hv
  · exact hrow
  · exact hactive

include hp in

theorem globalScaleIndex_mem_concrete_box (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B Y M Z) :=
  globalScaleIndex_mem_box p hp side x hk0 _
    (globalScaleVector_le_caps p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk)

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0173

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison
Source SHA256: b5996fd877bfc1cf91a35f87aa6e89d2ba575680b81871cef4ee8e60d7f7b176
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0174


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

namespace CanonicalQuadraticSieve

section

theorem hasSieveExponent_one_of_approximation
    (happrox : ∀ η : ℝ, 0<η → ∃ α : ℝ, α≤1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0<ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hNmn : N≤M*N := by nlinarith
  have hQ : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N^α ≤ (M*N)^(ε/2)*N := by
    calc
      _ ≤ N^(1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N^(ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N)^(ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N^α ≤ (M*N)^(ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^α) := hbound M N hM hN
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N)) := by gcongr
    _ = C*(M*N)^ε*(M+N^(1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity : 0<M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]

def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)

theorem bootstrapExponent_gt_one (n : ℕ) : 1<bootstrapExponent n := by
  unfold bootstrapExponent
  have h : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  linarith

theorem bootstrapExponent_le_two (n : ℕ) : bootstrapExponent n≤2 := by
  have h : 1/((n:ℝ)+1)≤(1:ℝ) := by
    apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold bootstrapExponent
  linarith

theorem bootstrapExponent_step (n : ℕ) :
    bootstrapExponent (n+1) = 2-1/bootstrapExponent n := by
  unfold bootstrapExponent
  push_cast
  field_simp
  ring

theorem hasSieveExponent_one_of_improvement
    (himprove : ∀ α : ℝ, 1<α → α≤2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def divisorTwist {n : Type} (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*quadraticRow (cols j) (idealGenerator q)

def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (6:ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealRange K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))

def centeredMaskedSource {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum G (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeRange G K => I.val) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M

def maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily G cols a W M - (6:ℂ)⁻¹ *
    maskedPrincipalSourceSum G (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeRange G K => I.val) cols a M

lemma finite_centering_identity {ι : Type*} (S : Finset ι) (w R D : ι → ℂ) (c h : ℂ) :
    (∑ q∈S, w q*(c*R q-h*D q)) = c*(∑ q∈S,w q*R q)-h*(∑ q∈S,w q*D q) := by
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem maskedPoissonDifference_centered {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (6:ℂ)*maskedPoissonDifference G W cols a M K =
      (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
      (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K +
      paperRadialFourier (quadraticSquareProfile W) 0 *
        ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K) := by
  rw [←actual_source_dual_density_cancellation cols a G hG M K hM.le hcols hray hGc hbad]
  unfold maskedPoissonDifference centeredRetainedDual centeredMaskedSource divisorTwist
  rw [maskedDualFamily_retained G hG cols a W M K hM hcols hray]
  simp only [quadraticSquareProfile_principal_equal]
  rw [finite_centering_identity]
  ring

theorem maskedPoissonDifference_norm_le {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
      (∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) +
      6*‖maskedDualTailFamily G cols a W M K‖ + ‖centeredMaskedSource G W cols a M K‖ +
      ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
        ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ := by
  rw [maskedPoissonDifference_centered G hG W cols a M K hM hcols hray hGc hbad]
  have hs : ‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ ≤
      ∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one q)
  calc
    _ ≤ (‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ +
        ‖(6:ℂ)*maskedDualTailFamily G cols a W M K‖) + ‖centeredMaskedSource G W cols a M K‖ +
        ‖paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K)‖ := by
      have h1 := norm_add_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K)
        (paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K))
      have h2 := norm_sub_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K) (centeredMaskedSource G W cols a M K)
      have h3 := norm_add_le
        (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q)
        ((6:ℂ)*maskedDualTailFamily G cols a W M K)
      linarith
    _ ≤ _ := by
      simp only [norm_mul]
      norm_num
      gcongr

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem divisorTwist_norm_le {n : Type} (cols : n → Ideal O) (a : n → ℂ)
    (q : Ideal O) (j : n) : ‖divisorTwist cols a q j‖≤‖a j‖ := by
  rw [divisorTwist,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem retainedDualMajorant_coefficient_scale_le {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a a' : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0<N) (hM : 0≤M) (hF : 1≤F) (hT : 0≤T)
    (ha : ∀j, ‖a' j‖≤‖a j‖) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a' W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M 1 T a W := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' a a' ha ha
  have he0 := divisorEnergyFactor_nonneg ε hε N a' a'
  have he1 := divisorEnergyFactor_nonneg ε hε N a a
  have hea : (∑j, ‖a' j‖^2)≤∑j, ‖a j‖^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
  have hs := (supportConstant_pos ε hε).le
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have hF0 : 0<F := by linarith
  have hMF : M/F≤M := div_le_self hM hF
  have hNF : N≤F*N := by nlinarith
  have hMN : 2*M/(F*N)≤2*M/N :=
    div_le_div_of_nonneg_left (by positivity) hN hNF
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  simp only [div_one,one_mul]
  gcongr

theorem centeredRetainedDual_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_global l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT cols hc hcols hray a W
  classical
  have hqbound (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖centeredRetainedDual W cols a M K q‖ ≤
        (columnDyadicLength K+1:ℕ)*
          retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
    have hqd := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqd; exact hG hqd
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hh := hbound hexp hα deltaLoss hδ ε hε K N M (Ideal.absNorm q:ℝ) T hK hN hM
      (by linarith) hT cols hc hcols hray (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact retainedDualMajorant_coefficient_scale_le s C hC.le l hexp deltaLoss hδ ε hε
      (2*K) N M (Ideal.absNorm q:ℝ) T a (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
      (by linarith) (by linarith) hM.le hq1 (by linarith) (divisorTwist_norm_le cols a q)
  calc
    _ ≤ ∑_q∈idealDivisors G, (columnDyadicLength K+1:ℕ)*
        retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) :=
      Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  6*(256*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)

theorem HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by
  obtain ⟨sD,CD,hCD,hdual⟩ := centeredRetainedDual_sum_bound l
  obtain ⟨sS,CS,hCS,hsource⟩ := masked_source_principal_global l
  obtain ⟨sT,CT,hCT,htail⟩ := maskedDualTailFamily_bound A
  obtain ⟨CP,hCP,hprincipal⟩ := hexp.actual_principal_difference deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro n _ _ ε hε G hG hbad K N M T hK hN hM hT cols hc hcols hray hGc a W hW
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hcols0 : ∀j, Admissible (cols j) := fun j => (hcols j).1
  have hcolsu : ∀j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N :=
    fun j => ⟨(hcols j).1,(hcols j).2.2⟩
  have hd := hdual hexp hα deltaLoss hδ ε hε G hG.ne_zero K N M T hK hN hM0 hT cols hc hcols hray a W
  have hs := hsource hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM0 hT
    (coprimeSquarefreeRange G K)
    (fun I hI => mem_idealRange.mp (coprimeSquarefreeRange_subset_idealRange G hbad K hI))
    cols hc hcolsu hGc a (quadraticSquareProfile W)
    (by simpa only [quadraticSquareProfile_apply,zero_pow (by decide : 2≠0)] using hW)
  have ht := htail G cols a W M N K hG.ne_zero hc hM0 hN (by linarith)
    (fun j => ⟨(hcols j).1.1,(hcols j).2⟩)
  have hp := hprincipal cols hc M N K hM hN hK hcolsu hray
    (densityColumn cols a) G hG hbad ε hε
  have he := densityColumn_energy_le cols a (fun j => (hcols j).1.1)
  have hsupp := (supportConstant_pos ε hε).le
  have hp' : ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ ≤
      ((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2 := by
    apply hp.trans
    gcongr
  have hmain := maskedPoissonDifference_norm_le G hG.ne_zero W cols a M K hM0 hcols0 hray hGc hbad
  apply hmain.trans
  change _ ≤ _+_+_+_
  have hs' : ‖centeredMaskedSource G W cols a M K‖ ≤
      (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a
        (quadraticSquareProfile W) := hs
  exact add_le_add (add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left ht (by norm_num))) hs')
    (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))

end
section

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open DivisorBlockCauchy

theorem gcdRaySupport_energy_eq {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, if D∣cols j ∧ columnRay (cols j)=c then ‖a j‖^2 else 0 := by
  classical
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  simp only [gcdRaySupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,ne_eq,not_true_eq_false,and_false,ite_self,zero_pow (by decide : 2≠0)]
  · simp only [hz,ne_eq,not_false_eq_true,and_true]

theorem gcdRaySupport_energy_ray_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, ‖if D∣cols j then a j else 0‖^2 := by
  classical
  simp_rw [gcdRaySupport_energy_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : D∣cols j
  · simp only [hd,true_and,ite_true]
    rw [Finset.sum_eq_single (columnRay (cols j))]
    · simp only [ite_true]
    · intro c hc hne
      exact ite_eq_right (Ne.symm hne)
    · simp
  · simp only [hd,false_and,ite_false,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem gcdRaySupport_energy_divisor_sum {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X : ℝ)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
      ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤
      (divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [gcdRaySupport_energy_ray_sum]
  apply (divisor_mask_energy S cols hcols a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 (cols j) (hcols j)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hX j hz) hε.le) (divisorConstant_pos ε hε).le

theorem gcdRaySupport_weighted_sum_bound {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X C : ℝ) (hC : 0≤C)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X)
    (F : Ideal O → EisensteinEPrimaryPhase.Coord → ℝ)
    (hF : ∀D∈S, ∀c, F D c≤C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S, F D c) ≤
      C*(divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  calc
    _ ≤ ∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2 :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun D hD => hF D hD c))
    _ = C*(∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) := by simp only [Finset.mul_sum]
    _ ≤ C*((divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left (gcdRaySupport_energy_divisor_sum ε hε S cols hcols a X hX) hC
    _ = _ := by ring

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem divisorEnergyFactor_diagonal {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (N : ℝ) (a : n → ℂ) :
    divisorEnergyFactor ε hε N a a =
      (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑j, ‖a j‖^2 := by
  unfold divisorEnergyFactor
  have hs : 0≤∑j, ‖a j‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _),Real.mul_self_sqrt hs]

theorem poissonComparisonMajorant_energy_factor {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W =
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
        (fun _ : Unit => (1:ℂ)) W * ∑j, ‖a j‖^2 := by
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,mul_one]
  ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondOuterWeight (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    (secondNormalizedExpansionWeight p hp hcop hg Ψ (m*b0) c d z X Y x.source *
      (secondExpansionScale p X r (expansionSupportData x.common x.firstDivisor x.source) : ℂ)⁻¹)

theorem globalSecondOuterWeight_squarefree
    (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex) (ell Y : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (h : globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x ≠ 0) :
    Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x)) := by
  apply actualSecondLabel_squarefree_of_weight p hp hcop hg x.cube.support x.common
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit hx.2.2.1 Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor) z x.source hx.2.1
  intro hw
  unfold secondArithmeticWeight at hw
  rcases mul_eq_zero.mp hw with hA|hB
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hA,mul_zero,zero_mul]
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hB,mul_zero,zero_mul]

theorem globalSecondOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      (Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
        (globalFirstColumnScale p ell x side)^2)*‖secondRayCoefficient z‖ := by
  have ht := FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon
  have hX := globalFirstColumnScale_pos p hp ell hell x side
  have hh := secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc x.common x.firstDivisor
    Ψ (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
    z (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y (div_pos hX ht) hY x.source (hΨ _) (hΨ _)
  rw [primeSubsetGenerator_norm_eq_productNorm] at hh
  unfold globalSecondOuterWeight
  dsimp only
  rw [norm_mul,norm_inv,Complex.norm_of_nonneg ht.le]
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq
  field_simp

def globalPooledOuterBound (z : SecondRayIndex) (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  (Y*(Real.exp 1)^6*globalLogRep j 2*globalLogRep j 3*(globalLogRep j 0)^2*(globalLogRep j 1)^2/ell^2)*
    ‖secondRayCoefficient z‖

theorem globalSecondOuterWeight_bin_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      globalPooledOuterBound z ell Y (globalScaleIndex p side x) := by
  apply (globalSecondOuterWeight_norm_le p hp hcop hg hinj hc Ψ hΨ m z ell Y hell hY side x).trans
  let j := globalScaleIndex p side x
  have ha := (globalScaleIndex_bounds p hp side x hk 0).2
  have hc' := (globalScaleIndex_bounds p hp side x hk 1).2
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p (x.cube.sideDivisor side) ≤ globalLogRep j 0*Real.exp 1 at ha
  change primeProductNorm p x.common ≤ globalLogRep j 1*Real.exp 1 at hc'
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have hn : Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
      (globalFirstColumnScale p ell x side)^2 =
      Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*
        (primeProductNorm p (x.cube.sideDivisor side))^2*(primeProductNorm p x.common)^2/ell^2 := by
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    unfold globalFirstColumnScale
    field_simp

  rw [hn]
  have h0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).le
  have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).le
  have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have h3 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hr0 := (globalLogRep_pos j 0).le
  have hr1 := (globalLogRep_pos j 1).le
  have hr2 := (globalLogRep_pos j 2).le
  have hr3 := (globalLogRep_pos j 3).le
  calc
    _ ≤ (Y*(globalLogRep j 2*Real.exp 1)*(globalLogRep j 3*Real.exp 1)*
      (globalLogRep j 0*Real.exp 1)^2*(globalLogRep j 1*Real.exp 1)^2/ell^2)*‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by unfold globalPooledOuterBound;ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0174

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins
Source SHA256: bf074f36dd6e567704233e03f0cd611879cae6cb4e32fbeebb4427a22d05a99e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0175


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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalArithmeticBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j)

def globalSquarefreeBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  (globalArithmeticBin p s side q j).filter (fun x => Squarefree (newLabel (globalSecondTuple p x)))

def globalArithmeticTargets (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (Ideal O × O) :=
  (globalSquarefreeBin p s side q j).image (fun x => (newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalArithmeticTargets_squarefree (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) :
    ∀ z∈globalArithmeticTargets p s side q j,Squarefree z.1 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact (Finset.mem_filter.mp hx).2

include hp in
theorem globalArithmeticTargets_bounds (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0) :
    ∀ z∈globalArithmeticTargets p s side q j,z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ globalPooledLabelScale j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ globalLogRep j 8*Real.exp 1 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hx',hsf⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxs,hq,hj⟩ := Finset.mem_filter.mp hx'
  have hb := globalPooled_target_bounds p hp side x (hk x hxs)
  rw [hj] at hb
  refine ⟨?_,hb⟩
  exact secondSupportNewLabel_ne_bot p hp x.cube.support x.common x.firstDivisor
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.source

def globalBinZ (ell : ℝ) (side : Bool) (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j)
    (expansionSupportData x.common x.firstDivisor x.source)

def globalBinUd (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUd p (globalLogRep j 5) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinUe (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUe p (globalLogRep j 6) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinUv (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUv p (globalLogRep j 7) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinKap (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorKap p (globalLogRep j 8) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinRadial (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  Y*globalLogRep j 8/(globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2)

theorem globalBinRadial_pos (ell Y : ℝ) (hell : 0 < ell) (hY : 0 < Y) (j : GlobalLogIndex) :
    0 < globalBinRadial ell Y j := by
  have h5 := globalLogRep_pos j 5
  have h6 := globalLogRep_pos j 6
  have h7 := globalLogRep_pos j 7
  have h8 := globalLogRep_pos j 8
  have hX := globalPooledColumnScale_pos ell hell j
  unfold globalBinRadial
  positivity

def globalArithmeticBinSource (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) : ℂ :=
  globalSecondRawSource p hp hcop hg (globalArithmeticBin p s side q j)
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side)
    F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j)

theorem globalArithmeticBinSource_squarefree (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hs : ∀ x∈s,GlobalSecondAdmissible x)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) :
    globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray A₁ A₂ W V ell Y =
    globalSecondRawSource p hp hcop hg (globalSquarefreeBin p s side q j)
      (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side)
      F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
      (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
      (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  unfold globalArithmeticBinSource globalSecondRawSource globalSquarefreeBin
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hsf : Squarefree (newLabel (globalSecondTuple p x))
  · rw [ite_eq_left hsf]
  · rw [ite_eq_right hsf]
    have hz : globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x=0 := by
      by_contra hn
      exact hsf (globalSecondOuterWeight_squarefree p hp hcop hg Ψ m ray ell Y side x
        (hs x (Finset.mem_filter.mp hx).1) hn)
    rw [hz,zero_mul]

theorem globalArithmeticBin_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray A₁ A₂ W V ell Y‖ ≤
      C*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := globalSecondRawSource_uniform_transfer p hp hcop hg hinj ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro s side q j F Ψ m ray ell Y hell hY hq hΨ hs hk
  rw [globalArithmeticBinSource_squarefree p hp hcop hg s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
