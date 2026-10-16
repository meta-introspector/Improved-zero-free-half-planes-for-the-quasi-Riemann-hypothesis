    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add coeff.function_continuous

lemma fullFunction_fourier (constant : ℂ) (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.fullFunction constant (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then constant*(v:ℂ)^(2/3:ℂ) else coeff.amplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => (constant*(v:ℂ)^(2/3:ℂ))*ShortDraftTrace.breveE (-cuspFrequency k*z))
    (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((coeff.series_height_continuous v hv).mul hphase)
  simp_rw [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,coeff.series_fourier v hv k]
  by_cases hk : k=0
  · simp only [ite_eq_left hk,amplitude,mul_zero]
    ring
  · simp only [ite_eq_right hk,mul_zero,zero_add]

lemma fullFunction_period (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.fullFunction constant (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      coeff.fullFunction constant (upperPoint z v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    coeff.series_period]

lemma fullFunction_height_continuous (constant : ℂ) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.fullFunction constant (upperPoint z v hv)) := by
  have hc := coeff.series_height_continuous v hv
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma fullFunction_height_memLp (constant : ℂ) (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => coeff.fullFunction constant (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := coeff.fullFunction_height_continuous constant v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖coeff.fullFunction constant (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

end SubexponentialBesselCoefficients
end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D∣r-r0) (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) : D∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    D∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert dvd_neg.mpr hh using 1 ; ring

theorem fixed_additive_sector {K : Type*} [Field K]
    (ι : R→+*K) (ψ : AddChar K ℂ) (lam D r r0 u u0 d d0 x : R)
    (hlam : ι lam≠0) (hD : ι D≠0)
    (hperiod : ∀y : R,ψ (ι y/ι lam)=1)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    ψ (ι (-d*u)*ι x/(ι lam*ι D))=
      ψ (ι (-d0*u0)*ι x/(ι lam*ι D)) :=
  addChar_congr_of_dvd ι ψ lam D (-d*u) (-d0*u0) x hlam hD hperiod
    (inverse_weight_residue_congr D r r0 u u0 d d0 hcop hr hu hu0 hd)

theorem strong_sector_additive_congruences (M lam c r r0 d d0 : R)
    (hlam : lam^3∣M) (hc : c∣M) (hr : M^2∣r-r0) (hd : M*c∣d-d0) :
    lam^3*c∣r-r0 ∧ lam^3*c∣d-d0 := by
  constructor
  · apply (show lam^3*c∣M^2 by simpa only [pow_two] using mul_dvd_mul hlam hc).trans hr
  · exact (mul_dvd_mul hlam (dvd_refl c)).trans hd

end ShortDraftCRT

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedHeightCompact (M:levelTwo) (a b:ℝ) : Set KernelQuotient :=
  kernelSourceAction M '' cuspHeightQuotientCompact a b

lemma translatedHeightCompact_isCompact (M:levelTwo) (a b:ℝ) (ha:0<a) :
    IsCompact (translatedHeightCompact M a b) :=
  (cuspHeightQuotientCompact_isCompact a b ha).image (kernelSourceAction_continuous M)

def translatedHeightFourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) : KernelQuotientL2→L[ℂ]ℂ :=
  (kernelCuspHeightFourier a b ha ρ h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedHeightFourier_integral (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M F=
      ∫w in cuspPeriodStrip a b,F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,kernelCuspHeightFourier_integral]
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp (kernelSourcePullback_ae_eq M F)
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w) hw

lemma translatedHeightFourier_restrict (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M
      (kernelMassRestrictionCLM (translatedHeightCompact M a b)
        (translatedHeightCompact_isCompact M a b ha).measurableSet F)=translatedHeightFourier a b ha ρ h M F := by
  rw [translatedHeightFourier_integral,translatedHeightFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha).measurableSet F)
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem hm _))

def translatedHeightFamily (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) : ℂ :=
  translatedHeightFourier a b ha ρ h M
    (kernelLocalCorrectedSeed (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma translatedHeightFamily_analyticAt (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0) :
    AnalyticAt ℂ (translatedHeightFamily a b ha ρ h M) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedHeightFourier a b ha ρ h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedHeightCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma translatedHeightFamily_residue_limit (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) :
    Tendsto (fun s:ℂ=>(s-4/3)*translatedHeightFamily a b ha ρ h M s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (translatedHeightFourier a b ha ρ h M cubicEisensteinResidue)) := by
  have hh:=(translatedHeightFourier a b ha ρ h M).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (translatedHeightCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedHeightFourier_restrict,
    translatedHeightFamily] using hh

lemma translatedHeightFamily_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    translatedHeightFamily a b ha ρ h M s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  have hcorrected:kernelCorrectedSeed 2 3 (by norm_num) (by norm_num) s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi] with q hq
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hq]
    ring
  have hlocal:=kernelLocalCorrectedSeed_ae_eq _ (translatedHeightCompact_isCompact M a b ha)
    2 3 (by norm_num) (by norm_num) s
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hlocal
  have hE:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hp:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  have hpE:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hE
  rw [translatedHeightFamily,translatedHeightFourier_integral]
  apply integral_congr_ae
  filter_upwards [hp,hpE,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwe hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  dsimp only [Function.comp_def] at hw hwe
  rw [hw,Set.indicator_of_mem hm,hwe,kernelSourceAction_mk,kernelQuotientEisenstein_mk]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0278

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
Source SHA256: 8e22a1da1ba6e6d7ef545bfca144513d8904d00ffbbb83bcab81232707dbf7c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0279


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

def cubicBesselDensityDeriv (x t : ℝ) : ℝ := -(x/(2*t))*cubicBesselDensity x t

lemma cubicBesselDensity_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => cubicBesselDensity y t) (cubicBesselDensityDeriv x t) x := by
  have he := ((((hasDerivAt_id x).pow 2).div_const (4*t)).const_sub (-t)).exp.const_mul (t^(-(2:ℝ)/3))
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one] at he
  convert he using 1
  · funext y
    rfl
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    ring

lemma cubic_exp_damping (y : ℝ) : y*Real.exp (-y)≤1 := by
  have hy : y≤Real.exp y := by linarith [Real.add_one_le_exp y]
  calc
    _ ≤ Real.exp y*Real.exp (-y) := mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]

lemma cubicBesselDensityDeriv_bound (delta x t : ℝ)
    (hdelta : 0<delta) (hx : delta≤x) (ht : 0<t) :
    ‖cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hdamp : (x/(2*t))*Real.exp (-(x^2/(8*t)))≤4/x := by
    have hrewrite : x/(2*t)=(4/x)*(x^2/(8*t)) := by field_simp;ring
    rw [hrewrite,mul_assoc]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (cubic_exp_damping (x^2/(8*t))) (by positivity : 0≤4/x)
  have hyoung : x/2-t/2≤x^2/(8*t) :=
    (le_div_iff₀ (show 0<8*t by positivity)).mpr (by nlinarith [sq_nonneg (x-2*t)])
  have he : Real.exp (-t-x^2/(4*t))≤
      Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t))) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsplit : x^2/(4*t)=2*(x^2/(8*t)) := by ring
    rw [hsplit]
    linarith
  have hnorm : ‖cubicBesselDensityDeriv x t‖=
      (x/(2*t))*t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t)) := by
    unfold cubicBesselDensityDeriv cubicBesselDensity
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    ring
  rw [hnorm]
  calc
    _ ≤ (x/(2*t))*t^(-(2:ℝ)/3)*
        (Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((x/(2*t))*Real.exp (-(x^2/(8*t))))*
        Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by ring
    _ ≤ (4/x)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
      gcongr
    _ ≤ _ := by
      gcongr

lemma cubicBesselDerivativeMajorant_integrable :
    IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) volume := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=-(2:ℝ)/3) (p:=1) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  apply hh.congr
  filter_upwards with t
  rw [Real.rpow_one]
  congr 1
  congr 1
  ring

lemma cubicBesselDensityDeriv_integrable (x : ℝ) (hx : 0<x) :
    IntegrableOn (cubicBesselDensityDeriv x) (Set.Ioi 0) volume := by
  apply (cubicBesselDerivativeMajorant_integrable.const_mul ((4/x)*Real.exp (-x/2))).mono'
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensityDeriv_bound x x t hx le_rfl ht

lemma cubicBesselIntegral_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => ∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  have hU : Set.Ioi delta∈𝓝 x := isOpen_Ioi.mem_nhds (by
    change delta<x
    dsimp [delta]
    linarith)
  have hbound : ∀ᵐt ∂volume.restrict (Set.Ioi (0:ℝ)),∀y∈Set.Ioi delta,
      ‖cubicBesselDensityDeriv y t‖≤(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0<t := ht
    intro y hy
    have hyp : 0<y := hdelta.trans hy
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (F := cubicBesselDensity) (F' := cubicBesselDensityDeriv)
    (bound := fun t => (4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2))) hU
    (Eventually.of_forall (fun y => by unfold cubicBesselDensity;fun_prop))
    (cubicBesselDensity_integrable x)
    (by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
    hbound (cubicBesselDerivativeMajorant_integrable.const_mul (4/delta))
    (Eventually.of_forall (fun t y _ => cubicBesselDensity_hasDerivAt y t))
  exact h.2

def cubicBesselRealDeriv (x : ℝ) : ℝ :=
  (-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)+
    (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)

def schlafliBesselK_cubic_derivative (x : ℝ) : ℂ := (cubicBesselRealDeriv x:ℂ)

lemma schlafliBesselK_cubic_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => schlafliBesselK (1/3) y)
      (schlafliBesselK_cubic_derivative x) x := by
  have hp : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3))
      ((-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)) x := by
    have hh := (((hasDerivAt_id x).div_const 2).rpow_const
      (p:=-(1:ℝ)/3) (Or.inl (by positivity : x/2≠0))).const_mul (1/2:ℝ)
    convert hh using 1 <;> norm_num ; ring
  have hr := hp.mul (cubicBesselIntegral_hasDerivAt x hx)
  have hreal : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3)*
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)) (cubicBesselRealDeriv x) x := by
    exact hr
  apply hreal.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_cubic_real y hy

lemma cubicBesselDerivativeMajorant_integral :
    (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  convert hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf

lemma cubicBesselIntegral_norm_bound (x : ℝ) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hpos : 0≤∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensity_nonneg x t ht.le
  rw [Real.norm_of_nonneg hpos]
  exact cubicBesselIntegral_upper x

lemma cubicBesselIntegralDeriv_norm_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi := cubicBesselDensityDeriv_integrable x (hdelta.trans_le hx)
  have hb := integral_mono_ae hi.norm
    (cubicBesselDerivativeMajorant_integrable.const_mul ((4/delta)*Real.exp (-x/2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensityDeriv_bound delta x t hdelta hx ht)
  rw [integral_const_mul,cubicBesselDerivativeMajorant_integral] at hb
  exact (norm_integral_le_integral_norm _).trans hb

def cubicBesselDerivativeUpper (delta : ℝ) : ℝ :=
  ((1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)+
    (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*(4/delta))*
      ((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselDerivativeUpper_nonneg (delta : ℝ) (hdelta : 0<delta) :
    0≤cubicBesselDerivativeUpper delta := by
  unfold cubicBesselDerivativeUpper
  positivity

lemma schlafliBesselK_cubic_derivative_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖schlafliBesselK_cubic_derivative x‖≤cubicBesselDerivativeUpper delta*Real.exp (-x/2) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hp1 : (x/2)^(-(1:ℝ)/3)≤(delta/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hp4 : (x/2)^(-(4:ℝ)/3)≤(delta/2)^(-(4:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [schlafliBesselK_cubic_derivative,Complex.norm_real,cubicBesselRealDeriv]
  calc
    _ ≤ ‖(-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)‖+
        ‖(1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)‖ := norm_add_le _ _
    _ = (1/12:ℝ)*(x/2)^(-(4:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖+
        (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖ := by
      have hn4 : ‖(x/2)^(-(4:ℝ)/3)‖=(x/2)^(-(4:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      have hn1 : ‖(x/2)^(-(1:ℝ)/3)‖=(x/2)^(-(1:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      simp only [norm_mul,hn4,hn1]
      norm_num
    _ ≤ (1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)*
          (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)))+
        (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*
          ((4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      gcongr
      · exact cubicBesselIntegral_norm_bound x
      · exact cubicBesselIntegralDeriv_norm_bound delta x hdelta hx
    _ = _ := by unfold cubicBesselDerivativeUpper;ring

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicGauss_add_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):primeCubicGauss p hp hprimary (e+3) h=primeCubicGauss p hp hprimary e h:=by
  unfold primeCubicGauss
  rw [pow_add,primeCubicMulChar_cube,mul_one]

lemma cubicUnitGaussSum_prime_cube_shift_pos (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(n+4))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^(n+1)):=by
  by_cases hd:p^n∣h
  · obtain ⟨r,rfl⟩:=hd
    have harg:p^n*r*p^3=p^(n+3)*r:=by rw [pow_add];ring
    rw [harg,show n+4=(n+3)+1 by omega,
      cubicUnitGaussSum_prime_power_lift p hp hprimary (n+3) r,
      cubicUnitGaussSum_prime_power_lift p hp hprimary n r]
    rw [show n+3+1=(n+1)+3 by omega,primeCubicGauss_add_three,pow_add]
    ring
  · have hlow:cubicUnitGaussSum h (p^(n+1))=0:=by
      by_contra hh
      exact hd (cubicUnitGaussSum_prime_power_support p hp hprimary n h hh)
    have hhigh:cubicUnitGaussSum (h*p^3) (p^(n+4))=0:=by
      by_contra hh
      have hh':cubicUnitGaussSum (h*p^3) (p^((n+3)+1))≠0:=by convert hh using 1
      have hd':p^(n+3)∣h*p^3:=cubicUnitGaussSum_prime_power_support p hp hprimary (n+3) (h*p^3) hh'
      have hd'':p^3*p^n∣p^3*h:=by simpa only [pow_add,mul_comm,mul_left_comm,mul_assoc] using hd'
      exact hd ((mul_dvd_mul_iff_left (pow_ne_zero 3 hp.ne_zero)).mp hd'')
    rw [hhigh,hlow,mul_zero]

lemma cubicUnitGaussSum_prime_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (k:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(k+3))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^k)-
        if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2 else 0:=by
  cases k with
  | zero=>
    rw [Nat.zero_add,cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      (dvd_mul_left (p^3) h)]
    have he:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at he ⊢
    rw [he]
    ring
  | succ n=>
    simpa only [show n+1+3=n+4 by omega,Nat.succ_ne_zero,ite_false,sub_zero] using
      cubicUnitGaussSum_prime_cube_shift_pos p hp hprimary n h

private def primeExpansionTerm (p:Eis) (s:ℂ) (h:Eis) (k:ℕ):ℂ:=
  ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*cubicUnitGaussSum h (p^k)*
    unramifiedPrimeDeletedSeries p s (h*p^k)

private lemma primeExpansionTerm_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (h:Eis) (k:ℕ):
    primeExpansionTerm p s (h*p^3) (k+3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        primeExpansionTerm p s h k-
      if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*unramifiedPrimeDeletedSeries p s h else 0:=by
  have hv:unramifiedPrimeDeletedSeries p s (h*p^3*p^(k+3))=
      unramifiedPrimeDeletedSeries p s (h*p^k):=by
    have he:h*p^3*p^(k+3)=(h*p^k*p^3)*p^3:=by rw [pow_add];ring
    rw [he,unramifiedPrimeDeletedSeries_cube_shift p hp,
      unramifiedPrimeDeletedSeries_cube_shift p hp]
  unfold primeExpansionTerm
  rw [cubicUnitGaussSum_prime_cube_shift p hp hprimary k h,hv,pow_add]
  split_ifs with hk
  · subst k
    simp only [pow_zero,mul_one,cubicUnitGaussSum_one]
    ring
  · ring

theorem unramifiedCubicGaussSeries_cube_step (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+3))=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^a)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph (a+3)
  have hold:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph a
  change unramifiedCubicGaussSeries s (h*p^a)=
    ∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a) k at hold
  have harg:h*p^(a+3)=(h*p^a)*p^3:=by rw [pow_add,mul_assoc]
  change unramifiedCubicGaussSeries s (h*p^(a+3))=
    ∑k∈Finset.range (a+3+2),primeExpansionTerm p s (h*p^(a+3)) k at he
  rw [show a+3+2=3+(a+2) by omega,Finset.sum_range_add,harg] at he
  have hsmall:∑k∈Finset.range 3,primeExpansionTerm p s (h*p^a*p^3) k=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    have hg1:cubicUnitGaussSum (h*p^a*p^3) p=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ hp.ne_zero
        ((dvd_pow_self p (by decide:3≠0)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    have hg2:cubicUnitGaussSum (h*p^a*p^3) (p^2)=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
        ((pow_dvd_pow p (by omega:2≤3)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,primeExpansionTerm,
      pow_zero,pow_one,cubicUnitGaussSum_one,mul_one,one_mul,zero_add,hg1,hg2,
      mul_zero,zero_mul,add_zero]
    rw [unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hsmall] at he
  have htail:∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a*p^3) (3+k)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedPrimeDeletedSeries p s (h*p^a):=by
    simp_rw [show ∀k:ℕ,3+k=k+3 by omega,primeExpansionTerm_cube_shift p hp hprimary]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←hold]
    simp
  rw [htail,←harg] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_cube_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+6))=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^(a+3))-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have hfirst:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph a
  have hsecond:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph (a+3)
  have hv:unramifiedPrimeDeletedSeries p s (h*p^(a+3))=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    rw [pow_add,←mul_assoc,unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hv,show a+3+3=a+6 by omega] at hsecond
  linear_combination hsecond-hfirst

end

section

open scoped BigOperators Classical Topology
open Filter Set
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem unramifiedGaussResidue_of_initial_relation (h0 h1 h2:Eis) (A B:ℂ→ℂ)
    (hA:AnalyticOnNhd ℂ A {s:ℂ|1<s.re ∧ 0<s.im})
    (hB:AnalyticOnNhd ℂ B {s:ℂ|1<s.re ∧ 0<s.im})
    (hAc:ContinuousAt A (4/3:ℂ)) (hBc:ContinuousAt B (4/3:ℂ))
    (hrel:∀s:ℂ,4<s.re→0<s.im→unramifiedCubicGaussSeries s h0=
      A s*unramifiedCubicGaussSeries s h1+B s*unramifiedCubicGaussSeries s h2):
    unramifiedGaussResidue h0=A (4/3)*unramifiedGaussResidue h1+
      B (4/3)*unramifiedGaussResidue h2:=by
  let T (h:Eis):ℂ→ℂ:=translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  let H (h:Eis):ℂ→ℂ:=fun s=>cuspWhittakerHeightFactor s (3*h)
  let D:Set ℂ:={s|1<s.re ∧ 0<s.im}
  let f:ℂ→ℂ:=fun s=>T h0 s*H h1 s*H h2 s
  let g:ℂ→ℂ:=fun s=>A s*T h1 s*H h0 s*H h2 s+B s*T h2 s*H h0 s*H h1 s
  have hT (h:Eis):AnalyticOnNhd ℂ (T h) D:=fun s hs=>
    translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hH (h:Eis):AnalyticOnNhd ℂ (H h) D:=fun s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1
  have hf:AnalyticOnNhd ℂ f D:=fun s hs=>((hT h0 s hs).mul (hH h1 s hs)).mul (hH h2 s hs)
  have hg:AnalyticOnNhd ℂ g D:=fun s hs=>
    (((hA s hs).mul (hT h1 s hs)).mul (hH h0 s hs)).mul (hH h2 s hs) |>.add
      ((((hB s hs).mul (hT h2 s hs)).mul (hH h0 s hs)).mul (hH h1 s hs))
  have hconvex:Convex ℝ D:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hstart:(5+Complex.I:ℂ)∈D:=by norm_num [D]
  have hopen:IsOpen {s:ℂ|4<s.re ∧ 0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:f=ᶠ[𝓝 (5+Complex.I:ℂ)]g:=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g,T,H]
    rw [translatedCuspFamily_opposite_initial h0 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h1 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h2 s hs.1 hs.2,hrel s hs.1 hs.2]
    ring
  have heq:=hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hlimH (h:Eis):Tendsto (H h) (𝓝[≠] (4/3:ℂ)) (𝓝 (H h (4/3))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  let R (h:Eis):ℂ:=translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue
  have hlimT (h:Eis):Tendsto (fun s:ℂ=>(s-4/3)*T h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (R h)):=
    translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  have hl:=(((hlimT h0).mul (hlimH h1)).mul (hlimH h2)).comp upperVertical_tendsto_cubic_punctured
  have hr:=((((hAc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h1)).mul (hlimH h0)).mul
    (hlimH h2) |>.add ((((hBc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h2)).mul
      (hlimH h0)).mul (hlimH h1))).comp upperVertical_tendsto_cubic_punctured
  have hcross:R h0*H h1 (4/3)*H h2 (4/3)=
      A (4/3)*R h1*H h0 (4/3)*H h2 (4/3)+B (4/3)*R h2*H h0 (4/3)*H h1 (4/3):=by
    apply tendsto_nhds_unique_of_eventuallyEq hl hr
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have htD:(4/3:ℂ)+(t:ℂ)*Complex.I∈D:=by
      constructor
      · norm_num
      · simpa using ht
    have hc:=heq htD
    dsimp only [Function.comp_def,f,g] at *
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hc
  change R h0/H h0 (4/3)=A (4/3)*(R h1/H h1 (4/3))+B (4/3)*(R h2/H h2 (4/3))
  have h0ne:H h0 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h0)
  have h1ne:H h1 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h1)
  have h2ne:H h2 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h2)
  field_simp [h0ne,h1ne,h2ne]
  linear_combination hcross

lemma gaussPrimeWeight_analytic (p:Eis) (hp:Prime p) (s:ℂ):
    AnalyticAt ℂ (fun z:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-z)) s:=by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow (Or.inl
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))))

lemma gaussPrimeWeight_center (p:Eis) (hp:Prime p):
    (Ideal.absNorm (Ideal.span {p}):ℂ)^3*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ)))^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹:=by
  have hQ:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  rw [←Complex.cpow_nat_mul,←Complex.cpow_natCast _ 3,←Complex.cpow_add _ _ hQ]
  convert Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}):ℂ) using 1 ;congr 1 ;norm_num

theorem unramifiedGaussResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h):
    unramifiedGaussResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 h*
        unramifiedGaussResidue (h*p):=by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  let B:ℂ→ℂ:=fun s=>-((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h)
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s:ℂ):AnalyticAt ℂ B s:=((gaussPrimeWeight_analytic p hp s).mul analyticAt_const).neg
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^3) h (h*p) A B
    (fun s _=>hA s) (fun s _=>hB s) (hA _).continuousAt (hB _).continuousAt
    (fun s hs _=>by
      have hh:=unramifiedCubicGaussSeries_prime_recurrence p hp hprimary s (by linarith) h hph
      simpa only [A,B,neg_mul,sub_eq_add_neg] using hh)
  dsimp only [A,B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul,sub_eq_add_neg] using he

end

section

open scoped BigOperators Classical Topology
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem unramifiedGaussResidue_cube_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedGaussResidue (h*p^(a+6))=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^(a+3))-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue (h*p^a):=by
  let q:ℂ→ℂ:=fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hq (s:ℂ):AnalyticAt ℂ q s:=analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3)
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^(a+6)) (h*p^(a+3)) (h*p^a)
    (fun s=>1+q s) (fun s=>-q s)
    (fun s _=>analyticAt_const.add (hq s)) (fun s _=>(hq s).neg)
    (continuousAt_const.add (hq _).continuousAt) (hq _).continuousAt.neg
    (fun s hs _=>by
      have hh:=unramifiedCubicGaussSeries_cube_recurrence p hp hprimary s (by linarith) h hph a
      simpa only [q,neg_mul,sub_eq_add_neg] using hh)
  dsimp only [q] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul,sub_eq_add_neg] using he

private lemma recurrence_roots_closed (r:ℕ→ℂ) (q:ℂ)
    (hr:∀k,r (k+2)=(1+q)*r (k+1)-q*r k) (k:ℕ):
    (1-q)*r k=(r 1-q*r 0)+(r 0-r 1)*q^k:=by
  have hpair:∀k:ℕ,
      ((1-q)*r k=(r 1-q*r 0)+(r 0-r 1)*q^k) ∧
      ((1-q)*r (k+1)=(r 1-q*r 0)+(r 0-r 1)*q^(k+1)):=by
    intro k
    induction k with
    | zero=>constructor <;>norm_num <;>ring
    | succ k ih=>
      refine ⟨ih.2,?_⟩
      have hk:=hr k
      rw [show k+1+1=k+2 by omega]
      simp only [pow_succ] at *
      linear_combination (1-q)*hk+(1+q)*ih.2-q*ih.1
  exact (hpair k).1

theorem unramifiedGaussResidue_cube_closed (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ):
    (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^(3*k))=
      (unramifiedGaussResidue (h*p^3)-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue h)+
      (unramifiedGaussResidue h-unramifiedGaussResidue (h*p^3))*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)^k:=by
  let r:ℕ→ℂ:=fun j=>unramifiedGaussResidue (h*p^(3*j))
  have hr:∀j,r (j+2)=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*r (j+1)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*r j:=by
    intro j
    have he:=unramifiedGaussResidue_cube_recurrence p hp hprimary h hph (3*j)
    rw [show 3*j+6=3*(j+2) by omega,show 3*j+3=3*(j+1) by omega] at he
    exact he
  have he:=recurrence_roots_closed r (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ hr k
  simpa only [r,Nat.mul_zero,Nat.mul_one,pow_zero,mul_one] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

def inverseCuspPath (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) : ℂ×ℝ :=
  (-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)),
    v/(‖c‖^2*(v^2+t^2*‖direction‖^2)))

lemma inverseCuspPath_zero (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    inverseCuspPath c d v direction 0=(-d/c,1/(‖c‖^2*v)) := by
  unfold inverseCuspPath
  simp only [Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_mul,add_zero,zero_div,sub_zero]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hc,hv.ne']

theorem inverseCuspPath_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    HasDerivAt (inverseCuspPath c d v direction)
      (-(star direction)/(c^2*(v:ℂ)^2),0) 0 := by
  have hn : ‖c‖≠0 := norm_ne_zero_iff.mpr hc
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hden : HasDerivAt (fun t : ℝ=>v^2+t^2*‖direction‖^2) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (‖direction‖^2)).const_add (v^2) using 1 <;> norm_num
  have hnum : HasDerivAt (fun t : ℝ=>(t:ℂ)*star direction) (star direction) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const (star direction))
  have hdenC := hden.ofReal_comp.const_mul (c^2)
  have hdenR := hden.const_mul (‖c‖^2)
  have hcz : c^2*((v^2+(0:ℝ)^2*‖direction‖^2:ℝ):ℂ)≠0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hvc)
  have hrz : ‖c‖^2*(v^2+(0:ℝ)^2*‖direction‖^2)≠0 := by positivity
  have hz : HasDerivAt
      (fun t : ℝ=>-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)))
      (-(star direction)/(c^2*(v:ℂ)^2)) 0 := by
    convert (hnum.div hdenC hcz).const_sub (-d/c) using 1 ;
      simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero,Complex.ofReal_pow,
        Complex.ofReal_zero,mul_zero,sub_zero]
    field_simp

  have hvd : HasDerivAt (fun t : ℝ=>v/(‖c‖^2*(v^2+t^2*‖direction‖^2))) 0 0 := by
    convert (hasDerivAt_const (0:ℝ) v).div hdenR hrz using 1 ; simp
  exact hz.prodMk hvd

theorem inverseCuspPath_comp_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    HasDerivAt (fun t=>F (inverseCuspPath c d v direction t))
      (A (-(star direction)/(c^2*(v:ℂ)^2),0)) 0 := by
  have hf : HasFDerivAt F A (inverseCuspPath c d v direction 0) := by
    rwa [inverseCuspPath_zero c d v direction hc hv]
  exact hf.comp_hasDerivAt 0 (inverseCuspPath_hasDerivAt c d v direction hc hv)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0279

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates
Source SHA256: b6fe12c57904fccfa6ea027e2b9a41b595de257635dd4615b21b8ddd2f8bade9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0280


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
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

def inverseCuspCoordinates (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ×ℝ :=
  (-d/c-star z/(c^2*((v^2+‖z‖^2:ℝ):ℂ)),v/(‖c‖^2*(v^2+‖z‖^2)))

lemma inverseCuspCoordinates_height_pos (c d : ℂ) (v : ℝ) (z : ℂ)
    (hc : c≠0) (hv : 0<v) : 0<(inverseCuspCoordinates c d v z).2 := by
  dsimp [inverseCuspCoordinates]
  positivity

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t:ℂ)*direction)=inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates,inverseCuspPath,star_mul,Complex.star_def,
    Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_comm]

theorem inverse_cusp_action (g : SL(2,ℂ)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    g⁻¹ • upperPoint (z+g 0 0/g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0=g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1= -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0= -g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1=g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have hl : (-g 1 0)*(z+g 0 0/g 1 0)+g 0 0= -(g 1 0*z) := by
    field_simp
    ; ring
  have ht : g 1 1*(z+g 0 0/g 1 0)+(-g 0 1)=g 1 1*z+1/g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0*z)‖^2+‖-g 1 0‖^2*v^2=
      ‖g 1 0‖^2*(v^2+‖z‖^2) := by rw [norm_neg,norm_neg,norm_mul,mul_pow];ring
  have hnormc : ((‖g 1 0‖^2:ℝ):ℂ)=g 1 0*star (g 1 0) := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖^2:ℝ):ℂ)=z*star z := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v^2+‖z‖^2≠0 := by positivity
  have hTc : ((v^2+‖z‖^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0)≠0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00,h01,h10,h11,hl,ht,hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul,hnormc]
    simp only [Complex.star_def,map_neg,map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc,hcc,hTc]
    rw [Complex.ofReal_add,Complex.ofReal_pow,hnormz]
    simp only [Complex.star_def,]
    ; ring
  · rw [h10,h11,hl,hden]
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma real_linear_horizontal_decompose (A : (ℂ×ℝ)→L[ℝ]ℂ) (z : ℂ) :
    A (z,0)=(z.re:ℂ)*A (1,0)+(z.im:ℂ)*A (Complex.I,0) := by
  have hz : ((z,0):ℂ×ℝ)=z.re • (1,0)+z.im • (Complex.I,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_add,Prod.smul_fst,Complex.real_smul,mul_one] using z.re_add_im.symm
    · simp
  rw [hz,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℂ×ℝ)→L[ℝ]ℂ) (k : ℂ) :
    (1/2:ℂ)*(A (k,0)+Complex.I*A (-Complex.I*k,0))=
      k*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  rw [real_linear_horizontal_decompose A k,real_linear_horizontal_decompose A (-Complex.I*k)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,
    zero_add,zero_sub,Complex.ofReal_neg]
  conv_rhs => lhs; rw [←k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inverse_cusp_wirtingerBar (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  have h1 := (inverseCuspPath_comp_hasDerivAt c d v 1 hc hv F A hF).deriv
  have hI := (inverseCuspPath_comp_hasDerivAt c d v Complex.I hc hv F A hF).deriv
  have he1 : (fun t : ℝ=>F (inverseCuspCoordinates c d v (t:ℂ)))=
      (fun t : ℝ=>F (inverseCuspPath c d v 1 t)) := by
    funext t
    rw [←inverseCuspCoordinates_line]
    simp only [mul_one]
  have heI : (fun t : ℝ=>F (inverseCuspCoordinates c d v ((t:ℂ)*Complex.I)))=
      (fun t : ℝ=>F (inverseCuspPath c d v Complex.I t)) := by
    funext t
    rw [inverseCuspCoordinates_line]
  rw [horizontalWirtingerBar]
  simp only [zero_add]
  rw [he1,heI,h1,hI]
  simp only [star_one,Complex.star_def,Complex.conj_I,neg_neg]
  convert real_linear_wirtinger_swap A (-1/(c^2*(v:ℂ)^2)) using 1 ;
    congr 2 ; ring_nf

def horizontalWirtingerZ (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ=>f (z+(t:ℂ))) 0-
    Complex.I*deriv (fun t : ℝ=>f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerZ_eq_fderiv (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerZ (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ,h1,hI]

theorem inverse_cusp_wirtinger_rule (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*
        horizontalWirtingerZ (fun z=>F (z,1/(‖c‖^2*v))) (-d/c) := by
  rw [horizontalWirtingerZ_eq_fderiv F A _ _ hF]
  exact inverse_cusp_wirtingerBar c d v hc hv F A hF

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

theorem cusp_mellin_reflection (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) (2*s)=
      A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  have he : (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹)))=
      (fun v : ℝ=>A • ((v:ℂ)^(-2:ℂ) • g ((Q*v)⁻¹))) := by
    funext v; simp only [smul_eq_mul]
  rw [he,mellin_const_smul,mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ=>g v⁻¹) (2*s+(-2:ℂ)) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2*s+(-2:ℂ))=2-2*s by ring]
  ring

theorem cusp_mellin_reflection_of_identity (f g : ℝ→ℂ) (A s : ℂ)
    (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) :
    mellin f (2*s)=A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  rw [←cusp_mellin_reflection g A s Q hQ]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hfg v hv]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalPhaseCLM (freq : ℂ) : ℂ →L[ℝ] ℂ :=
  (2*Real.pi*Complex.I:ℂ) •
    (freq • ContinuousLinearMap.id ℝ ℂ +
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (freq • ContinuousLinearMap.id ℝ ℂ))

lemma horizontalPhaseCLM_apply (freq direction : ℂ) :
    horizontalPhaseCLM freq direction = horizontalPhaseMultiplier freq direction := by
  simp [horizontalPhaseCLM,horizontalPhaseMultiplier]
  ring

lemma brevePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => ShortDraftTrace.breveE (freq*w))
      (ShortDraftTrace.breveE (freq*z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x:=z)
  convert! hh using 1

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def amplitudeDeriv (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*
    (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)+
      (v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v))

lemma amplitude_hasDerivAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    HasDerivAt (fun y : ℝ => coeff.amplitude y h) (coeff.amplitudeDeriv v h) v := by
  by_cases hh : h=0
  · simp only [amplitude,amplitudeDeriv,ite_eq_left hh]
    exact hasDerivAt_const v 0
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4*Real.pi*‖cuspFrequency h‖*y)
      (4*Real.pi*‖cuspFrequency h‖) v := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (4*Real.pi*‖cuspFrequency h‖)
  have hk := (schlafliBesselK_cubic_hasDerivAt (4*Real.pi*‖cuspFrequency h‖*v)
    (by positivity)).scomp v hslope
  have hvd := (Complex.ofRealCLM.hasDerivAt (x:=v)).mul hk
  have hfull := hvd.const_mul (coeff.value h)
  simp only [amplitude,amplitudeDeriv,ite_eq_right hh]
  convert! hfull using 1 <;> simp [Function.comp_def,Pi.mul_apply,Complex.ofRealCLM_apply,Complex.real_smul,mul_assoc]

def termFDeriv (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  if h=0 then 0 else
    (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (coeff.amplitudeDeriv p.1 h*ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p • (horizontalPhaseCLM (cuspFrequency h)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)

lemma term_hasFDerivAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt (coeff.term h) (coeff.termFDeriv h p) p := by
  by_cases hh : h=0
  · have hzero : coeff.term h=(fun _ : ℝ × ℂ => (0:ℂ)) := by
      funext q
      simp only [term,ite_eq_left hh]
    rw [hzero,termFDeriv,ite_eq_left hh]
    exact hasFDerivAt_const (𝕜:=ℝ) (0:ℂ) p
  have hvd := (coeff.amplitude_hasDerivAt p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hzd := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=p))
  have hprod : HasFDerivAt (fun q : ℝ × ℂ => coeff.amplitude q.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*q.2)) (coeff.termFDeriv h p) p := by
    convert! hvd.mul hzd using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv,ite_eq_right hh]
    change (direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))+
      coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2 =
      coeff.amplitude p.1 h*(ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        horizontalPhaseCLM (cuspFrequency h) direction.2)+
      ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        ((direction.1:ℂ)*coeff.amplitudeDeriv p.1 h)
    rw [coeff.term_eq_amplitude p.1 hp h p.2]
    ring
  apply hprod.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.term_eq_amplitude q.1 hq h q.2

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma weighted_bessel_bounds (a : ℝ) (ha : 0<a) :
    ∃A B : ℝ,0≤A ∧ 0≤B ∧ ∀(h : ActualEisensteinCubic.O),h≠0 → ∀v : ℝ,a≤v →
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) ∧
      ‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hKu := (cubicBesselUpperAway_pos delta hdelta).le
  have hKd := cubicBesselDerivativeUpper_nonneg delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,C*cubicBesselDerivativeUpper delta,
    mul_nonneg hC hKu,mul_nonneg hC hKd,?_⟩
  intro h hh v hv
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  have hcombine (y D : ℝ) (hy : 0≤y) (hD : 0≤D)
      (hbound : y≤D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :
      ‖coeff.value h‖*y≤(C*D)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
    calc
      _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*
          (D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
        mul_le_mul (hcoeff h hh) hbound hy (by positivity)
      _ = (C*D)*Real.exp ((Real.pi*a)*‖cuspFrequency h‖-
          (4*Real.pi*‖cuspFrequency h‖*v)/2) := by
        rw [show (Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2=
          (Real.pi*a)*‖cuspFrequency h‖+(-(4*Real.pi*‖cuspFrequency h‖*v)/2) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos hr).le]
  exact ⟨hcombine _ _ (norm_nonneg _) hKu
    (schlafliBesselK_cubic_upper_away delta _ hdelta hx),
    hcombine _ _ (norm_nonneg _) hKd
    (schlafliBesselK_cubic_derivative_bound delta _ hdelta hx)⟩

lemma amplitudeDeriv_norm_le (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖coeff.amplitudeDeriv v h‖≤
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      (v*(4*Real.pi*‖cuspFrequency h‖))*
        (‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) := by
  rw [amplitudeDeriv,ite_eq_right hh,norm_mul]
  calc
    _ ≤ ‖coeff.value h‖*(‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      ‖(v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_mul,norm_mul,Complex.norm_of_nonneg hv.le,
        Complex.norm_of_nonneg (by positivity : 0≤4*Real.pi*‖cuspFrequency h‖)]
      ring

lemma termFDeriv_norm_le (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) :
    ‖coeff.termFDeriv h p‖≤‖coeff.amplitudeDeriv p.1 h‖+
      ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := by
  by_cases hh : h=0
  · simp only [termFDeriv,ite_eq_left hh,norm_zero]
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  simp only [termFDeriv,ite_eq_right hh]
  change ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖≤_
  calc
    _ ≤ ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))‖+
      ‖coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖ := norm_add_le _ _
    _ = ‖direction.1‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*‖horizontalPhaseMultiplier (cuspFrequency h) direction.2‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,breveE_norm,mul_one,norm_mul,
        horizontalPhaseCLM_apply]
    _ ≤ ‖direction‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*((4*Real.pi*‖cuspFrequency h‖)*‖direction‖) := by
      gcongr
      · exact norm_fst_le direction
      · exact (horizontalPhaseMultiplier_norm _ _).trans (by
          gcongr
          exact norm_snd_le direction)
    _ = _ := by ring

lemma termFDeriv_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.termFDeriv h p‖≤C*((1+‖cuspFrequency h‖)*
        Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨A,B,hA,hB,hweighted⟩ := coeff.weighted_bessel_bounds a ha
  obtain ⟨T,hT,hterm⟩ := coeff.slab_bound a b ha hab
  let D := B*b*(4*Real.pi)+T*(4*Real.pi)
  have hb : 0<b := ha.trans_le hab
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨A+D,add_nonneg hA hD,?_⟩
  intro h p hp
  by_cases hh : h=0
  · simp only [termFDeriv,ite_eq_left hh,norm_zero]
    positivity
  have hv : 0<p.1 := ha.trans_le hp.1
  obtain ⟨hKu,hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖coeff.amplitudeDeriv p.1 h‖≤
      A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
      (b*(4*Real.pi*‖cuspFrequency h‖))*
        (B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
    apply (coeff.amplitudeDeriv_norm_le p.1 hv h hh).trans
    gcongr
    exact hp.2
  calc
    _ ≤ ‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := coeff.termFDeriv_norm_le h p
    _ ≤ (A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
        (b*(4*Real.pi*‖cuspFrequency h‖))*(B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))+
        (T*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))*(4*Real.pi*‖cuspFrequency h‖) := by
      gcongr
      exact hterm h p hp
    _ = (A+D*‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
      dsimp [D]
      ring
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_nonneg hA (norm_nonneg (cuspFrequency h))]

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O

lemma summable_one_add_norm_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => (1+‖cuspFrequency h‖)*Real.exp (-a*‖cuspFrequency h‖)) := by
  simpa only [add_mul,one_mul] using
    (summable_exp_neg_cuspFrequency_norm a ha).add (summable_norm_mul_exp_neg_cuspFrequency a ha)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma termFDeriv_summable (p : ℝ × ℂ) (hp : 0<p.1) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.termFDeriv h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _)
    (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

lemma series_hasFDerivAt (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt coeff.series (∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p) p := by
  let a := p.1/2
  let b := 2*p.1
  have ha : 0<a := by dsimp [a];linarith
  have hab : a≤b := by dsimp [a,b];linarith
  have hap : a<p.1 := by dsimp [a];linarith
  have hpb : p.1<b := by dsimp [b];linarith
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  have hsum := (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a)
    (mul_pos Real.pi_pos ha)).mul_left C
  let slab : Set (ℝ × ℂ) := Set.Ioo a b ×ˢ Set.univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p∈slab := ⟨⟨hap,hpb⟩,Set.mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => coeff.term_hasFDerivAt h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q ⟨hq.1.1.le,hq.1.2.le⟩)
    hpSlab (coeff.summable p hp) hpSlab

lemma series_differentiableAt (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ coeff.series p := (coeff.series_hasFDerivAt p hp).differentiableAt

lemma fullFunction_cusp_eq (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    coeff.fullFunction constant (cuspCoordinateLift p)=
      constant*(p.1:ℂ)^(2/3:ℂ)+coeff.series p := by
  rw [show p=(p.1,p.2) from rfl,cuspCoordinateLift_positive p.1 p.2 hp]
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

lemma fullFunction_cusp_differentiableAt (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hc := ((hasDerivAt_ofReal_cpow_const hp.ne' (r:=(2/3:ℂ))
    (by norm_num)).const_mul constant).differentiableAt.comp p
      (differentiableAt_fst (𝕜:=ℝ) (p:=p))
  have ht : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
      constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p := by
    convert! hc.add (coeff.series_differentiableAt p hp) using 1
  apply ht.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_split_differentiableAt (constant : ℂ) (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_cusp_differentiableAt constant (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def truncatedCuspProfile (c : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℂ :=
  if c<x then f x else 0

lemma truncatedCuspProfile_eventually_top (c : ℝ) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop c] with x hx
  simp only [truncatedCuspProfile,ite_eq_left hx]

lemma truncatedCuspProfile_eventually_zero (c : ℝ) (hc : 0<c) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[𝓝[>] 0] 0 := by
  have he : ∀ᶠx : ℝ in 𝓝[>] 0,x<c := (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with x hx
  simp only [truncatedCuspProfile,ite_eq_right (not_lt_of_ge hx.le),Pi.zero_apply]

lemma truncatedCuspProfile_locallyIntegrable (c : ℝ) (hc : 0<c) (f : ℝ→ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    LocallyIntegrable (truncatedCuspProfile c f) volume := by
  have hcont : Continuous (fun x : ℝ=>f (max (c/2) x)) :=
    hf.comp_continuous (continuous_const.max continuous_id)
      (fun x=>lt_of_lt_of_le (by linarith : 0<c/2) (le_max_left _ _))
  have he : truncatedCuspProfile c f=
      (Set.Ioi c).indicator (fun x : ℝ=>f (max (c/2) x)) := by
    funext x
    by_cases hx : c<x
    · have hm : max (c/2) x=x := max_eq_right (by linarith)
      simp [truncatedCuspProfile,Set.indicator,hx,hm]
    · simp [truncatedCuspProfile,Set.indicator,hx]
  rw [he]
  exact hcont.locallyIntegrable.indicator measurableSet_Ioi

theorem truncatedCuspProfile_mellin_entire (c decay : ℝ) (hc : 0<c) (hdecay : 0<decay)
    (f : ℝ→ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x))) :
    (∀s : ℂ,MellinConvergent (truncatedCuspProfile c f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile c f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable c hc f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile c f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top c f).symm Filter.EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile c f =O[𝓝[>] 0] (fun x : ℝ=>x^(-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ=>x^(-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero c hc f).symm Filter.EventuallyEq.rfl
  constructor
  · intro s
    exact mellinConvergent_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)
  · intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0280

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SourceBesselExpansion
Source SHA256: 945330421ef559aed774fb3776019a4a3d767a5f86ab2d5004dbc1f68d8d0968
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0281


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
open scoped BigOperators Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

lemma opposite_height_fourier_average (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
      cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
    cuspWeightedFourierPhase ρ h w
  have hg:Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*unramifiedCubicGaussSeries s (9*h) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ) : oppositeEisenstein z v hv0 s*(ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ρ v*(oppositeEisenstein z v hv0 s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by ring
    simp_rw [he]
    rw [integral_const_mul,oppositeEisenstein_fourier v hv0 s hs h]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring

lemma oppositeHeight_cross_identity (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    Set.EqOn (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*
      cuspWhittakerHeightFactor s h) domain := fun s hs=>
    (translatedHeightFamily_analyticAt a b ha ρ h oppositeSource s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspIntervalWhittakerHeightFactor a b ρ s h) domain := fun s hs=>
    (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedHeightFamily_initial a b ha ρ h oppositeSource s hs.1 hs.2,
      opposite_height_fourier_average a b ha ρ h s (by linarith [hs.1]),
      translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      opposite_cusp_fourier_average s (by linarith [hs.1])]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedHeightFourier_opposite_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hfixed := (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hvar := (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hl:=((translatedHeightFamily_residue_limit a b ha ρ h oppositeSource).mul hfixed).comp upperVertical_tendsto_cubic_punctured
  have hr:=((translatedCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num)).mul hvar).comp
    upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedHeightFamily a b ha ρ h oppositeSource ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeHeight_cross_identity a b ha ρ h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      translatedCuspFourier h oppositeSource cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hev
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq,translatedCuspFourier_unramified_residue]
  ring

end

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_height_fourier_right_T (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip a b,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspWeightedFourierPhase ρ h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  change (∫w in cuspPeriodStrip a b,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha f hf.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha f hf),
    cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hslice : (∫z in periodDomain,f (cuspCoordinateLift (v,z)))=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫z in periodDomain,g (cuspCoordinateLift (v,z)) := by
    simp only [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    simpa only [mul_assoc] using period_integral_fourier_translation
      (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0)*ρ v)
      (fun m z=>congrArg (fun q:ℂ=>q*ρ v) (hyperbolicEisenstein_rational_periodic r m s hs z v hv0)) h (n:ℂ)
  dsimp only
  rw [hslice]
  ring

lemma translatedHeightFourier_residue_scaled_of_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume) :
    translatedHeightFourier a b ha ρ h M cubicEisensteinResidue=
      c*translatedHeightFourier a b ha ρ h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedHeightFamily a b ha ρ h M
  let g : ℂ→ℂ := fun s=>c*translatedHeightFamily a b ha ρ h N s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedHeightFamily_analyticAt a b ha ρ h M s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedHeightFamily_analyticAt a b ha ρ h N s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedHeightFamily_initial a b ha ρ h M s hs.1 hs.2,
      translatedHeightFamily_initial a b ha ρ h N s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedHeightFamily_residue_limit a b ha ρ h M).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedHeightFamily_residue_limit a b ha ρ h N).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedHeightFourier_one (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h 1 F=kernelCuspHeightFourier a b ha ρ h F := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedHeightFourier_bruhat (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (e:Fin 2) (sector:Fin 3⊕(Fin 3×Fin 3)) :
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep (e,sector))) cubicEisensteinResidue=
      match sector with
      | Sum.inl _=>kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue := by
  cases sector with
  | inl index =>
    rw [←one_mul (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue),←translatedHeightFourier_one a b ha ρ h]
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_height_fourier_right_T a b ha ρ ModularGroup.S ab.2.val h s (by linarith)

theorem kernelSourceProjection_height_fourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedHeightFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue)))=_
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspIntervalWhittakerHeightFactor_zero_center (a b:ℝ) (_ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) 0=
      (3*(Real.pi:ℂ))*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero (4/3) (by norm_num)]
  have he : -(4/3:ℂ)-1=-(7/3:ℂ) := by ring
  rw [he]
  ring

lemma kernelCuspHeightFourier_principal_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds,cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    simp only [principalArithmeticResidue,ite_true]
    ring
  · simpa only [principalArithmeticResidue,ite_eq_right hh] using kernelCuspHeightFourier_residue_factor a b ha ρ h hh

lemma principalArithmeticResidue_not_horizontal (h:Eis) (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    principalArithmeticResidue h=0 := by
  have h0:h≠0 := by intro he;subst h;simp [cuspFrequency] at hh
  rw [principalArithmeticResidue,ite_eq_right h0,nonzeroScatteringResidue,
    kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh,zero_div]

theorem kernelSourceProjection_height_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  rw [kernelSourceProjection_height_fourier,kernelCuspHeightFourier_principal_residue,
    translatedHeightFourier_opposite_residue,sourceRayPhaseSum_eq,sourceArithmeticResidue]
  split_ifs with hh
  · field_simp [cusp_volume_ne_zero]

  · rw [principalArithmeticResidue_not_horizontal h hh]
    ring

def sourceResidualFourierCoefficient (h:Eis) : ℂ := cubicBesselNormalizer h*sourceArithmeticResidue h

def sourceResidualFullModeAmplitude (v:ℝ) (h:Eis) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else sourceResidualFourierCoefficient h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma sourceResidualFullModeAmplitude_zero_density (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  simpa [sourceResidualFullModeAmplitude,cubicResidualFullModeAmplitude] using
    cubicResidualFullModeAmplitude_zero_density v hv

lemma sourceResidualFullModeAmplitude_nonzero_density (v:ℝ) (hv:0<v) (h:Eis) (hh:h≠0) :
    sourceResidualFullModeAmplitude v h/(v:ℂ)^3=sourceResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [sourceResidualFullModeAmplitude,ite_eq_right hh]
  have hv0:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

lemma kernelSourceProjection_height_bessel (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (hh:h≠0) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFourierCoefficient h*
        ∫v in Set.Icc a b,ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [kernelSourceProjection_height_residue,cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,
    sourceResidualFourierCoefficient]
  ring

theorem kernelSourceProjection_height_full (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  by_cases hh:h=0
  · subst h
    rw [kernelSourceProjection_height_residue,sourceArithmeticResidue_zero,
      cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelSourceProjection_height_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3))=
        sourceResidualFourierCoefficient h*∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring

end

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖(kernelSourceProjection cubicEisensteinResidue)‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelSourceProjection_height_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h (kernelSourceProjection cubicEisensteinResidue)
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound

lemma sourceResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := sourceResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (sourceResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp

def sourceBesselCoefficients : SubexponentialBesselCoefficients where
  value := sourceResidualFourierCoefficient
  growth := sourceResidualFourierCoefficient_subexponential

def sourceBesselFunction : HyperbolicSpace→ℂ :=
  sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceBesselFunction_continuous : Continuous sourceBesselFunction :=
  sourceBesselCoefficients.fullFunction_continuous _

lemma sourceBesselFunction_fourier (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,sourceBesselFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [sourceBesselFunction,sourceBesselCoefficients.fullFunction_fourier]
  by_cases hh:h=0
  · simp [sourceResidualFullModeAmplitude,hh]
  · simp only [ite_eq_right hh,SubexponentialBesselCoefficients.amplitude,sourceResidualFullModeAmplitude]
    rfl

lemma sourceBesselFunction_period (v:ℝ) (hv:0<v) (z:ℂ) (n:ActualEisensteinCubic.O) :
    sourceBesselFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      sourceBesselFunction (upperPoint z v hv) :=
  sourceBesselCoefficients.fullFunction_period _ v hv z n

lemma sourceBesselFunction_height_memLp (v:ℝ) (hv:0<v) :
    MemLp (fun z:ℂ=>sourceBesselFunction (cuspCoordinateLift (v,z))) 2 (volume.restrict periodDomain) :=
  sourceBesselCoefficients.fullFunction_height_memLp _ v hv

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => sourceResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (sourceResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

lemma projectedResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h (kernelSourceProjection cubicEisensteinResidue))
    ((sourceResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h (kernelSourceProjection cubicEisensteinResidue),
    kernelSourceProjection_height_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma projectedResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => projectedResidue_slice_coefficient_ae a b ha h)

lemma projectedResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        (kernelSourceProjection cubicEisensteinResidue) (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  filter_upwards [projectedResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

theorem projectedResidue_cell_slices_ae (a b:ℝ) (ha:0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z:ℂ=>kernelSourceProjection cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain] (fun z=>sourceBesselFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [projectedResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha (kernelSourceProjection cubicEisensteinResidue),
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos:0<v:=ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (sourceBesselFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using sourceBesselFunction_fourier v hpos h

theorem sourceBesselFunction_represents_projection :
    (fun w=>kernelSourceProjection cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceBesselFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable (kernelSourceProjection cubicEisensteinResidue)).measurable.comp
      (measurable_integralOrbitProjection _)) sourceBesselFunction_continuous.measurable
  · intro v hv z n
    exact congrArg (kernelSourceProjection cubicEisensteinResidue) (kernelProjection_upper_period v hv z n)
  · exact sourceBesselFunction_period
  · exact projectedResidue_cell_slices_ae

theorem cubicSourceResidualFunction_eq_bessel : cubicSourceResidualFunction=sourceBesselFunction := by
  have he : cubicSourceResidualFunction=ᵐ[hyperbolicVolume]sourceBesselFunction := by
    filter_upwards [cubicSourceResidualFunction_represents_projection,sourceBesselFunction_represents_projection]
      with w hw hs
    exact hw.symm.trans hs
  exact Measure.eq_of_ae_eq he cubicSourceResidualFunction_continuous sourceBesselFunction_continuous

theorem cubicSourceResidualFunction_fourier_full (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier v hv h

theorem cubicSourceResidualFunction_bessel (v:ℝ) (hv:0<v) (z:ℂ) :
    cubicSourceResidualFunction (upperPoint z v hv)=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+
      ∑'h:ActualEisensteinCubic.O,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    sourceBesselCoefficients.series_bessel v hv z]
  rfl

theorem sourceResidual_series_uniform (a b:ℝ) (ha:0<a) (hab:a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑ h ∈ t, sourceBesselCoefficients.term h p)
      sourceBesselCoefficients.series atTop {p : ℝ × ℂ | p.1 ∈ Set.Icc a b} :=
  sourceBesselCoefficients.series_uniform a b ha hab

theorem sourceResidual_bessel_normal (a b:ℝ) (ha:0<a) (hab:a≤b) :
    ∃g : ActualEisensteinCubic.O→ℝ, Summable g ∧ ∀(h:ActualEisensteinCubic.O)(v:ℝ),v∈Set.Icc a b→∀z:ℂ,
      ‖(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z)‖≤g h := by
  obtain ⟨C,hC,hbound⟩:=sourceBesselCoefficients.slab_bound a b ha hab
  refine ⟨fun h=>C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖),
    (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C,?_⟩
  intro h v hv z
  have he:=hbound h (v,z) hv
  rw [sourceBesselCoefficients.term_eq_amplitude v (ha.trans_le hv.1) h z] at he
  exact he

end CubicEisenstein

end

end OAI
end OAIOriginalModule0281

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin
Source SHA256: d46a7926f33947f15ae3e9d00fdb5495e8af6cdf1b771dc9035a6ebc5cb47edd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0282



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
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def reflectedCuspProfile (A : ℂ) (Q : ℝ) (g : ℝ→ℂ) (v : ℝ) : ℂ :=
  A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))

lemma reflectedCuspProfile_mellin (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (reflectedCuspProfile A Q g) s=
      A*(Q:ℂ)^(2-s)*mellin g (2-s) := by
  unfold reflectedCuspProfile
  have hh := cusp_mellin_reflection g A (s/2) Q hQ
  simpa only [show (2*(s/2):ℂ)=s by ring,reflectedCuspProfile] using hh

lemma reflectedCuspProfile_mellinConvergent (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ)
    (hQ : 0<Q) (hg : MellinConvergent g (2-s)) :
    MellinConvergent (reflectedCuspProfile A Q g) s := by
  unfold reflectedCuspProfile
  have hinv : MellinConvergent (fun t : ℝ=>g t⁻¹) (s-2) := by
    have hh := (MellinConvergent.comp_rpow (f := g) (s := s-2)
      (a := -1) (by norm_num : (-1:ℝ)≠0)).mpr
        (show MellinConvergent g ((s-2)/(-1:ℝ)) by
          simpa only [show ((s-2)/(-1:ℝ):ℂ)=2-s by push_cast;ring] using hg)
    simpa only [Real.rpow_neg_one] using hh
  have hscale := (MellinConvergent.comp_mul_left (f := fun t : ℝ=>g t⁻¹)
    (s := s-2) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun t : ℝ=>g (Q*t)⁻¹)
    (s := s) (a := -2)).mpr (by simpa only [sub_eq_add_neg] using hscale)
  simpa only [reflectedCuspProfile,smul_eq_mul] using hpow.const_smul A

lemma cusp_truncation_reflection_ae (f g : ℝ→ℂ) (A : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    f =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun v=>truncatedCuspProfile 1 f v+
        reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) := by
  have hne : ∀ᵐv : ℝ ∂volume.restrict (Set.Ioi 0),v≠1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with v hv hv1
  have hrel : 1/Q<(Q*v)⁻¹ ↔ v<1 := by
    rw [inv_eq_one_div,div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    constructor <;> intro hh <;> nlinarith
  by_cases hhi : 1<v
  · have hlo : ¬1/Q<(Q*v)⁻¹ := fun hh=>not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile,ite_eq_left hhi,reflectedCuspProfile,ite_eq_right hlo,
      mul_zero,add_zero]
  · have hlo : 1/Q<(Q*v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile,ite_eq_right hhi,reflectedCuspProfile,ite_eq_left hlo,zero_add]
    exact hfg v hv

theorem cusp_mellin_entire (f g : ℝ→ℂ) (A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0<Q) (hdecayF : 0<decayF) (hdecayG : 0<decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ=>Real.exp (-decayF*v)))
    (hgbound : g =O[atTop] (fun v : ℝ=>Real.exp (-decayG*v)))
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    (∀s : ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc,hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc,hgd⟩ := truncatedCuspProfile_mellin_entire (1/Q) decayG
    (by positivity) hdecayG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s+
        A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) := by
    have hr := reflectedCuspProfile_mellinConvergent
      (truncatedCuspProfile (1/Q) g) A s Q hQ (hgc (2-s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ=>(v:ℂ)^(s-1) • z) hv.symm
    · have he : mellin f s=mellin (fun v=>truncatedCuspProfile 1 f v+
          reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he,hsum.2,reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s=>(hresult s).1,?_⟩
  have he : mellin f=(fun s : ℂ=>mellin (truncatedCuspProfile 1 f) s+
      A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) :=
    funext (fun s=>(hresult s).2)
  rw [he]
  let : NeZero (Q:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q:ℂ)).comp
    ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2:ℂ)).sub differentiable_id)))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def directionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*coeff.term h (v,z)

lemma term_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))
      (coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (coeff.amplitude v h)
  have hf : (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => coeff.amplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact coeff.term_eq_amplitude v hv h _
  rw [hf]
  convert hh using 1
  rw [directionalTerm,coeff.term_eq_amplitude v hv h]
  ring

lemma directionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖coeff.directionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma directionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.directionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma series_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.series (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => coeff.term h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using coeff.summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => coeff.term_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma fullFunction_horizontal_hasDerivAt (constant : ℂ) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.fullFunction constant (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (coeff.series_horizontal_hasDerivAt v hv z direction t).const_add
    (constant*(v:ℂ)^(2/3:ℂ))
  simpa only [fullFunction,function,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

theorem fullFunction_wirtingerBar (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*coeff.term h (v,z) := by
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  have hs1 := coeff.directionalTerm_summable v hv z 1
  have hsI := (coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

lemma fullFunction_wirtingerBar_summable (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => (2*Real.pi*Complex.I*star (cuspFrequency h))*coeff.term h (v,z)) := by
  have hs := ((coeff.directionalTerm_summable v hv z 1).add
    ((coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I)).mul_left (1/2:ℂ)
  apply hs.congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma term_cusp_bound (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.term h (v,z)‖≤C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,mul_nonneg hC (cubicBesselUpperAway_pos delta hdelta).le,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hav ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [coeff.term_bessel h hh v hv z,norm_mul,norm_mul,norm_mul,
    breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*v*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcoeff h hh) hv.le)
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*cubicBesselUpperAway delta)*v*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*v)/2=
        -(4*Real.pi*‖cuspFrequency h‖*v/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hav (mul_pos Real.pi_pos hr).le]

lemma directionalTerm_cusp_majorant (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.directionalTerm h v z direction‖≤
        (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.term_cusp_bound a ha
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    simp only [directionalTerm,term,ite_true,mul_zero,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
      Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
      (show 0≤Real.pi*v/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
    unfold residualCuspDecayRate
    nlinarith
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma directionalSeries_cusp_decay (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hbound⟩ := coeff.directionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem fullFunction_wirtingerBar_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma spatialComplexSplit_differentiable : Differentiable ℝ spatialComplexSplit := by
  change Differentiable ℝ (fun p : EuclideanSpatial => (p 2,(p 0:ℂ)+(p 1:ℂ)*Complex.I))
  fun_prop

lemma spatialComplexSplit_symm_differentiable : Differentiable ℝ spatialComplexSplit.symm := by
  change Differentiable ℝ (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  have hlin := (WithLp.linearEquiv 2 ℝ (Fin 3→ℝ)).symm.toContinuousLinearMap.differentiable
  have hcoords : Differentiable ℝ (fun q : ℝ × ℂ => ![q.2.re,q.2.im,q.1]) := by
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.re)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.im)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.1)
      fun_prop
  exact hlin.comp hcoords

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_euclidean_differentiableAt (constant : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    DifferentiableAt ℝ (fun q : EuclideanSpatial => coeff.fullFunction constant (euclideanToHyperbolic q)) p := by
  have hh := (coeff.fullFunction_cusp_differentiableAt constant (spatialComplexSplit p) hp).comp p
    spatialComplexSplit_differentiable.differentiableAt
  simpa only [Function.comp_def,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using hh

lemma fullFunction_translate_cusp_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (g • cuspCoordinateLift q)) p := by
  have hx : 0<(spatialComplexSplit.symm p) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hp
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g (spatialComplexSplit.symm p) hx
  have hh := ((coeff.fullFunction_euclidean_differentiableAt constant
    (euclideanAction g (spatialComplexSplit.symm p)) (euclideanAction_positive _ _)).comp _
      hA.differentiableAt).comp p spatialComplexSplit_symm_differentiable.differentiableAt
  simpa only [Function.comp_def,euclideanAction,euclideanToHyperbolic_coordinates,cuspCoordinateLift] using hh

lemma fullFunction_translate_split_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (g • cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_translate_cusp_differentiableAt constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (g • cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_differentiableAt
    ((3*(Real.pi:ℂ))*constantArithmeticResidue) g p hp

lemma cubicSourceResidualFunction_split_differentiableAt (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (cuspCoordinateLift (q.2,q.1))) p := by
  simpa only [one_smul] using cubicSourceResidualFunction_translate_split_differentiableAt 1 p hp

lemma cubicSourceResidualFunction_wirtingerBar (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*sourceBesselCoefficients.term h (v,z) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar _ v hv z

lemma cubicSourceResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar_cusp_decay _ a ha

end

local notation "O" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_wirtingerZ (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1-
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma horizontalWirtingerBar_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => star (f w)) z=star (horizontalWirtingerZ f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp []

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_wirtingerZ (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*cuspFrequency h)*coeff.term h (v,z) := by
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI]
  have hs1 := coeff.directionalTerm_summable v hv z 1
  have hsI := (coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_sub hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtingerZ (cuspFrequency h)

lemma fullFunction_wirtingerZ_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_wirtingerZ (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*cuspFrequency h)*sourceBesselCoefficients.term h (v,z) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ _ v hv z

lemma cubicSourceResidualFunction_wirtingerZ_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ_cusp_decay _ a ha

def cubicSourceConjugateFunction (w : HyperbolicSpace) : ℂ := star (cubicSourceResidualFunction w)

lemma cubicSourceConjugateFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceConjugateFunction (g • cuspCoordinateLift (q.2,q.1))) p :=
  (cubicSourceResidualFunction_translate_split_differentiableAt g p hp).star

lemma cubicSourceConjugateFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceConjugateFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerZ_cusp_decay a ha
  refine ⟨C,hC,?_⟩
  intro v hv z hav
  simpa only [cubicSourceConjugateFunction,horizontalWirtingerBar_star,norm_star] using hbound v hv z hav

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma horizontalWirtingerBar_translate (f : ℂ→ℂ) (a : ℂ) :
    horizontalWirtingerBar (fun z=>f (z+a)) 0=horizontalWirtingerBar f a := by
  unfold horizontalWirtingerBar
  simp only [zero_add]
  have h1 : (fun t : ℝ=>f ((t:ℂ)+a))=(fun t : ℝ=>f (a+(t:ℂ))) := by
    funext t
    rw [add_comm]
  have hI : (fun t : ℝ=>f ((t:ℂ)*Complex.I+a))=(fun t : ℝ=>f (a+(t:ℂ)*Complex.I)) := by
    funext t
    rw [add_comm]
  rw [h1,hI]

lemma cuspDerivative_of_transform (f : HyperbolicSpace→ℂ) (g H : SL(2,ℂ))
    (κ : ℂ) (htransform : ∀w,f (g•w)=κ*f (H•w)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v)
    (hD : DifferentiableAt ℝ
      (fun q : ℂ × ℝ=>f (H•cuspCoordinateLift (q.2,q.1)))
      (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))) :
    horizontalWirtingerBar (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)=
      (κ*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  let FH : ℂ × ℝ→ℂ := fun q=>f (H•cuspCoordinateLift (q.2,q.1))
  let base : ℂ × ℝ := (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))
  let D := fderiv ℝ FH base
  have hF : HasFDerivAt FH D base := hD.hasFDerivAt
  have hscaled : HasFDerivAt (fun q=>κ*FH q) (κ • D) base := hF.const_mul κ
  have he := inverse_cusp_wirtingerBar (g 1 0) (g 1 1) v hc hv
    (fun q=>κ*FH q) (κ • D) hscaled
  have hline : (fun z=>κ*FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))=
      (fun z=>f (upperPoint (z+g 0 0/g 1 0) v hv)) := by
    funext z
    have ht := htransform (g⁻¹•upperPoint (z+g 0 0/g 1 0) v hv)
    rw [smul_inv_smul,inverse_cusp_action g hc v hv z] at ht
    change κ*f (H•cuspCoordinateLift
      ((inverseCuspCoordinates (g 1 0) (g 1 1) v z).2,
       (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1))=_
    rw [cuspCoordinateLift_positive _ _ (inverseCuspCoordinates_height_pos _ _ _ _ hc hv)]
    exact ht.symm
  rw [hline] at he
  have hshift := horizontalWirtingerBar_translate (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)
  rw [hshift] at he
  have hz := horizontalWirtingerZ_eq_fderiv FH D (-g 1 1/g 1 0) (1/(‖g 1 0‖^2*v)) hF
  have hFH : (fun z=>FH (z,1/(‖g 1 0‖^2*v)))=
      (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity))) := by
    funext z
    exact congrArg (fun w=>f (H•w)) (cuspCoordinateLift_positive _ _ (by positivity))
  rw [hFH] at hz
  rw [hz]
  rw [he]
  simp only [_root_.smul_apply,smul_eq_mul]
  ring

lemma cubicSourceResidualFunction_levelThree (G : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (complexMatrix G•w)=
      CubicKubota.complexCharacter G*cubicSourceResidualFunction w := by
  have hh := cubicSourceResidualFunction_automorphy (CubicKubota.sourceLevelInclusion G) w
  change cubicSourceResidualFunction (complexMatrix G•w)=
    CubicKubota.levelTwoComplexCharacter ⟨G.val,CubicKubota.levelThree_le_levelTwo G.property⟩*
      cubicSourceResidualFunction w at hh
  rw [CubicKubota.levelTwoComplexCharacter_restrict] at hh
  exact hh

lemma cubicSourceConjugateFunction_levelThree (G : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicSourceConjugateFunction (complexMatrix G•w)=
      star (CubicKubota.complexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_levelThree,star_mul]
  ring

theorem cubicSourceResidualFunction_cuspDerivative (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceResidualFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (CubicKubota.complexCharacter G*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceResidualFunction (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceResidualFunction g H
    (CubicKubota.complexCharacter G) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceResidualFunction_levelThree]
  · exact cubicSourceResidualFunction_translate_split_differentiableAt H _ (by positivity)

theorem cubicSourceConjugateFunction_cuspDerivative (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (CubicKubota.complexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (CubicKubota.complexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelThree]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0282

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift
Source SHA256: 58bf5cc6eea4e4cbb530518eab4067c296833000fbd13ef3cc603a4faa727a7f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0283


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

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

lemma gaussian_regulator_norm (ε σ t : ℝ) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖=Real.exp (ε*(σ^2-t^2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma gaussian_regulator_norm_le (ε σ t : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖≤Real.exp (σ^2) := by
  rw [gaussian_regulator_norm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg σ,sq_nonneg t,mul_nonneg hε0 (sq_nonneg t),
    mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg σ)]

def gaussianRegulatorSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma gaussianRegulatorSequence_pos (n : ℕ) : 0<gaussianRegulatorSequence n := by
  unfold gaussianRegulatorSequence
  positivity

lemma gaussianRegulatorSequence_le_one (n : ℕ) : gaussianRegulatorSequence n≤1 := by
  unfold gaussianRegulatorSequence
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma gaussianRegulatorSequence_tendsto : Tendsto gaussianRegulatorSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem gaussian_regulator_integral_tendsto (g : ℝ→ℂ) (hg : Integrable g) (σ : ℝ) :
    Tendsto (fun n : ℕ=>∫t : ℝ,
      Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)*g t)
      atTop (𝓝 (∫t : ℝ,g t)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ=>Real.exp (σ^2)*‖g t‖)
  · intro n
    have hc : Continuous (fun t : ℝ=>
        Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    exact Filter.Eventually.of_forall (fun t=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (gaussian_regulator_norm_le _ σ t (gaussianRegulatorSequence_pos n).le
          (gaussianRegulatorSequence_le_one n)) (norm_nonneg _))
  · filter_upwards with t
    have hε : Tendsto (fun n : ℕ=>(gaussianRegulatorSequence n:ℂ)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def,Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp gaussianRegulatorSequence_tendsto
    have he := (Complex.continuous_exp.tendsto 0).comp
      (by simpa only [zero_mul] using hε.mul_const (((σ:ℂ)+t*Complex.I)^2))
    simpa only [Function.comp_def,Complex.exp_zero,one_mul] using he.mul_const (g t)

lemma rpow_between_endpoints (y a b σ : ℝ) (hy : 0<y) (ha : a≤σ) (hb : σ≤b) :
    y^σ≤y^a+y^b := by
  by_cases h1 : 1≤y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

theorem mellin_uniform_strip_bound (f : ℝ→ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,a≤s.re→s.re≤b→‖mellin f s‖≤C := by
  let B : ℝ→ℝ := fun y=>‖(y:ℂ)^((a:ℂ)-1)*f y‖+‖(y:ℂ)^((b:ℂ)-1)*f y‖
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact ha.norm.add hb.norm
  refine ⟨∫y in Set.Ioi 0,B y,integral_nonneg (fun y=>add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0<y at hy
  have hp := rpow_between_endpoints y (a-1) (b-1) (s.re-1) hy (by linarith) (by linarith)
  change ‖(y:ℂ)^(s-1)*f y‖≤B y
  dsimp only [B]
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

end VerticalContourShift

namespace GaussianMoment

lemma gaussian_le_inverse_quadratic (c t:ℝ) (hc:0<c) :
    Real.exp (-c*t^2)≤(1+2/c)/(1+t^2) := by
  have h0:Real.exp (-c*t^2)≤1:=by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg t]
  have h1:t^2*Real.exp (-c*t^2)≤2/c:=by
    have hm:=gaussian_moment_term_bound (t^2) c (sq_nonneg t) hc
    have he:Real.exp (-(c*t^2/2))≤1:=by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg t]
    exact hm.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (div_nonneg (by norm_num) hc.le))
  apply (le_div_iff₀ (by positivity : 0<1+t^2)).mpr
  nlinarith

lemma linear_height_young (A ε t:ℝ) (hε:0<ε) :
    A*|t|≤ε*t^2/2+A^2/(2*ε) := by
  have hs:0≤ε^2*t^2-2*ε*A*|t|+A^2:=by
    calc
      0≤(ε*|t|-A)^2:=sq_nonneg _
      _=ε^2*t^2-2*ε*A*|t|+A^2:=by rw [sub_sq,mul_pow,sq_abs];ring
  apply le_of_mul_le_mul_left (a := 2*ε) ?_
    (mul_pos (by norm_num : (0:ℝ)<2) hε)
  calc
    2*ε*(A*|t|)≤ε^2*t^2+A^2:=by nlinarith [hs]
    _=2*ε*(ε*t^2/2+A^2/(2*ε)):=by field_simp

theorem gaussian_regulator_strip_bound (a b A B ε:ℝ) (hB:0≤B) (hε:0<ε)
    (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|))
    (σ t:ℝ) (hσ:σ∈Set.Icc a b) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤
      (B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε))/(1+t^2) := by
  let R:ℝ:=max |a| |b|
  have hR:0≤R:=le_trans (abs_nonneg a) (le_max_left _ _)
  have hsabs:|σ|≤R:=abs_le_max_abs_abs hσ.1 hσ.2
  have hs:σ^2≤R^2:=by
    calc
      _=|σ|^2:=(sq_abs σ).symm
      _≤R^2:=pow_le_pow_left₀ (abs_nonneg σ) hsabs 2
  have hre:((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2).re=ε*(σ^2-t^2):=by
    simp [pow_two,Complex.mul_re,Complex.mul_im]

  have hE:ε*(σ^2-t^2)+A*|t|≤
      (ε*R^2+A^2/(2*ε))-(ε/2)*t^2:=by
    have hy:=linear_height_young A ε t hε
    nlinarith
  have hg:=gaussian_le_inverse_quadratic (ε/2) t (by positivity)
  have hg':Real.exp (-(ε/2)*t^2)≤(1+4/ε)/(1+t^2):=by
    convert hg using 1 ;field_simp ;ring
  rw [norm_mul,Complex.norm_exp,hre]
  calc
    _≤Real.exp (ε*(σ^2-t^2))*(B*Real.exp (A*|t|)):=
      mul_le_mul_of_nonneg_left (hf σ hσ t) (Real.exp_pos _).le
    _=B*Real.exp (ε*(σ^2-t^2)+A*|t|):=by rw [Real.exp_add];ring
    _≤B*Real.exp ((ε*R^2+A^2/(2*ε))-(ε/2)*t^2):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hB
    _=(B*Real.exp (ε*R^2+A^2/(2*ε)))*Real.exp (-(ε/2)*t^2):=by
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,neg_mul]
      ring
    _≤(B*Real.exp (ε*R^2+A^2/(2*ε)))*((1+4/ε)/(1+t^2)):=
      mul_le_mul_of_nonneg_left hg' (mul_nonneg hB (Real.exp_pos _).le)
    _=_:=by dsimp only [R];ring

theorem gaussian_regulator_strip_decay (a b A B ε:ℝ) (_hab:a≤b) (_hA:0≤A)
    (hB:0≤B) (hε:0<ε) (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|)) :
    ∃K:ℝ,0≤K ∧ ∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤K/(1+t^2) := by
  refine ⟨B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε),by positivity,?_⟩
  intro σ hσ t
  exact gaussian_regulator_strip_bound a b A B ε hB hε f hf σ t hσ

end GaussianMoment

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

theorem integral_eq_of_exponential_strip_growth
    (f : ℂ→ℂ) (a b A B : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B)
    (hdiff : ∀z : ℂ,a≤z.re→z.re≤b→DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)))
    (hb : Integrable (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)))
    (hbound : ∀σ∈Set.Icc a b,∀t : ℝ,‖f ((σ:ℂ)+t*Complex.I)‖≤B*Real.exp (A*|t|)) :
    (∫t : ℝ,f ((a:ℂ)+t*Complex.I))=∫t : ℝ,f ((b:ℂ)+t*Complex.I) := by
  let F : ℕ→ℂ→ℂ := fun n z=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)*f z
  have hreg (n : ℕ) : Continuous (fun z : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)) := by
    fun_prop
  have hint (n : ℕ) (σ : ℝ) (hσ : Integrable (fun t : ℝ=>f ((σ:ℂ)+t*Complex.I))) :
      Integrable (fun t : ℝ=>F n ((σ:ℂ)+t*Complex.I)) := by
    apply hσ.bdd_mul (c:=Real.exp (σ^2))
    · exact ((hreg n).comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t=>gaussian_regulator_norm_le _ σ t
        (gaussianRegulatorSequence_pos n).le (gaussianRegulatorSequence_le_one n))
  have heq (n : ℕ) :
      (∫t : ℝ,F n ((a:ℂ)+t*Complex.I))=∫t : ℝ,F n ((b:ℂ)+t*Complex.I) := by
    obtain ⟨K,hK,hdec⟩ := GaussianMoment.gaussian_regulator_strip_decay a b A B
      (gaussianRegulatorSequence n) hab hA hB (gaussianRegulatorSequence_pos n) f hbound
    apply integral_eq_of_strip_decay (F n) a b K hab
    · intro z hza hzb
      have hg : Differentiable ℂ (fun w : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*w^2)) := by
        fun_prop
      exact hg.differentiableAt.mul (hdiff z hza hzb)
    · exact hint n a ha
    · exact hint n b hb
    · exact hdec
  have hleft := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)) ha a
  have hright := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)) hb b
  change Tendsto (fun n=>∫t : ℝ,F n ((a:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((a:ℂ)+t*Complex.I))) at hleft
  change Tendsto (fun n=>∫t : ℝ,F n ((b:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((b:ℂ)+t*Complex.I))) at hright
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end VerticalContourShift

namespace CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

lemma norm_Gamma_le_real (z : ℂ) (hz : 0<z.re) :
    ‖Complex.Gamma z‖≤Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖≤Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ ‖Complex.exp (-z*Complex.I)‖+‖Complex.exp (z*Complex.I)‖ := norm_sub_le _ _
    _ = Real.exp z.im+Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _)) (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = _ := by ring

lemma Gamma_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im≠0) : Complex.Gamma z≠0 := by
  apply Complex.Gamma_ne_zero
  intro n he
  apply hz
  have h:=congrArg Complex.im he
  simpa using h

lemma inverse_Gamma_reflection (z : ℂ) (hz : z.im≠0) :
    (Complex.Gamma z)⁻¹=Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
  have hg:=Gamma_ne_zero_of_im_ne_zero z hz
  have hh:=Gamma_ne_zero_of_im_ne_zero (1-z) (by simpa using hz)
  have hp : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin (Real.pi*z)≠0 := by
    intro hs
    have he:=Complex.Gamma_mul_Gamma_one_sub z
    rw [hs,div_zero] at he
    exact (mul_ne_zero hg hh) he
  apply mul_left_cancel₀ hg
  rw [mul_inv_cancel₀ hg]
  symm
  calc
    _ = (Complex.Gamma z*Complex.Gamma (1-z))*Complex.sin (Real.pi*z)/Real.pi := by ring
    _ = 1 := by
      rw [Complex.Gamma_mul_Gamma_one_sub,div_mul_cancel₀ _ hs,div_self hp]

lemma inverse_Gamma_norm_of_left (z : ℂ) (hz : z.re<1) (hi : z.im≠0) :
    ‖(Complex.Gamma z)⁻¹‖≤
      (Real.Gamma (1-z.re)/Real.pi)*Real.exp (Real.pi*|z.im|) := by
  rw [inverse_Gamma_reflection z hi,norm_div,norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hgamma:=norm_Gamma_le_real (1-z) (by simp;linarith)
  have hsin:=norm_sin_le_exp_abs_im (Real.pi*z)
  simp only [Complex.sub_re,Complex.one_re] at hgamma
  have him : |((Real.pi:ℂ)*z).im|=Real.pi*|z.im| := by
    simp [abs_mul]
  rw [him] at hsin
  calc
    _ ≤ (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|))/Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul hgamma hsin (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
        Real.pi_pos.le
    _ = _ := by ring

lemma inverse_Gamma_norm_le_shift_left (z : ℂ) (n : ℕ) (hi : 1≤|z.im|) :
    ‖(Complex.Gamma z)⁻¹‖≤‖(Complex.Gamma (z-n))⁻¹‖ := by
  have he:=congrArg norm (CubicReflectionKernel.inverse_Gamma_shift (z-n) n)
  simp only [sub_add_cancel,norm_mul] at he
  have hprod : 1≤‖∏k∈Finset.range n,(z-(n:ℂ)+k)‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod₀
    intro k hk
    calc
      1 ≤ |z.im| := hi
      _ = |(z-(n:ℂ)+k).im| := by simp
      _ ≤ _ := Complex.abs_im_le_norm _
  rw [he]
  exact le_mul_of_one_le_left (norm_nonneg _) hprod

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀x∈Set.Icc a b,Real.Gamma x≤C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx=>ha.trans_le hx.1)
  obtain ⟨C,hC⟩:=(isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

lemma inverse_Gamma_compact_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t∈Set.Icc (-1:ℝ) 1,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C := by
  have hc : Continuous (fun p : ℝ×ℝ=>
      ‖(Complex.Gamma ((p.1:ℂ)+p.2*Complex.I))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm
  obtain ⟨C,hC⟩:=((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))).bddAbove_image hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro σ hσ t ht
  exact (hC ⟨(σ,t),⟨hσ,ht⟩,rfl⟩).trans (by linarith [le_abs_self C])

theorem inverse_Gamma_strip_exp_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t : ℝ,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C*Real.exp (Real.pi*|t|) := by
  obtain ⟨n,hn⟩:=exists_nat_gt b
  obtain ⟨Cg,hCg,hg⟩:=real_Gamma_compact_bound ((n:ℝ)+1-b) ((n:ℝ)+1-a) (by linarith)
  obtain ⟨Cc,hCc,hc⟩:=inverse_Gamma_compact_strip_bound a b
  refine ⟨Cc+Cg/Real.pi,by positivity,?_⟩
  intro σ hσ t
  have hexp : 1≤Real.exp (Real.pi*|t|) := Real.one_le_exp (by positivity)
  by_cases ht:|t|≤1
  · have hsmall:=hc σ hσ t (abs_le.mp ht)
    calc
      _ ≤ Cc := hsmall
      _ ≤ Cc+Cg/Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        le_mul_of_one_le_right (by positivity) hexp
  · have ht1 : 1 < |t| :=lt_of_not_ge ht
    have ht0 : t≠0 := by intro ht0;subst t;norm_num at ht1
    let z : ℂ := (σ:ℂ)+t*Complex.I
    let w : ℂ := z-n
    have hw : w.re<1 := by
      dsimp [w,z]
      simp only [Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      linarith [hσ.2]
    have hwi : w.im≠0 := by simpa [w,z] using ht0
    have he : 1-w.re=(n:ℝ)+1-σ := by simp [w,z];ring
    have hi : w.im=t := by simp [w,z]
    have hbound:=inverse_Gamma_norm_of_left w hw hwi
    rw [he,hi] at hbound
    have hgbound:=hg ((n:ℝ)+1-σ) ⟨by linarith [hσ.2],by linarith [hσ.1]⟩
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ :=
        inverse_Gamma_norm_le_shift_left z n (by simpa [z] using ht1.le)
      _ ≤ (Real.Gamma ((n:ℝ)+1-σ)/Real.pi)*Real.exp (Real.pi*|t|) := hbound
      _ ≤ (Cg/Real.pi)*Real.exp (Real.pi*|t|) := by gcongr
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le) (Real.exp_pos _).le

theorem inverse_Gamma_strip_exp_bound_complex (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀z : ℂ,z.re∈Set.Icc a b →
      ‖(Complex.Gamma z)⁻¹‖≤C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨C,hC,hb⟩:=inverse_Gamma_strip_exp_bound a b
  refine ⟨C,hC,?_⟩
  intro z hz
  simpa only [Complex.re_add_im] using hb z.re hz z.im

theorem inverse_cubic_Gamma_pair_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖(Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹‖≤
        C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨C1,hC1,h1⟩:=inverse_Gamma_strip_exp_bound_complex (a+1/3) (b+1/3)
  obtain ⟨C2,hC2,h2⟩:=inverse_Gamma_strip_exp_bound_complex (a+2/3) (b+2/3)
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro s hs
  have hb1:=h1 (s+1/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  have hb2:=h2 (s+2/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  norm_num at hb1 hb2
  rw [mul_inv_rev,norm_mul,norm_inv,norm_inv]
  calc
    _ ≤ (C2*Real.exp (Real.pi*|s.im|))*(C1*Real.exp (Real.pi*|s.im|)) :=
      mul_le_mul hb2 hb1 (by positivity) (by positivity)
    _ = C1*C2*Real.exp (2*Real.pi*|s.im|) := by
      rw [show 2*Real.pi*|s.im|=Real.pi*|s.im|+Real.pi*|s.im| by ring,Real.exp_add]
      ring

end CubicGammaExponential

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma cubic_bessel_mellin_norm_scale (s : ℂ) (r : ℝ) (hr : 0<r) :
    (∫v : ℝ in Set.Ioi 0,‖(v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*r*v)‖)=
    r^(-(2*s.re+1))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  let g : ℝ→ℝ := fun v=>‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖
  have hp (v : ℝ) (hv : 0<v) :
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*r*v)‖=
        r^(-(2*s.re))*g (r*v) := by
    dsimp only [g]
    rw [norm_mul,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hr hv)]
    simp only [show (2*s).re=2*s.re by simp]
    rw [Real.mul_rpow hr.le hv.le]
    rw [show 4*Real.pi*r*v=4*Real.pi*(r*v) by ring]
    have hc : r^(-(2*s.re))*r^(2*s.re)=1 := by
      rw [←Real.rpow_add hr]
      simp
    linear_combination -(v^(2*s.re)*‖schlafliBesselK (1/3) (4*Real.pi*(r*v))‖)*hc
  calc
    _=∫v : ℝ in Set.Ioi 0,r^(-(2*s.re))*g (r*v) :=
      setIntegral_congr_fun measurableSet_Ioi hp
    _=r^(-(2*s.re))*(r⁻¹*(∫v : ℝ in Set.Ioi 0,g v)) := by
      rw [integral_const_mul,integral_comp_mul_left_Ioi g 0 hr]
      simp
    _=_ := by
      rw [←mul_assoc,←Real.rpow_neg_one,←Real.rpow_add hr]
      congr 2
      ring

lemma weighted_cubic_bessel_integral_norm (s : ℂ) (freq a : ℂ) (hf : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,‖a*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v))‖)=
    (‖a‖*‖freq‖^(-(2*s.re+1)))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  simp only [norm_mul,integral_const_mul]
  rw [←integral_const_mul]
  have h:=cubic_bessel_mellin_norm_scale s ‖freq‖ (norm_pos_iff.mpr hf)
  simp only [norm_mul] at h
  rw [integral_const_mul,h]
  ring

theorem cubic_bessel_series_mellin {α : Type*} [Countable α]
    (freq a : α→ℂ) (hf : ∀i,freq i≠0) (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*‖freq i‖^(-(2*s.re+1)))) :
    (∫v : ℝ in Set.Ioi 0,∑'i,a i*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v)))=
    ∑'i,a i*(((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
      ((4*Real.pi*‖freq i‖:ℝ):ℂ)^(2*s+1)) := by
  have hi (i : α) := (source_cubic_bessel_mellin_integrable s (freq i) hs (hf i)).const_mul (a i)
  have hsum : Summable (fun i=>∫v : ℝ in Set.Ioi 0,
      ‖a i*((v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v))‖) := by
    simp only [weighted_cubic_bessel_integral_norm s _ _ (hf _)]
    exact ha.mul_right _
  rw [←integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_congr
  intro i
  rw [integral_const_mul,source_cubic_bessel_mellin s (freq i) hs (hf i)]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma positive_sqrt_cpow_twice (r : ℝ) (hr : 0<r) (s : ℂ) :
    (Real.sqrt r:ℂ)^(2*s+1)=(r:ℂ)^(s+1/2) := by
  have ha : Complex.arg (Real.sqrt r:ℂ)=0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg r)
  have h := Complex.cpow_nat_mul' (x:=(Real.sqrt r:ℂ)) (n:=2)
    (by simpa only [ha,mul_zero] using (neg_lt_zero.mpr Real.pi_pos))
    (by simpa only [ha,mul_zero] using Real.pi_pos.le) (s+1/2)
  have hs : (Real.sqrt r:ℂ)^2=(r:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt hr.le]
  norm_num only at h
  simpa only [hs,show (2:ℂ)*(s+1/2)=2*s+1 by ring] using h

lemma radial_bessel_coefficient_norm (r q σ : ℝ) (hr : 0<r) (hq : 0<q) (a : ℂ) :
    ‖a*(r:ℂ)‖*‖((q*Real.sqrt r:ℝ):ℂ)‖^(-(2*σ+1))=
      q^(-(2*σ+1))*(‖a‖*r^(1/2-σ)) := by
  rw [norm_mul,Complex.norm_of_nonneg hr.le,
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr hr)).le,
    Real.mul_rpow hq.le (Real.sqrt_nonneg r),Real.sqrt_eq_rpow,
    ←Real.rpow_mul hr.le]
  have hp : r*r^((1/2)*(-(2*σ+1)))=r^(1/2-σ) := by
    calc
      _=r^1*r^((1/2)*(-(2*σ+1))) := by rw [Real.rpow_one]
      _=r^(1+(1/2)*(-(2*σ+1))) := (Real.rpow_add hr _ _).symm
      _=_ := by congr 1;ring
  calc
    _=q^(-(2*σ+1))*(‖a‖*(r*r^((1/2)*(-(2*σ+1))))) := by ring
    _=_ := by rw [hp]

lemma radial_bessel_coefficient_identity (r q : ℝ) (hr : 0<r) (hq : 0<q)
    (a B s : ℂ) :
    (a*(r:ℂ))*(B/((q*Real.sqrt r:ℝ):ℂ)^(2*s+1))=
      (B/(q:ℂ)^(2*s+1))*(a*(r:ℂ)^(1/2-s)) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le (Real.sqrt_nonneg r),
    positive_sqrt_cpow_twice r hr s]
  have hp : (r:ℂ)/(r:ℂ)^(s+1/2)=(r:ℂ)^(1/2-s) := by
    have h := Complex.cpow_sub (1:ℂ) (s+1/2) (Complex.ofReal_ne_zero.mpr hr.ne')
    rw [Complex.cpow_one] at h
    simpa only [show (1:ℂ)-(s+1/2)=1/2-s by ring] using h.symm
  calc
    _=(B/(q:ℂ)^(2*s+1))*(a*((r:ℂ)/(r:ℂ)^(s+1/2))) := by ring
    _=_ := by rw [hp]

def radialBesselProfile {α : Type*} (r : α→ℝ) (a : α→ℂ) (q v : ℝ) : ℂ :=
  ∑'i,(a i*(r i:ℂ))*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*q*Real.sqrt (r i)*v)

theorem radialBesselProfile_mellin {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ) (q : ℝ) (hq : 0<q)
    (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*(r i)^(1/2-s.re))) :
    mellin (radialBesselProfile r a q) (2*s)=
      (((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*q:ℝ):ℂ)^(2*s+1))*(∑'i,a i*(r i:ℂ)^(1/2-s)) := by
  let f : α→ℂ := fun i=>((q*Real.sqrt (r i):ℝ):ℂ)
  have hf (i : α) : f i≠0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hq (Real.sqrt_pos.mpr (hr i))).ne'
  have has : Summable (fun i=>‖a i*(r i:ℂ)‖*‖f i‖^(-(2*s.re+1))) := by
    simp only [f,radial_bessel_coefficient_norm _ q s.re (hr _) hq]
    exact ha.mul_left _
  have hid := cubic_bessel_series_mellin f (fun i=>a i*(r i:ℂ)) hf s hs has
  calc
    _=(∫v : ℝ in Set.Ioi 0,∑'i,(a i*(r i:ℂ))*((v:ℂ)^(2*s)*
        schlafliBesselK (1/3) (4*Real.pi*‖f i‖*v))) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only [radialBesselProfile]
      simp only [smul_eq_mul]
      rw [←tsum_mul_left]
      apply tsum_congr
      intro i
      have hp : (v:ℂ)^(2*s-1)*(v:ℂ)=(v:ℂ)^(2*s) := by
        calc
          _=(v:ℂ)^(2*s-1)*(v:ℂ)^1 := by rw [Complex.cpow_one]
          _=(v:ℂ)^((2*s-1)+1) :=
            (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
          _=_ := by rw [sub_add_cancel]
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn]
      have hk : 4*Real.pi*q*Real.sqrt (r i)*v=4*Real.pi*(q*Real.sqrt (r i))*v := by ring
      rw [hk]
      change (v:ℂ)^(2*s-1)*_=_
      linear_combination (a i*(r i:ℂ))*schlafliBesselK (1/3) (4*Real.pi*(q*Real.sqrt (r i))*v)*hp
    _=_ := by
      rw [hid,←tsum_mul_left]
      apply tsum_congr
      intro i
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn,show 4*Real.pi*(q*Real.sqrt (r i))=(4*Real.pi*q)*Real.sqrt (r i) by ring]
      exact radial_bessel_coefficient_identity (r i) (4*Real.pi*q) (hr i)
        (by positivity) (a i) _ s

end CubicEisenstein

end

end OAI
end OAIOriginalModule0283

/-! Original module: OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
Source SHA256: 30c6799e21e12a66c29bc84f4f60be9a1dc84b95740f346bf659a788a9a017f3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0284


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

namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def cubeDiagonal (p : Eis) : Matrix (Fin 2) (Fin 2) Eis := !![p^3,0;0,1]

def cubeCorrespondence (p : Eis) : Subgroup (levelThree × levelThree) where
  carrier := {MN | cubeDiagonal p * (MN.1 : SL(2,Eis)).val =
    (MN.2 : SL(2,Eis)).val * cubeDiagonal p}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨M,N⟩ ⟨M',N'⟩ h h'
    change cubeDiagonal p * ((M : SL(2,Eis)).val * (M' : SL(2,Eis)).val) =
      ((N : SL(2,Eis)).val * (N' : SL(2,Eis)).val) * cubeDiagonal p
    calc
      _ = (cubeDiagonal p * (M : SL(2,Eis)).val) * (M' : SL(2,Eis)).val :=
        (Matrix.mul_assoc _ _ _).symm
      _ = ((N : SL(2,Eis)).val * cubeDiagonal p) * (M' : SL(2,Eis)).val := by rw [h]
      _ = (N : SL(2,Eis)).val * (cubeDiagonal p * (M' : SL(2,Eis)).val) := Matrix.mul_assoc _ _ _
      _ = (N : SL(2,Eis)).val * ((N' : SL(2,Eis)).val * cubeDiagonal p) := by rw [h']
      _ = _ := (Matrix.mul_assoc _ _ _).symm
  inv_mem' := by
    rintro ⟨M,N⟩ h
    change cubeDiagonal p * ((M : SL(2,Eis))⁻¹).val =
      ((N : SL(2,Eis))⁻¹).val * cubeDiagonal p
    calc
      _ = (((N : SL(2,Eis))⁻¹).val * ((N : SL(2,Eis)).val * cubeDiagonal p)) *
          ((M : SL(2,Eis))⁻¹).val := by
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = (((N : SL(2,Eis))⁻¹).val * (cubeDiagonal p * (M : SL(2,Eis)).val)) *
          ((M : SL(2,Eis))⁻¹).val := by rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

def cubeCorrespondenceLeft (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.fst levelThree levelThree).comp (cubeCorrespondence p).subtype

def cubeCorrespondenceRight (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.snd levelThree levelThree).comp (cubeCorrespondence p).subtype

lemma cubeCorrespondence_entries (p : Eis) (MN : cubeCorrespondence p) :
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 0 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 0) * p^3 ∧
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 1 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 1) ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 0) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 0) * p^3 ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 1) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 1) := by
  have h := MN.property
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 1) h
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 0) h
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 1) h
  norm_num [cubeDiagonal, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00,h01,h10,h11⟩

lemma cubeCorrespondenceLeft_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hM : x.1.1=y.1.1 := h
  apply Subtype.ext
  apply Prod.ext hM
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.1.symm.trans (by rw [hM]; exact hy.1))
  · exact hx.2.1.symm.trans (by rw [hM]; exact hy.2.1)
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.2.2.1.symm.trans (by rw [hM]; exact hy.2.2.1))
  · exact hx.2.2.2.symm.trans (by rw [hM]; exact hy.2.2.2)

lemma cubeCorrespondenceRight_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceRight p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hN : x.1.2=y.1.2 := h
  apply Subtype.ext
  refine Prod.ext ?_ hN
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.1.trans (by rw [hN]; exact hy.1.symm))
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.2.1.trans (by rw [hN]; exact hy.2.1.symm))
  · exact hx.2.2.1.trans (by rw [hN]; exact hy.2.2.1.symm)
  · exact hx.2.2.2.trans (by rw [hN]; exact hy.2.2.2.symm)

lemma cubeCorrespondence_value (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    value (cubeCorrespondenceLeft p MN) = value (cubeCorrespondenceRight p MN) := by
  have he := cubeCorrespondence_entries p MN
  let M : levelThree := MN.1.1
  let N : levelThree := MN.1.2
  have ha : (M : SL(2,Eis)) 0 0 = (N : SL(2,Eis)) 0 0 :=
    mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
  have hc : (M : SL(2,Eis)) 1 0 = p^3 * (N : SL(2,Eis)) 1 0 :=
    he.2.2.1.trans (mul_comm _ _)
  have hd : (M : SL(2,Eis)) 0 0 * (M : SL(2,Eis)) 1 1 -
      (M : SL(2,Eis)) 0 1 * (M : SL(2,Eis)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,Eis)).property
  have hcop : IsCoprime p ((N : SL(2,Eis)) 0 0) := by
    refine ⟨-(M : SL(2,Eis)) 0 1 * p^2 * (N : SL(2,Eis)) 1 0,
      (M : SL(2,Eis)) 1 1,?_⟩
    rw [ha,hc] at hd
    linear_combination hd
  change symbol ((M : SL(2,Eis)) 1 0) ((M : SL(2,Eis)) 0 0) =
    symbol ((N : SL(2,Eis)) 1 0) ((N : SL(2,Eis)) 0 0)
  rw [ha,hc,symbol_mul_numerator _ _ _ (levelThree_primary N),
    symbol_pow_numerator _ _ (levelThree_primary N),
    symbol_cube_of_isCoprime _ _ (levelThree_primary N) hcop,one_mul]

lemma cubeCorrespondence_character (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    complexCharacter (cubeCorrespondenceLeft p MN) =
      complexCharacter (cubeCorrespondenceRight p MN) := by
  exact congrArg ConcreteTraceCRT.eisEmbedding (cubeCorrespondence_value p hp MN)

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def cubePrincipalLevel (p : Eis) : Subgroup levelThree :=
  ((Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3}))).comp levelThree.subtype).ker

lemma cubePrincipalLevel_entry (p : Eis) (M : cubePrincipalLevel p) (i j : Fin 2) :
    (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) i j-(if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})) ((M.1 : levelThree) : SL(2,Eis)) = 1 := M.property
  have h := congrArg (fun N : SL(2,Eis ⧸ Ideal.span {(3:Eis)*p^3}) => N i j) hm
  change Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})
    (((M.1 : levelThree) : SL(2,Eis)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {(3:Eis)*p^3})) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h

lemma cubePrincipalLevel_finiteIndex (p : Eis) (hp : p ≠ 0) :
    (cubePrincipalLevel p).FiniteIndex := by
  let : Finite (Eis ⧸ Ideal.span {(3:Eis)*p^3}) :=
    finite_quotient_span (mul_ne_zero (by norm_num) (pow_ne_zero 3 hp))
  unfold cubePrincipalLevel
  infer_instance

lemma cubePrincipalLevel_left_mate (p : Eis) (M : cubePrincipalLevel p) :
    ∃ N : levelThree, ((M.1 : levelThree),N) ∈ cubeCorrespondence p := by
  obtain ⟨c,hc⟩ : (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) 1 0 := by
    simpa using cubePrincipalLevel_entry p M 1 0
  let A : SL(2,Eis) := M.1
  let N : SL(2,Eis) := ⟨!![A 0 0,p^3*A 0 1;3*c,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 1 0=(3:Eis)*p^3*c at hc
    rw [hc] at hd
    linear_combination hd⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry M.1 0 0
    · change (3:Eis)∣p^3*A 0 1-0
      simpa using dvd_mul_of_dvd_right (levelThree_upper M.1) (p^3)
    · change (3:Eis)∣3*c-0
      simp
    · exact levelThree_entry M.1 1 1
  refine ⟨⟨N,hN⟩,?_⟩
  change cubeDiagonal p*A.val=N.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,N,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 1 0=(3:Eis)*p^3*c at hc
    change A 1 0=3*c*p^3
    rw [hc]
    ring

lemma cubePrincipalLevel_right_mate (p : Eis) (N : cubePrincipalLevel p) :
    ∃ M : levelThree, (M,(N.1 : levelThree)) ∈ cubeCorrespondence p := by
  obtain ⟨b,hb⟩ : (3:Eis)*p^3 ∣ ((N.1 : levelThree) : SL(2,Eis)) 0 1 := by
    simpa using cubePrincipalLevel_entry p N 0 1
  let A : SL(2,Eis) := N.1
  let M : SL(2,Eis) := ⟨!![A 0 0,3*b;p^3*A 1 0,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 0 1=(3:Eis)*p^3*b at hb
    rw [hb] at hd
    linear_combination hd⟩
  have hM : M∈levelThree := by
    apply (mem_levelThree_iff_entries M).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry N.1 0 0
    · change (3:Eis)∣3*b-0
      simp
    · change (3:Eis)∣p^3*A 1 0-0
      simpa using dvd_mul_of_dvd_right (levelThree_lower N.1) (p^3)
    · exact levelThree_entry N.1 1 1
  refine ⟨⟨M,hM⟩,?_⟩
  change cubeDiagonal p*M.val=A.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,M,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 0 1=(3:Eis)*p^3*b at hb
    change p^3*(3*b)=A 0 1
    rw [hb]
    ring
  · ring

lemma cubePrincipalLevel_le_left_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceLeft p).range := by
  intro M hM
  obtain ⟨N,hN⟩ := cubePrincipalLevel_left_mate p ⟨M,hM⟩
  exact ⟨⟨(M,N),hN⟩,rfl⟩

lemma cubePrincipalLevel_le_right_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceRight p).range := by
  intro N hN
  obtain ⟨M,hM⟩ := cubePrincipalLevel_right_mate p ⟨N,hN⟩
  exact ⟨⟨(M,N),hM⟩,rfl⟩

lemma cubeCorrespondence_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) ∧
    Function.Injective (cubeCorrespondenceRight p) ∧
    (cubeCorrespondenceLeft p).range.FiniteIndex ∧
    (cubeCorrespondenceRight p).range.FiniteIndex := by
  let : (cubePrincipalLevel p).FiniteIndex := cubePrincipalLevel_finiteIndex p hp
  exact ⟨cubeCorrespondenceLeft_injective p hp,cubeCorrespondenceRight_injective p hp,
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_left_range p),
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_right_range p)⟩

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def cubeKernelCorrespondence (p : Eis) : Subgroup (cubeCorrespondence p) :=
  (finiteCubicMultiplier.comp (cubeCorrespondenceLeft p)).ker

def cubeKernelLeft (p : Eis) : cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceLeft p x.1,x.property⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceLeft p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceLeft p) x.1 y.1

lemma cubeKernel_right_mem (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeCorrespondenceRight p x.1 ∈ finiteCubicMultiplier.ker := by
  apply (finiteCubicMultiplier_eq_one _).mpr
  rw [←cubeCorrespondence_character p hp x.1]
  exact (finiteCubicMultiplier_eq_one _).mp x.property

def cubeKernelRight (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceRight p x.1,cubeKernel_right_mem p hp x⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceRight p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceRight p) x.1 y.1

lemma cubeKernelLeft_range (p : Eis) :
    (cubeKernelLeft p).range =
      (cubeCorrespondenceLeft p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      change finiteCubicMultiplier (cubeCorrespondenceLeft p x)=1
      rw [hx]
      exact y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

lemma cubeKernelRight_range (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRight p hp).range =
      (cubeCorrespondenceRight p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      apply (finiteCubicMultiplier_eq_one _).mpr
      rw [cubeCorrespondence_character p hp x,hx]
      exact (finiteCubicMultiplier_eq_one _).mp y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

lemma cubeKernel_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeKernelLeft p) ∧ Function.Injective (cubeKernelRight p hp) ∧
    (cubeKernelLeft p).range.FiniteIndex ∧ (cubeKernelRight p hp).range.FiniteIndex := by
  have hcov := cubeCorrespondence_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro x y h
    apply Subtype.ext
    apply hcov.1
    exact congrArg Subtype.val h
  · intro x y h
    apply Subtype.ext
    apply hcov.2.1
    exact congrArg Subtype.val h
  · rw [cubeKernelLeft_range]
    infer_instance
  · rw [cubeKernelRight_range]
    infer_instance

def cubeKernelLeftGlobal (p : Eis) : cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelLeft p))

def cubeKernelRightGlobal (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelRight p hp))

lemma cubeKernelLeftGlobal_le (p : Eis) :
    (cubeKernelLeftGlobal p).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelLeft p x).1,(cubeKernelLeft p x).property,rfl⟩

lemma cubeKernelRightGlobal_le (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRightGlobal p hp).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelRight p hp x).1,(cubeKernelRight p hp x).property,rfl⟩

private lemma finiteIndex_subtype_image {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] (J : Subgroup H) [J.FiniteIndex] : (J.map H.subtype).FiniteIndex := by
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H:=J))
    (Subgroup.FiniteIndex.index_ne_zero (H:=H))

lemma cubeKernelGlobal_finite_covers (p : Eis) (hp : p ≠ 0) :
    (cubeKernelLeftGlobal p).range.FiniteIndex ∧
    (cubeKernelRightGlobal p hp).range.FiniteIndex := by
  have hcov := cubeKernel_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  have hL : ((cubeKernelLeft p).range.map finiteCubicMultiplier.ker.subtype).FiniteIndex :=
    finiteIndex_subtype_image _ _
  have hR : ((cubeKernelRight p hp).range.map finiteCubicMultiplier.ker.subtype).FiniteIndex :=
    finiteIndex_subtype_image _ _
  constructor
  · rw [cubeKernelLeftGlobal,MonoidHom.range_comp,MonoidHom.range_comp]
    exact finiteIndex_subtype_image _ _
  · rw [cubeKernelRightGlobal,MonoidHom.range_comp,MonoidHom.range_comp]
    exact finiteIndex_subtype_image _ _

lemma cubeKernelGlobal_intertwining (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeDiagonal p * (cubeKernelLeftGlobal p x).val =
      (cubeKernelRightGlobal p hp x).val * cubeDiagonal p := x.1.property

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeArchimedean_correspondence (p : Eis) (hp : p ≠ 0) :
    ∃ g : SL(2,ℂ), g 0 1=0 ∧ g 1 0=0 ∧ g 0 0/g 1 1=eisEmbedding p^3 ∧
      ∀ x : cubeKernelCorrespondence p,
        g*integralComplexMatrix (cubeKernelLeftGlobal p x)=
          integralComplexMatrix (cubeKernelRightGlobal p hp x)*g := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2)
  have hz0 : z≠0 := by
    intro he
    rw [he,zero_pow (by decide)] at hz
    exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hz.symm
  let g : SL(2,ℂ) := ⟨!![z,0;0,z⁻¹],by simp [Matrix.det_fin_two_of,hz0]⟩
  refine ⟨g,rfl,rfl,?_,?_⟩
  · change z/z⁻¹=eisEmbedding p^3
    rw [div_inv_eq_mul,←pow_two,hz]
  · intro x
    have he := cubeCorrespondence_entries p x.1
    have ha : (((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0 =
        (((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0 :=
      mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
    have he00 := congrArg eisEmbedding ha
    have he01 := congrArg eisEmbedding he.2.1
    have he10 := congrArg eisEmbedding he.2.2.1
    have he11 := congrArg eisEmbedding he.2.2.2
    simp only [map_mul,map_pow] at he01 he10
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
        integralComplexMatrix_apply]
    · change z*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0)+0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 0) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0)*z+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 1)*0
      rw [he00]
      ring
    · change z*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 1)+0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 1) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 0)*0+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 0 1)*z⁻¹
      rw [←he01,←hz]
      field_simp
      ring
    · change 0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 0)+z⁻¹*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 0) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 0)*z+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 1)*0
      rw [he10,←hz]
      field_simp
      ring
    · change 0*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 0 1)+z⁻¹*eisEmbedding ((((x.1).1.1 : levelThree) : SL(2,Eis)) 1 1) =
        eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 0)*0+eisEmbedding ((((x.1).1.2 : levelThree) : SL(2,Eis)) 1 1)*z⁻¹
      rw [he11]
      ring

end CubicKubota

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def cuspBarProfile (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerBar (fun w=>f (cuspCoordinateLift (v,w))) z

def cuspZProfile (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerZ (fun w=>f (cuspCoordinateLift (v,w))) z

lemma cuspBarProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspBarProfile f z v=horizontalWirtingerBar (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspBarProfile,cuspCoordinateLift_positive v _ hv]

lemma cuspZProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile f z v=horizontalWirtingerZ (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspZProfile,cuspCoordinateLift_positive v _ hv]

lemma horizontalWirtingerZ_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (f w)) z=star (horizontalWirtingerBar f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp [sub_eq_add_neg]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def directionalSeries (direction : ℂ) (p : ℝ × ℂ) : ℂ :=
  ∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h p.1 p.2 direction

lemma directionalSeries_continuousOn_slab (direction : ℂ) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound a b ha hab direction
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h
    have ht : ContinuousOn (coeff.term h) {p : ℝ × ℂ|p.1∈Set.Icc a b} :=
      (coeff.term_continuousOn h).mono (fun p hp=>ha.trans_le hp.1)
    exact ht.const_mul (horizontalPhaseMultiplier (cuspFrequency h) direction)
  · exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · intro h p hp
    exact hbound h p.1 p.2 hp

lemma directionalSeries_continuousOn (direction : ℂ) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|0<p.1} := by
  intro p hp
  have hclosed := coeff.directionalSeries_continuousOn_slab direction (p.1/2) (2*p.1)
    (by change 0<p.1 at hp;linarith) (by change 0<p.1 at hp;linarith)
  have hnb : {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by change 0<p.1 at hp;linarith)
      (by change 0<p.1 at hp;linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma cuspBarProfile_full_eq (constant z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspBarProfile (coeff.fullFunction constant) z v=
      (1/2:ℂ)*(coeff.directionalSeries 1 (v,z)+Complex.I*coeff.directionalSeries Complex.I (v,z)) := by
  rw [cuspBarProfile_positive _ _ _ hv,horizontalWirtingerBar]
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [h1,hI]
  rfl

lemma cuspZProfile_full_eq (constant z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile (coeff.fullFunction constant) z v=
      (1/2:ℂ)*(coeff.directionalSeries 1 (v,z)-Complex.I*coeff.directionalSeries Complex.I (v,z)) := by
  rw [cuspZProfile_positive _ _ _ hv,horizontalWirtingerZ]
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [h1,hI]
  rfl

lemma cuspBarProfile_continuousOn (constant z : ℂ) :
    ContinuousOn (cuspBarProfile (coeff.fullFunction constant) z) (Set.Ioi 0) := by
  have hd (direction : ℂ) : ContinuousOn (fun v : ℝ=>coeff.directionalSeries direction (v,z)) (Set.Ioi 0) :=
    (coeff.directionalSeries_continuousOn direction).comp
      (continuousOn_id.prodMk continuousOn_const) (fun v hv=>hv)
  apply (continuousOn_const.mul ((hd 1).add (continuousOn_const.mul (hd Complex.I)))).congr
  intro v hv
  exact coeff.cuspBarProfile_full_eq constant z v hv

lemma cuspZProfile_continuousOn (constant z : ℂ) :
    ContinuousOn (cuspZProfile (coeff.fullFunction constant) z) (Set.Ioi 0) := by
  have hd (direction : ℂ) : ContinuousOn (fun v : ℝ=>coeff.directionalSeries direction (v,z)) (Set.Ioi 0) :=
