    exact hT b hb z hz
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ₂ m₂ T hΓ hw hK hell hB hF hH hadm hΨ₂ hb₁ hb₂ hT' hT0
  have hprefix : 0≤Cfirst*Ymax^deltaLoss := mul_nonneg hCfirst (Real.rpow_nonneg hYmax0 _)
  apply hf.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _))

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0192

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
Source SHA256: 1d27c07cfa41e4438dd61f0c6f2de6abc26091f352260eab6d6d1ee2a7771b76
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0193


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def residualScale (Z : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Z/(elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)*
    elementNorm (secondExpansionQuotient p x))

def sourceWeight (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (Z H : ℝ) (x : SecondExpansionData ι) : ℂ :=
  secondNormalizedExpansionWeight p hp hcop hg Ψ m 1 1 ray Z H x *
    (residualScale p Z x : ℂ)⁻¹

theorem sourceWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex) (Z H : ℝ) (x : SecondExpansionData ι)
    (hZ : 0<Z) (hH : 0≤H)
    (hΨG : ‖Ψ (∏i∈x.sourceCommon,p i)‖≤1) (hΨV : ‖Ψ (∏i∈x.overlap,p i)‖≤1) :
    ‖sourceWeight p hp hcop hg Ψ m ray Z H x‖≤
      H*elementNorm (secondExpansionQuotient p x)/Z^2*‖secondRayCoefficient ray‖ := by
  simpa only [sourceWeight,residualScale,elementNorm,secondExpansionScale,expansionSupportData] using
    secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc ∅ ∅ Ψ m 1 1
      (secondExpansionQuotient p x) ray Z H hZ hH x hΨG hΨV

end

theorem initial_source_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
        (x : SecondExpansionData ι) (Z H E V₀ X₀ K : ℝ),
        x.divisor⊆x.sourceCommon → x.frequency≠0 →
        0<Z → 0<E → 0<V₀ → 0<X₀ → 0<K →
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
        let r := secondExpansionQuotient p x
        let X := residualScale p Z x
        let z := Real.log (primeProductNorm p x.overlap*X₀/X)
        let ue := Real.log (elementNorm e/E)
        let uv := Real.log (primeProductNorm p x.overlap/V₀)
        let kap := Real.log (elementNorm (e*x.frequency)/K)
        |z|≤B → |ue|≤B → |uv|≤B → |kap|≤B →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        sourceWeight p hp hcop hg Ψ m ray Z H x *
          postCommonSmoothPair p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
            (m*r) (e*∏i∈x.overlap,p i) (e*x.frequency) (-(e*x.frequency))
            A₁ A₂ W windows z 0 ue uv kap X₀ X₀ (H*K/(E^2*V₀^2*X₀^2)) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A B hA hB h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray x Z H E V₀ X₀ K hE hk hZ hEs hV hX₀ hK
  dsimp only
  intro hz hue huv hkap
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  let r := secondExpansionQuotient p x
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hq : secondMaskQuotient p x.divisor x.sourceCommon hE=r :=
    (secondExpansionQuotient_of_subset p x hE).symm
  have hr : r≠0 := by
    rw [←hq]
    intro hr0
    have hs := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
    rw [hr0,mul_zero] at hs
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hs
  have hX : 0<residualScale p Z x := div_pos hZ
    (mul_pos (SecondPassIntegration.elementNorm_pos e he) (SecondPassIntegration.elementNorm_pos r hr))
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.sourceCommon x.divisor hE F x.overlap Ψ Ψ m 1 1 x.frequency r ray
      (congrArg (fun a:O => Ideal.span {a}) hq) Z H hZ U hUc hUs g₁ g₂ W hU₁ hU₂
  dsimp only at hnorm
  have hnormone : elementNorm (1:O)=1 := by simp [elementNorm]
  have hid' := hid p hp hcop hg 1 E V₀ (residualScale p Z x) X₀ K H
    (by norm_num) hEs hV hX hX₀ hK F x.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      m r 1 1 e x.frequency one_ne_zero he hk hz
      (by simpa only [hnormone,div_one,Real.log_one,abs_zero] using hB) hue huv
      (by simpa only [one_mul] using hkap)
  simp only [one_mul,mul_neg,hnormone,div_one,Real.log_one] at hid'
  have hscale : Z/(‖eisEmbedding e‖^2*‖eisEmbedding r‖^2)=residualScale p Z x := rfl
  rw [hscale,hid'] at hnorm
  rw [hq] at hnorm
  have hgoal := congrArg (fun t:ℂ => ((H:ℂ)*secondSourceCommonCoefficient p hg Ψ m 1 1 x.sourceCommon x.divisor)*t) hnorm
  simp only [secondExpansionSource,Finset.sum_singleton,sourceWeight,
    secondNormalizedExpansionWeight,e,r,mul_assoc] at hgoal ⊢
  exact hgoal

end

open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def sourceElementData (x : SecondExpansionData ι) : ElementDatum where
  divisor := ∏i∈x.divisor,Ideal.span {p i}
  shared := ∏i∈x.overlap,p i
  frequency := x.frequency

def sourceObservation (x : SecondExpansionData ι) : O×O :=
  (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*x.frequency,
   primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*∏i∈x.overlap,p i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceObservation_eq (x : SecondExpansionData ι) :
    sourceObservation p x=elementObservation idealGenerator (sourceElementData p x) := rfl

include hinj in

theorem sourceElementData_injective (r : O) :
    Set.InjOn (sourceElementData p) {x | InSecondQuotientSector p r x} := by
  intro x hx y hy heq
  have hE := congrArg ElementDatum.divisor heq
  have hV := congrArg ElementDatum.shared heq
  have hk := congrArg ElementDatum.frequency heq
  have he : x.divisor=y.divisor := FirstCauchyArithmetic.family_product_injective _ hinj hE
  have hv : x.overlap=y.overlap := by
    apply FirstCauchyArithmetic.family_product_injective _ hinj
    have hh := congrArg (fun a:O => Ideal.span {a}) hV
    simpa only [sourceElementData,FiniteGaussPhase.span_finset_prod] using hh
  apply expansionSupportData_injOn p hinj ∅ ∅ r hx hy
  exact SecondSupportData.ext rfl rfl he hv hk

include hinj in

theorem source_fiber_card_le (r : O) (s : Finset (SecondExpansionData ι))
    (hs : ∀x∈s,InSecondQuotientSector p r x) (y f : O) (hy : y≠0) :
    (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      (idealDivisors (Ideal.span {y})).card := by
  have hmap : (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      ((s.image (sourceElementData p)).filter (fun x => elementObservation idealGenerator x=(y,f))).card := by
    apply Finset.card_le_card_of_injOn (sourceElementData p)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,rfl⟩,?_⟩
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy he
      exact sourceElementData_injective p hinj r (hs x (Finset.mem_filter.mp hx).1)
        (hs y (Finset.mem_filter.mp hy).1) he
  exact hmap.trans (element_fiber_card_le idealGenerator span_idealGenerator _ y f hy)

end

theorem source_weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (sourceObservation p x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P A K hA hK hs hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t (sourceObservation p) w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hyI : (Ideal.span {y.1}:Ideal O)≠0 := by intro hz; exact ht y hy (Ideal.span_singleton_eq_bot.mp hz)
  have hcard : ((s.filter (fun x => sourceObservation p x=y)).card:ℝ)≤C*K^ε := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {y.1})).card:ℝ) := by
        exact_mod_cast source_fiber_card_le p hinj r s hs y.1 y.2 (ht y hy)
      _ ≤ C*(Ideal.absNorm (Ideal.span {y.1}):ℝ)^ε := hdiv _ hyI
      _ ≤ C*K^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hh

theorem source_weighted_cauchy (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P Q : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      ‖∑x∈s,w x*P (sourceObservation p x)*star (Q (sourceObservation p x))‖≤
        A*C*K^ε*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by
  obtain ⟨C,hC,hpool⟩ := source_weighted_energy_pushforward ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P Q A K hA hK hs hmap ht hnorm hw
  have hP := hpool p hinj r s t w P A K hA hK hs hmap ht hnorm hw
  have hQ := hpool p hinj r s t w Q A K hA hK hs hmap ht hnorm hw
  have hD : 0≤A*C*K^ε := by positivity
  apply (DescentWeightedCauchy.weighted_cauchy s w (fun x => P (sourceObservation p x))
    (fun x => Q (sourceObservation p x))).trans
  calc
    _ ≤ Real.sqrt (A*C*K^ε*∑y∈t,‖P y‖^2)*Real.sqrt (A*C*K^ε*∑y∈t,‖Q y‖^2) := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt (A*C*K^ε))^2*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end InitialMeanSquare

namespace CubicEisenstein

section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)
example : InnerProductSpace ℂ EuclideanGradientL2 := inferInstance
example : CompleteSpace EuclideanGradientL2 := inferInstance
abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2

lemma euclideanL2Distribution_injective : Function.Injective euclideanL2Distribution := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker

lemma mem_euclideanWeakGradientGraph (f : EuclideanL2) (g : EuclideanGradientL2) :
    (f,g)∈euclideanWeakGradientGraph ↔ ∀j,
      ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)=euclideanL2Distribution (g j) := by
  change (fun j => ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)-
    euclideanL2Distribution (g j))=0 ↔ _
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

lemma euclideanWeakGradientGraph_unique (x : EuclideanL2 × EuclideanGradientL2)
    (hx : x∈euclideanWeakGradientGraph) (hzero : x.1=0) : x.2=0 := by
  have hh := (mem_euclideanWeakGradientGraph x.1 x.2).mp hx
  apply (WithLp.equiv 2 (Fin 3 → EuclideanL2)).injective
  funext j
  change x.2 j=(0:EuclideanL2)
  apply euclideanL2Distribution_injective
  simpa only [hzero,map_zero,lineDerivOp_zero,WithLp.ofLp_zero,Pi.zero_apply] using (hh j).symm

def euclideanWeakGradient : EuclideanL2 →ₗ.[ℂ] EuclideanGradientL2 :=
  euclideanWeakGradientGraph.toLinearPMap

lemma euclideanWeakGradient_graph : euclideanWeakGradient.graph=euclideanWeakGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ euclideanWeakGradientGraph_unique

theorem euclideanWeakGradient_closed : euclideanWeakGradient.IsClosed := by
  rw [LinearPMap.IsClosed,euclideanWeakGradient_graph]
  exact euclideanGradientEquations.isClosed_ker

lemma schwartz_mem_euclideanWeakGradientGraph (f : 𝓢(EuclideanSpatial,ℂ)) :
    (f.toLp 2 volume,WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} f).toLp 2 volume))∈euclideanWeakGradientGraph := by
  apply (mem_euclideanWeakGradientGraph _ _).mpr
  intro j
  dsimp only [euclideanL2Distribution]
  simp only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq («μ» := volume) f _

theorem euclideanWeakGradient_dense_domain : Dense (euclideanWeakGradient.domain : Set EuclideanL2) := by
  apply (SchwartzMap.denseRange_toLpCLM (E := EuclideanSpatial) (F := ℂ) (p := 2)
    («μ» := volume) (by norm_num)).mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [euclideanWeakGradient_graph]
  exact schwartz_mem_euclideanWeakGradientGraph f

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe
example : InnerProductSpace ℂ EuclideanH1 := inferInstance

def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

lemma euclideanH1Embedding_eq_zero (u : EuclideanH1) (hu : euclideanH1Embedding u=0) : u=0 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (EuclideanL2 × EuclideanGradientL2)).injective
  apply Prod.ext
  · exact hu
  · exact euclideanWeakGradientGraph_unique u.1.ofLp u.2 hu

lemma euclideanH1Embedding_injective : Function.Injective euclideanH1Embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply euclideanH1Embedding_eq_zero
  rw [map_sub,huv,sub_self]

lemma euclideanH1Embedding_dense : DenseRange euclideanH1Embedding := by
  apply euclideanWeakGradient_dense_domain.mono
  intro f hf
  obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
  rw [euclideanWeakGradient_graph] at hg
  refine ⟨⟨WithLp.toLp 2 (f,g),hg⟩,?_⟩
  rfl

lemma euclideanH1_norm_sq (u : EuclideanH1) :
    ‖u‖^2=‖euclideanH1Embedding u‖^2+‖euclideanH1Gradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

end CubicEisenstein

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp

lemma normCharacter_prod {ι : Type*} (p : ι→O) (S : Finset ι)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normCharacter χ (∏i∈S,p i)=χ (Ideal.absNorm (∏i∈S,Ideal.span {p i})) := by
  change χ (Ideal.absNorm (Ideal.span {∏i∈S,p i}))=_
  rw [FiniteGaussPhase.span_finset_prod]

lemma pool_support_product (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    idealSupport F (∏i∈S,i.val)=S := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏i∈S,i.val)≠(0:Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  ext i
  rw [mem_idealSupport_iff,UniqueFactorizationMonoid.mem_normalizedFactors_iff hn]
  simp only [family_prime_dvd_product_iff _ Subtype.val_injective S i,hp,true_and]

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl

def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0

theorem idealRowSum_eq_mobiusRow (F : Finset (Ideal O)) (hF : ∀I∈F,Admissible I)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (z : O) :
    let hFpos := fun I hI => (hF I hI).1
    let hFgood := fun I hI P hP => ((hF I hI).2.2 P hP).1
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowSum F hFpos hFgood χ W z=
      mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
        (selectedIdealTest F W) z := by
  dsimp only
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hP : (fun i:primePool F => Ideal.span {poolPrimary F i})=(fun i:primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  unfold idealRowSum
  rw [sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  unfold mobiusRow
  apply Finset.sum_congr rfl
  intro S hS
  have ht := normCharacter_prod (poolPrimary F) S χ
  simp only [hP] at ht
  by_cases hs : (∏i∈S,i.val)∈F
  · rw [ite_eq_left hs]
    simp only [inputColumn,selectedIdealTest,ite_eq_left hs,mul_one,ht]
    have hm : rowCoprimeMask (fun i => Ideal.span {poolPrimary F i}) S 1=1 := by
      simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
    rw [hm,mul_one]
    simp only [supportMobius,hP,baseChangeWeight,idealSexticRow,pool_support_product]
    ring
  · rw [ite_eq_right hs]
    simp only [inputColumn,selectedIdealTest,ite_eq_right hs,mul_zero,zero_mul]

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def sourceChildEnergy (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑u∈T,‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative)
    u.2 (if rowNegative then -u.1 else u.1)‖^2

def sourceEnergyMagnitude (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑u∈T,(rowMagnitude p hp hcop hg F Ψ m u.2 (if rowNegative then -u.1 else u.1)
    V X testNegative)^2

lemma sourceChildEnergy_le (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (tn rn : Bool) (a b : ℝ) :
    sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn a b≤
      sourceEnergyMagnitude p hp hcop hg F Ψ m T V X tn rn := by
  unfold sourceChildEnergy sourceEnergyMagnitude
  apply Finset.sum_le_sum
  intro u hu
  exact pow_le_pow_left₀ (norm_nonneg _) (fixedRow_norm_le p hp hcop hg F Ψ m _ _ V X a b tn) 2

lemma sourceChildEnergy_continuous (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (tn rn : Bool) (τ σ : Frequency→ℝ)
    (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun q => sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn (τ q) (σ q)) := by
  unfold sourceChildEnergy
  apply continuous_finsetSum
  intro u hu
  exact (fixedRow_continuous p hp hcop hg F Ψ m _ _ V X tn τ σ hτ hσ).norm.pow 2

def sourceGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2)*
    Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)

def sourceFixedMode (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℂ :=
  ∑x∈s,w q x*
    star (fixedChildRow p hp hcop hg F Ψ₁ m (fixedSecondTest p V₁ X₁ q.1 q.2.2 true)
      (sourceObservation p x).2 (sourceObservation p x).1)*
    fixedChildRow p hp hcop hg F Ψ₂ m (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      (sourceObservation p x).2 (-(sourceObservation p x).1)

def integratedSourceMode (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)*
    sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

end

private theorem weighted_conjugate_pair_swap {α : Type*} (s : Finset α)
    (w P Q : α → ℂ) (B X Y : ℝ)
    (h : ‖∑ x ∈ s, w x * P x * star (Q x)‖ ≤ B * X * Y) :
    ‖∑ x ∈ s, w x * star (Q x) * P x‖ ≤ B * (Y * X) := by
  have he : (∑ x ∈ s, w x * star (Q x) * P x) =
      ∑ x ∈ s, w x * P x * star (Q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  exact h.trans_eq (by ring)

theorem integrated_source_transfer (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
      (w : Frequency→SecondExpansionData ι→ℂ) (A K : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
      (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀q,∀x∈s,‖w q x‖≤A) → (∀x∈s,Continuous (fun q => w q x)) →
      ‖integratedSourceMode p hp hcop hg b₁ b₂ b₃ s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖≤
        A*C*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖*
          sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C,hC,hpointwise⟩ := source_weighted_cauchy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hA hK hs hmap hT hnorm hw hwc
  let f := sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂
  let G := sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := sourceChildEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := sourceChildEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀q,0≤G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false)*
    Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀q,G q≤M := by
    intro q
    dsimp [G,sourceGeometricMean,M]
    gcongr
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f sourceFixedMode
    apply continuous_finsetSum
    intro x hx
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 V₁ X₁ true
      (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) V₂ X₂ false
      (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact ((hwc x hx).mul h₁.star).mul h₂
  have hpoint : ∀q,‖f q‖≤(A*C*K^ε)*G q := by
    intro q
    let P : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false) u.2 (-u.1)
    let Q : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) u.2 u.1
    have hh := hpointwise p hinj r s T (w q) P Q
      A K hA hK hs hmap hT hnorm (hw q)
    have hh' := weighted_conjugate_pair_swap s (w q)
      (fun x => P (sourceObservation p x)) (fun x => Q (sourceObservation p x))
      (A*C*K^ε) _ _ hh
    simpa only [f,G,sourceFixedMode,sourceGeometricMean,sourceChildEnergy,P,Q,
      Bool.false_eq_true,ite_false,ite_true] using hh'
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0 (A*C*K^ε) M (by positivity) hM hpoint

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0193

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins
Source SHA256: f3f4a46d2183c3388b0fc8566c45384dfe5f8c189dd9322e86421889052d90bb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0194


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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FourierBridge (logPhase)

def initialOuterWeight {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma initialOuterWeight_continuous {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (x : SecondExpansionData ι) :
    Continuous (fun q => initialOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => logPhase (q.1 + q.2.1) (z x)) :=
    (FourierBridge.logPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (FourierBridge.logPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold initialOuterWeight
  fun_prop

lemma initialOuterWeight_norm {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) :
    ‖initialOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [initialOuterWeight, norm_mul, FourierBridge.logPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def initialSourceSum (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2
    (sourceObservation p x).1 (-(sourceObservation p x).1) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem initialSource_eq_integrated
    (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSourceMode p hp hcop hg (𝓕 A₁) (𝓕 A₂) b s
        (initialOuterWeight V w z ud ue uv kap) F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : SecondExpansionData ι → Frequency → ℂ := fun x q =>
    initialOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ q.1 q.2.2 true) (sourceObservation p x).2 (sourceObservation p x).1) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ q.2.1 q.2.2 false) (sourceObservation p x).2 (-(sourceObservation p x).1)
  let M : SecondExpansionData ι → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true *
      rowMagnitude p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
  have hc (x : SecondExpansionData ι) : Continuous (Q x) := by
    have hw := initialOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : SecondExpansionData ι) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, initialOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, initialOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

theorem initial_source_uniform_transfer (ε : ℝ) (hε : 0<ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (M : Fin 7→ℝ)
    (hM : ∀j,0≤M j) (hV : ∀j x,V j x≠0→|x|≤M j) (N J : ℕ) :
    ∃ Cₐ : ℝ,0<Cₐ ∧ ∃ Cₛ : ℝ,0≤Cₛ ∧ ∀R:ℝ,0<R→∃b:𝓢(ℝ,ℂ),
      (∀t₁ t₂ t₃:ℝ,(1+R)^N*‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖≤
        Cₛ*FirstPassCubeLabels.firstLogDensity J t₁*FirstPassCubeLabels.firstLogDensity J t₂*
          FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
        (w : SecondExpansionData ι→ℂ) (A K : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O)
        (z ud ue uv kap : SecondExpansionData ι→ℝ) (X₁ X₂ : ℝ),
        0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
        (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
        (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
        (∀x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖≤A) →
        ‖initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖≤
          A*Cₐ*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖*
            sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ,hCₐ,htrans⟩ := integrated_source_transfer ε hε
  obtain ⟨Cₛ,hCₛ,hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV N J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR
  obtain ⟨b,hpoint,hid⟩ := hsep R hR
  refine ⟨b,hpoint,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hA hK hs hmap hT hnorm hw
  have hsource := initialSource_eq_integrated p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid p hp hcop hg F Ψ₁ Ψ₂ m
      (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans p hp hcop hg hinj r s T (initialOuterWeight V w z ud ue uv kap) A K
    F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hA hK hs hmap hT hnorm
  · intro q x hx
    rw [initialOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact initialOuterWeight_continuous V w z ud ue uv kap x

end

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def initialLogIndex (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor),normLogBin (primeProductNorm p x.overlap),
    normLogBin (elementNorm (sourceObservation p x).1))

def initialLogColumn (Z B : ℝ) (j : SecondLogIndex) : ℝ :=
  Z/(secondLogE j*secondLogV j*B)

def initialLogLabel (j : SecondLogIndex) : ℝ := secondLogE j*secondLogV j*Real.exp 2

omit [DecidableEq ι] in
lemma sourceRow_nonzero (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    (sourceObservation p x).1≠0 := mul_ne_zero (primeSubsetGenerator_ne_zero _ _) hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_span (x : SecondExpansionData ι) :
    Ideal.span {(sourceObservation p x).2}=
      (∏i∈x.divisor,Ideal.span {p i})*(∏i∈x.overlap,Ideal.span {p i}) := by
  simp only [sourceObservation,←Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,FiniteGaussPhase.span_finset_prod]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_norm (x : SecondExpansionData ι) :
    elementNorm (sourceObservation p x).2=primeProductNorm p x.divisor*primeProductNorm p x.overlap := by
  simp only [elementNorm,sourceObservation,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceQuotient_nonzero (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    secondExpansionQuotient p x≠0 := by
  rw [secondExpansionQuotient_of_subset p x hE]
  intro he
  have hh := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
  rw [he,mul_zero] at hh
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hh

include hp in

theorem initial_log_coordinates (Z : ℝ) (hZ : 0<Z) (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hk : x.frequency≠0) :
    let j := initialLogIndex p x
    let B := elementNorm (secondExpansionQuotient p x)
    let X₀ := initialLogColumn Z B j
    |Real.log (primeProductNorm p x.overlap*X₀/residualScale p Z x)|≤2 ∧
    |Real.log (primeProductNorm p x.divisor/secondLogE j)|≤2 ∧
    |Real.log (primeProductNorm p x.overlap/secondLogV j)|≤2 ∧
    |Real.log (elementNorm (sourceObservation p x).1/secondLogK j)|≤2 := by
  dsimp only
  have he := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hv := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hn : 1≤elementNorm (sourceObservation p x).1 := element_norm_ge_one _ (sourceRow_nonzero p x hk)
  have hrow := normLogBin_error (elementNorm (sourceObservation p x).1) hn
  have hE0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have hV0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne'
  have hB0 := (SecondPassIntegration.elementNorm_pos _ (sourceQuotient_nonzero p hp x hE)).ne'
  have hE1 := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hV1 := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio : primeProductNorm p x.overlap*initialLogColumn Z
      (elementNorm (secondExpansionQuotient p x)) (initialLogIndex p x)/residualScale p Z x=
      (primeProductNorm p x.divisor/normLogScale (normLogBin (primeProductNorm p x.divisor)))*
      (primeProductNorm p x.overlap/normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [initialLogColumn,residualScale,initialLogIndex,secondLogE,secondLogV,
      elementNorm,primeSubsetGenerator_norm_eq_productNorm]
    have hZ0 := hZ.ne'
    dsimp [elementNorm] at hB0
    have hBn : ‖eisEmbedding (secondExpansionQuotient p x)‖≠0 := by
      intro hz
      apply hB0
      rw [hz]
      norm_num
    field_simp [hBn]

  refine ⟨?_,?_,?_,?_⟩
  · rw [hratio,Real.log_mul (div_ne_zero hE0 hE1) (div_ne_zero hV0 hV1),
      abs_of_nonneg (add_nonneg he.1 hv.1)]
    linarith [he.2,hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg he.1]
    linarith [he.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hv.1]
    linarith [hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hrow.1]
    linarith [hrow.2]

include hp in

omit [DecidableEq ι] in
theorem initial_log_target_bounds (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    elementNorm (sourceObservation p x).2 ≤ initialLogLabel (initialLogIndex p x) ∧
    elementNorm (sourceObservation p x).1≤secondLogK (initialLogIndex p x)*Real.exp 1 := by
  have he := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.divisor)).2
  have hv := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.overlap)).2
  have hk' := (normLogBin_scale_bounds _ (element_norm_ge_one _ (sourceRow_nonzero p x hk))).2
  refine ⟨?_,hk'⟩
  rw [sourceLabel_norm]
  have hh := mul_le_mul he hv (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (mul_nonneg (normLogScale_pos _).le (Real.exp_pos _).le)
  simpa only [initialLogLabel,initialLogIndex,secondLogE,secondLogV,
    show (2:ℝ)=1+1 by norm_num,Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

theorem initial_log_mass (Z B : ℝ) (hB : B≠0) (j : SecondLogIndex) :
    initialLogColumn Z B j*initialLogLabel j=Z/B*Real.exp 2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn initialLogLabel secondLogE secondLogV
  field_simp

theorem initial_log_radial (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) (j : SecondLogIndex) :
    H*secondLogK j/(secondLogE j^2*secondLogV j^2*initialLogColumn Z B j^2)=
      H*secondLogK j*B^2/Z^2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn secondLogE secondLogV
  field_simp

end

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

include hcop in
theorem sourceLabel_squarefree (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    Squarefree (Ideal.span {(sourceObservation p x).2}) := by
  have hd : Disjoint x.divisor x.overlap := hV.mono_left hE
  rw [sourceLabel_span,←Finset.prod_union hd]
  exact primeSpanProduct_squarefree p hcop _

include hcop in
theorem sourceMask_coprime (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    IsCoprime (Ideal.span {secondExpansionQuotient p x})
      (Ideal.span {(sourceObservation p x).2}) := by
  rw [secondExpansionQuotient_of_subset p x hE,secondMaskQuotient_span,sourceLabel_span]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.mul_right
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => (Finset.mem_sdiff.mp hi).2 (he.symm ▸ hj))
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => Finset.disjoint_left.mp hV (Finset.mem_sdiff.mp hi).1 (he.symm ▸ hj))

include hp in
theorem initialLogIndex_mem_box (Z M K : ℝ) (x : SecondExpansionData ι)
    (hs : SecondSourceSupport p Z M x) (hE : x.divisor⊆x.sourceCommon)
    (hk : x.frequency≠0) (hK : elementNorm (sourceObservation p x).1≤K) :
    initialLogIndex p x∈secondLogBinBox (Z*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp Z M x hs hE
  simp only [initialLogIndex,secondLogBinBox,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (SecondPassIntegration.elementNorm_pos _ (sourceRow_nonzero p x hk)) hK⟩

end

theorem initial_log_box_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ U V K : ℝ,1≤U → 0<V → 0<K → V≤U → K≤U →
      ((secondLogBinBox V K).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hpow⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro U V K hU hV hK hVU hKU
  have hv := normLogBin_le_log_upper V U hV hVU hU
  have hk := normLogBin_le_log_upper K U hK hKU hU
  have hlog := Real.log_nonneg hU
  let B := 1+Real.log 27+22*Real.log U
  have h27 : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1≤B := by dsimp [B]; linarith
  have hvB : (normLogBin V:ℝ)+1≤B := by dsimp [B]; linarith
  have hkB : (normLogBin K:ℝ)+1≤B := by dsimp [B]; linarith
  have hh : ((secondLogBinBox V K).card:ℝ)≤B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) hvB 2) hkB
        (by positivity) (sq_nonneg B)
      _ = B^3 := by ring
  exact hh.trans ((pow_le_pow_right₀ hB (by decide : 3≤10)).trans (hpow U hU))

end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem local_first_conductor_balance (parityBit e₁ e₂ : Bool) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      2*bit (!parityBit && e₁ && e₂)=bit e₁+bit e₂+bit parityBit := by
  cases parityBit <;> cases e₁ <;> cases e₂ <;> decide

theorem local_first_conductor_bound (parityBit e₁ e₂ : Bool) (n : ℕ) (hn : 0<n) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2*n := by
  have h : (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2 := by
    cases parityBit <;> cases e₁ <;> cases e₂ <;> decide
  omega

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

omit [DecidableEq ι] in
theorem firstActiveProduct_as_primeProduct (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)=
      primeProduct p S (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 then 0 else 1) := by
  unfold cubeActiveSupport primeProduct
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 <;> simp [h]

omit [DecidableEq ι] in
theorem first_conductor_product_balance (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)*dilationLabel p S v ε₁ ε₂*j2Label p S v ε₁ ε₂^2 =
      aLabel p S ε₁*aLabel p S ε₂*squarefreeLabel p S v := by
  rw [firstActiveProduct_as_primeProduct]
  simp only [dilationLabel,j2Label,aLabel,squarefreeLabel,primeProduct,← Finset.prod_pow,
    ← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  simpa only [evenDouble,mul_comm] using local_first_conductor_balance (parity (v i)) (ε₁ i) (ε₂ i)

variable [∀ i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by
  rw [firstActiveProduct_as_primeProduct,← primeProduct_add]
  simp only [dilationLabel,jLabel,aLabel,primeProduct,← Finset.prod_pow,← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  simpa only [mul_comm] using local_first_conductor_bound (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i) (v₁ i+v₂ i) (hv i hi)

variable (hp : ∀ i,p i≠0)
include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_norm_bound (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) (B : ℝ) (hB : 0≤B)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B) :
    ‖eisEmbedding (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2*
      ‖eisEmbedding (dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2*
      ‖eisEmbedding (jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤
    ‖eisEmbedding (aLabel p S ε₁)‖^2*‖eisEmbedding (aLabel p S ε₂)‖^2*B^4 := by
  have hn : aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2≠0 := by
    apply mul_ne_zero (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
    exact pow_ne_zero _ (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
  have h := element_norm_le_of_dvd hn (first_conductor_product_dvd p S v₁ v₂ ε₁ ε₂ hv)
  simp only [map_mul,map_pow,norm_mul,norm_pow,mul_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm 2
  convert hs using 1 <;> ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma first_row_numeric_bound (an en jn a1 a2 cn dn hn fn ell K B F : ℝ)
    (ha : 0≤an) (he : 0≤en) (hj : 0<jn) (h1 : 0<a1) (h2 : 0<a2) (hc : 0<cn)
    (hd : 0≤dn) (_hh : 0≤hn) (hf : 0≤fn) (hell : 0<ell) (hK : 0<K) (_hB : 0<B) (hF : 0<F)
    (hcon : an*en*jn≤a1*a2*B^4) (hfreq : hn≤ell^2*an*dn/(K*a1*a2*cn^2)) (hlabel : fn≤F) :
    hn*fn^2*en≤ell^2*B^4*F^2*dn/(K*cn^2*jn) := by
  have hratio : an*en/(a1*a2)≤B^4/jn := by
    apply (div_le_div_iff₀ (mul_pos h1 h2) hj).mpr
    nlinarith [hcon]
  calc
    hn*fn^2*en ≤ (ell^2*an*dn/(K*a1*a2*cn^2))*F^2*en := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul hfreq (pow_le_pow_left₀ hf hlabel 2) (sq_nonneg _) (by positivity)
    _ = (ell^2*dn*F^2/(K*cn^2))*(an*en/(a1*a2)) := by
      field_simp

    _ ≤ (ell^2*dn*F^2/(K*cn^2))*(B^4/jn) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstRowScale_le_pooled (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (b : GlobalCubeBlock ι) :
    globalFirstRowScale p K ell B F ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).2
  have hc := (hbds 1).1
  have hJ := (hbds 4).1
  change primeProductNorm p b.firstDivisor≤globalLogRep j 5*Real.exp 1 at hd
  change globalLogRep j 1≤primeProductNorm p b.common at hc
  change globalLogRep j 4≤globalCubeJNorm p x at hJ
  change ell^2*B^4*F^2*primeProductNorm p b.firstDivisor/
      (K*(primeProductNorm p b.common)^2*globalCubeJNorm p x) ≤
    Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  have hdpos := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
  have h5 := (globalLogRep_pos j 5).le
  apply div_le_div₀ (by positivity)
  · calc
      _ ≤ ell^2*B^4*F^2*(globalLogRep j 5*Real.exp 1) := by gcongr
      _ = _ := by ring
  · exact mul_pos (mul_pos hK (sq_pos_of_pos (globalLogRep_pos j 1))) (globalLogRep_pos j 4)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (globalLogRep_pos j 1).le hc 2) hK.le)
      hJ (globalLogRep_pos j 4).le (by positivity)

include hp in

theorem first_row_enlargement (b : GlobalCubeBlock ι) (x : Ideal O × O)
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : (Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ‖eisEmbedding x.2‖^2 ≤
      ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
      primeProductNorm p b.firstDivisor/
      (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
        ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x)‖^2 ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let active := cubeActiveSupport b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let e := dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let j := jLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let a1 := aLabel p b.cube.support b.cube.leftBit
  let a2 := aLabel p b.cube.support b.cube.rightBit
  have hpos (v : ι → ℕ) : 0<‖eisEmbedding (primeProduct p b.cube.support v)‖^2 :=
    zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))
  have hcon := first_conductor_norm_bound p hp b.cube.support b.cube.leftExponent b.cube.rightExponent
    b.cube.leftBit b.cube.rightBit b.cube.support_pos B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2) (‖eisEmbedding j‖^2)
    (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2) (primeProductNorm p b.common) (primeProductNorm p b.firstDivisor)
    (‖eisEmbedding x.2‖^2) (Ideal.absNorm x.1) ell K B F
    (FirstPassCubeLabels.primeProductNorm_pos p hp active).le (sq_nonneg _) (hpos _) (hpos _) (hpos _)
    (FirstPassCubeLabels.primeProductNorm_pos p hp b.common) (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
    (sq_nonneg _) (Nat.cast_nonneg _) hell hK hB hF hcon hh hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2=(Ideal.absNorm x.1 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e x)‖^2 =
      ‖eisEmbedding x.2‖^2*(Ideal.absNorm x.1 : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [show (‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2)^2 =
        (Ideal.absNorm x.1 : ℝ)^2 by rw [hgen]]
  rw [hrow]
  exact hnum.trans (globalFirstRowScale_le_pooled p hp K ell B F hK hell hB hF b)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstFrequencyScale (K ell : ℝ) (b : GlobalCubeBlock ι) : ℝ :=
  ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
    primeProductNorm p b.firstDivisor/
    (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
      ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)

def globalCubeFirstTargets (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O)) : Finset O :=
  s.image (DescentWeightedCauchy.firstElementRowMap
    (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
      b.cube.leftBit b.cube.rightBit))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_mem (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (x : Ideal O × O) (hx : x∈s) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x∈globalCubeFirstTargets p b s :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_ne_zero (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (hsf : ∀ x∈s,Squarefree x.1) (hs0 : ∀ x∈s,x.2≠0)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) : z≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  apply mul_ne_zero
  · apply mul_ne_zero (hs0 x hx)
    exact pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (by simpa using (hsf x hx).ne_zero))
  · exact primeProduct_ne_zero p hp _ _

include hp in
theorem globalCubeFirstTargets_norm_bound (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : ∀ x∈s,(Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ∀ x∈s,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  exact first_row_enlargement p hp b x K ell B F hK hell hB hF hb₁ hb₂ (hf x hx) (hh x hx)

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0194

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
Source SHA256: 1ffb8b680360de85a1d968c7147aed82866a5f2547d375429f41c47a8eefd707
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0195



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
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def globalFirstRowCap (K ell B F : ℝ) : ℝ :=
  (Real.exp 1)^2*ell^2*B^6*F^2/K

theorem globalFirstRowCap_pos (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) :
    0<globalFirstRowCap K ell B F := by
  unfold globalFirstRowCap
  positivity

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_le_cap (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) (hadm : GlobalCubeAdmissible b)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤globalFirstRowCap K ell B F := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).1
  have hc := (hbds 1).2
  change globalLogRep j 5≤primeProductNorm p b.firstDivisor at hd
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  have hrad := globalCube_radical_bound p hp B hB.le x hb₁ hb₂
  have h1p := globalLogRep_pos j 1
  have hd' : globalLogRep j 5≤globalLogRep j 1*Real.exp 1*B^2 := by
    calc
      _ ≤ primeProductNorm p b.firstDivisor := hd
      _ ≤ primeProductNorm p (b.common∪b.cube.support) := primeProductNorm_mono p hp hadm.2.2
      _ = primeProductNorm p b.common*primeProductNorm p b.cube.support :=
        FirstPassCubeLabels.primeProductNorm_union p _ _ hadm.2.1
      _ ≤ (globalLogRep j 1*Real.exp 1)*B^2 :=
        mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h4p := globalLogRep_pos j 4
  have hm : globalLogRep j 1≤(globalLogRep j 1)^2*globalLogRep j 4 := by
    calc
      globalLogRep j 1 = globalLogRep j 1*1*1 := by ring
      _ ≤ globalLogRep j 1*globalLogRep j 1*globalLogRep j 4 := by gcongr
      _ = _ := by ring
  have hr : globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)≤Real.exp 1*B^2 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos h1p) h4p)).mpr
    calc
      _ ≤ globalLogRep j 1*Real.exp 1*B^2 := hd'
      _ ≤ ((globalLogRep j 1)^2*globalLogRep j 4)*Real.exp 1*B^2 := by gcongr
      _ = _ := by ring
  change Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)≤_
  calc
    _ = (Real.exp 1*ell^2*B^4*F^2/K)*(globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)) := by ring
    _ ≤ (Real.exp 1*ell^2*B^4*F^2/K)*(Real.exp 1*B^2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = globalFirstRowCap K ell B F := by unfold globalFirstRowCap; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_original_ranges
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Ct₁ C₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    globalTwoPassage_transfer W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H
    hΓ hK hell hB hF hH hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  exact htransfer p hp hinj hcop hg hc hpr pool blocks s a w
    (fun b => globalCubeFirstTargets p b (s b)) Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H (globalFirstRowCap K ell B F)
    hΓ hK hell hB hF hH (globalFirstRowCap_pos K ell B F hK hell hB hF).le hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0
    (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx)
    (fun b hb z hz => globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz)
    (fun b hb z hz => globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

noncomputable abbrev actualSextic := ActualEisensteinCubic.canonicalSextic

def exceptionalPiece (P : Ideal O) [P.IsMaximal] (e : Fin 3) (n b : O) : ℂ :=
  if e=0 then -(rootCard (O ⧸ P) : ℂ)⁻¹
  else if e=1 then (rootCard (O ⧸ P) : ℂ)*(if n∈P then 1 else 0)
  else (rootCard (O ⧸ P) : ℂ)*(if n∉P ∧ b∈P then 1 else 0)

theorem bracket_four_eq_sum_exceptionalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (n b : O) :
    bracket (actualSextic P hg) 4 (Ideal.Quotient.mk P (n*b^3)) =
      ∑e : Fin 3, exceptionalPiece P e n b := by
  rw [canonical_bracket_four_cube_split]
  simp [Fin.sum_univ_succ,exceptionalPiece]
  ring

def exceptionalBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i, exceptionalPiece (P i) (e i) n b

theorem prod_bracket_four_eq_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) 4 (Ideal.Quotient.mk (P i) (n*b^3))) =
      ∑e : ι→Fin 3, exceptionalBranch P e n b := by
  simp_rw [bracket_four_eq_sum_exceptionalPiece]
  simpa only [Fintype.piFinset_univ,exceptionalBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => exceptionalPiece (P i) e n b)

def exceptionalDivisor {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    (e : ι→Fin 3) (v : Fin 3) : Ideal O := ∏i, if e i=v then P i else 1

theorem exceptionalBranch_support {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O)
    (hne : exceptionalBranch P e n b≠0) :
    (∀i,e i=1 → n∈P i) ∧ (∀i,e i=2 → n∉P i ∧ b∈P i) := by
  have hn i : exceptionalPiece (P i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  constructor
  · intro i hi
    by_contra h
    exact hn i (by simp [exceptionalPiece,hi,h])
  · intro i hi
    by_contra h
    exact hn i (by simp [exceptionalPiece,hi,h])

theorem exceptionalBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (e : ι→Fin 3) (n b : O) (hne : exceptionalBranch P e n b≠0) :
    exceptionalDivisor P e 1 ∣ Ideal.span {n} ∧
    exceptionalDivisor P e 2 ∣ Ideal.span {b} ∧
    (∀i,e i=2 → n∉P i) := by
  have hs := exceptionalBranch_support P e n b hne
  have hprod (v : Fin 3) (z : O) (hz : ∀i,e i=v → z∈P i) :
      exceptionalDivisor P e v ∣ Ideal.span {z} := by
    rw [exceptionalDivisor]
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      change IsCoprime (if e i=v then P i else 1) (if e j=v then P j else 1)
      by_cases hi : e i=v
      · rw [ite_eq_left hi]
        by_cases hj : e j=v
        · rw [ite_eq_left hj]
          exact hcop hij
        · rw [ite_eq_right hj]
          exact isCoprime_one_right
      · rw [ite_eq_right hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  exact ⟨hprod 1 n hs.1,hprod 2 b (fun i hi => (hs.2 i hi).2),fun i hi => (hs.2 i hi).1⟩

theorem rootCard_eq_sqrt_absNorm (P : Ideal O) [P.IsMaximal] :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

def exceptionalSize {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) : ℝ :=
  ∏i, if e i=0 then (rootCard (O ⧸ P i))⁻¹ else rootCard (O ⧸ P i)

theorem exceptionalPiece_norm_le (P : Ideal O) [P.IsMaximal]
    (e : Fin 3) (n b : O) :
    ‖exceptionalPiece P e n b‖≤(if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P)) := by
  have hr : 0≤rootCard (O ⧸ P) := rootCard_pos.le
  fin_cases e <;> simp only [exceptionalPiece,Fin.isValue,Fin.zero_eta,↓reduceIte]
  · simp [abs_of_nonneg hr]
  · by_cases hn : n∈P <;> simp [hn,abs_of_nonneg hr,hr]
  · by_cases hn : n∉P ∧ b∈P <;> simp [hn,abs_of_nonneg hr,hr]

theorem exceptionalBranch_norm_le {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) :
    ‖exceptionalBranch P e n b‖≤exceptionalSize P e := by
  rw [exceptionalBranch,norm_prod,exceptionalSize]
  exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => exceptionalPiece_norm_le _ _ _ _)

theorem exceptionalDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hp : ∀i,P i≠0) (e : ι→Fin 3) (v : Fin 3) :
    exceptionalDivisor P e v≠0 := by
  rw [exceptionalDivisor]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · exact hp i
  · exact one_ne_zero

theorem sqrt_norm_exceptionalDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (exceptionalDivisor P e v):ℝ)=
      ∏i,if e i=v then rootCard (O ⧸ P i) else 1 := by
  rw [exceptionalDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    split_ifs with hi
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem exceptionalSize_eq {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) :
    exceptionalSize P e=
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 0):ℝ) := by
  rw [sqrt_norm_exceptionalDivisor,sqrt_norm_exceptionalDivisor,sqrt_norm_exceptionalDivisor,
    ←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  generalize e i=x
  fin_cases x <;> simp

theorem exceptional_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hp : ∀i,P i≠0)
    (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖exceptionalBranch P e n b‖ /
      (Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*U)*
        ((Ideal.absNorm (exceptionalDivisor P e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 0):ℝ)*
        (Ideal.absNorm (exceptionalDivisor P e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (exceptionalDivisor P e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => exceptionalDivisor_ne_zero P hp e v (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (exceptionalDivisor P e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (exceptionalBranch_norm_le P e n b) (by positivity)).trans
  rw [exceptionalSize_eq,Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith

end CompletedGauss

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss

theorem product_quadratic_norm_scaled (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀b∈T,‖β n b‖≤lengthScale) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_all ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβ
  by_cases hL0 : lengthScale=0
  · have hz n hn b hb : β n b=0 := norm_eq_zero.mp (le_antisymm (by simpa [hL0] using hβ n hn b hb) (norm_nonneg _))
    simp only [hL0,pow_two,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k _
    have hh : (∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro b hb
      rw [hz n hn b hb,mul_zero]
    rw [hh,norm_zero,zero_mul]
  have hLp : 0<lengthScale := lt_of_le_of_ne hL (Ne.symm hL0)
  have hLc : (lengthScale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL0
  let γ : Ideal O→Ideal O→ℂ := fun n b => β n b/(lengthScale:ℂ)
  have hγ (n : Ideal O) (hn : n∈S) (b : Ideal O) (hb : b∈T) : ‖γ n b‖≤1 := by
    dsimp [γ]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hL]
    exact (div_le_one hLp).mpr (hβ n hn b hb)
  have hb := hbound K U B hK hU hB S T hS hT γ hγ
  have he (k : idealRange K) :
      (∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b)=
      (lengthScale:ℂ)*(∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*γ n b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [γ]
    field_simp
  simp_rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL,mul_pow]
  rw [←Finset.mul_sum]
  calc
    _ ≤ lengthScale^2*(C*(K*(U*B))^ε*(K+U*B)*(U*B)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem completed_quadratic_dyad (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B r S₀ E : ℝ,
      1≤K → 1≤U → 1≤B → 0<r → 0<S₀ → 0<E →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,
      (∀n∈S,∀b∈T,‖β n b‖≤1/(Real.sqrt U*B*r*Real.sqrt (S₀*E))) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)/(B*r^2*S₀*E) := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B r S₀ E hK hU hB hr hS₀ hE S T hS hT β hβ
  apply (hbound K U B _ hK hU hB (by positivity) S T hS hT β hβ).trans
  apply le_of_eq
  have hU0 : U≠0 := by linarith
  have hB0 : B≠0 := by linarith
  have hr0 := ne_of_gt hr
  have hS0 := ne_of_gt hS₀
  have hE0 := ne_of_gt hE
  simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt (show 0≤U by linarith),
    Real.sq_sqrt (show 0≤S₀*E by positivity)]
  field_simp

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein

def spatialHorizontal (p : SpatialCoordinates) : ℂ := (p 0:ℂ)+(p 1:ℂ)*Complex.I

def mobiusSpatialDenominator (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℝ :=
  Complex.normSq (g 1 0*spatialHorizontal p+g 1 1)+Complex.normSq (g 1 0)*(p 2)^2

def mobiusSpatialHorizontal (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℂ :=
  ((g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
    g 0 0*star (g 1 0)*(p 2:ℂ)^2)/(mobiusSpatialDenominator g p:ℂ)

def mobiusSpatial (g : SL(2,ℂ)) (p : SpatialCoordinates) : SpatialCoordinates :=
  ![(mobiusSpatialHorizontal g p).re,(mobiusSpatialHorizontal g p).im,
    p 2/mobiusSpatialDenominator g p]

lemma mobiusSpatialDenominator_pos (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<mobiusSpatialDenominator g p := by
  simpa only [mobiusSpatialDenominator,Complex.normSq_eq_norm_sq] using
    mobius_denominator_pos g (spatialHorizontal p) (p 2) hp

lemma mobiusSpatial_positive (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)

lemma mobiusSpatial_coordinates (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    hyperbolicSpatialCoordinates (g • upperPoint (spatialHorizontal p) (p 2) hp)=mobiusSpatial g p := by
  rw [mobius_upperPoint]
  simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,
    mobiusSpatial,mobiusSpatialHorizontal,mobiusSpatialDenominator,Complex.normSq_eq_norm_sq]

lemma spatialHorizontal_contDiff : ContDiff ℝ ∞ spatialHorizontal := by
  unfold spatialHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)

lemma mobiusSpatialDenominator_contDiff (g : SL(2,ℂ)) : ContDiff ℝ ∞ (mobiusSpatialDenominator g) := by
  unfold mobiusSpatialDenominator
  have hz : ContDiff ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) :=
    (contDiff_const.mul spatialHorizontal_contDiff).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hz
  have him := Complex.imCLM.contDiff.comp hz
  change ContDiff ℝ ∞ (fun p =>
    (g 1 0*spatialHorizontal p+g 1 1).re*(g 1 0*spatialHorizontal p+g 1 1).re+
    (g 1 0*spatialHorizontal p+g 1 1).im*(g 1 0*spatialHorizontal p+g 1 1).im+
    Complex.normSq (g 1 0)*(p 2)^2)
  exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 2).pow 2))

lemma mobiusSpatial_contDiffAt (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (mobiusSpatial g) p := by
  have hD := (mobiusSpatialDenominator_contDiff g).contDiffAt (x := p)
  have hDc : ContDiffAt ℝ ∞ (fun p => (mobiusSpatialDenominator g p:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hD
  have hnum : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates =>
      (g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
        g 0 0*star (g 1 0)*(p 2:ℂ)^2) p := by
    have hz := spatialHorizontal_contDiff.contDiffAt (x := p)
    have hcz : ContDiffAt ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) p :=
      (contDiffAt_const.mul hz).add contDiffAt_const
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp p hcz
    have hv : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => (p 2:ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ 2).contDiffAt
    exact (((contDiffAt_const.mul hz).add contDiffAt_const).mul hc).add
      (contDiffAt_const.mul (hv.pow 2))
  have hh : ContDiffAt ℝ ∞ (mobiusSpatialHorizontal g) p :=
    by
      unfold mobiusSpatialHorizontal
      simp only [div_eq_mul_inv]
      exact hnum.mul (hDc.inv (Complex.ofReal_ne_zero.mpr (mobiusSpatialDenominator_pos g p hp).ne'))
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact Complex.reCLM.contDiff.contDiffAt.comp p hh
  · exact Complex.imCLM.contDiff.contDiffAt.comp p hh
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => p 2) p).div hD
      (mobiusSpatialDenominator_pos g p hp).ne'

abbrev PositiveSpatial := {p : SpatialCoordinates // 0<p 2}

def positiveSpatialToUpper (p : PositiveSpatial) : UpperCoordinates :=
  ⟨(spatialHorizontal p.1,p.1 2),p.2⟩
def upperToPositiveSpatial (p : UpperCoordinates) : PositiveSpatial :=
  ⟨![p.1.1.re,p.1.1.im,p.1.2],p.2⟩

lemma positiveSpatialToUpper_continuous : Continuous positiveSpatialToUpper := by
  apply Continuous.subtype_mk
  exact (spatialHorizontal_contDiff.continuous.comp continuous_subtype_val).prodMk
    ((continuous_apply 2).comp continuous_subtype_val)
lemma upperToPositiveSpatial_continuous : Continuous upperToPositiveSpatial := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

def positiveSpatialUpperHomeomorph : PositiveSpatial ≃ₜ UpperCoordinates where
  toFun := positiveSpatialToUpper
  invFun := upperToPositiveSpatial
  left_inv p := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [upperToPositiveSpatial,positiveSpatialToUpper,spatialHorizontal]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Complex.re_add_im _
    · rfl
  continuous_toFun := positiveSpatialToUpper_continuous
  continuous_invFun := upperToPositiveSpatial_continuous

def positiveSpatialHomeomorph : PositiveSpatial ≃ₜ HyperbolicSpace :=
  positiveSpatialUpperHomeomorph.trans upperCoordinatesHomeomorph

lemma hyperbolicSpatial_isOpenEmbedding : Topology.IsOpenEmbedding hyperbolicSpatialCoordinates := by
  have ho : IsOpen {p : SpatialCoordinates | 0<p 2} := isOpen_lt continuous_const (by fun_prop)
  have he := ho.isOpenEmbedding_subtypeVal.comp positiveSpatialHomeomorph.symm.isOpenEmbedding
  exact he

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

namespace CubicEisenstein

abbrev KernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def hyperbolicSpatialChart : OpenPartialHomeomorph HyperbolicSpace SpatialCoordinates :=
  hyperbolicSpatial_isOpenEmbedding.toOpenPartialHomeomorph hyperbolicSpatialCoordinates

@[simp] lemma hyperbolicSpatialChart_apply (w : HyperbolicSpace) :
    hyperbolicSpatialChart w=hyperbolicSpatialCoordinates w := rfl

@[simp] lemma hyperbolicSpatialChart_source : hyperbolicSpatialChart.source=Set.univ := rfl

lemma hyperbolicSpatialChart_target_positive {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) : 0<p 2 := by
  have he := hyperbolicSpatialChart.right_inv hp
  have hh := hyperbolicSpatialCoordinates_positive (hyperbolicSpatialChart.symm p)
  rwa [← hyperbolicSpatialChart_apply,he] at hh

def kernelLocalLift (w : HyperbolicSpace) : OpenPartialHomeomorph KernelQuotient HyperbolicSpace :=
  kernelQuotient_localHomeomorph.localInverseAt w

@[simp] lemma kernelLocalLift_symm (w : HyperbolicSpace) :
    (kernelLocalLift w).symm=integralOrbitProjection globalKubotaKernel :=
  kernelQuotient_localHomeomorph.localInverseAt_symm w

lemma kernelLocalLift_project {w : HyperbolicSpace} {q : KernelQuotient}
    (hq : q∈(kernelLocalLift w).source) :
    integralOrbitProjection globalKubotaKernel (kernelLocalLift w q)=q :=
  kernelQuotient_localHomeomorph.apply_localInverseAt_of_mem hq

lemma kernel_lifts_eventually_eq {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hfg : f x=g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) : f=ᶠ[𝓝 x]g := by
  obtain ⟨U,hU,hx,hUinj⟩ := kernelQuotient_localHomeomorph.isLocallyInjective (f x)
  have hfn : ∀ᶠ y in 𝓝 x,f y∈U := hf (hU.mem_nhds hx)
  have hgn : ∀ᶠ y in 𝓝 x,g y∈U := hg (hU.mem_nhds (hfg ▸ hx))
  filter_upwards [hfn,hgn,hproj] with y hyf hyg hye
  exact hUinj hyf hyg hye

lemma kernel_lifts_eventually_deck {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) :
    ∃M : globalKubotaKernel, f=ᶠ[𝓝 x](fun y => integralComplexMatrix M • g y) := by
  have he := (integralOrbitProjection_eq_iff globalKubotaKernel (f x) (g x)).mp
    hproj.self_of_nhds
  obtain ⟨M,hM⟩ := MulAction.mem_orbit_iff.mp he
  refine ⟨M,kernel_lifts_eventually_eq hf
    ((continuous_hyperbolic_action (integralComplexMatrix M)).continuousAt.comp hg) hM.symm ?_⟩
  filter_upwards [hproj] with y hy
  simpa only [integralOrbitProjection_eq] using hy

lemma mobiusSpatial_coordinates_global (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicSpatialCoordinates (g•w)=mobiusSpatial g (hyperbolicSpatialCoordinates w) := by
  have hp := hyperbolicSpatialCoordinates_positive w
  have hr := hyperbolicSpatialCoordinates_reconstruct w
  nth_rw 1 [← hr]
  exact mobiusSpatial_coordinates g (hyperbolicSpatialCoordinates w) hp

def kernelCoordinateTransition (w : HyperbolicSpace) (p : SpatialCoordinates) : SpatialCoordinates :=
  hyperbolicSpatialCoordinates (kernelLocalLift w
    (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)))

lemma kernelCoordinateTransition_eventually (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) :
    ∃M : globalKubotaKernel,kernelCoordinateTransition w=ᶠ[𝓝 p]
      mobiusSpatial (integralComplexMatrix M) := by
  have hc : ContinuousAt hyperbolicSpatialChart.symm p :=
    hyperbolicSpatialChart.symm.continuousAt hp
  have hπ : ContinuousAt (fun y => integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)) p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp hc
  have hl : ContinuousAt (fun y => kernelLocalLift w (integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y))) p :=
    ((kernelLocalLift w).continuousAt hq).comp
      (f := fun y : SpatialCoordinates => integralOrbitProjection globalKubotaKernel
        (hyperbolicSpatialChart.symm y)) hπ
  have hqn : ∀ᶠ y in 𝓝 p,integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)∈(kernelLocalLift w).source :=
    hπ ((kernelLocalLift w).open_source.mem_nhds hq)
  have hproj : (fun y => integralOrbitProjection globalKubotaKernel (kernelLocalLift w
      (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y))))=ᶠ[𝓝 p]
      (fun y => integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y)) := by
    filter_upwards [hqn] with y hy
    exact kernelLocalLift_project hy
  obtain ⟨M,hM⟩ := kernel_lifts_eventually_deck hl hc hproj
  refine ⟨M,?_⟩
  filter_upwards [hM,hyperbolicSpatialChart.open_target.mem_nhds hp] with y hy hyt
  change hyperbolicSpatialCoordinates _=mobiusSpatial _ y
  rw [hy,mobiusSpatial_coordinates_global]
  exact congrArg _ (hyperbolicSpatialChart.right_inv hyt)

lemma kernelCoordinateTransition_contDiffAt (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) : ContDiffAt ℝ ∞ (kernelCoordinateTransition w) p := by
  obtain ⟨M,hM⟩ := kernelCoordinateTransition_eventually w p hp hq
  exact (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq hM

def kernelQuotientChart (q : KernelQuotient) : OpenPartialHomeomorph KernelQuotient SpatialCoordinates :=
  (kernelLocalLift q.out).trans hyperbolicSpatialChart

@[simp] lemma kernelQuotientChart_symm (q : KernelQuotient) (p : SpatialCoordinates) :
    (kernelQuotientChart q).symm p=
      integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p) := by
  change (kernelLocalLift q.out).symm (hyperbolicSpatialChart.symm p)=_
  rw [kernelLocalLift_symm]

lemma kernelQuotientChart_contDiffOn (q r : KernelQuotient) :
    ContDiffOn ℝ ∞ ((kernelQuotientChart q).symm.trans (kernelQuotientChart r))
      ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)).source := by
  intro p hp
  have hp' : p∈hyperbolicSpatialChart.target := hp.1.1
  have hq' : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift r.out).source := by
    rw [← kernelQuotientChart_symm q p]
    exact hp.2.1
  have he : (fun p => ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)) p)=
      kernelCoordinateTransition r.out := by
    funext y
    change hyperbolicSpatialChart (kernelLocalLift r.out ((kernelQuotientChart q).symm y))=_
    rw [kernelQuotientChart_symm]
    rfl
  change ((kernelQuotientChart q).symm.trans (kernelQuotientChart r) : SpatialCoordinates→SpatialCoordinates)=_ at he
  rw [he]
  exact (kernelCoordinateTransition_contDiffAt r.out p hp' hq').contDiffWithinAt

end CubicEisenstein

end

end OAI
end OAIOriginalModule0195

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.SmoothTests
Source SHA256: aba89b76bc4b7c11533c26af4e024843ff64af8f632c909c0802e10788308db6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0196


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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

instance hyperbolicSpatialChartedSpace : ChartedSpace SpatialCoordinates HyperbolicSpace :=
  hyperbolicSpatialChart.singletonChartedSpace hyperbolicSpatialChart_source

instance hyperbolicSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ HyperbolicSpace :=
  hyperbolicSpatialChart.isManifold_singleton hyperbolicSpatialChart_source

lemma kernelLocalLift_source_out (q : KernelQuotient) : q∈(kernelLocalLift q.out).source := by
  have h := kernelQuotient_localHomeomorph.apply_self_mem_localInverseAt_source (x := q.out)
  change integralOrbitProjection globalKubotaKernel q.out∈(kernelLocalLift q.out).source at h
  rwa [show integralOrbitProjection globalKubotaKernel q.out=q from Quotient.out_eq q] at h

instance kernelSpatialChartedSpace : ChartedSpace SpatialCoordinates KernelQuotient where
  atlas := Set.range kernelQuotientChart
  chartAt := kernelQuotientChart
  mem_chart_source q := ⟨kernelLocalLift_source_out q,Set.mem_univ _⟩
  chart_mem_atlas q := ⟨q,rfl⟩

instance kernelSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ KernelQuotient := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨q,rfl⟩ ⟨r,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    kernelQuotientChart_contDiffOn q r

@[simp] lemma hyperbolicSpatial_chartAt (w : HyperbolicSpace) :
    chartAt SpatialCoordinates w=hyperbolicSpatialChart := rfl

@[simp] lemma kernelSpatial_chartAt (q : KernelQuotient) :
    chartAt SpatialCoordinates q=kernelQuotientChart q := rfl

lemma kernelProjection_contMDiff : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
    (integralOrbitProjection globalKubotaKernel) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_integralOrbitProjection globalKubotaKernel).continuousAt,?_⟩
  have hp : hyperbolicSpatialCoordinates w∈hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hq : integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w))∈
      (kernelLocalLift (integralOrbitProjection globalKubotaKernel w).out).source := by
    have hleft := hyperbolicSpatialChart.left_inv (Set.mem_univ w)
    change hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w)=w at hleft
    rw [hleft]
    exact kernelLocalLift_source_out _
  have h : ContDiffWithinAt ℝ ∞
      (kernelCoordinateTransition (integralOrbitProjection globalKubotaKernel w).out) Set.univ
      (hyperbolicSpatialCoordinates w) :=
    (kernelCoordinateTransition_contDiffAt _ _ hp hq).contDiffWithinAt
  unfold kernelCoordinateTransition at h
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    kernelSpatial_chartAt,hyperbolicSpatial_chartAt,kernelCoordinateTransition,
    kernelQuotientChart,OpenPartialHomeomorph.trans_apply,Function.comp_def,
    hyperbolicSpatialChart_apply,id_eq] using h

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal NNReal

def kernelSmoothTests : Submodule ℂ (KernelQuotient→ℂ) where
  carrier f := ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f ∧ HasCompactSupport f
  zero_mem' := ⟨contMDiff_const,HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  smul_mem' c f hf := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c*z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1,hf.2.smul_left⟩

lemma kernelSmoothTests_memLp (f : kernelSmoothTests) :
    MemLp f.1 2 (integralQuotientVolume globalKubotaKernel) :=
  f.2.1.continuous.memLp_of_hasCompactSupport f.2.2

def kernelSmoothTestsToL2 : kernelSmoothTests→ₗ[ℂ]KernelQuotientL2 where
  toFun f := (kernelSmoothTests_memLp f).toLp f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelSmoothTestsToL2_injective : Function.Injective kernelSmoothTestsToL2 := by
  intro f g hfg
  apply Subtype.ext
  apply kernel_continuous_eq_of_ae_eq _ _ f.2.1.continuous g.2.1.continuous
  exact ((kernelSmoothTests_memLp f).toLp_eq_toLp_iff (kernelSmoothTests_memLp g)).mp hfg

lemma kernelL2_smooth_compact_approx (f : KernelQuotientL2) (ε : ℝ) (hε : 0<ε) :
    ∃g : kernelSmoothTests,
      eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)≤
        ENNReal.ofReal ε := by
  obtain ⟨g,hgK,hfg,hgc,hgLp⟩ := kernelL2_continuous_compact_approx f
    (ENNReal.ofReal (ε/2)) (by positivity)
  let mass : ℝ≥0∞ := (integralQuotientVolume globalKubotaKernel Set.univ)^((2:ℝ≥0∞).toReal⁻¹)
  have hm : mass≠(∞:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  let deltaLoss : ℝ := ε/(2*(mass.toReal+1))
  have hδ : 0<deltaLoss := div_pos hε (by positivity)
  obtain ⟨k,hkg,hksupp⟩ := hgc.exists_contMDiff_approx 𝓘(ℝ,SpatialCoordinates) ⊤
    (ε := fun _ => deltaLoss) continuous_const (fun _ => hδ)
  have hkK : HasCompactSupport (k : KernelQuotient→ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hgK (hksupp.trans (subset_tsupport g))
  let kt : kernelSmoothTests := ⟨k,k.contMDiff,hkK⟩
  have hkgLp : eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel)≤
      ENNReal.ofReal (ε/2) := by
    have hb : ∀ᵐ q ∂integralQuotientVolume globalKubotaKernel,‖g q-k q‖≤deltaLoss :=
      Filter.Eventually.of_forall fun q => by
        simpa only [dist_eq_norm,norm_sub_rev] using (hkg q).le
    have hmul : mass.toReal*deltaLoss≤ε/2 := by
      have he : deltaLoss*(2*(mass.toReal+1))=ε := div_mul_cancel₀ _ (by positivity)
      have hp := ENNReal.toReal_nonneg (a := mass)
      nlinarith [mul_nonneg hp hδ.le]
    calc
      _ ≤ mass*ENNReal.ofReal deltaLoss := eLpNorm_le_of_ae_bound (hgc.sub k.contMDiff.continuous).aestronglyMeasurable hb
      _ = ENNReal.ofReal (mass.toReal*deltaLoss) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hm]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal hmul
  refine ⟨kt,?_⟩
  have he : (f : KernelQuotient→ℂ)-kt.1=((f : KernelQuotient→ℂ)-g)+(g-(k : KernelQuotient→ℂ)) := by
    funext q
    change f q-k q=(f q-g q)+(g q-k q)
    ring
  rw [he]
  calc
    _ ≤ eLpNorm ((f : KernelQuotient→ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)+
        eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel) :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hfg hkgLp
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma kernelSmoothTestsToL2_dense : DenseRange kernelSmoothTestsToL2 := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨g,hg⟩ := kernelL2_smooth_compact_approx f (ε/2) (by positivity)
  refine ⟨g,?_⟩
  have he : ‖f-kernelSmoothTestsToL2 g‖=
      (eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans ((Filter.EventuallyEq.refl _ _).sub
      (kernelSmoothTests_memLp g).coeFn_toLp)
  rw [dist_eq_norm,he]
  exact lt_of_le_of_lt ((ENNReal.toReal_mono (by simp) hg).trans_eq (ENNReal.toReal_ofReal (by positivity)))
    (by linarith)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal

lemma hyperbolicSpatialChart_symm_eq {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) :
    hyperbolicSpatialChart.symm p=upperPoint (spatialHorizontal p) (p 2)
      (hyperbolicSpatialChart_target_positive hp) := by
  have h := hyperbolicSpatialCoordinates_reconstruct (hyperbolicSpatialChart.symm p)
  have he : hyperbolicSpatialCoordinates (hyperbolicSpatialChart.symm p)=p :=
    hyperbolicSpatialChart.right_inv hp
  simpa only [he,spatialHorizontal] using h.symm

lemma kernelQuotientDefect_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    {p : SpatialCoordinates} (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientDefect a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedDefectField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p
  rw [smoothCuspSeedDefectField,dite_eq_left (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientDefect_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientDefect a b s) := by
  intro q
  rw [contMDiffAt_iff]
  refine ⟨(kernelQuotientDefect_continuous a b s ha hab).continuousAt,?_⟩
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hF := actual_smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialChart_target_positive hp)
  have he : (fun p => kernelQuotientDefect a b s ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)]
      smoothCuspSeedDefectField a b s := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact kernelQuotientDefect_coordinate a b s q hp
  have hh := hF.congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

def kernelDefectSmoothTest (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) : kernelSmoothTests :=
  ⟨kernelQuotientDefect a b s,kernelQuotientDefect_contMDiff a b s ha hab,
    kernelQuotientDefect_hasCompactSupport a b (by linarith) hab s⟩

lemma kernelDefectSmoothTest_toL2 (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) :
    kernelSmoothTestsToL2 (kernelDefectSmoothTest a b ha hab s)=
      kernelL2Defect a b (by linarith) hab s := rfl

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma quotient_span_fixed (r : O) (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x) :
    Ideal.span {secondExpansionQuotient p x}=Ideal.span {r} := by
  obtain ⟨hE,hr⟩ := hx
  rwa [secondExpansionQuotient_of_subset p x hE]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma quotient_norm_fixed (r : O) (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x) :
    elementNorm (secondExpansionQuotient p x)=elementNorm r := by
  simp only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,quotient_span_fixed p r x hx]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma residualScale_fixed (Z : ℝ) (r : O) (x : SecondExpansionData ι)
    (hx : InSecondQuotientSector p r x) :
    residualScale p Z x=Z/(elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)*elementNorm r) := by
  rw [residualScale,quotient_norm_fixed p r x hx]

variable (hp : ∀i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem postCommonSmoothPair_fixed_mask (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m r f y₁ y₂ : O)
    (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (z ud ue uv kap X₁ X₂ R : ℝ) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*secondExpansionQuotient p x) f y₁ y₂
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R=
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r) f y₁ y₂
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R := by
  have hm : Ideal.span {m*secondExpansionQuotient p x}=Ideal.span {m*r} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      quotient_span_fixed p r x hx]
  simp only [postCommonSmoothPair,secondChildColumn,rowCoprimeMask_congr_span p _ hm]

theorem sourceWeight_norm_fixed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex) (Z H : ℝ) (x : SecondExpansionData ι)
    (hx : InSecondQuotientSector p r x) (hZ : 0<Z) (hH : 0≤H)
    (hΨG : ‖Ψ (∏i∈x.sourceCommon,p i)‖≤1) (hΨV : ‖Ψ (∏i∈x.overlap,p i)‖≤1) :
    ‖sourceWeight p hp hcop hg Ψ m ray Z H x‖≤H*elementNorm r/Z^2*‖secondRayCoefficient ray‖ := by
  simpa only [quotient_norm_fixed p r x hx] using
    sourceWeight_norm_le p hp hcop hg hinj hc Ψ m ray Z H x hZ hH hΨG hΨV

end

lemma normCharacter_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (a : O) :
    ‖normCharacter χ a‖≤1 := χ.norm_le_one _

lemma conjugateMonoid_norm_le_one (Ψ : O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (a : O) :
    ‖conjugateMonoid Ψ a‖≤1 := by
  simpa only [conjugateMonoid,MonoidHom.coe_mk,OneHom.coe_mk,norm_star] using hΨ a

end
section

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
def sourceLogZ (Z X : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap*X/residualScale p Z x)
def sourceLogE (E : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)/E)
def sourceLogV (V : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap/V)
def sourceLogK (K : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (elementNorm (sourceObservation p x).1/K)
end

theorem initial_sector_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<E → 0<V → 0<X → 0<K →
        (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        initialSourceSum p hp hcop hg s (sourceWeight p hp hcop hg Ψ m ray Z H)
          F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r) A₁ A₂ W windows
          (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K)
          X X (H*K/(E^2*V^2*X^2)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_source_fixed_profiles
    U hUc hUs g₁ g₂ W A 2 hA (by norm_num) hU₁ hU₂ hg₁ hg₂
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap
  calc
    _ = ∑x∈s,secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
        (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
        (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H := by
          simp only [secondExpansionSource,Finset.sum_singleton]
    _ = _ := by
      unfold initialSourceSum
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨hsubset,_⟩ := hs x hx
      have hh := hid p hp hcop hg hinj hpr F Ψ m ray x Z H E V X K
        hsubset (hk x hx) hZ hE hV hX hK (hz x hx) (he x hx) (hv x hx) (hkap x hx)
      rw [hh]
      rw [postCommonSmoothPair_fixed_mask p hp hcop hg F (secondRayMinus Ψ ray)
        (secondRayPlus Ψ ray) m r _ _ _ x (hs x hx)]
      rfl

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)

theorem initial_sector_transfer
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀t,g t≠0→U t=1) (hgA : ∀t,g t≠0→|t|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃ (windows : Fin 7→ℝ→ℂ) (C Cₛ : ℝ),0≤C ∧ 0≤Cₛ ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<H → 0<E → 0<V → 0<X → 0<K →
        (∀a,‖Ψ a‖≤1) → (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        ∃ B : Frequency→ℝ,
          (∀q,0≤B q) ∧
          (∀q,(1+H*K/(E^2*V^2*X^2))^N*B q≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S)
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H‖≤
          (C*H*elementNorm r/Z^2*‖secondRayCoefficient ray‖*(K*Real.exp 2)^ε)*
            (∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_sector_fixed_profiles
    U hUc hUs g g W A hA hU hU hgA hgA
  obtain ⟨Cw,hCw,hwbound⟩ := outerWindow_global_bound windows hwc (fun i => (hws i).continuous)
  have hM : 0≤A+2+1 := by linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := initial_source_uniform_transfer ε hε A₁ A₂ W windows
    (fun _ => A+2+1) (fun _ => hM) hwb N J
  refine ⟨windows,Cw*Cₐ,Cₛ,mul_nonneg hCw hCₐ.le,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m r ray s Z H E V X K hZ hH hE hV hX hK hΨ hs hk hz he hv hkap
  let R := H*K/(E^2*V^2*X^2)
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨b,hpoint,hbound⟩ := htrans R hR
  let B : Frequency→ℝ := fun q => ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b q‖
  refine ⟨B,fun q => norm_nonneg _,?_,?_⟩
  · intro q
    simpa only [B,R,tripleCoefficient,mul_assoc] using hpoint q.1 q.2.1 q.2.2
  · let T := s.image (sourceObservation p)
    have hT0 : ∀y∈T,y.1≠0 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact sourceRow_nonzero p x (hk x hx)
    have hTK : ∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K*Real.exp 2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hpos := elementNorm_pos _ (sourceRow_nonzero p x (hk x hx))
      have hl : Real.log (elementNorm (sourceObservation p x).1/K)≤2 :=
        (le_abs_self _).trans (hkap x hx)
      have hh := Real.exp_le_exp.mpr hl
      rw [Real.exp_log (div_pos hpos hK)] at hh
      have hh' := (div_le_iff₀ hK).mp hh
      simpa only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,mul_comm] using hh'
    let D := H*elementNorm r/Z^2*‖secondRayCoefficient ray‖
    have hD : 0≤D := by dsimp [D,elementNorm]; positivity
    have hweights : ∀x∈s,‖sourceWeight p hp hcop hg Ψ m ray Z H x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)‖≤D*Cw := by
      intro x hx
      exact mul_le_mul (sourceWeight_norm_fixed p hp hcop hg hinj hc Ψ m r ray Z H x
        (hs x hx) hZ hH.le (hΨ _) (hΨ _)) (hwbound _ _ _ _ _) (norm_nonneg _) hD
    have hh := hbound p hp hcop hg hinj r s T (sourceWeight p hp hcop hg Ψ m ray Z H) (D*Cw)
      (K*Real.exp 2) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r)
      (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K) X X
      (mul_nonneg hD hCw) (by positivity) hs (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hT0 hTK hweights
    rw [hid p hp hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap]
    convert hh using 1 ; dsimp [D,B,R,T] ; ring

end InitialMeanSquare

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem descent_ideal_inverse_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀ I∈S,(Ideal.absNorm I : ℝ)≤H) :
    (∑ I∈S,1/(Ideal.absNorm I : ℝ))≤128*Real.exp 1*(normLogBin H+1 : ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  let T := Finset.range (normLogBin H+1)
  let bin (j : ℕ) := S.filter (fun I => normLogBin (Ideal.absNorm I)=j)
  have hmap : ∀ I∈S,normLogBin (Ideal.absNorm I : ℝ)∈T := by
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (normLogBin_mono (by linarith [hpos I hI]) (hH I hI)))
  have hbin (j : ℕ) : (∑ I∈bin j,1/(Ideal.absNorm I : ℝ))≤128*Real.exp 1 := by
    have hp := normLogScale_pos j
    have hone := normLogScale_ge_one j
    have he := Real.one_le_exp (show (0 : ℝ)≤1 by norm_num)
    have hc : ((bin j).card : ℝ)≤128*(normLogScale j*Real.exp 1) := by
      apply DescentFiberCost.finite_ideal_count_real _ _ (by nlinarith)
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        simpa only [hj] using (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).2
    have ht (I : Ideal O) (hI : I∈bin j) : 1/(Ideal.absNorm I : ℝ)≤1/normLogScale j := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).1
      rw [hj] at hb
      exact one_div_le_one_div_of_le hp hb
    calc
      _ ≤ ∑ _I∈bin j,1/normLogScale j := Finset.sum_le_sum ht
      _ = ((bin j).card : ℝ)/normLogScale j := by simp [div_eq_mul_inv]
      _ ≤ (128*(normLogScale j*Real.exp 1))/normLogScale j := div_le_div_of_nonneg_right hc hp.le
      _ = _ := by field_simp
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _j∈T,128*Real.exp 1 := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp [T]; ring

theorem descent_normLogBin_small_power (ε : ℝ) (hε : 0<ε) (H : ℝ) (hH : 1≤H) :
    (normLogBin H+1 : ℝ)≤(1+1/ε)*H^ε := by
  have hH0 : 0<H := by linarith
  have hb : (normLogBin H : ℝ)≤Real.log H := Nat.floor_le (Real.log_nonneg hH)
  have hl := Real.log_le_rpow_div hH0.le hε
  have hp := Real.one_le_rpow hH hε.le
  calc
    _ ≤ H^ε/ε+1 := by linarith
    _ ≤ H^ε/ε+H^ε := add_le_add le_rfl hp
    _ = _ := by ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

def cubeProductIdeal (x : CubeCoordinates ι) : Ideal O :=
  Ideal.span {primeProduct p x.support x.leftExponent}*
    Ideal.span {primeProduct p x.support x.rightExponent}

def cubeParityKey (x : CubeCoordinates ι) : Ideal O × Ideal O :=
  (Ideal.span {squarefreeLabel p x.support (fun i => x.leftExponent i+x.rightExponent i)},
   Ideal.span {b0Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit*
     j2Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit})

def cubeDivisorKey (x : CubeCoordinates ι) : Fin 3 → Ideal O :=
  ![Ideal.span {primeProduct p x.support x.leftExponent},
    Ideal.span {aLabel p x.support x.leftBit},Ideal.span {aLabel p x.support x.rightBit}]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_product (x : CubeCoordinates ι) :
    cubeProductIdeal p x=(cubeParityKey p x).2^2*(cubeParityKey p x).1 := by
  have h := FirstPassCubeLabels.cube_pair_product_decomposition p x.support
    x.leftExponent x.rightExponent x.leftBit x.rightBit x.support_pos
  have h' := congrArg (fun z : O => (Ideal.span {z} : Ideal O)) h
  simp only [cubeProductIdeal,cubeParityKey,pow_two,←Ideal.span_singleton_mul_span_singleton] at h' ⊢
  convert h' using 1 ; congr 1 ; ring

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeDivisorKey_dvd (x : CubeCoordinates ι) (i : Fin 3) :
    cubeDivisorKey p x i ∣ cubeProductIdeal p x := by
  have hA1 := span_dvd_of_element_dvd
    (aLabel_dvd_primeProduct p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.support_pos)
  have hA2 := span_dvd_of_element_dvd
    (aLabel_dvd_primeProduct p x.support (fun i => x.leftExponent i+x.rightExponent i) x.rightBit x.support_pos)
  rw [primeProduct_add,←Ideal.span_singleton_mul_span_singleton] at hA1 hA2
  fin_cases i
  · exact dvd_mul_right _ _
  · exact hA1
  · exact hA2

variable (hp : ∀ i,p i≠0)
include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_ne_zero (x : CubeCoordinates ι) :
    (cubeParityKey p x).1≠0 ∧ (cubeParityKey p x).2≠0 := by
  constructor
  · exact (Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp _ _)
  · exact (Ideal.span_singleton_eq_bot.not).mpr
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeProductIdeal_ne_zero (x : CubeCoordinates ι) : cubeProductIdeal p x≠0 := by
  rw [cubeParityKey_product]
  exact mul_ne_zero (pow_ne_zero _ (cubeParityKey_ne_zero p hp x).2) (cubeParityKey_ne_zero p hp x).1

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem cubeDivisorKey_injective_on_product {x y : CubeCoordinates ι}
    (hx : x.Admissible) (hy : y.Admissible)
    (hprod : cubeProductIdeal p x=cubeProductIdeal p y)
    (hk : cubeDivisorKey p x=cubeDivisorKey p y) : x=y := by
  have h1 := congrFun hk 0
  have hA1 := congrFun hk 1
  have hA2 := congrFun hk 2
  change Ideal.span {primeProduct p x.support x.leftExponent}=
    Ideal.span {primeProduct p y.support y.leftExponent} at h1
  have h2 : Ideal.span {primeProduct p x.support x.rightExponent}=
    Ideal.span {primeProduct p y.support y.rightExponent} := by
    apply mul_left_cancel₀ ((Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp x.support x.leftExponent))
    simpa only [cubeProductIdeal,h1] using hprod
  have hv1 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.leftExponent y.leftExponent x.left_off y.left_off h1
  have hv2 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.rightExponent y.rightExponent x.right_off y.right_off h2
  change Ideal.span {aLabel p x.support x.leftBit}=Ideal.span {aLabel p y.support y.leftBit} at hA1
  change Ideal.span {aLabel p x.support x.rightBit}=Ideal.span {aLabel p y.support y.rightBit} at hA2
  rw [CubeCoordinates.aLabel_left p x hx,CubeCoordinates.aLabel_left p y hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA1
  rw [CubeCoordinates.aLabel_right p x hx,CubeCoordinates.aLabel_right p y hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA2
  exact CubeCoordinates.ext (Finsupp.ext (congrFun hv1)) (Finsupp.ext (congrFun hv2))
    (FirstCauchyArithmetic.family_product_injective _ hinj hA1)
    (FirstCauchyArithmetic.family_product_injective _ hinj hA2)

theorem cubeParityKey_fiber_card (s : Finset (CubeCoordinates ι)) (q : Ideal O × Ideal O)
    (hq1 : q.1≠0) (hq2 : q.2≠0) (hs : ∀ x∈s,x.Admissible)
    (hk : ∀ x∈s,cubeParityKey p x=q) :
    s.card≤(idealDivisors (q.2^2*q.1)).card^3 := by
  let D := idealDivisors (q.2^2*q.1)
  have hprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq2) hq1
  let encode (x : s) : Fin 3 → D := fun i => ⟨cubeDivisorKey p x.val i,by
    apply (mem_idealDivisors hprod0).mpr
    have h := cubeDivisorKey_dvd p x.val i
    simpa only [cubeParityKey_product,hk x.val x.property] using h⟩
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply cubeDivisorKey_injective_on_product p hp hinj (hs _ x.property) (hs _ y.property)
    · simp only [cubeParityKey_product,hk _ x.property,hk _ y.property]
    · funext i
      exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,D] using Fintype.card_le_of_injective encode hi

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0196

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.DivisorTargets
Source SHA256: ae1b1b13dcf96ea3040b69a4e4cffcc301a2dded5b72860ffde9210b51ac603f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0197


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
open scoped BigOperators

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic

lemma parity_pair_norm_bounds (s u : Ideal O) (B : ℝ) (hB : 0<B)
    (hs : s≠0) (hu : u≠0)
    (h : (Ideal.absNorm u : ℝ)^2*Ideal.absNorm s≤B^2) :
    (Ideal.absNorm s : ℝ)≤B^2 ∧ (Ideal.absNorm u : ℝ)≤B/Real.sqrt (Ideal.absNorm s) := by
  have hs1 : 1≤(Ideal.absNorm s : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hs (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu1 : 1≤(Ideal.absNorm u : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hu (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs0 : 0<(Ideal.absNorm s : ℝ) := by linarith
  have hsqrt : 0<Real.sqrt (Ideal.absNorm s : ℝ) := Real.sqrt_pos.mpr hs0
  refine ⟨(le_mul_of_one_le_left hs0.le (one_le_pow₀ hu1)).trans h,?_⟩
  apply (le_div_iff₀ hsqrt).mpr
  have hh : ((Ideal.absNorm u : ℝ)*Real.sqrt (Ideal.absNorm s : ℝ))^2≤B^2 := by
    simpa only [mul_pow,Real.sq_sqrt hs0.le] using h
  nlinarith [mul_nonneg (Nat.cast_nonneg (Ideal.absNorm u)) hsqrt.le]

lemma parity_pair_fiber_count (S : Finset (Ideal O × Ideal O)) (B : ℝ) (hB : 0<B)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2)
    (s : Ideal O) (hs : s∈S.image Prod.fst) :
    ((S.filter (fun x => x.1=s)).card : ℝ)≤128*B/Real.sqrt (Ideal.absNorm s) := by
  obtain ⟨x,hx,hxs⟩ := Finset.mem_image.mp hs
  have hnx := parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2
  have hu1 : 1≤(Ideal.absNorm x.2 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (hS x hx).2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤B/Real.sqrt (Ideal.absNorm s) := by simpa only [hxs] using hu1.trans hnx.2
  let T := S.filter (fun x => x.1=s)
  have hi : Set.InjOn (fun x : Ideal O × Ideal O => x.2) (↑T : Set (Ideal O × Ideal O)) := by
    intro x hx y hy he
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) he
  have hcount := DescentFiberCost.finite_ideal_count_real (T.image Prod.snd)
    (B/Real.sqrt (Ideal.absNorm s)) hscale (fun u hu => by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      exact (hS x (Finset.mem_filter.mp hx).1).2.1) (fun u hu => by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      have hn := parity_pair_norm_bounds x.1 x.2 B hB (hS x (Finset.mem_filter.mp hx).1).1
        (hS x (Finset.mem_filter.mp hx).1).2.1 (hS x (Finset.mem_filter.mp hx).1).2.2
      simpa only [(Finset.mem_filter.mp hx).2] using hn.2)
  rw [Finset.card_image_iff.mpr hi] at hcount
  simpa only [mul_div_assoc] using hcount

theorem parity_ideal_pair_count (S : Finset (Ideal O × Ideal O)) (B H : ℝ)
    (hB : 0<B) (hH : 0≤H)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2)
    (hactive : ∀ x∈S,(Ideal.absNorm x.1 : ℝ)≤H^2) :
    (S.card : ℝ)≤16384*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ) := by
  let A := S.image Prod.fst
  have hA (s : Ideal O) (hs : s∈A) : s≠0 ∧ (Ideal.absNorm s : ℝ)≤B^2 ∧ (Ideal.absNorm s : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hS x hx).1,(parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).1,hactive x hx⟩
  have he : (S.card : ℝ)=∑s∈A,((S.filter (fun x => x.1=s)).card : ℝ) := by
    calc
      _ = ∑_x∈S,(1 : ℝ) := by simp
      _ = ∑s∈A,∑_x∈S.filter (fun x => x.1=s),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem Prod.fst hx) _).symm
      _ = _ := by simp
  rw [he]
  have hpoint (s : Ideal O) (hs : s∈A) :
      1/Real.sqrt (Ideal.absNorm s : ℝ)≤H/(Ideal.absNorm s : ℝ) := by
    have hs0 : 0<(Ideal.absNorm s : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun hz => (hA s hs).1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hroot : 0<Real.sqrt (Ideal.absNorm s : ℝ) := Real.sqrt_pos.mpr hs0
    have hrootle : Real.sqrt (Ideal.absNorm s : ℝ)≤H := by nlinarith [Real.sq_sqrt hs0.le,(hA s hs).2.2]
    apply (div_le_div_iff₀ hroot hs0).mpr
    nlinarith [Real.sq_sqrt hs0.le]
  calc
    _ ≤ ∑s∈A,128*B/Real.sqrt (Ideal.absNorm s) :=
      Finset.sum_le_sum (fun s hs => parity_pair_fiber_count S B hB hS s hs)
    _ ≤ ∑s∈A,(128*B*H)*(1/(Ideal.absNorm s : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have h := mul_le_mul_of_nonneg_left (hpoint s hs) (by positivity : 0≤128*B)
      convert h using 1 <;> ring
    _ = (128*B*H)*∑s∈A,1/(Ideal.absNorm s : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (128*B*H)*(128*Real.exp 1*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (descent_ideal_inverse_sum A (B^2) (fun s hs => (hA s hs).1)
        (fun s hs => (hA s hs).2.1)) (by positivity)
    _ = _ := by ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_norm_product (x : CubeCoordinates ι) :
    (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1 =
      ‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2*
        ‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2 := by
  have h := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (cubeParityKey_product p x)
  simpa only [cubeProductIdeal,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,
    ←eisEmbedding_norm_sq_eq_absNorm_span] using h.symm

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_active_bound (x : CubeCoordinates ι) (H : ℝ)
    (ha : ‖eisEmbedding (∏ i∈cubeActiveSupport x.support
      (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) :
    (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤H^2 := by
  have h := squarefreeLabel_active_bound p hp x.support
    (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit
  change ‖eisEmbedding _‖^2≤‖eisEmbedding _‖^2 at h
  exact (show (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤‖eisEmbedding
    (∏ i∈cubeActiveSupport x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖^2 from
    by simpa only [cubeParityKey,←eisEmbedding_norm_sq_eq_absNorm_span] using h).trans
      (pow_le_pow_left₀ (norm_nonneg _) ha 2)

end

theorem cube_coordinates_parity_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B H : ℝ),
      1≤B → 0≤H → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) →
      (s.card : ℝ)≤C*B^(1+ε)*H := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(16384*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B H hB hH hs hb1 hb2 ha
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hQactive (q : Ideal O × Ideal O) (hq : q∈Q) : (Ideal.absNorm q.1 : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact cubeParityKey_active_bound p hp x H (ha x hx)
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hqcard := parity_ideal_pair_count Q B H hB0 hH hQ hQactive
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hsum : (s.card : ℝ)=∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ) := by
    calc
      _ = ∑_x∈s,(1 : ℝ) := by simp
      _ = ∑q∈Q,∑_x∈s.filter (fun x => cubeParityKey p x=q),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by simp
  rw [hsum]
  calc
    _ ≤ ∑_q∈Q,D^3*B^(ε/2) := Finset.sum_le_sum hfiber
    _ = (Q.card : ℝ)*(D^3*B^(ε/2)) := by simp
    _ ≤ (16384*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ))*(D^3*B^(ε/2)) := by gcongr
    _ ≤ (16384*Real.exp 1*B*H*((1+1/(ε/4))*B^(ε/2)))*(D^3*B^(ε/2)) := by gcongr
    _ = C*B^(1+ε)*H := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(16384*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2))*H := by ring
        _ = _ := by rw [he]; ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors)

theorem parity_ideal_pair_inverse_sqrt_sum (S : Finset (Ideal O × Ideal O)) (B : ℝ)
    (hB : 0<B)
    (hS : ∀ x∈S,x.1≠0 ∧ x.2≠0 ∧ (Ideal.absNorm x.2 : ℝ)^2*Ideal.absNorm x.1≤B^2) :
    (∑q∈S,1/Real.sqrt (Ideal.absNorm q.1 : ℝ))≤
      16384*Real.exp 1*B*(normLogBin (B^2)+1 : ℝ) := by
  let A := S.image Prod.fst
  have hA (s : Ideal O) (hs : s∈A) : s≠0 ∧ (Ideal.absNorm s : ℝ)≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(hS x hx).1,(parity_pair_norm_bounds x.1 x.2 B hB (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).1⟩
  have he : (∑q∈S,1/Real.sqrt (Ideal.absNorm q.1 : ℝ))=
      ∑s∈A,((S.filter (fun x => x.1=s)).card : ℝ)/Real.sqrt (Ideal.absNorm s : ℝ) := by
    calc
      _ = ∑s∈A,∑q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm q.1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem Prod.fst hx) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        have h : (∑q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm q.1 : ℝ))=
            ∑_q∈S.filter (fun x => x.1=s),1/Real.sqrt (Ideal.absNorm s : ℝ) :=
          Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])
        rw [h]
        simp [div_eq_mul_inv]
  rw [he]
  calc
    _ ≤ ∑s∈A,128*B/(Ideal.absNorm s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hpos : 0<(Ideal.absNorm s : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun hz => (hA s hs).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      calc
        _ ≤ (128*B/Real.sqrt (Ideal.absNorm s : ℝ))/Real.sqrt (Ideal.absNorm s : ℝ) :=
          div_le_div_of_nonneg_right (parity_pair_fiber_count S B hB hS s hs) (Real.sqrt_nonneg _)
        _ = _ := by rw [div_div,←pow_two,Real.sq_sqrt hpos.le]
    _ = (128*B)*∑s∈A,1/(Ideal.absNorm s : ℝ) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs; ring
    _ ≤ (128*B)*(128*Real.exp 1*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (descent_ideal_inverse_sum A (B^2)
        (fun s hs => (hA s hs).1) (fun s hs => (hA s hs).2)) (by positivity)
    _ = _ := by ring

theorem cube_coordinates_inverse_active_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B : ℝ),
      1≤B → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∑x∈s,1/‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)≤C*B^(1+ε) := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(16384*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B hB hs hb1 hb2
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hpoint (x : CubeCoordinates ι) :
      1/‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤
        1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) := by
    have hs0 : 0<(Ideal.absNorm (cubeParityKey p x).1 : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun hz => (cubeParityKey_ne_zero p hp x).1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have ha := cubeParityKey_active_bound p hp x _ le_rfl
    have hh : Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ)≤
        ‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖ := by
      nlinarith [Real.sq_sqrt hs0.le,norm_nonneg (eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i))]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hs0) hh
  have he : (∑x∈s,1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ))=
      ∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)*(1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := by
    calc
      _ = ∑q∈Q,∑x∈s.filter (fun x => cubeParityKey p x=q),1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun x (hx : x∈s.filter (fun x => cubeParityKey p x=q)) =>
          show 1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ)=1/Real.sqrt (Ideal.absNorm q.1 : ℝ) by
            rw [(Finset.mem_filter.mp hx).2])
        rw [h]
        simp
  calc
    _ ≤ ∑x∈s,1/Real.sqrt (Ideal.absNorm (cubeParityKey p x).1 : ℝ) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := he
    _ ≤ ∑q∈Q,(D^3*B^(ε/2))*(1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := by
      exact Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (by positivity))
    _ = (D^3*B^(ε/2))*(∑q∈Q,1/Real.sqrt (Ideal.absNorm q.1 : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D^3*B^(ε/2))*(16384*Real.exp 1*B*(normLogBin (B^2)+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (parity_ideal_pair_inverse_sqrt_sum Q B hB0 hQ) (by positivity)
    _ ≤ (D^3*B^(ε/2))*(16384*Real.exp 1*B*((1+1/(ε/4))*B^(ε/2))) := by gcongr
    _ = C*B^(1+ε) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(16384*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2)) := by ring
        _ = _ := by rw [he]; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalFirst_diagonal_scalar (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (side : Bool) (b : GlobalFirstData ι) :
    globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹ ≤
      (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*
        (1/primeProductNorm p b.firstCommon)*
        (1/‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  let A := globalCubeActiveRoot p x
  have hbds := globalScaleIndex_bounds p hp side x (by exact one_ne_zero)
  have hc := (hbds 1).2
  have ha := (hbds 9).2
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  change A^2≤globalLogRep j 9*Real.exp 1 at ha
  have hcp := FirstPassCubeLabels.primeProductNorm_pos p hp b.common
  have htp := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
  have hA := globalCubeActiveRoot_pos p hp x
  change 0<A at hA
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h1p := globalLogRep_pos j 1
  have h4p := globalLogRep_pos j 4
  have h5p := globalLogRep_pos j 5
  have h9p := globalLogRep_pos j 9
  have h9s := Real.sqrt_pos.mpr h9p
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have has : A≤Real.sqrt (globalLogRep j 9)*Real.exp 1 := by
    apply (sq_le_sq₀ hA.le (mul_nonneg h9s.le (Real.exp_pos _).le)).mp
    rw [mul_pow,Real.sq_sqrt h9p.le]
    exact ha.trans (mul_le_mul_of_nonneg_left (by nlinarith : Real.exp 1≤(Real.exp 1)^2) h9p.le)
  have hcA : primeProductNorm p b.common*A ≤
      (Real.exp 1)^2*((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by
    calc
      _ ≤ (globalLogRep j 1*Real.exp 1)*(Real.sqrt (globalLogRep j 9)*Real.exp 1) :=
        mul_le_mul hc has hA.le (by positivity)
      _ = (Real.exp 1)^2*(globalLogRep j 1*1*1*Real.sqrt (globalLogRep j 9)) := by ring
      _ ≤ (Real.exp 1)^2*(globalLogRep j 1*globalLogRep j 1*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by gcongr
      _ = _ := by ring
  have hr : 1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9))≤
      (Real.exp 1)^2/(primeProductNorm p b.common*A) := by
    apply (div_le_div_iff₀ (by positivity) (mul_pos hcp hA)).mpr
    simpa only [one_mul] using hcA
  change (K/(globalLogRep j 5*ell*B^2*F*Real.sqrt (globalLogRep j 9)))*
      (Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4))*
      (primeProductNorm p b.firstCommon)⁻¹≤_
  calc
    _ = (Real.exp 1*ell*B^2*F)*(1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)))*
        (primeProductNorm p b.firstCommon)⁻¹ := by field_simp
    _ ≤ (Real.exp 1*ell*B^2*F)*((Real.exp 1)^2/(primeProductNorm p b.common*A))*
        (primeProductNorm p b.firstCommon)⁻¹ := by gcongr
    _ = _ := by change _ = (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*(1/A); ring

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def globalFirstCountKey (b : GlobalFirstData ι) : CubeCoordinates ι × Finset ι × Finset ι :=
  (b.cube,b.common,b.firstCommon)

def globalFirstDivisorTarget (q : CubeCoordinates ι × Finset ι × Finset ι) : Ideal O :=
  (∏i∈q.2.1,Ideal.span {p i})*(∏i∈q.1.support,Ideal.span {p i})

theorem globalFirstDivisorTarget_ne_zero (q : CubeCoordinates ι × Finset ι × Finset ι) :
    globalFirstDivisorTarget p q≠0 := by
  apply mul_ne_zero <;> exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirst_divisor_dvd_target (b : GlobalFirstData ι) (hb : GlobalFirstAdmissible b) :
    (∏i∈b.firstDivisor,Ideal.span {p i})∣globalFirstDivisorTarget p (globalFirstCountKey b) := by
  have h := Finset.prod_dvd_prod_of_subset b.firstDivisor (b.common∪b.cube.support)
    (fun i => (Ideal.span {p i} : Ideal O)) hb.2.2
  rw [Finset.prod_union hb.2.1] at h
  exact h

include hinj in
theorem globalFirst_divisor_fiber_card (s : Finset (GlobalFirstData ι))
    (q : CubeCoordinates ι × Finset ι × Finset ι)
    (hs : ∀b∈s,GlobalFirstAdmissible b) (hq : ∀b∈s,globalFirstCountKey b=q) :
    s.card≤(idealDivisors (globalFirstDivisorTarget p q)).card := by
  let D := idealDivisors (globalFirstDivisorTarget p q)
  let encode (b : s) : D := ⟨∏i∈b.val.firstDivisor,Ideal.span {p i},by
    apply (mem_idealDivisors (globalFirstDivisorTarget_ne_zero p q)).mpr
    simpa only [hq b.val b.property] using globalFirst_divisor_dvd_target p b.val (hs b.val b.property)⟩
  have hi : Function.Injective encode := by
    intro b c he
    have hd := FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj (congrArg Subtype.val he)
    have hk := (hq b.val b.property).trans (hq c.val c.property).symm
    apply Subtype.ext
    exact GlobalFirstData.ext (congrArg Prod.fst hk) (congrArg (fun q => q.2.2) hk)
      (congrArg (fun q => q.2.1) hk) hd
  simpa only [Fintype.card_coe,D] using Fintype.card_le_of_injective encode hi

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstDivisorTarget_norm_bound (b : GlobalFirstData ι) (B U : ℝ)
    (hB : 0≤B) (hU : 0≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    (Ideal.absNorm (globalFirstDivisorTarget p (globalFirstCountKey b)) : ℝ)≤U*B^2 := by
  have hrad := globalCube_radical_bound p hp B hB (b.append ⟨∅,∅,∅,1⟩) hb1 hb2
  change (Ideal.absNorm ((∏i∈b.common,Ideal.span {p i})*(∏i∈b.cube.support,Ideal.span {p i})) : ℝ)≤_
  rw [map_mul,Nat.cast_mul,←primeProductNorm_eq_ideal_norm,←primeProductNorm_eq_ideal_norm]
  exact mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le hU

include hinj in
theorem primeSupport_inverse_sum (s : Finset (Finset ι)) (U : ℝ)
    (hs : ∀S∈s,primeProductNorm p S≤U) :
    (∑S∈s,1/primeProductNorm p S)≤128*Real.exp 1*(normLogBin U+1 : ℝ) := by
  let f := fun S : Finset ι => ∏i∈S,(Ideal.span {p i} : Ideal O)
  have hi : Function.Injective f := FirstCauchyArithmetic.family_product_injective _ hinj
  have he : (∑S∈s,1/primeProductNorm p S)=∑I∈s.image f,1/(Ideal.absNorm I : ℝ) := by
    rw [Finset.sum_image (fun S _ T _ h => hi h)]
    exact Finset.sum_congr rfl (fun S hS => by rw [primeProductNorm_eq_ideal_norm])
  rw [he]
  apply descent_ideal_inverse_sum
  · intro I hI
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro I hI
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hI
    simpa only [f,←primeProductNorm_eq_ideal_norm] using hs S hS

end

theorem globalFirstData_harmonic_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (B U : ℝ),
      1≤B → 1≤U → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
        (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))≤
        C*B^(1+ε)*(U*B^2)^ε*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2 := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  obtain ⟨E,hE,hcube⟩ := cube_coordinates_inverse_active_sum ε hε
  refine ⟨D*E,mul_pos hD hE,?_⟩
  intro ι _ p hp _ hinj s B U hB hU hs hC ht hb1 hb2
  let Q := s.image globalFirstCountKey
  let cubes := s.image GlobalFirstData.cube
  let commons := s.image GlobalFirstData.common
  let firsts := s.image GlobalFirstData.firstCommon
  let weight := fun q : CubeCoordinates ι × Finset ι × Finset ι =>
    (1/primeProductNorm p q.2.1)*(1/primeProductNorm p q.2.2)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport q.1.support
        (fun i => q.1.leftExponent i+q.1.rightExponent i) q.1.leftBit q.1.rightBit,p i)‖)
  have hw (q : CubeCoordinates ι × Finset ι × Finset ι) : 0≤weight q := by
    have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp q.2.1).le
    have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp q.2.2).le
    dsimp [weight]
    positivity
  have hfiber (q : CubeCoordinates ι × Finset ι × Finset ι) (hq : q∈Q) :
      ((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)≤D*(U*B^2)^ε := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    have hc : ((s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b)).card : ℝ)≤
        ((idealDivisors (globalFirstDivisorTarget p (globalFirstCountKey b))).card : ℝ) := by
      exact_mod_cast globalFirst_divisor_fiber_card p hinj (s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b))
        (globalFirstCountKey b) (fun d hd => hs d (Finset.mem_filter.mp hd).1) (fun d hd => (Finset.mem_filter.mp hd).2)
    apply hc.trans ((hdiv _ (globalFirstDivisorTarget_ne_zero p _)).trans _)
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (globalFirstDivisorTarget_norm_bound p hp b B U (by linarith) (by linarith) (hC b hb) (hb1 b hb) (hb2 b hb)) hε.le
  have hsub : Q⊆cubes.product (commons.product firsts) := by
    intro q hq
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,Finset.mem_image_of_mem _ hb⟩⟩
  have he : (∑b∈s,weight (globalFirstCountKey b))=
      ∑q∈Q,((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)*weight q := by
    calc
      _ = ∑q∈Q,∑b∈s.filter (fun b => globalFirstCountKey b=q),weight (globalFirstCountKey b) :=
        (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_image_of_mem globalFirstCountKey hb) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun b (hb : b∈s.filter (fun b => globalFirstCountKey b=q)) =>
          show weight (globalFirstCountKey b)=weight q by rw [(Finset.mem_filter.mp hb).2])
        rw [h]
        simp
  have hcube' := hcube p hp hinj cubes B hB (by
      intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact (hs b hb).1)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb1 b hb)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb2 b hb)
  have hC' := primeSupport_inverse_sum p hinj commons U (by
    intro C hCmem; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hCmem; exact hC b hb)
  have ht' := primeSupport_inverse_sum p hinj firsts U (by
    intro T hT; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hT; exact ht b hb)
  have hC0 : 0≤∑C∈commons,1/primeProductNorm p C :=
    Finset.sum_nonneg (fun C _ => one_div_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp C).le)
  have ht0 : 0≤∑T∈firsts,1/primeProductNorm p T :=
    Finset.sum_nonneg (fun T _ => one_div_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp T).le)
  change (∑b∈s,weight (globalFirstCountKey b))≤_
  rw [he]
  calc
    _ ≤ ∑q∈Q,(D*(U*B^2)^ε)*weight q := Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (hw q))
    _ = (D*(U*B^2)^ε)*∑q∈Q,weight q := (Finset.mul_sum _ _ _).symm
    _ ≤ (D*(U*B^2)^ε)*∑q∈cubes.product (commons.product firsts),weight q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw q)) (by positivity)
    _ = (D*(U*B^2)^ε)*
        ((∑x∈cubes,1/‖eisEmbedding (∏i∈cubeActiveSupport x.support
          (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)*
          (∑C∈commons,1/primeProductNorm p C)*(∑T∈firsts,1/primeProductNorm p T)) := by
      congr 1
      simp only [Finset.product_eq_sprod,Finset.sum_product,weight]
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hCmem
      ring
    _ ≤ (D*(U*B^2)^ε)*((E*B^(1+ε))*(128*Real.exp 1*(normLogBin U+1 : ℝ))*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by
      gcongr
    _ = _ := by ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0197

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
Source SHA256: 28afd7885f63e547d36737cc05e3cab2cfe4ad2f4e0dc8ad73590776ee2e7b3f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0198


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
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem columnLog_norm_lower (X M : ℝ) (hX : 0<X) (S : Finset ι)
    (h : -M≤columnLog p X S) : X*Real.exp (-M)≤primeProductNorm p S := by
  have he := Real.exp_le_exp.mpr h
  rw [columnLog,Real.exp_log (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)] at he
  simpa only [mul_comm] using (le_div_iff₀ hX).mp he

omit [DecidableEq ι] in
theorem normalized_second_coefficient_sq_le
    (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G X : ℝ) (hG : ∀t,‖g t‖≤G) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2≤G^2/primeProductNorm p S := by
  have hG0 : 0≤G := (norm_nonneg (g 0)).trans (hG 0)
  have ht := secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (normalizedColumn p (fun A => g (columnLog p X A))) S
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  simp only [normalizedColumn,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_pow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hG _) 2) (sq_nonneg _)

include hp in

omit [DecidableEq ι] in
theorem normalized_second_mass_zero
    (F : Finset ι) (Ψ : O→*ℂ) (m c d : O) (g : ℝ→ℂ)
    (M X : ℝ) (hX : 0<X) (hM : ∀t,g t≠0 → |t|≤M) (hsmall : X*Real.exp M<1) :
    (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have hz : g (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X M hX S ((le_abs_self _).trans (hM _ hn))
    have ho := primeProductNorm_ge_one p hp S
    linarith
  simp [secondInputCoefficient,normalizedColumn,hz]

include hp in

theorem normalized_second_mass_fixed_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G M X : ℝ) (hX : 0<X)
    (hG : ∀t,‖g t‖≤G) (hM : ∀t,g t≠0 → |t|≤M) :
    (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤
      128*Real.exp (2*M)*G^2 := by
  by_cases hsmall : X*Real.exp M<1
  · rw [normalized_second_mass_zero p hp hg F Ψ m c d g M X hX hM hsmall]
    positivity
  have hH : 1≤X*Real.exp M := le_of_not_gt hsmall
  let T := F.powerset.filter (fun S => g (columnLog p X S)≠0)
  have hsub : T⊆boundedPrimeSupports p F (X*Real.exp M) := by
    intro S hS
    obtain ⟨hSF,hSn⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,columnLog_norm_upper p hp X M hX S
      ((le_abs_self _).trans (hM _ hSn))⟩
  have hcard : (T.card:ℝ)≤128*(X*Real.exp M) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    exact boundedPrimeSupports_card p hinj F (X*Real.exp M) hH
  have he : (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=
      ∑S∈T,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hz : g (columnLog p X S)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hS,hh⟩)
    simp [secondInputCoefficient,normalizedColumn,hz]
  rw [he]
  calc
    _ ≤ ∑_S∈T,G^2/(X*Real.exp (-M)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply (normalized_second_coefficient_sq_le p hg Ψ hΨ m c d g G X hG S).trans
      have hlo := columnLog_norm_lower p hp X M hX S (abs_le.mp (hM _ (Finset.mem_filter.mp hS).2)).1
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hlo
    _ = (T.card:ℝ)*(G^2/(X*Real.exp (-M))) := by simp
    _ ≤ (128*(X*Real.exp M))*(G^2/(X*Real.exp (-M))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 128*Real.exp (2*M)*G^2 := by
      rw [show 2*M=M+M by ring,Real.exp_add,Real.exp_neg]
      field_simp [hX.ne',Real.exp_ne_zero]

end

theorem full_uniform_normalized_second_mass (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O) (X : ℝ),0<X →
      (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤C := by
  refine ⟨128*Real.exp (2*M)*(SchwartzMap.seminorm ℝ 0 0 g)^2+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d X hX
  exact (normalized_second_mass_fixed_bound p hp hg hinj F Ψ hΨ m c d g _ M X hX
    (fun t => g.norm_le_seminorm ℝ t) hM).trans (by linarith)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

def globalFirstColumnMass (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) : ℝ :=
  ∑G∈(globalFirstRawPool pool b).powerset,
    ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) G‖^2

include hp in
theorem globalFirstColumnMass_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (side : Bool)
    (hmass : globalFirstColumnMass p hg pool b Ψ m g ell side≠0) :
    primeProductNorm p b.common≤ell*Real.exp M ∧
      primeProductNorm p b.firstCommon≤ell*Real.exp M := by
  let a := primeProductNorm p (b.cube.sideDivisor side)
  let c := primeProductNorm p b.common
  let t := primeProductNorm p b.firstCommon
  have ha : 1≤a := primeProductNorm_ge_one p hp _
  have hc : 1≤c := primeProductNorm_ge_one p hp _
  have ht : 1≤t := primeProductNorm_ge_one p hp _
  have hden : 0<a*c*t := by positivity
  have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
    change 0<ell/(a*c)/t
    positivity
  have hlow : 1≤(globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon)*Real.exp M := by
    by_contra hh
    apply hmass
    exact normalized_second_mass_zero p hp hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) g M
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX hM (lt_of_not_ge hh)
  have heq : (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon)*Real.exp M=
      ell*Real.exp M/(a*c*t) := by change (ell/(a*c)/t)*Real.exp M=_; ring
  rw [heq] at hlow
  have hb : a*c*t≤ell*Real.exp M := by simpa only [one_mul] using (le_div_iff₀ hden).mp hlow
  constructor
  · change c≤_
    calc
      c=1*c*1 := by ring
      _ ≤ a*c*t := by gcongr
      _ ≤ _ := hb
  · change t≤_
    calc
      t=1*1*t := by ring
      _ ≤ a*c*t := by gcongr
      _ ≤ _ := hb

include hp in
theorem globalFirstColumnMass_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U) (side : Bool)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstColumnMass p hg pool b Ψ m g ell side=0 := by
  by_contra hm
  have h := globalFirstColumnMass_support p hp hg pool b Ψ m g ell M hell hM side hm
  exact hoff ⟨h.1.trans hU,h.2.trans hU⟩

include hp in
theorem globalFirstDiagonalCost_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell M U : ℝ) (hell : 0<ell) (hM : ∀t,g t≠0 → |t|≤M)
    (hU : ell*Real.exp M≤U) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y=
      globalFirstDiagonalCost p hg pool
        (s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U))
        w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U) := by
    intro h; exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  have hz := globalFirstColumnMass_zero_off_support p hp hg pool b Ψ m g ell M U hell hM hU side hoff
  change globalFirstColumnMass p hg pool b Ψ m g ell side=0 at hz
  change ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)=0
  rw [hz,mul_zero,mul_zero]

end

theorem globalDiagonalPowers (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ B U : ℝ,1≤B → 1≤U →
      B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2≤C*(B*U)^ε := by
  let k : ℝ := 128*Real.exp 1
  let C := k^2*(1+1/(ε/3))^2
  refine ⟨C,by dsimp [C,k]; positivity,?_⟩
  intro B U hB hU
  have hB0 : 0<B := by linarith
  have hU0 : 0<U := by linarith
  have hη : 0<ε/3 := by positivity
  have hlog := descent_normLogBin_small_power (ε/3) hη U hU
  have hBp : B^(ε/3)*(B^2)^(ε/3)=B^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le,←Real.rpow_add hB0]
    congr 1
    ring
  have hUp : U^(ε/3)*(U^(ε/3))^2=U^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le,←Real.rpow_add hU0]
    congr 1
    ring
  calc
    _ ≤ B^(ε/3)*(U*B^2)^(ε/3)*(k*((1+1/(ε/3))*U^(ε/3)))^2 := by
      dsimp [k]
      gcongr
    _ = k^2*(1+1/(ε/3))^2*(B^(ε/3)*(B^2)^(ε/3))*(U^(ε/3)*(U^(ε/3))^2) := by
      rw [Real.mul_rpow hU0.le (sq_nonneg B)]
      ring
    _ = C*(B*U)^ε := by rw [hBp,hUp,Real.mul_rpow hB0.le hU0.le]; dsimp [C]; ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem globalFirstDiagonalCost_parent_bound (ε : ℝ) (hε : 0<ε)
    (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Ψ : O →* ℂ) (m : O) (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U → ell*Real.exp M≤U →
      (∀z,‖Ψ z‖≤1) → (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      globalFirstDiagonalCost p hg pool s
        (fun b => ((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        Ψ m g W ell side (globalFirstPooledRow p K ell B F side)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cg,hCg,hmass⟩ := full_uniform_normalized_second_mass g M hM
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  let P := Cd*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨P*Cp+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj pool s w Ψ m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨ hw hs hb1 hb2
  have hB0 : 0<B := by linarith
  let T := s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have ht (b : GlobalFirstData ι) (hb : b∈T) : b∈s := (Finset.mem_filter.mp hb).1
  have hsum := hcount p hp hinj T B U hB hU
    (fun b hb => hs b (ht b hb)) (fun b hb => (Finset.mem_filter.mp hb).2.1)
    (fun b hb => (Finset.mem_filter.mp hb).2.2)
    (fun b hb => hb1 b (ht b hb)) (fun b hb => hb2 b (ht b hb))
  change (∑b∈T,θ b)≤_ at hsum
  rw [globalFirstDiagonalCost_eq_supported p hp hg pool s _ Ψ m g W ell M U hell hM hellU side]
  change globalFirstDiagonalCost p hg pool T _ Ψ m g W ell side _≤_
  have hterm (b : GlobalFirstData ι) (hb : b∈T) :
      ‖((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ)‖*(primeProductNorm p b.firstCommon)⁻¹*
        (|globalFirstPooledRow p K ell B F side b| *‖paperRadialFourier W 0‖*
          globalFirstColumnMass p hg pool b Ψ m g ell side)≤
        (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
    have hcpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.common
    have hapos := FirstPassCubeLabels.primeProductNorm_pos p hp (b.cube.sideDivisor side)
    have hX : 0<globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon := by
      unfold globalFirstBlockColumnScale
      positivity
    have hm := hmass p hp hg hinj (globalFirstRawPool pool b) Ψ hΨ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) hX
    change globalFirstColumnMass p hg pool b Ψ m g ell side≤Cg at hm
    have hm0 : 0≤globalFirstColumnMass p hg pool b Ψ m g ell side :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hwb := hw b (ht b hb)
    have hwΓ := hwb.2
    rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hwb.1 hc),abs_of_pos hY]
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = (w b*‖paperRadialFourier W 0‖*globalFirstColumnMass p hg pool b Ψ m g ell side)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*
          (globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹) := by gcongr
      _ ≤ (Γ*‖paperRadialFourier W 0‖*Cg)*(((Real.exp 1)^3*ell*B^2*F)*θ b) :=
        mul_le_mul_of_nonneg_left hsc' (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*(∑b∈T,θ b) := by
      unfold globalFirstDiagonalCost
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*Cg*‖paperRadialFourier W 0‖*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = P*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      dsimp [P]
      ring
    _ ≤ P*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ ≤ (P*Cp+1)*Γ*(ell*B^3*F)*(B*U)^ε := by
      calc
        _ = (P*Cp)*(Γ*(ell*B^3*F)*(B*U)^ε) := by ring
        _ ≤ (P*Cp+1)*(Γ*(ell*B^3*F)*(B*U)^ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

theorem bracket_one_eq_quadratic (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P z)=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 := by
  simp only [bracket,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,↓reduceIte]
  rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  by_cases hz : z∈P
  · have he : Ideal.Quotient.mk P z=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg z
    change actualSextic P hg (Ideal.Quotient.mk P (z^6))=_ at h6
    simp only [map_pow,ite_eq_right hz] at h6
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P z))^6 := by ring
      _ = 1 := h6

theorem quadratic_value_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (b : O) :
    (actualSextic P hg (Ideal.Quotient.mk P (b^3)))^3=
      (actualSextic P hg (Ideal.Quotient.mk P b))^3 := by
  simp only [map_pow]
  by_cases hb : b∈P
  · have he : Ideal.Quotient.mk P b=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg b
    change actualSextic P hg (Ideal.Quotient.mk P (b^6))=_ at h6
    simp only [map_pow,ite_eq_right hb] at h6
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P b))^3 *
          (actualSextic P hg (Ideal.Quotient.mk P b))^6 := by ring
      _ = _ := by rw [h6,mul_one]

theorem residual_bracket_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z n b : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (z*n*b^3))=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 *
      (actualSextic P hg (Ideal.Quotient.mk P (n*b)))^3 := by
  rw [bracket_one_eq_quadratic]
  simp only [map_mul,mul_pow]
  rw [quadratic_value_cube]
  ring

theorem residual_bracket_product {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (z n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) 1 (Ideal.Quotient.mk (P i) (z*n*b^3)))=
      finiteSexticRow P hg (fun _ => 3) z * finiteSexticRow P hg (fun _ => 3) (n*b) := by
  simp_rw [residual_bracket_cube,Finset.prod_mul_distrib]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_inverse_norm_sum (S : Finset (Ideal O))
    (hS : ∀I∈S,PowerfulIdeal I) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤1048576 := by
  let A := S.image powerfulBase
  let B := S.image squarefreePart
  let pair : Ideal O→Ideal O×Ideal O := fun I => (powerfulBase I,squarefreePart I)
  have ha (I : Ideal O) (hI : I∈A) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (powerfulBase_spec J (hS J hJ)).1
  have hb (I : Ideal O) (hI : I∈B) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (squarefree_squarefreePart J).ne_zero
  have hca : (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)≤1024 :=
    finite_inverse_norm_square_sum A (∑I∈A,(Ideal.absNorm I:ℝ)) ha
      (fun I hI => Finset.single_le_sum (fun J _ => Nat.cast_nonneg _) hI)
  have hcb : (∑I∈B,1/(Ideal.absNorm I:ℝ)^2)≤1024 :=
    finite_inverse_norm_square_sum B (∑I∈B,(Ideal.absNorm I:ℝ)) hb
      (fun I hI => Finset.single_le_sum (fun J _ => Nat.cast_nonneg _) hI)
  have hinj : Set.InjOn pair S := by
    intro I hI J hJ he
    exact powerfulBase_injective_on_fiber I J (hS I hI) (hS J hJ)
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  have hsub : S.image pair ⊆ A×ˢB := by
    intro p hp
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  calc
    _ ≤ ∑I∈S,1/(Ideal.absNorm (powerfulBase I):ℝ)^2 *
        (1/(Ideal.absNorm (squarefreePart I):ℝ)^2) := by
      apply Finset.sum_le_sum
      intro I hI
      have hni := (powerfulBase_spec I (hS I hI)).2
      have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hz => (squarefree_squarefreePart I).ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
      have ha0 : 0<(Ideal.absNorm (powerfulBase I):ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero
          (fun hz => (powerfulBase_spec I (hS I hI)).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      have he : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (powerfulBase I):ℝ)^2*
          (Ideal.absNorm (squarefreePart I):ℝ)^3 := by
        have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) hni
        simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h.symm
      rw [he,one_div,one_div,one_div,←mul_inv]
      exact inv_anti₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _))
    _ = ∑p∈S.image pair,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑p∈A×ˢB,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)*(∑I∈B,1/(Ideal.absNorm I:ℝ)^2) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.mul_sum]
    _ ≤ 1024*1024 := mul_le_mul hca hcb (by positivity) (by norm_num)
    _ = _ := by norm_num

end

open ActualEisensteinCubic UniqueFactorizationMonoid

theorem prime_square_dvd_powerful (I P : Ideal O) (hI : PowerfulIdeal I)
    (hP : Prime P) (hd : P∣I) : P^2∣I := by
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mpr ⟨hP,hd⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hP.ne_zero) hI.1).mpr
  rw [normalizedFactors_pow,normalizedFactors_irreducible hP.irreducible,normalize_eq]
  apply Multiset.le_iff_count.mpr
  intro Q
  by_cases hQP : Q=P
  · subst Q
    simpa using hI.2 P hm
  · simp [hQP]

theorem nonresidual_prime_square_dvd (I Q P : Ideal O) (hI : I≠0) (hP : Prime P)
    (hd : P∣I) (hr : ¬P∣rowResidualPart I Q) :
    P^2∣rowPowerfulPart I*(rowMaskPart I Q)^2 := by
  have hh : P∣rowPowerfulPart I*rowMaskPart I Q := by
    rw [←row_powerful_mask_residual_product I Q hI] at hd
    exact (hP.dvd_mul.mp hd).resolve_right hr
  rcases hP.dvd_mul.mp hh with ha|ht
  · exact dvd_mul_of_dvd_left (prime_square_dvd_powerful _ _ (rowPowerfulPart_powerful I) hP ha) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _

def nonresidualGain (I P : Ideal O) : Ideal O := if P∣I then P^2 else P

theorem nonresidual_gain_product_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) :
    (∏i,nonresidualGain I (P i)) ∣ rowPowerfulPart I*(rowMaskPart I Q)^2*Q := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    change IsCoprime (nonresidualGain I (P i)) (nonresidualGain I (P j))
    unfold nonresidualGain
    by_cases hi : P i∣I
    · rw [ite_eq_left hi]
      by_cases hj : P j∣I
      · rw [ite_eq_left hj]
        exact (hcop hij).pow
      · rw [ite_eq_right hj]
        exact (hcop hij).pow_left
    · rw [ite_eq_right hi]
      by_cases hj : P j∣I
      · rw [ite_eq_left hj]
        exact (hcop hij).pow_right
      · rw [ite_eq_right hj]
        exact hcop hij
  · intro i
    have hp : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
    by_cases hi : P i∣I
    · rw [nonresidualGain,ite_eq_left hi]
      exact dvd_mul_of_dvd_left (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)) Q
    · rw [nonresidualGain,ite_eq_right hi]
      exact dvd_mul_of_dvd_right ((hp.dvd_mul.mp (hpool i)).resolve_left hi) _

open ActualEisensteinCubic UniqueFactorizationMonoid

def completedLocalExponent (I F P : Ideal O) : ℕ :=
  ((normalizedFactors I).count P+4*(if P∣F then 1 else 0))%6

def reflectionExtractedPrime (P : Ideal O) (j : ℕ) (e v : Fin 3) : Ideal O :=
  if (j=4 ∧ e=v) ∨ (j=0 ∧ v=0) then P else 1

def reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) : Ideal O :=
  ∏i,reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) : ℝ :=
  (Ideal.absNorm (∏i,P i):ℝ)^2/
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)^4)

def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=2 then 1/q^2 else q)
  else if j=0 then q else q^2

theorem reflectionConductorCost_eq_prod {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) :
    reflectionConductorCost P j e=∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (j i) (e i) := by
  have hn i : (Ideal.absNorm (P i):ℝ)≠0 := by
    exact_mod_cast (fun hz => hP i (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [reflectionConductorCost,reflectionExtractedDivisor,map_prod,Nat.cast_prod,
    ←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize he : e i=v
    fin_cases v <;> simp [reflectionExtractedPrime,reflectionLocalCost] <;> field_simp
  · by_cases hj0 : j i=0
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj0]
      field_simp
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj4,hj0]

theorem reflectionLocalCost_nonneg (q : ℝ) (hq : 0≤q) (j : ℕ) (e : Fin 3) :
    0≤reflectionLocalCost q j e := by
