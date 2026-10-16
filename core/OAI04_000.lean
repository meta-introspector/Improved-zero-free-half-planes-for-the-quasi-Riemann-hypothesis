import core.OAI03
-- import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
-- import Mathlib.Analysis.Complex.LocallyUniformLimit
-- import Mathlib.Analysis.MellinInversion
-- import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
-- import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
-- import Mathlib.MeasureTheory.Integral.Pi
-- import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
import PrimeNumberTheoremAnd.Wiener

/-! Pinned OAI dependency closure, consolidated without changing public namespaces.
Original module boundaries and hashes are preserved below. -/

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding
Source SHA256: 61322cab57ec244b17c5d2175464de8a7806d65b1b7c4519bc7f6644d9465cd5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0335


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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma initialOrbit_reflection_inputs {q:ℕ} (χ:DirichletCharacter ℂ q)
    (Ψ:Eis→*ℂ) (hΨ:IsBaseRayTwist (initialBase χ) Ψ) :
    FactorsModulo (fixedBaseConductor q) Ψ ∧ (∀n:Eis,‖Ψ n‖≤1) :=
  ⟨initialOrbit_factorsModulo χ Ψ hΨ,fun n=>hΨ.norm_le (initialBase_norm χ) n⟩

lemma canonicalLabel_squarefree {X:ℝ} (f:idealRange X) : Squarefree f.val :=
  (mem_idealRange.mp f.property).1.2.1

lemma canonicalLabel_generator_ne_zero {X:ℝ} (f:idealRange X) :
    ConcretePrimeRowBridge.idealGenerator f.val≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero f.val (mem_idealRange.mp f.property).1.1

lemma unitRowFamily_actual {X:ℝ} (f:idealRange X) (Ψ:Eis→*ℂ) (q:ℕ) (m:Eis)
    (u:Eisˣ) (I:Ideal Eis) :
    CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator (reflectionExcludedPrimes q)) u f I=
      rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f.val)
        (u.val*ConcretePrimeRowBridge.idealGenerator I) := rfl

theorem fixedShellModels_of_actual_fiber_identity
    (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) (scale:ℂ)
    [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
    (hidentity:
      ∀(Ψ:Eis→*ℂ),FactorsModulo (fixedBaseConductor q) Ψ→
      ∀hΨnorm:(∀n:Eis,‖Ψ n‖≤1),∀(m:Eis)(hm:m≠0),
      ∀(F:Ideal Eis)(hF:Squarefree F)(u:Eisˣ),∀(W:ℝ→ℂ)(a b:ℝ),
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀(K X:ℝ),0<K→0<X→∀rows:Finset (Ideal Eis),
      ∀hrows:(∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K),
      ∀(R:Ideal Eis)(hR:R∈rows),∀J:ActualFiber.RowIndex q m rows R F,
        completedT (rowTwist Ψ (ActualFiber.maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
        scale*(ActualFiber.reflectedFiber q hq m hm rows R F (hrows R hR).1 hF
          (fun I hI=>(hrows I hI).1) u K Ψ hΨnorm).idealValue W X 1 completedRamifiedStep
            (rowResidualPart J.val (ActualFiber.maskIdeal q m F))) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)) scale
      1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  intro Ψ hΨ m hm Xlabel f u W a b ha hs hW K X hK hX rows hrows
  obtain ⟨hperiod,hnorm⟩:=initialOrbit_reflection_inputs χ Ψ hΨ
  let models:=fun (R:Ideal Eis) (hR:R∈rows)=>
    ActualFiber.reflectedFiber q hq m hm rows R f.val (hrows R hR).1 (canonicalLabel_squarefree f)
      (fun I hI=>(hrows I hI).1) u K Ψ hnorm
  apply hasExactCompletedModels_of_representative_identity
    (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    rows K X 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) f.val
    (ActualFiber.maskIdeal q m f.val) W
    (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator (reflectionExcludedPrimes q)) u f)
    scale models
  intro R hR J hJ
  rw [unitRowFamily_actual]
  exact hidentity Ψ hperiod hnorm m hm f.val (canonicalLabel_squarefree f) u W a b ha hs hW
    K X hK hX rows hrows R hR ⟨J,hJ⟩

end

theorem finite_selected_branch_collection
    {H U B:Type*} {R:H→Type*} {E:B→Type*}
    [Fintype H] [Fintype U] [Fintype B]
    [∀h,Fintype (R h)] [∀b,Fintype (E b)]
    (f:(h:H)→R h→U→(b:B)→E b→ℂ)
    (g:H→U→(b:B)→E b→ℂ)
    (chosen:(h:H)→B→R h) (α:H→ℂ) (shape:H→B→ℂ) (w:B→ℂ)
    (hbranch:∀h r u b e,4*f h r u b e=
      if r=chosen h b then α h*shape h b*g h u b e else 0) :
    4*(∑h,∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑h,α h*∑b,w b*shape h b*∑u,∑e:E b,g h u b e := by
  have hpoint (h:H) (b:B) :
      4*(∑r:R h,∑u,∑e:E b,f h r u b e)=
        α h*shape h b*(∑u,∑e:E b,g h u b e) := by
    simp_rw [Finset.mul_sum,hbranch]
    calc
      _=∑r:R h,if r=chosen h b then
          α h*shape h b*(∑u,∑e:E b,g h u b e) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases he:r=chosen h b
        · simp only [he,ite_true,Finset.mul_sum]
        · simp only [he,ite_false,Finset.sum_const_zero]
      _=_:=by simp [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hswap : (∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑b,w b*(∑r:R h,∑u,∑e:E b,f h r u b e) := by
    calc
      _=∑r:R h,∑b,∑u,w b*∑e:E b,f h r u b e := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _=∑b,∑r:R h,∑u,w b*∑e:E b,f h r u b e := Finset.sum_comm
      _=_:=by simp_rw [Finset.mul_sum]
  rw [hswap,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    _=w b*(4*(∑r:R h,∑u,∑e:E b,f h r u b e)) := by ring
    _=w b*(α h*shape h b*(∑u,∑e:E b,g h u b e)) := by rw [hpoint]
    _=_:=by ring

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem fixedRayFiberFromRows_value
    (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar
    d.value W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑B:Finset (pool I Q Q0),
        reflectionInactiveStratumWeight I F Q Q0 B*
          ∑l:B→Fin 3,(d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨B,l⟩)).value W X ρ q k := by
  dsimp only
  unfold fixedRayFiberFromRows
  rw [fixedRayFiber_value]
  simp only [mul_one, Finset.mul_sum]

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_value (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (W:ℝ→ℂ) (X:ℝ) (k:idealRange (completedResidualScale K R (maskIdeal q m F))) :
    let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
    d.value W X 1 completedRamifiedStep k=
      ∑r:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
        ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
          FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
            ∑l:B→Fin 3,(d.branch (fixedReflectionRayEquiv (reflectionConductor q)
              (reflectionConductor_ne_zero q hq) r,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k := by
  exact FreeReflection.fixedRayFiberFromRows_value (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)
    W X 1 completedRamifiedStep k

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

omit [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})] in
theorem sourceStratumValue_eq_compressed
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X=
      fixedRadialCoefficientScalar*
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
          ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
            ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
              freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)*
        ∑'u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let p:A→Eis:=fun P=>freePrimaryPrime lengthScale (freeConductor q) P.val
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  let j:A→ℕ:=fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6
  let : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  have hjres (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F))) : j (E (Sum.inl P))=1:=by
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inl P)).val.val.val%6=1
    rw [selectedActiveEquiv_inl]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  have hPB:(fun b:B=>Ideal.span {p (E (Sum.inr b))}:B→Ideal Eis)=(fun b=>b.val.val):=by
    funext b
    rw [show p (E (Sum.inr b))=freePrimaryPrime lengthScale (freeConductor q) (E (Sum.inr b)).val from rfl,
      freePrimaryPrime_span lengthScale (freeConductor q) hL,selectedActiveEquiv_inr]
    exact splitIndex_prime_val q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hjB:(fun b:B=>j (E (Sum.inr b)))=(fun b=>completedLocalExponent R F b.val.val):=by
    funext b
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inr b)).val.val.val%6=completedLocalExponent R F b.val.val
    rw [selectedActiveEquiv_inr]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hdiv (l:B→Fin 3) (side:Fin 3) :
      reflectionExtractedDivisor (fun b:B=>Ideal.span {p (E (Sum.inr b))})
        (fun b:B=>j (E (Sum.inr b))) l side=sourceDivisor q m R F B l side := by
    rw [hPB,hjB]
    rfl
  have hcop:Pairwise (fun a b:A=>IsCoprime (Ideal.span {p a}) (Ideal.span {p b})):=by
    intro a b hab
    exact freePrimaryPrime_coprime lengthScale (freeConductor q) hL (fun he=>hab (Subtype.ext he))
  have he := @FixedFourierGeometry.smoothedValue_eq_nonresidual_equiv _ _ G
    _ B A _ (Finset.Subtype.fintype B) (Finset.Subtype.fintype A) p _ E
    (sourceStratum q hq m hm rows R F hR hF hrows v h B J)
    (fun P => freePrimaryPrime_maximal lengthScale (freeConductor q) hL P.val)
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ p (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val) hcop
    (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>freePrimaryPrime_odd lengthScale (freeConductor q) hL P.val) j
    (fun _=>Nat.mod_lt _ (by decide)) hjres W lo hi hlo hsupp hW X hX
  refine he.trans ?_
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏P:A,p P)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr (by ext l; simp only [Finset.mem_univ])
  intro l hl
  unfold sourceCompressedTerm
  dsimp only
  apply tsum_congr
  intro x
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.1.val) (hdiv l 1)
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.2.val) (hdiv l 2)

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma one_le_residualScale (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis))
    (R F:Ideal Eis) (K:ℝ)
    (hrows:∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F) :
    1≤completedResidualScale K R (maskIdeal q m F) := by
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows R (maskIdeal q m F) J K]
  exact one_le_completedResidualScale K J.val (maskIdeal q m F) hJ.1 hJ.2.2

lemma residual_shell (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis))
    (R F:Ideal Eis) (K:ℝ)
    (hrows:∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F) :
    0<completedResidualScale K R (maskIdeal q m F) ∧
      completedResidualScale K R (maskIdeal q m F)/2≤
        (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ) := by
  refine ⟨lt_of_lt_of_le zero_lt_one (one_le_residualScale q m rows R F K hrows J),?_⟩
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows R (maskIdeal q m F) J K]
  exact actualResidualModelRow_shell K J.val (maskIdeal q m F) hJ.1
    (mask_bad q m F) hJ.2.2 hJ.2.1

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance sourceUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def sourceShapeFactor
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) : ℂ :=
  (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
    ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
      ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
        freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)

noncomputable def sourceFixedCoefficient
    (Ψ:Eis→*ℂ) (h:Eis⧸Ideal.span {reflectionConductor q})
    (J:RowIndex q m rows R F) : ℂ :=
  fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    ((data q m hm rows R F hF hrows v J).fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h

noncomputable def compressedSourceTotal (Ψ:Eis→*ℂ)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {reflectionConductor q},
    sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*
    ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
      FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
      ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X

theorem completedT_eq_compressedSourceTotal
    (Ψ:Eis→*ℂ)
    (hΨ:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨnorm:∀n,‖Ψ n‖≤1)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  rw [completedT_eq_nonresidual_source q hq m hm rows R F hR hF hrows v Ψ hΨ hΨnorm
    J W lo hi hlo hsupp hW X hX]
  unfold compressedSourceTotal
  rw [mul_assoc]
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [mul_left_comm fixedRadialCoefficientScalar]
  apply congrArg (fun z:ℂ=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [sourceStratumValue_eq_compressed q hq m hm rows R F hR hF hrows v h B J
    W lo hi hlo hsupp hW X hX,tsum_fintype]
  change _=(fixedRadialCoefficientScalar*
    (FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
        ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X))
  dsimp only [sourceShapeFactor]
  ring

end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators

namespace CompletedGauss
variable {α β γ ι:Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] in
lemma residualLabelVia_nonresidual_equiv (E:α⊕β≃ι) (T:β≃γ)
    (l:β→Fin 3) (l':γ→Fin 3) (hl:∀b,l' (T b)=l b) :
    residualLabelVia ((Equiv.sumCongr (Equiv.refl α) T.symm).trans E) l'=
      residualLabelVia E l := by
  let E':=((Equiv.sumCongr (Equiv.refl α) T.symm).trans E)
  funext i
  obtain ⟨a,rfl⟩:=E.surjective i
  cases a with
  | inl a=>
    have he:E (Sum.inl a)=E' (Sum.inl a):=rfl
    calc
      _=residualLabelVia E' l' (E' (Sum.inl a)):=by rw [he]
      _=0:=residualLabelVia_apply E' l' (Sum.inl a)
      _=_:=(residualLabelVia_apply E l (Sum.inl a)).symm
  | inr b=>
    have he:E (Sum.inr b)=E' (Sum.inr (T b)):=by simp [E']
    calc
      _=residualLabelVia E' l' (E' (Sum.inr (T b))):=by rw [he]
      _=l' (T b):=residualLabelVia_apply E' l' (Sum.inr (T b))
      _=l b:=hl b
      _=_:=(residualLabelVia_apply E l (Sum.inr b)).symm

end CompletedGauss

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma activeModelPrimeEquiv_labels
    (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    residualLabelVia (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J)
      (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
    residualLabelVia (selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J)
      (reflectionSixSupport e)) (fun b=>reflectionSixLabel (e b.val)) := by
  exact residualLabelVia_nonresidual_equiv _
    (FreeReflection.supportActivePoolEquiv R (maskIdeal q m F) (freeConductor q) e)
    _ _ (fun _=>rfl)

lemma reflectionSixLabel_encode_at {β:Type*} [Fintype β]
    (B:Finset β) (l:B→Fin 3) (b:B) :
    reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b := by
  classical
  apply Fin.ext
  simp only [encodeReflectionSix,dite_eq_left b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hb:=(l b).isLt
  omega

end CanonicalRowCompletion.ActualFiber

open scoped BigOperators Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma supportActivePoolEquiv_divisor (I F Q Q0:Ideal Eis)
    (e:pool I Q Q0 → Fin 6) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 e=>P.val)
      (fun P=>completedLocalExponent I F P.val) (reflectionActiveLabel I Q Q0 e) side=
    reflectionExtractedDivisor (fun b:reflectionSixSupport e=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) (fun b=>reflectionSixLabel (e b.val)) side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (supportActivePoolEquiv I Q Q0 e)
  intro b
  rfl

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_decoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let B:=reflectionSixSupport e
    let l:=fun b:B=>reflectionSixLabel (e b.val)
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let Em:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let Es:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)
  let labels:=fun b:reflectionSixSupport e=>reflectionSixLabel (e b.val)
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*
      Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  have ht:=reflectedFiber_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    e W lo hi hlo hsupp hW X hX hK hk
  refine ht.trans (congrArg (fun z:ℂ=>if rho=D.sourceRowResidue
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
    h G A then fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*z
    else 0) ?_)
  unfold sourceCompressedTerm
  apply tsum_congr
  intro x
  have hlabel:residualLabelVia Em (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
      residualLabelVia Es labels:=activeModelPrimeEquiv_labels q hq m hm rows R F hR hF hrows v e J
  have hdiv (side:Fin 3):columnDivisor q m R F e side=
      sourceDivisor q m R F (reflectionSixSupport e) labels side:=
    FreeReflection.supportActivePoolEquiv_divisor R F (maskIdeal q m F) (freeConductor q) e side
  have harg:nonzeroDualDilation (columnDivisor q m R F e 1) (columnDivisor q m R F e 2)
      (columnDivisor_ne_zero q m R F e 1) (columnDivisor_ne_zero q m R F e 2) x=
    nonzeroDualDilation (sourceDivisor q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor q m R F (reflectionSixSupport e) labels 2)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 2) x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> dsimp only [nonzeroDualDilation] <;> rw [hdiv]
  exact congrArg₂ (fun label arg =>
    @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A)
      _ _ S _ hp hg j u label W X arg) hlabel harg

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_encoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        encodeReflectionSix ⟨B,l⟩)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let result:(ΣB:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),B→Fin 3) → ℂ := fun x =>
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v x.1 J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A then
      fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h x.1 J u x.2 W X
    else 0
  have ht:=reflectedFiber_decoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    (encodeReflectionSix ⟨B,l⟩) W lo hi hlo hsupp hW X hX hK hk
  change _=result (decodeReflectionSix (encodeReflectionSix ⟨B,l⟩)) at ht
  rw [decode_encodeReflectionSix] at ht
  change _=result ⟨B,l⟩
  exact ht

end CanonicalRowCompletion.ActualFiber

end

end OAI
end OAIOriginalModule0335

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion
Source SHA256: 0342d5cd682913d53289281c0bc421a37abaa626845fb4bf1a7288871f3deab8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0336


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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_four_mul_value
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).value
      W X 1 completedRamifiedStep k=
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  let : ∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
    fun h=>Fintype.ofFinite _
  let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let f:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      (d.branch (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        ⟨h,rho,u⟩,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k
  let g:=fun (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
  let chosen:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))=>
      (data q m hm rows R F hF hrows v J).sourceRowResidue
        (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
        h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
        (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)
  let α:=fun h=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J
  let shape:=fun h B=>sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J
  let w:=FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q)
  have hbranch:∀h rho u B l,4*f h rho u B l=
      if rho=chosen h B then α h*shape h B*g h u B l else 0 := by
    intro h rho u B l
    exact reflectedFiber_encoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound
      J h rho u B l W lo hi hlo hsupp hW X hX hK hk
  have hvalue:d.value W X 1 completedRamifiedStep k=
      ∑h,∑rho,∑u,∑B,w B*∑l,f h rho u B l := by
    rw [reflectedFiber_value q hq m hm rows R F hR hF hrows v K Ψ hΨ W X k]
    exact sum_fixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) _
  change 4*d.value W X 1 completedRamifiedStep k=_
  rw [hvalue]
  exact finite_selected_branch_collection f g chosen α shape w hbranch

theorem completedT_eq_reflectedFiber_idealValue
    (Ψ:Eis→*ℂ)
    (hΨperiod:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨ:∀n,‖Ψ n‖≤1)
    (K:ℝ) (hshell:∀I∈rows,K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).idealValue W X 1 completedRamifiedStep
          (rowResidualPart J.val (maskIdeal q m F)) := by
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,(hshell I hI).2⟩) J
  have hs:=residual_shell q m rows R F K (fun I hI=>⟨hrows I hI,hshell I hI⟩) J
  have he:=reflectedFiber_four_mul_value q hq m hm rows R F hR hF hrows v K Ψ hΨ
    (fun I hI=>(hshell I hI).2) J W lo hi hlo hsupp hW X hX hs.1 hs.2
  rw [completedT_eq_compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ hΨperiod hΨ
    J W lo hi hlo hsupp hW X hX,←he]
  have hid:rowResidualPart J.val (maskIdeal q m F)=k.val:=rfl
  rw [hid,ReflectedFiberData.idealValue_at]
  ring

end CanonicalRowCompletion.ActualFiber

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def actualReflectionScale : ℂ :=
  4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar

theorem actual_fixedShellModels (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      actualReflectionScale 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor q)) := by
  let : Finite (Eis⧸Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis⧸Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  apply fixedShellModels_of_actual_fiber_identity q hq χ actualReflectionScale
  intro Ψ hperiod hnorm m hm F hF u W a b ha hs hW K X hK hX rows hrows R hR J
  exact ActualFiber.completedT_eq_reflectedFiber_idealValue q hq m hm rows R F
    (hrows R hR).1 hF (fun I hI=>(hrows I hI).1) u Ψ hperiod hnorm K
    (fun I hI=>(hrows I hI).2) J W a b ha hs hW X hX

theorem exists_actual_fixedShellModels (q:ℕ) [NeZero q] (χ:DirichletCharacter ℂ q) :
    ∃(rays:ℕ) (scale:ℂ),
      HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
        rays scale 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  exact ⟨fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q (NeZero.ne q)),
    actualReflectionScale,actual_fixedShellModels q (NeZero.ne q) χ⟩

end

theorem dirichletTarget_unconditional : ShortDraft.DirichletTarget :=
  dirichletTarget_of_reflection_shells exists_actual_fixedShellModels

end CanonicalRowCompletion

namespace ShortDraft

theorem dirichlet_LFunction_ne_zero (q:ℕ) [NeZero q]
    (χ:DirichletCharacter ℂ q) (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hpole:¬(χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s≠0 :=
  CanonicalRowCompletion.dirichletTarget_unconditional q χ s hs hpole

theorem riemannZeta_ne_zero_of_re_gt (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hs1:s≠1) : riemannZeta s≠0 :=
  zeta_nonvanishing_of_dirichletTarget
    CanonicalRowCompletion.dirichletTarget_unconditional s hs hs1

end ShortDraft

end

end OAI
end OAIOriginalModule0336

/-! Original module: OAI.NumberTheory.DirichletL.Foundation
Source SHA256: ebfe6353a647f9e09bce1891343398e49094bc60f72b9b525f1e0fe97ee9e59d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0337

end OAIOriginalModule0337

/-! Original module: OAI.NumberTheory.DirichletL.CenteredExceptionalCount
Source SHA256: 6a4b97305d8ca1be0bd66708886e7c0e7a4c56ea5fc8c2670f6b95f7fbb536be
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0338


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredExceptionalCount
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

def valuation (I P : Ideal O) : ℕ := (normalizedFactors I).count P

def factorMultiset (I : Ideal O) (e : ℕ → ℕ) : Multiset (Ideal O) :=
  ∑ P ∈ (normalizedFactors I).toFinset, Multiset.replicate (e (valuation I P)) P

theorem factorMultiset_subset (I : Ideal O) (e : ℕ → ℕ) :
    factorMultiset I e ⊆ normalizedFactors I := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Multiset.mem_sum.mp hP
  have he : P = Q := (Multiset.mem_replicate.mp hPQ).2
  exact he ▸ Multiset.mem_toFinset.mp hQ

theorem factorMultiset_count (I P : Ideal O) (e : ℕ → ℕ) (he : e 0 = 0) :
    (factorMultiset I e).count P = e (valuation I P) := by
  unfold factorMultiset
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  split_ifs with hP
  · rfl
  · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (Multiset.mem_toFinset.mpr h))
    rw [hz, he]

def factorPart (I : Ideal O) (e : ℕ → ℕ) : Ideal O := (factorMultiset I e).prod

theorem factorPart_ne_zero (I : Ideal O) (e : ℕ → ℕ) : factorPart I e ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (factorMultiset_subset I e)

theorem factorPart_valuation (I P : Ideal O) (e : ℕ → ℕ) (he : e 0 = 0) :
    valuation (factorPart I e) P = e (valuation I P) := by
  unfold valuation factorPart
  rw [normalizedFactors_prod_eq_self_of_subset (factorMultiset_subset I e)]
  exact factorMultiset_count I P e he

def sixthRemainder (I : Ideal O) : Ideal O := factorPart I (fun n => n % 6)

def sixthQuotient (I : Ideal O) : Ideal O := factorPart I (fun n => n / 6)

theorem sixthRemainder_ne_zero (I : Ideal O) : sixthRemainder I ≠ 0 := factorPart_ne_zero I _
theorem sixthQuotient_ne_zero (I : Ideal O) : sixthQuotient I ≠ 0 := factorPart_ne_zero I _

@[simp] theorem sixthRemainder_valuation (I P : Ideal O) :
    valuation (sixthRemainder I) P = valuation I P % 6 :=
  factorPart_valuation I P _ (by norm_num)

@[simp] theorem sixthQuotient_valuation (I P : Ideal O) :
    valuation (sixthQuotient I) P = valuation I P / 6 :=
  factorPart_valuation I P _ (by norm_num)

theorem valuation_mul (I J P : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    valuation (I * J) P = valuation I P + valuation J P := by
  simp only [valuation, normalizedFactors_mul hI hJ, Multiset.count_add]

theorem valuation_pow (I P : Ideal O) (n : ℕ) :
    valuation (I ^ n) P = n * valuation I P := by
  simp only [valuation, normalizedFactors_pow, Multiset.count_nsmul]

theorem ideal_eq_of_valuation_eq {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ P, valuation I P = valuation J P) : I = J := by
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ]
  exact congrArg Multiset.prod (Multiset.ext.mpr h)

theorem sixth_normal_form (I : Ideal O) (hI : I ≠ 0) :
    sixthRemainder I * sixthQuotient I ^ 6 = I := by
  apply ideal_eq_of_valuation_eq
    (mul_ne_zero (sixthRemainder_ne_zero I) (pow_ne_zero _ (sixthQuotient_ne_zero I))) hI
  intro P
  rw [valuation_mul _ _ _ (sixthRemainder_ne_zero I)
    (pow_ne_zero _ (sixthQuotient_ne_zero I)), valuation_pow,
    sixthRemainder_valuation, sixthQuotient_valuation]
  omega

theorem sixthRemainder_valuation_lt (I P : Ideal O) : valuation (sixthRemainder I) P < 6 := by
  rw [sixthRemainder_valuation]
  omega

theorem sixthRemainder_eq_iff (I J : Ideal O) :
    sixthRemainder I = sixthRemainder J ↔
      ∀ P, valuation I P % 6 = valuation J P % 6 := by
  constructor
  · intro h P
    simpa only [sixthRemainder_valuation] using congrArg (fun K => valuation K P) h
  · intro h
    exact ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) (sixthRemainder_ne_zero J)
      (by simpa only [sixthRemainder_valuation] using h)

theorem sixth_normal_form_unique {A B C D : Ideal O}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hAf : ∀ P, valuation A P < 6) (hCf : ∀ P, valuation C P < 6)
    (h : A * B ^ 6 = C * D ^ 6) : A = C ∧ B = D := by
  have hv (P : Ideal O) := congrArg (fun I => valuation I P) h
  simp only [valuation_mul _ _ _ hA (pow_ne_zero _ hB),
    valuation_mul _ _ _ hC (pow_ne_zero _ hD), valuation_pow] at hv
  have he (P : Ideal O) : valuation A P = valuation C P ∧ valuation B P = valuation D P := by
    have := hv P
    have := hAf P
    have := hCf P
    omega
  exact ⟨ideal_eq_of_valuation_eq hA hC (fun P => (he P).1),
    ideal_eq_of_valuation_eq hB hD (fun P => (he P).2)⟩

theorem sixthQuotient_injective_on_remainder {I J : Ideal O}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hr : sixthRemainder I = sixthRemainder J)
    (hq : sixthQuotient I = sixthQuotient J) : I = J := by
  rw [← sixth_normal_form I hI, ← sixth_normal_form J hJ, hr, hq]

theorem sixthRemainder_eq_of_profile {I R : Ideal O} (hR : R ≠ 0)
    (hprofile : ∀ P, valuation I P % 6 = valuation R P) : sixthRemainder I = R := by
  apply ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) hR
  intro P
  simpa only [sixthRemainder_valuation] using hprofile P

theorem forced_fourth_power_dvd (I D : Ideal O) (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    D ^ 4 ∣ sixthRemainder I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hD.ne_zero)
    (sixthRemainder_ne_zero I)).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  change valuation (D ^ 4) P ≤ valuation (sixthRemainder I) P
  rw [valuation_pow, sixthRemainder_valuation]
  have hcount : valuation D P ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD) P
  by_cases hP : P ∈ normalizedFactors D
  · rw [hfour P hP]
    omega
  · have hz : valuation D P = 0 := Multiset.count_eq_zero.mpr hP
    simp only [hz, mul_zero, Nat.zero_le]

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm J : ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ))

theorem forced_fourth_power_norm_le (I D : Ideal O) (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    (Ideal.absNorm D : ℝ) ^ 4 ≤ (Ideal.absNorm (sixthRemainder I) : ℝ) := by
  simpa only [map_pow, Nat.cast_pow] using
    norm_le_of_dvd (sixthRemainder_ne_zero I) (forced_fourth_power_dvd I D hD hfour)

theorem sixth_normal_form_norm (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm (sixthRemainder I) : ℝ) *
      (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 = (Ideal.absNorm I : ℝ) := by
  have h := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ)) (sixth_normal_form I hI)
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using h

theorem sixthRemainder_norm_le (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm (sixthRemainder I) : ℝ) ≤ (Ideal.absNorm I : ℝ) :=
  norm_le_of_dvd hI ⟨sixthQuotient I ^ 6, (sixth_normal_form I hI).symm⟩

theorem sixthQuotient_norm_le (I : Ideal O) (hI : I ≠ 0) {H : ℝ} (hH : 0 ≤ H)
    (hNI : (Ideal.absNorm I : ℝ) ≤ H) :
    (Ideal.absNorm (sixthQuotient I) : ℝ) ≤
      (H / Ideal.absNorm (sixthRemainder I)) ^ (1 / 6 : ℝ) := by
  have hr := norm_pos (sixthRemainder_ne_zero I)
  have hp : (Ideal.absNorm (sixthQuotient I) : ℝ) ^ (6 : ℝ) ≤
      H / Ideal.absNorm (sixthRemainder I) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, le_div_iff₀ hr]
    rw [mul_comm, sixth_normal_form_norm I hI]
    exact hNI
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (div_nonneg hH hr.le)
      (by norm_num : (0 : ℝ) < 6)).mpr hp

theorem empty_of_below_remainder (S : Finset (Ideal O)) (R : Ideal O) {H : ℝ}
    (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H)
    (hH : H < Ideal.absNorm R) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  have hn := sixthRemainder_norm_le I (hS I hI)
  rw [hR I hI] at hn
  exact (not_le_of_gt hH) (hn.trans (hN I hI))

theorem ideal_count_fixed_remainder (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  by_cases hne : S.Nonempty
  · have hqbound (I : Ideal O) (hI : I ∈ S) :
        (Ideal.absNorm (sixthQuotient I) : ℝ) ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
      simpa only [hrem I hI] using sixthQuotient_norm_le I (hS I hI) hH (hN I hI)
    obtain ⟨I, hI⟩ := hne
    have hscale : 1 ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      (norm_one_le (sixthQuotient_ne_zero I)).trans (hqbound I hI)
    have hinj : Set.InjOn sixthQuotient S := by
      intro I hI J hJ he
      exact sixthQuotient_injective_on_remainder (hS I hI) (hS J hJ)
        ((hrem I hI).trans (hrem J hJ).symm) he
    have hc := DescentFiberCost.finite_ideal_count_real (S.image sixthQuotient)
      ((H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) hscale
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact sixthQuotient_ne_zero I)
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact hqbound I hI)
    rwa [Finset.card_image_iff.mpr hinj] at hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg hH (norm_pos hR).le) _)

theorem ideal_count_valuation_profile (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ I ∈ S, I ≠ 0)
    (hprofile : ∀ I ∈ S, ∀ P, valuation I P % 6 = valuation R P)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
  ideal_count_fixed_remainder S R hR H hH hS
    (fun I hI => sixthRemainder_eq_of_profile hR (hprofile I hI)) hN

theorem ideal_count_remainder_family (S Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (H : ℝ) (hH : 0 ≤ H)
    (hS : ∀ I ∈ S, I ≠ 0) (hrem : ∀ I ∈ S, sixthRemainder I ∈ Rs)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ ∑ R ∈ Rs, 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := Rs) hrem, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact ideal_count_fixed_remainder (S.filter (fun I => sixthRemainder I = R)) R
    (hRs R hR) H hH
    (fun I hI => hS I (Finset.mem_filter.mp hI).1)
    (fun I hI => (Finset.mem_filter.mp hI).2)
    (fun I hI => hN I (Finset.mem_filter.mp hI).1)

theorem ideal_count_of_remainder_norm_lower (S : Finset (Ideal O)) (R : Ideal O)
    (hR : R ≠ 0) (H L : ℝ) (hH : 0 ≤ H) (hL : 0 < L)
    (hLR : L ≤ Ideal.absNorm R) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / L) ^ (1 / 6 : ℝ) := by
  apply (ideal_count_fixed_remainder S R hR H hH hS hrem hN).trans
  gcongr

theorem element_count_le_six_ideal_count (S : Finset O) (hS : ∀ z ∈ S, z ≠ 0) :
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) := by
  have h := CompletedUnitRows.sum_nonzero_element_le_units S hS (fun _ => 1)
    (fun _ => by norm_num)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    CompletedUnitRows.unit_card, Nat.cast_ofNat] using h

theorem element_count_fixed_remainder (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  have hc := ideal_count_fixed_remainder (S.image (fun z => Ideal.span {z})) R hR H hH
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact Ideal.span_singleton_eq_bot.not.mpr (hS z hz))
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hrem z hz)
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hN z hz)
  calc
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) :=
      element_count_le_six_ideal_count S hS
    _ ≤ 6 * (128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) := by gcongr
    _ = 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by ring

theorem element_count_valuation_profile (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hprofile : ∀ z ∈ S, ∀ P, valuation (Ideal.span {z}) P % 6 = valuation R P)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
  element_count_fixed_remainder S R hR H hH hS
    (fun z hz => sixthRemainder_eq_of_profile hR (hprofile z hz)) hN

theorem element_count_remainder_family (S : Finset O) (Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (H : ℝ) (hH : 0 ≤ H)
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ ∑ R ∈ Rs, 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := Rs) hrem, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact element_count_fixed_remainder (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R
    (hRs R hR) H hH
    (fun z hz => hS z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hN z (Finset.mem_filter.mp hz).1)

theorem elements_empty_of_below_remainder (S : Finset O) (R : Ideal O) {H : ℝ}
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H)
    (hH : H < Ideal.absNorm R) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hn := sixthRemainder_norm_le (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hS z hz))
  rw [hrem z hz] at hn
  exact (not_le_of_gt hH) (hn.trans (hN z hz))

theorem element_count_power_scale (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : Z ^ d ≤ (Ideal.absNorm R : ℝ)) (hS : ∀ z ∈ S, z ≠ 0)
    (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hM : 0 ≤ C * Z ^ m := mul_nonneg hC (Real.rpow_nonneg hZ.le _)
  have hdiv : (C * Z ^ m) / Ideal.absNorm R ≤ (C * Z ^ m) / Z ^ d :=
    div_le_div_of_nonneg_left hM (Real.rpow_pos_of_pos hZ _) hRnorm
  calc
    (S.card : ℝ) ≤ 768 * ((C * Z ^ m) / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      element_count_fixed_remainder S R hR _ hM hS hrem hN
    _ ≤ 768 * ((C * Z ^ m) / Z ^ d) ^ (1 / 6 : ℝ) := by gcongr
    _ = 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      rw [mul_div_assoc, ← Real.rpow_sub hZ, Real.mul_rpow hC (Real.rpow_nonneg hZ.le _),
        ← Real.rpow_mul hZ.le]
      rw [show (m - d) * (1 / 6 : ℝ) = (m - d) / 6 by ring, mul_assoc]

theorem ideal_count_power_scale (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : Z ^ d ≤ (Ideal.absNorm R : ℝ)) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 128 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hM : 0 ≤ C * Z ^ m := mul_nonneg hC (Real.rpow_nonneg hZ.le _)
  have hdiv : (C * Z ^ m) / Ideal.absNorm R ≤ (C * Z ^ m) / Z ^ d :=
    div_le_div_of_nonneg_left hM (Real.rpow_pos_of_pos hZ _) hRnorm
  calc
    (S.card : ℝ) ≤ 128 * ((C * Z ^ m) / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      ideal_count_fixed_remainder S R hR _ hM hS hrem hN
    _ ≤ 128 * ((C * Z ^ m) / Z ^ d) ^ (1 / 6 : ℝ) := by gcongr
    _ = 128 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      rw [mul_div_assoc, ← Real.rpow_sub hZ, Real.mul_rpow hC (Real.rpow_nonneg hZ.le _),
        ← Real.rpow_mul hZ.le]
      rw [show (m - d) * (1 / 6 : ℝ) = (m - d) / 6 by ring, mul_assoc]

theorem element_count_forced_fourth_power (S : Finset O) (R D : Ideal O)
    (hR : R ≠ 0) (hD : Squarefree D) (Z C m f : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hDnorm : Z ^ (f / 2) ≤ (Ideal.absNorm D : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hfour : ∀ z ∈ S, ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - 2 * f) / 6) := by
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz⟩ := hne
    have hforced := forced_fourth_power_norm_le (Ideal.span {z}) D hD (hfour z hz)
    rw [hrem z hz] at hforced
    have hRnorm : Z ^ (2 * f) ≤ (Ideal.absNorm R : ℝ) := by
      calc
        Z ^ (2 * f) = (Z ^ (f / 2)) ^ (4 : ℕ) := by
          rw [← Real.rpow_mul_natCast hZ.le]
          congr 1
          norm_num
          ring
        _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := by gcongr
        _ ≤ (Ideal.absNorm R : ℝ) := hforced
    exact element_count_power_scale S R hR Z C m (2 * f) hZ hC hRnorm hS hrem hN
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity

theorem element_count_forced_fourth_power_weaker (S : Finset O) (R D : Ideal O)
    (hR : R ≠ 0) (hD : Squarefree D) (Z C m f : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hf : 0 ≤ f)
    (hDnorm : Z ^ (f / 2) ≤ (Ideal.absNorm D : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hfour : ∀ z ∈ S, ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - f) / 6) := by
  apply (element_count_forced_fourth_power S R D hR hD Z C m f
    (zero_lt_one.trans_le hZ) hC hDnorm hS hrem hfour hN).trans
  gcongr
  linarith

theorem valuation_eq_multiplicity {I P : Ideal O} (hI : I ≠ 0) (hP : Prime P) :
    valuation I P = multiplicity P I := by
  simpa only [valuation, normalize_eq] using
    (multiplicity_eq_count_normalizedFactors hP.irreducible hI).symm

theorem sixthRemainder_eq_of_prime_profile {I R : Ideal O} (hR : R ≠ 0)
    (hprofile : ∀ P, Prime P → valuation I P % 6 = valuation R P) :
    sixthRemainder I = R := by
  apply sixthRemainder_eq_of_profile hR
  intro P
  by_cases hP : Prime P
  · exact hprofile P hP
  · have hI0 : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    have hR0 : valuation R P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    simp only [hI0, hR0, Nat.zero_mod]

theorem element_count_power_scale_family (S : Finset O) (Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : ∀ R ∈ Rs, Z ^ d ≤ (Ideal.absNorm R : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * (Rs.card : ℝ) * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hcard : (S.card : ℝ) =
      ∑ R ∈ Rs, ((S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (t := Rs) hrem
  rw [hcard]
  calc
    _ ≤ ∑ R ∈ Rs, 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      apply Finset.sum_le_sum
      intro R hR
      exact element_count_power_scale
        (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R (hRs R hR)
        Z C m d hZ hC (hRnorm R hR)
        (fun z hz => hS z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hN z (Finset.mem_filter.mp hz).1)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem element_count_squareNorm (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hprofile : ∀ z ∈ S, ∀ P, Prime P → valuation (Ideal.span {z}) P % 6 = valuation R P)
    (hN : ∀ z ∈ S, ‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
  element_count_fixed_remainder S R hR H hH hS
    (fun z hz => sixthRemainder_eq_of_prime_profile hR (hprofile z hz))
    (fun z hz => by simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hN z hz)

end SevenEighths.CenteredExceptionalCount
end

end OAI
end OAIOriginalModule0338

/-! Original module: OAI.NumberTheory.DirichletL.CompactProfileFamily
Source SHA256: 0d19eb7d35bb31d17270f794e92e2a20ca9c2abcc5c1e15c3f7e08e3e4263937
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0339


namespace OAI

noncomputable section
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.CompactProfileFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem section_deriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : E) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
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

theorem compact_family_fourier_power_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
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

theorem compact_family_fourier_weighted_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
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

end SevenEighths.CompactProfileFamily

end

end OAI
end OAIOriginalModule0339

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Ideal
Source SHA256: f0ca6e538033b2b6b163e80dc70960b04a0c0f93ebc87565388e061a086c6086
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0340





namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def Admissible (I : Ideal Eis) : Prop := Squarefree I ∧ primaryGenerator I ≠ 0

def idealKernel (I J : Ideal Eis) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I (primaryGenerator J))

theorem idealKernel_reciprocity (I J : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealKernel I J = idealKernel J I :=
  congrArg eisEmbedding (CubicJacobiGlobal.idealSymbol_reciprocity I J hI hJ)

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm (primaryGenerator J) I) 2).trans_eq (by norm_num)

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, ite_eq_right hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem idealSymbol_cube_mask (I : Ideal Eis) (x : Eis)
    (hI : primaryGenerator I ≠ 0) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 3 =
      if IsCoprime I (Ideal.span {x}) then 1 else 0 := by
  have hlocal (P : Ideal Eis) (hP : P.IsMaximal ∧ goodLambda ∉ P) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 3 =
        if IsCoprime P (Ideal.span {x}) then 1 else 0 := by
    let : P.IsMaximal := hP.1
    let : Field (Eis ⧸ P) := Ideal.Quotient.field P
    let : Fintype (Eis ⧸ P) := Fintype.ofFinite _
    let χ := actualSextic P hP.2 ^ 2
    have hχ : χ ^ 3 = 1 :=
      (congrArg (fun φ : MulChar (Eis ⧸ P) ℂ => φ ^ 3)
        (canonicalSextic_pow_two P hP.2)).trans <|
          (MulChar.ringHomComp_pow _ _ _).trans <|
            (congrArg (fun φ : MulChar (Eis ⧸ P) Eis => φ.ringHomComp eisEmbedding)
              (cubicChar_pow_three P hP.2)).trans (MulChar.ringHomComp_one eisEmbedding)
    rw [CubicJacobiGlobal.primeValue_eq P hP.2]
    have hv := congrArg (fun φ : MulChar (Eis ⧸ P) ℂ => φ (Ideal.Quotient.mk P x))
      (canonicalSextic_pow_two P hP.2)
    change χ (Ideal.Quotient.mk P x) = _ at hv
    simp only [MulChar.ringHomComp_apply] at hv
    rw [← hv]
    rw [← map_pow, cubic_cube_eq_mask χ hχ, SixthPowerAverage.prime_coprime_span_iff]
    have hu : IsUnit (Ideal.Quotient.mk P x) ↔ x ∉ P := by
      rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    simp only [hu]
    split_ifs <;> rfl
  have hprod (S : Multiset (Ideal Eis))
      (hS : ∀ P ∈ S, P.IsMaximal ∧ goodLambda ∉ P) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 3 =
        if IsCoprime S.prod (Ideal.span {x}) then 1 else 0 := by
    induction S using Multiset.induction_on with
    | empty => simp only [Multiset.map_zero, Multiset.prod_zero, map_one, one_pow,
        isCoprime_one_left, ite_true]
    | @cons P S ih =>
      have hp := hS P (Multiset.mem_cons_self _ _)
      have ht := fun Q hQ => hS Q (Multiset.mem_cons_of_mem hQ)
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow,
        hlocal P hp, ih ht, IsCoprime.mul_left_iff]
      by_cases hP : IsCoprime P (Ideal.span {x}) <;>
        by_cases hS : IsCoprime S.prod (Ideal.span {x}) <;> simp [hP, hS]
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hf : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      P.IsMaximal ∧ goodLambda ∉ P := by
    intro P hP
    have h := primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)
    exact ⟨h.1, h.2.1⟩
  have h := hprod (UniqueFactorizationMonoid.normalizedFactors I) hf
  rw [Ideal.prod_normalizedFactors_eq_self hI0] at h
  simpa only [CubicJacobiGlobal.idealSymbol, ite_eq_right hI0] using h

theorem idealKernel_square_eq_star (I J : Ideal Eis) :
    idealKernel I J ^ 2 = star (idealKernel I J) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I (primaryGenerator J))

def idealNumeratorHom (I : Ideal Eis) (hI : primaryGenerator I ≠ 0) : Ideal Eis →* ℂ where
  toFun := idealKernel I
  map_one' := by
    change eisEmbedding (CubicJacobiGlobal.idealSymbol I (primaryGenerator 1)) = 1
    rw [primaryGenerator_one, CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' A B := by
    simp only [idealKernel, primaryGenerator_mul,
      CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem idealKernel_row_decomposition (I A B C : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) :
    idealKernel I (A * B ^ 2 * C ^ 3) =
      idealKernel I A * star (idealKernel I B) * idealKernel I C ^ 3 := by
  change idealNumeratorHom I hI (A * B ^ 2 * C ^ 3) = _
  rw [map_mul, map_mul, map_pow, map_pow]
  change idealKernel I A * idealKernel I B ^ 2 * idealKernel I C ^ 3 = _
  rw [idealKernel_square_eq_star]

def idealRange (X : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌊X⌋₊).filter Admissible

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

def idealMatrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => idealKernel J.val I.val

def sieveNorm (M N : ℝ) : ℝ := squaredNorm (idealMatrix M N)

theorem sieveNorm_reciprocity (M N : ℝ) : sieveNorm M N = sieveNorm N M := by
  apply squaredNorm_reciprocity
  intro I J
  exact idealKernel_reciprocity J.val I.val
    (mem_idealRange.mp J.property).1.2 (mem_idealRange.mp I.property).1.2

theorem ideal_energy_bound (M N : ℝ) (coef : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      idealKernel J.val I.val * coef J‖ ^ 2) ≤
        sieveNorm M N * ∑ J, ‖coef J‖ ^ 2 :=
  energy_le_squaredNorm (idealMatrix M N) coef

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem ideal_cube_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal Eis) (B : b → Ideal Eis) (C : c → Ideal Eis)
    (cols : n → Ideal Eis) (hc : ∀ j, primaryGenerator (cols j) ≠ 0)
    (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j *
      idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)) =
        ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
          coef j * idealKernel (cols j) (C l) ^ 3 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [idealKernel_row_decomposition _ _ _ _ (hc j)]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · intro l j
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (idealKernel_norm_le_one _ _) 3).trans_eq (by norm_num)

theorem ideal_cubic_factorization (I : Ideal Eis) (hI : I ≠ 0) :
    I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0340

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Poisson
Source SHA256: f5af67bdbe06cc658e10c16dac2ac334d2e84b52304e2f09b881ab1df57d4cf4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0341


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
open CompletedGauss ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem canonical_finite_prime_gauss_transform_scalar_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => actualSextic (P i) (hgood i) ^ j i) ψ
    hχ h

theorem canonical_finite_prime_gauss_transform_conj_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar_of_nontrivial P hc hgood j hχ ψ,
    finiteSexticQuotientRow_inv_eq_star P hc hgood j h]

theorem canonical_principal_gauss_transform_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj_of_nontrivial P hcop hgood j hχ φ (e h)

theorem canonical_radial_poisson_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform_of_nontrivial P hcop hgood j hχ c
      (span_finitePrimeModulus P) ψ,
      principalSexticRow_mk P hcop hgood j c (span_finitePrimeModulus P) h]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk P hcop hgood j c
    (span_finitePrimeModulus P)] using hp

theorem canonical_radial_poisson_normalized_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson_of_nontrivial P hcop hgood j hχ W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem norm_canonicalGaussSum_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1) :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => actualSextic (P i) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i)
    e χ ψ hχ (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ P i) e ψ hψ i)
  change ‖canonicalGaussSum P hcop hgood j‖ ^ 2 =
    (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

theorem norm_canonicalNormalizedGauss_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1) :
    ‖canonicalNormalizedGauss P hcop hgood j‖ = 1 := by
  have hn : ‖eisEmbedding (finitePrimeModulus P)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  change ‖canonicalGaussSum P hcop hgood j /
    (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)‖ = 1
  rw [norm_div,
    norm_canonicalGaussSum_of_nontrivial P hcop hgood j hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]

theorem canonical_polya_vinogradov_of_nontrivial {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hg i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero P hg j, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized_of_nontrivial P hcop hg j hχ W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss_of_nontrivial P hcop hg j hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

theorem canonical_masked_polya_vinogradov_of_nontrivial
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, goodLambda ∉ Q i) (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (Q i) (hg i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov_of_nontrivial Q hcop hg j hχ W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

def cubicExponent (negative : Bool) : ℕ := if negative then 4 else 2

theorem cubicExponent_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (negative : Bool) :
    actualSextic P hg ^ cubicExponent negative ≠ 1 := by
  let χ := actualSextic P hg ^ 2
  have hχ : χ ≠ 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg]
    exact (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one P hg)
  have h3 : χ ^ 3 = 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg, MulChar.ringHomComp_pow, cubicChar_pow_three P hg, MulChar.ringHomComp_one]
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = χ ^ 2 * χ := by rw [h, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := h3
  cases negative with
  | false => simpa only [cubicExponent, Bool.false_eq_true, ite_false,
      ] using hχ
  | true =>
      have he : actualSextic P hg ^ 4 = χ ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      simpa only [cubicExponent, ite_true, he] using h2

theorem cubic_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (negative : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow P hg (fun i => cubicExponent (negative i)) z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hg
        (fun i => cubicExponent (negative i)) / (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)) *
      ∑' h : O, star (finiteSexticRow P hg (fun i => cubicExponent (negative i)) h) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2) :=
  canonical_radial_poisson_normalized_of_nontrivial P hcop hg _
    (fun i => cubicExponent_nonprincipal (P i) (hg i) (negative i)) W scale hscale

theorem cubic_polya_vinogradov {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (negative : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    ‖∑' z : O, finiteSexticRow P hg (fun i => cubicExponent (negative i)) z *
      W (‖eisEmbedding z‖ ^ 2 / scale)‖ ≤
        pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ :=
  canonical_polya_vinogradov_of_nontrivial P hcop hg _
    (fun i => cubicExponent_nonprincipal (P i) (hg i) (negative i)) W scale hscale

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0341

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Initial
Source SHA256: 94cb7b370d645596caf23ce7648aeaede6252086a8913a7bf160b4fa2dc486bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0342



namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CompletedGauss ConcretePrimeRowBridge ShortDraftHeckeBridge QuadraticInitialBound
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicFiniteRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 2

theorem cubicFiniteRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    cubicFiniteRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 2) z := by
  simp only [cubicFiniteRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => actualSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]

def activeCubicExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 4 else 2

theorem activeCubicExponent_nonprincipal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (i : activeSupport S T) :
    actualSextic (P i.val) (hg i.val) ^ activeCubicExponent S T i ≠ 1 := by
  have h := cubicExponent_nonprincipal (P i.val) (hg i.val)
    (decide (i.val ∈ S \ T))
  simpa only [cubicExponent, activeCubicExponent, decide_eq_true_eq] using h

theorem cubicFiniteRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α) (z : O) :
    star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
          (activeCubicExponent S T) z := by
  have h := congrArg (fun v : ℂ => v ^ 2) (finiteSquarefreeRow_pair_activeSupport P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 2 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hrow : finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeExponent S T) z ^ 2 =
      finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeCubicExponent S T) z := by
    unfold finiteSexticRow
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have h6 : actualSextic (P i.val) (hg i.val) ^ 6 = 1 :=
      (pow_mul _ 2 3).trans <|
        (congrArg (fun φ : MulChar (O ⧸ P i.val) ℂ => φ ^ 3)
          (canonicalSextic_pow_two (P i.val) (hg i.val))).trans <|
            (MulChar.ringHomComp_pow _ _ _).trans <|
              (congrArg (fun φ : MulChar (O ⧸ P i.val) O => φ.ringHomComp eisEmbedding)
                (cubicChar_pow_three (P i.val) (hg i.val))).trans
                  (MulChar.ringHomComp_one eisEmbedding)
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
    apply congrArg (fun χ : MulChar (O ⧸ P i.val) ℂ => χ (Ideal.Quotient.mk (P i.val) z))
    change (actualSextic (P i.val) (hg i.val) ^ activeExponent S T i) ^ 2 = _
    unfold activeExponent activeCubicExponent
    split_ifs
    · rw [← pow_mul, show (5 * 2 : ℕ) = 4 + 6 by decide, pow_add, h6, mul_one]
    · simp
  simpa only [mul_pow, ← star_pow, hm, hrow, cubicFiniteRow] using h

theorem cubic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [cubicFiniteRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov_of_nontrivial P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (activeCubicExponent S T) (activeCubicExponent_nonprincipal P hg S T) W M hM

theorem cubic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (cubic_gram_offdiagonal P hinj hg S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)

theorem cubicFiniteRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    ‖cubicFiniteRow P hg S z‖ ≤ 1 := by
  rw [cubicFiniteRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _

theorem cubic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem cubic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (cubic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem cubic_mean_summable {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem cubic_mean_expand {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem cubic_initial_mean_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (cubic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact cubic_gram_offdiagonal_of_norm_le P hinj hg _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [cubic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

theorem cubic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := cubic_mean_summable P hg C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := cubic_initial_mean_bound P hinj hg C support hsupp N hN hNorm
      a sieveCutoff M hM

theorem ideal_initial_cubic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := cubic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0342

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Norm
Source SHA256: 44aad4716899c8d675c1f1ed8075049d92a9733847ee00e5551803a9fb6f69d9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0343



namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_inj_on_cubic_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J)
    (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I hI.2).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J hJ.2).1

theorem idealSymbol_eq_idealSexticRow_sq
    (F : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hI : I ∈ F) (hsq : Squarefree I) (z : O) :
    eisEmbedding (CubicJacobiGlobal.idealSymbol I z) =
      (idealSexticRow F hFp hFg I z) ^ 2 := by
  rw [← CanonicalRowCompletion.idealRowHom_square]
  congr 1
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFp
  conv_lhs => rw [← idealSupport_product_eq F hI hsq, map_prod]
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact CanonicalRowCompletion.idealRowHom_prime z i.val (primePool_good F hFg i)

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I ((mem_idealRange.mp hI).1.2)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_cubic_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (idealMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      (idealSexticRow F hFp hFg J.val z) ^ 2 * a J
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val (primaryGenerator I.val)) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dite_eq_left J.property]
    rfl
  rw [heR, hea] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0343

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Extraction
Source SHA256: b9ab9c792d666079addc51bda93f261b34fdf2c372ee8d5947c2f43e14844fba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0344


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primary_extracted_parts (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryGenerator (firstPart I) ≠ 0 ∧ primaryGenerator (secondPart I) ≠ 0 ∧
      primaryGenerator (cubePart I) ≠ 0 := by
  have he := congrArg primaryGeneratorHom
    (cubic_factorization I (primaryGenerator_ne_zero_ideal I hI))
  simp only [map_mul, map_pow] at he
  change primaryGenerator I = primaryGenerator (firstPart I) *
    primaryGenerator (secondPart I) ^ 2 * primaryGenerator (cubePart I) ^ 3 at he
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem firstPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (firstPart I) := ⟨firstPart_squarefree I, (primary_extracted_parts I hI).1⟩

theorem secondPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (secondPart I) := ⟨secondPart_squarefree I, (primary_extracted_parts I hI).2.1⟩

theorem extracted_norm_product (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  apply family_squared_norm_le (fun I : idealRange M => I.val)
    (fun J : idealRange N => J.val) Subtype.val_injective Subtype.val_injective M' N'
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hM⟩
  · intro J
    exact ⟨(mem_idealRange.mp J.property).1, (mem_idealRange.mp J.property).2.trans hN⟩

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0344

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Elements
Source SHA256: 84fd15141c08dcf0c41df42416e726f03509a1611fc0c463400141e59bafefad
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0345


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (I : Ideal O) (hI : primaryGenerator I ≠ 0) : O →* ℂ where
  toFun x := eisEmbedding (CubicJacobiGlobal.idealSymbol I x)
  map_one' := by rw [CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' x y := by rw [CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

theorem element_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal O) (B : b → Ideal O) (D : c → O)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j * elementCharacter (cols j) (hc j)
      (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * elementCharacter (cols j) (hc j)
        (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)) =
      ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
        coef j * elementCharacter (cols j) (hc j) (D l) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, map_pow]
    change coef j * (idealKernel (cols j) (A i) * idealKernel (cols j) (B k) ^ 2 *
      elementCharacter (cols j) (hc j) (D l)) = _
    rw [idealKernel_square_eq_star]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · exact fun l j => elementCharacter_norm_le_one _ _ _

def goodPart (I : Ideal O) : Ideal O := CanonicalQuadraticSieve.goodSquarefreePart I

def badPart (I : Ideal O) : Ideal O :=
  ∏ P ∈ CanonicalQuadraticSieve.badPrimeSupport I, P

theorem goodPart_admissible (I : Ideal O) : Admissible (goodPart I) := by
  have h := CanonicalQuadraticSieve.goodSquarefreePart_admissible I
  exact ⟨h.2.1, CanonicalQuadraticSieve.primaryGenerator_admissible _ h⟩

theorem badPart_mul_goodPart (I : Ideal O) (hI : Squarefree I) :
    badPart I * goodPart I = I := CanonicalQuadraticSieve.squarefree_bad_good_product I hI

def extractedGenerator (I : Ideal O) : O :=
  primaryGenerator (goodPart (firstPart I)) *
    primaryGenerator (goodPart (secondPart I)) ^ 2 *
    idealGenerator (cubePart I) ^ 3 *
    (idealGenerator (badPart (firstPart I)) * idealGenerator (badPart (secondPart I)) ^ 2)

theorem span_extractedGenerator (I : Ideal O) (hI : I ≠ 0) :
    Ideal.span {extractedGenerator I} = I := by
  change CanonicalRowCompletion.principalIdealHom (extractedGenerator I) = I
  unfold extractedGenerator
  simp only [map_mul, map_pow]
  change Ideal.span {primaryGenerator (goodPart (firstPart I))} *
    Ideal.span {primaryGenerator (goodPart (secondPart I))} ^ 2 *
    Ideal.span {idealGenerator (cubePart I)} ^ 3 *
    (Ideal.span {idealGenerator (badPart (firstPart I))} *
      Ideal.span {idealGenerator (badPart (secondPart I))} ^ 2) = I
  rw [(primaryGenerator_spec _ (goodPart_admissible (firstPart I)).2).1,
    (primaryGenerator_spec _ (goodPart_admissible (secondPart I)).2).1,
    span_idealGenerator, span_idealGenerator, span_idealGenerator]
  calc
    _ = (badPart (firstPart I) * goodPart (firstPart I)) *
        (badPart (secondPart I) * goodPart (secondPart I)) ^ 2 * cubePart I ^ 3 := by
      rw [mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := by
      rw [badPart_mul_goodPart _ (firstPart_squarefree I),
        badPart_mul_goodPart _ (secondPart_squarefree I)]
    _ = I := (cubic_factorization I hI).symm

theorem element_cubic_extraction (z : O) (hz : z ≠ 0) :
    ∃ u : Oˣ, z = u.val * extractedGenerator (Ideal.span {z}) := by
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have ha : Associated (extractedGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_extractedGenerator _ hI)
  obtain ⟨u, hu⟩ := ha
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

theorem badPart_sector (I : Ideal O) :
    ∃ E : CanonicalQuadraticSieve.fixedBadPrimes.powerset, badPart I = ∏ P ∈ E.val, P := by
  exact ⟨⟨CanonicalQuadraticSieve.badPrimeSupport I,
    Finset.mem_powerset.mpr (CanonicalQuadraticSieve.badPrimeSupport_subset I)⟩, rfl⟩

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0345

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.FullExtraction
Source SHA256: 8dcc9e91401df27db94db3fa37cf9221bd4edb801883d9c10c7a66b129f1482c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0346


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (firstPart (Ideal.span {z})))
def secondImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => goodPart (secondPart (Ideal.span {z})))
def cubeImage (R : Finset O) : Finset (Ideal O) :=
  R.image (fun z => cubePart (Ideal.span {z}))

def sourceFactor (R : Finset O)
    (d : Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
      CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R) : O :=
  d.1.val * idealGenerator d.2.2.2.val ^ 3 *
    (idealGenerator (∏ P ∈ d.2.1.val, P) * idealGenerator (∏ P ∈ d.2.2.1.val, P) ^ 2)

theorem full_element_extraction_energy {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2) ≤
      (96 : ℝ) * (cubeImage R).card *
        min ((secondImage R).card * squaredNorm
            (fun (i : firstImage R) j => idealKernel (cols j) i.val))
          ((firstImage R).card * squaredNorm
            (fun (k : secondImage R) j => idealKernel (cols j) k.val)) *
        ∑ j, ‖coef j‖ ^ 2 := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  let D := Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
    CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R
  let T := D × secondImage R × firstImage R
  let reconstruct : T → O := fun p => primaryGenerator p.2.2.val *
    primaryGenerator p.2.1.val ^ 2 * sourceFactor R p.1
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2
  have hcover : R ⊆ Finset.univ.image reconstruct := by
    intro z hz
    let I : Ideal O := Ideal.span {z}
    obtain ⟨u, hu⟩ := element_cubic_extraction z (hR z hz)
    obtain ⟨e, he⟩ := badPart_sector (firstPart I)
    obtain ⟨f, hf⟩ := badPart_sector (secondPart I)
    let a : firstImage R := ⟨goodPart (firstPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let b : secondImage R := ⟨goodPart (secondPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let c : cubeImage R := ⟨cubePart I, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨((u, e, f, c), b, a), Finset.mem_univ _, ?_⟩
    change primaryGenerator (goodPart (firstPart I)) *
      primaryGenerator (goodPart (secondPart I)) ^ 2 *
        (u.val * idealGenerator (cubePart I) ^ 3 *
          (idealGenerator (∏ P ∈ e.val, P) * idealGenerator (∏ P ∈ f.val, P) ^ 2)) = z
    rw [hu]
    change _ = u.val * extractedGenerator I
    unfold extractedGenerator
    rw [he, hf]
    ring
  have hsum : (∑ z ∈ R, E z) ≤ ∑ p : T, E (reconstruct p) := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.image reconstruct, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
  have hb := element_block_energy_le
    (fun i : firstImage R => i.val) (fun k : secondImage R => k.val)
    (sourceFactor R) cols hc coef
  have hcard : Fintype.card D = 96 * (cubeImage R).card := by
    have hu : Fintype.card Oˣ = 6 := by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp only [D, Fintype.card_prod, Fintype.card_coe, hu,
      CanonicalQuadraticSieve.fixedBadPrimes_powerset_card]
    omega
  have heq : (∑ p : T, E (reconstruct p)) =
      ∑ l : D, ∑ k : secondImage R, ∑ i : firstImage R,
        ‖∑ j, coef j * elementCharacter (cols j) (hc j)
          (primaryGenerator i.val * primaryGenerator k.val ^ 2 * sourceFactor R l)‖ ^ 2 := by
    simp only [T, Fintype.sum_prod_type, E, reconstruct]
  rw [heq] at hsum
  apply hsum.trans
  dsimp only [D] at hcard
  convert hb using 1
  simp only [hcard, Nat.cast_mul, Nat.cast_ofNat, Fintype.card_coe]

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0346

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ExtractionBounds
Source SHA256: d6da5537a3a859a5502f63753567375cc4caa55e01c0baea6274b6ae1c031cd4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0347


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem extracted_parts_ne_zero (I : Ideal O) (hI : I ≠ 0) :
    firstPart I ≠ 0 ∧ secondPart I ≠ 0 ∧ cubePart I ≠ 0 := by
  have he := cubic_factorization I hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem goodPart_norm_le (I : Ideal O) (hI : Squarefree I) :
    (Ideal.absNorm (goodPart I) : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast CanonicalQuadraticSieve.goodSquarefreePart_norm_le I hI

theorem full_element_extraction_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (X Y H N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hfirst : ∀ z ∈ R, (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ X)
    (hsecond : ∀ z ∈ R, (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ Y)
    (hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤ H)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (96 * 128 ^ 2 : ℝ) * H *
        min (Y * sieveNorm X N) (X * sieveNorm Y N) * ∑ j, ‖coef j‖ ^ 2 := by
  have ha : ∀ I ∈ firstImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (firstPart_squarefree _)).trans (hfirst z hz)⟩
  have hb : ∀ I ∈ secondImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (secondPart_squarefree _)).trans (hsecond z hz)⟩
  have hca : ((firstImage R).card : ℝ) ≤ 128 * X :=
    DescentFiberCost.finite_ideal_count_real _ X hX
      (fun I hI => primaryGenerator_ne_zero_ideal I (ha I hI).1.2) (fun I hI => (ha I hI).2)
  have hcb : ((secondImage R).card : ℝ) ≤ 128 * Y :=
    DescentFiberCost.finite_ideal_count_real _ Y hY
      (fun I hI => primaryGenerator_ne_zero_ideal I (hb I hI).1.2) (fun I hI => (hb I hI).2)
  have hcc : ((cubeImage R).card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real _ H hH
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact (extracted_parts_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))).2.2
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact hcube z hz
  have hna := family_squared_norm_le (fun I : firstImage R => I.val) cols
    Subtype.val_injective hinj X N (fun I => ha I.val I.property) hcols
  have hnb := family_squared_norm_le (fun I : secondImage R => I.val) cols
    Subtype.val_injective hinj Y N (fun I => hb I.val I.property) hcols
  have hmin : min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) ≤
      128 * min (Y * sieveNorm X N) (X * sieveNorm Y N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 128)]
    apply min_le_min
    · calc
        _ ≤ (128 * Y) * sieveNorm X N := mul_le_mul hcb hna (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (128 * X) * sieveNorm Y N := mul_le_mul hca hnb (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
  have hn : 0 ≤ min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) := by
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
  calc
    _ ≤ _ := full_element_extraction_energy R hR cols (fun j => (hcols j).1.2) coef
    _ ≤ (96 * (128 * H)) * (128 * min (Y * sieveNorm X N) (X * sieveNorm Y N)) *
        ∑ j, ‖coef j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcc (by norm_num)) hmin hn (by positivity)
    _ = _ := by ring

theorem cubePart_norm_le_of_block (I : Ideal O) (hI : I ≠ 0)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H)
    (hx : X ≤ (Ideal.absNorm (firstPart I) : ℝ))
    (hy : Y ≤ (Ideal.absNorm (secondPart I) : ℝ))
    (hN : (Ideal.absNorm I : ℝ) ≤ X * Y ^ 2 * H ^ 3) :
    (Ideal.absNorm (cubePart I) : ℝ) ≤ H := by
  have hp := extracted_norm_product I hI
  have hxy : X * Y ^ 2 ≤ (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 :=
    mul_le_mul hx (pow_le_pow_left₀ hY.le hy 2) (sq_nonneg _) (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hH
  apply (mul_le_mul_iff_right₀ (mul_pos hX (sq_pos_of_pos hY))).mp
  calc
    _ ≤ (Ideal.absNorm (firstPart I) : ℝ) *
        (Ideal.absNorm (secondPart I) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart I) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hxy (by positivity)
    _ = Ideal.absNorm I := hp.symm
    _ ≤ _ := hN

theorem full_element_dyadic_block_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (M X Y N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X * Y ^ 2 ≤ M)
    (hfirst : ∀ z ∈ R, X ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ 2 * X)
    (hsecond : ∀ z ∈ R, Y ≤ (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ 2 * Y)
    (hnorm : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (192 * 128 ^ 2 : ℝ) * (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
        min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) * ∑ j, ‖coef j‖ ^ 2 := by
  have hp : 0 < X * Y ^ 2 := by positivity
  have hq : 1 ≤ M / (X * Y ^ 2) := (le_div_iff₀ hp).mpr (by simpa using hXY)
  have hH : 1 ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hpow : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ M / (X * Y ^ 2)) (by decide : (3 : ℕ) ≠ 0)
  have hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤
      (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
    intro z hz
    apply cubePart_norm_le_of_block _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))
      X Y _ (by linarith) (by linarith) (by linarith) (hfirst z hz).1 (hsecond z hz).1
    rw [hpow, mul_div_cancel₀ _ hp.ne']
    exact hnorm z hz
  have hb := full_element_extraction_norm_bound R hR (2 * X) (2 * Y) _ N
    (by linarith) (by linarith) hH (fun z hz => (hfirst z hz).2)
    (fun z hz => (hsecond z hz).2) hcube cols hinj hcols coef
  convert hb using 1
  have hm : min (2 * Y * sieveNorm (2 * X) N) (2 * X * sieveNorm (2 * Y) N) =
      2 * min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hm]
  ring

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0347

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Dyadic
Source SHA256: b715496a642627823a3d71ad86f043e83038ba92699a16060626d25d6cca295b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0348


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma extracted_norm_bounds (I : Ideal O) (hI : I ≠ 0) :
    (1 ≤ (Ideal.absNorm (firstPart I) : ℝ) ∧
      (Ideal.absNorm (firstPart I) : ℝ) ≤ Ideal.absNorm I) ∧
    (1 ≤ (Ideal.absNorm (secondPart I) : ℝ) ∧
      (Ideal.absNorm (secondPart I) : ℝ) ≤ Ideal.absNorm I) := by
  have hn : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp := extracted_parts_ne_zero I hI
  have ha : 1 ≤ Ideal.absNorm (firstPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.1)
  have hb : 1 ≤ Ideal.absNorm (secondPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
  have hda : firstPart I ∣ I := ⟨secondPart I ^ 2 * cubePart I ^ 3, by
    simpa only [mul_assoc] using cubic_factorization I hI⟩
  have hdb : secondPart I ∣ I := ⟨firstPart I * secondPart I * cubePart I ^ 3, by
    calc
      I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI
      _ = _ := by ring⟩
  exact ⟨⟨by exact_mod_cast ha, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hda)⟩,
    ⟨by exact_mod_cast hb, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdb)⟩⟩

def extractionLabel (M : ℝ) (z : O) :
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) :=
  (CanonicalQuadraticSieve.divisorDyadicLabel M (firstPart (Ideal.span {z})),
   CanonicalQuadraticSieve.divisorDyadicLabel M (secondPart (Ideal.span {z})))

def extractionBin (R : Finset O) (M : ℝ)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)) : Finset O :=
  R.filter (fun z => extractionLabel M z = j)

lemma sum_extractionBins {A : Type*} [AddCommMonoid A] (R : Finset O) (M : ℝ) (f : O → A) :
    (∑ z ∈ R, f z) = ∑ j, ∑ z ∈ extractionBin R M j, f z := by
  simp only [extractionBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

lemma extractionBin_bounds (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (z : O) (hz : z ∈ extractionBin R M j) :
    (CanonicalQuadraticSieve.divisorDyadicScale j.1.val ≤
        (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.1.val) ∧
    (CanonicalQuadraticSieve.divisorDyadicScale j.2.val ≤
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.2.val) := by
  obtain ⟨hzR, hj⟩ := Finset.mem_filter.mp hz
  have hparts := extracted_norm_bounds (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1)
  have hx := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.1.1
    (hparts.1.2.trans (hR z hzR).2)
  have hy := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.2.1
    (hparts.2.2.trans (hR z hzR).2)
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.1 at hj1
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.2 at hj2
  rw [hj1] at hx
  rw [hj2] at hy
  refine ⟨⟨max_le hparts.1.1 hx.1.le, ?_⟩, ⟨max_le hparts.2.1 hy.1.le, ?_⟩⟩
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.1.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hx.2]
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.2.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hy.2]

lemma extractionBin_scale_product (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (hj : (extractionBin R M j).Nonempty) :
    CanonicalQuadraticSieve.divisorDyadicScale j.1.val *
      CanonicalQuadraticSieve.divisorDyadicScale j.2.val ^ 2 ≤ M := by
  obtain ⟨z, hz⟩ := hj
  have hzR := (Finset.mem_filter.mp hz).1
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1
  have hh := extractionBin_bounds R M hR j z hz
  have hcube : 1 ≤ (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (extracted_parts_ne_zero _ hI).2.2)
  calc
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 :=
      mul_le_mul hh.1.1 (pow_le_pow_left₀
        (le_trans (by norm_num) (CanonicalQuadraticSieve.divisorDyadicScale_ge_one _)) hh.2.1 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcube)
    _ = Ideal.absNorm (Ideal.span {z}) := (extracted_norm_product _ hI).symm
    _ ≤ M := (hR z hzR).2

theorem full_element_dyadic_extraction {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hRne : R.Nonempty) (M N : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    ∃ X Y : ℝ, 1 ≤ X ∧ 1 ≤ Y ∧ X * Y ^ 2 ≤ M ∧
      (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
        (192 * 128 ^ 2 : ℝ) *
          (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ) ^ 2 *
          (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
          min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) *
          ∑ j, ‖coef j‖ ^ 2 := by
  let J := Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)
  let active : Finset J := Finset.univ.filter (fun j => (extractionBin R M j).Nonempty)
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2
  let b : J → ℝ := fun j => ∑ z ∈ extractionBin R M j, E z
  have hactive : active.Nonempty := by
    obtain ⟨z, hz⟩ := hRne
    refine ⟨extractionLabel M z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image active b hactive
  have hjne : (extractionBin R M j).Nonempty := (Finset.mem_filter.mp hj).2
  have hbnonneg : 0 ≤ b j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ z ∈ R, E z) ≤ (Fintype.card J : ℝ) * b j := by
    rw [sum_extractionBins R M E]
    calc
      _ ≤ ∑ k : J, b j := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hka : k ∈ active
        · exact hmax k hka
        · have hempty : extractionBin R M k = ∅ := by
            have hh : ¬ (extractionBin R M k).Nonempty := by
              simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hka
            exact Finset.not_nonempty_iff_eq_empty.mp hh
          simpa only [hempty, Finset.sum_empty] using hbnonneg
      _ = _ := by simp
  let X := CanonicalQuadraticSieve.divisorDyadicScale j.1.val
  let Y := CanonicalQuadraticSieve.divisorDyadicScale j.2.val
  have hX : 1 ≤ X := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hY : 1 ≤ Y := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hXY : X * Y ^ 2 ≤ M := extractionBin_scale_product R M hR j hjne
  refine ⟨X, Y, hX, hY, hXY, ?_⟩
  have hb := full_element_dyadic_block_bound (extractionBin R M j)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).1) M X Y N hX hY hXY
    (fun z hz => (extractionBin_bounds R M hR j z hz).1)
    (fun z hz => (extractionBin_bounds R M hR j z hz).2)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).2) cols hinj hcols coef
  calc
    _ ≤ (Fintype.card J : ℝ) * b j := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0348

/-! Original module: OAI.NumberTheory.DirichletL.Descent.DescentProfiles
Source SHA256: af9dc28056c60ef7c8ead58d9717c8f1416ceb5a497771e38a26db0e64f44343
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0349


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

theorem descent_profile_identity {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak : ι → ℝ)
    (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (he : ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t : ℝ, (∏ i, V i (y i) * logPhase t (ak i * y i)) * b t) :
    ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
        paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
          (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
            logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) := by
  intro y
  let P : ℂ := ∏ i, V i (y i)
  let x₁ : ℝ := ∑ i, a₁ i * y i
  let x₂ : ℝ := ∑ i, a₂ i * y i
  let xk : ℝ := ∑ i, ak i * y i
  have hphase (t : ℝ) (a : ι → ℝ) :
      (∏ i, logPhase t (a i * y i)) = logPhase t (∑ i, a i * y i) :=
    (logPhase_sum Finset.univ t (fun i => a i * y i)).symm
  have hk' : P * paperRadialFourier W (R * Real.exp xk) =
      ∫ t : ℝ, P * logPhase t xk * b t := by
    simpa only [Finset.prod_mul_distrib, hphase, P, xk] using he y
  have hprod (t₁ t₂ t₃ : ℝ) :
      (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
        logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) =
      P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk := by
    simp only [Finset.prod_mul_distrib, hphase, P, x₁, x₂, xk]
  simp only [hprod, tripleCoefficient]
  have hinner (t₁ t₂ : ℝ) :
      (∫ t₃ : ℝ, (𝓕 g₁) t₁ * ((𝓕 g₂) t₂ * b t₃) *
        (P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk)) =
      ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [hk', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t₃
    ring
  simp_rw [hinner]
  have hmid (t₁ : ℝ) :
      (∫ t₂ : ℝ, ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk))) =
      (logPhase t₁ x₁ * (𝓕 g₁) t₁) * g₂ x₂ *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [schwartz_logPhase_inversion g₂ x₂, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t₂
    ring
  simp_rw [hmid]
  rw [integral_mul_const, integral_mul_const, ← schwartz_logPhase_inversion]
  dsimp only [P, x₁, x₂, xk]
  ring

theorem descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
          paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hk⟩ := paperRadialFourier_log_separation_envelope W V ak M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b, ?_, hi, hb, hp⟩
  exact descent_profile_identity g₁ g₂ W V a₁ a₂ ak R b he

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

theorem tripleCoefficient_weighted_integral (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : Frequency,
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) =
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₁ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₂ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) := by
  have he (t : Frequency) :
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖ =
      ((1 + ‖t.1‖)^J * ‖b₁ t.1‖) *
        (((1 + ‖t.2.1‖)^J * ‖b₂ t.2.1‖) * ((1 + ‖t.2.2‖)^J * ‖b₃ t.2.2‖)) := by
    simp only [tripleCoefficient, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₁ t‖)
    (fun t : ℝ × ℝ => ((1 + ‖t.1‖)^J * ‖b₂ t.1‖) * ((1 + ‖t.2‖)^J * ‖b₃ t.2‖))]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₂ t‖) (fun t : ℝ => (1 + ‖t‖)^J * ‖b₃ t‖)]
  ring

theorem source_descent_profile_separation {ι : Type*} [Fintype ι]
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, a₁ i * y i)) *
          W₂ (Real.exp (∑ i, a₂ i * y i)) * paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  obtain ⟨C, hC, hsep⟩ := descent_profile_separation g₁ g₂ Φ V a₁ a₂ ak M hM hV A J
  let I₁ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₁) t‖
  let I₂ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₂) t‖
  have hI₁ : 0 ≤ I₁ := integral_nonneg (fun t => by positivity)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun t => by positivity)
  refine ⟨𝓕 g₁, 𝓕 g₂, I₁ * I₂ * C, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, heq, hi, hb, hp⟩ := hsep R hR
  refine ⟨b₃, ?_, tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  · simpa only [g₁, g₂, CubicReflectionKernel.logSchwartz_apply] using heq
  · rw [tripleCoefficient_weighted_integral]
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hI₁ hI₂)
    convert hh using 1 ; dsimp only [I₁, I₂] ; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0349

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualProfiles
Source SHA256: e18456e2afe7c61db5c483b64351251c7b7c2c6911dd70bae523115e26506fc4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0350


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def inverseNormWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.exp y : ℂ)
def inverseRootWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.sqrt (Real.exp y) : ℂ)

def firstRootWindows (V : Fin 9 → ℝ → ℂ) : Fin 9 → ℝ → ℂ :=
  ![V 0, V 1, V 2, inverseNormWindow (V 3), inverseRootWindow (V 4),
    inverseNormWindow (V 5), V 6, inverseRootWindow (V 7), inverseRootWindow (V 8)]

def firstLeftSlope : Fin 9 → ℝ := ![1, 0, 1, 0, 0, 1, 0, 1, 0]
def firstRightSlope : Fin 9 → ℝ := ![0, 1, 1, 0, 0, 1, 0, 0, 1]
def firstKernelSlope : Fin 9 → ℝ := ![0, 0, 0, -1, -1, -2, 1, -1, -1]

def secondRootWindows (V : Fin 6 → ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![V 0, inverseNormWindow (V 1), inverseNormWindow (V 2), V 3,
    inverseRootWindow (V 4), inverseRootWindow (V 5)]

def secondLeftSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 1, 0]
def secondRightSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 0, 1]
def secondKernelSlope : Fin 6 → ℝ := ![0, -1, -2, 1, -1, -1]

def firstPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (∏ i, firstRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, firstLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, firstRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, firstKernelSlope i * y i))

def secondPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (∏ i, secondRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, secondLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, secondRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, secondKernelSlope i * y i))

def profileMode {ι : Type*} [Fintype ι] (V : ι → ℝ → ℂ)
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) : ℂ :=
  ∏ i, V i (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

theorem first_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, firstRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope M hM hU A J

theorem second_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 6 → ℝ, secondPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope M hM hU A J

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0350

/-! Original module: OAI.NumberTheory.DirichletL.Descent.DescentHeight
Source SHA256: 3c10c23604c0e175c64f3cb796130de3db7fdfcd2a650e4fe8129e77f2f92976
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0351


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

theorem twisted_descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * frequencyTwist g₁ θ₁ (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ₂ (∑ i, a₂ i * y i) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ (t₁,t₂,t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ≤
        C * (1 + ‖θ₁‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1 + ‖θ₂‖)^(J + (volume : Measure ℝ).integrablePower) := by
  obtain ⟨Ck, hCk, hk⟩ := paperRadialFourier_log_separation_envelope Φ V ak M hM hV A J
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  refine ⟨C₁ * C₂ * Ck, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b₃, ?_⟩
  intro θ₁ θ₂
  refine ⟨descent_profile_identity _ _ Φ V a₁ a₂ ak R b₃ he,
    tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  rw [tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (mul_le_mul (h₁ θ₁) (h₂ θ₂)
    (integral_nonneg (fun t => by positivity)) (by positivity)) hb
    (by positivity : 0 ≤ (1 + R)^A * ∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) (by positivity)
  convert hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0351

/-! Original module: OAI.NumberTheory.DirichletL.Descent.IdealMasks
Source SHA256: f5ead07118118f452efb4ab516a1f19317b1dba32845ad5e4c1f9f4c880156e0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0352




namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem prime_mem_support_iff_dvd (P A : Ideal ActualEisensteinCubic.O)
    (hP : Prime P) (hA : A ≠ 0) :
    P ∈ IdealMobiusDivisorSum.primeSupport A ↔ P ∣ A := by
  simp only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hA, hP, true_and]

theorem ideal_primeMark_eq_divisibility {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P)
    (A : Ideal ActualEisensteinCubic.O) (hA : A ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport A) =
      ∏ i ∈ I, ∑ P ∈ L i, if P ∣ A then a i P else 0 := by
  unfold primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro P hP
  simp only [prime_mem_support_iff_dvd P A (hL i hi P hP) hA]

theorem ideal_primeSupport_mul_cube (n b : Ideal ActualEisensteinCubic.O)
    (hn : n ≠ 0) (hb : b ≠ 0) :
    IdealMobiusDivisorSum.primeSupport (n * b ^ 3) =
      IdealMobiusDivisorSum.primeSupport n ∪ IdealMobiusDivisorSum.primeSupport b := by
  simp only [IdealMobiusDivisorSum.primeSupport,
    normalizedFactors_mul hn (pow_ne_zero 3 hb), normalizedFactors_pow,
    Multiset.toFinset_add]
  congr 1
  ext P
  simp

theorem ideal_whole_mark_priority {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
    (a : σ → Ideal ActualEisensteinCubic.O → ℂ)
    (n b : Ideal ActualEisensteinCubic.O) (hn : n ≠ 0) (hb : b ≠ 0) :
    primeMark I L a (IdealMobiusDivisorSum.primeSupport (n * b ^ 3)) =
      ∑ J ∈ I.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport n) *
        primeMark (I \ J) L a
          (IdealMobiusDivisorSum.primeSupport b \ IdealMobiusDivisorSum.primeSupport n) := by
  rw [ideal_primeSupport_mul_cube n b hn hb]
  exact primeMark_priority _ _ _ _ _

theorem ideal_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (I : Finset σ) (L : σ → Finset (Ideal ActualEisensteinCubic.O))
      (a : σ → Ideal ActualEisensteinCubic.O → ℂ),
      (I : Set σ).PairwiseDisjoint L →
      (∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) →
      ∀ A : Ideal ActualEisensteinCubic.O, A ≠ 0 →
        ‖primeMark I L a (IdealMobiusDivisorSum.primeSupport A)‖ ≤
          C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro σ _ I L a hL ha A hA
  exact (primeMark_norm_le_divisor_count I L a _ hL ha).trans (hb A hA)

theorem ideal_coprime_mobius (K P : Ideal ActualEisensteinCubic.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]

theorem idealZeroMask_primary_indicator
    (D B : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0)
    (hB : CompletedGauss.primaryGenerator B ≠ 0) :
    CanonicalQuadraticSieve.idealZeroMask D (CompletedGauss.primaryGenerator B) =
      if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {CompletedGauss.primaryGenerator B} =
      Ideal.span {ConcretePrimeRowBridge.idealGenerator B} := by
    rw [(CompletedGauss.primaryGenerator_spec B hB).1,
      ConcretePrimeRowBridge.span_idealGenerator]
  rw [CanonicalQuadraticSieve.idealZeroMask_span_eq D _ _ he,
    CanonicalQuadraticSieve.idealZeroMask_generator_eq_indicator D B hD]

theorem hybrid_quadratic_square_mask
    (k n b c m h t : Ideal ActualEisensteinCubic.O)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) =
      (if IsCoprime k (c * t) then 1 else 0) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) := by
  have he : n * b = (c * t) ^ 2 * (m * h) := by rw [hn, hb]; ring
  rw [he, CanonicalQuadraticSieve.canonical_quadraticRow_primary_squarefree k hk,
    idealZeroMask_primary_indicator k (c * t) hk.1 hct]
  rw [isCoprime_comm]

theorem hybrid_double_mask_mobius
    (k P c : Ideal ActualEisensteinCubic.O) (hk : k ≠ 0) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

theorem hybrid_column_decomposition
    (n b : Ideal ActualEisensteinCubic.O) (hn : Squarefree n) (hb : b ≠ 0) :
    ∃ c m h t : Ideal ActualEisensteinCubic.O,
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ 0 := by
  let g := QuadraticSquarefreeKernel.squarefreePart b
  let t := QuadraticSquarefreeKernel.squarePart b
  let c := gcd n g
  let m := CanonicalQuadraticSieve.idealQuotient c n
  let h := CanonicalQuadraticSieve.idealQuotient c g
  have hg : Squarefree g := QuadraticSquarefreeKernel.squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (CanonicalQuadraticSieve.idealQuotient_mul hcn).symm
  have hgh : g = c * h := (CanonicalQuadraticSieve.idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (QuadraticSquarefreeKernel.squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    QuadraticSquarefreeKernel.squarePart_ne_zero hb⟩

theorem ideal_product_fiber_card
    (s t : Finset (Ideal ActualEisensteinCubic.O))
    (J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    (((s ×ˢ t).filter (fun p => p.1 * p.2 = J)).card) ≤ (idealDivisors J).card :=
  CanonicalQuadraticSieve.product_fiber_card (s ×ˢ t) J hJ

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O))
    (B J : Ideal ActualEisensteinCubic.O) (hJ : J ≠ 0) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ 0 := by
      intro hz
      apply hJ
      rw [← hep, hz, mul_zero]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end

end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0352

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Gcd
Source SHA256: 5b55cbddd422dc616d489815c5a04cf30f4f6f5a6fd9dfb09b30c26ebb0097e9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0353



namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicRow (I : Ideal O) (z : O) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I z)

lemma cubicRow_mul (I J : Ideal O) (z : O) :
    cubicRow (I * J) z = cubicRow I z * cubicRow J z := by
  simp only [cubicRow, ← CanonicalRowCompletion.idealRowHom_square, map_mul, mul_pow]

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

lemma cubicRow_common_mask (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

lemma cubicRow_common_mobius (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [cubicRow_common_mask D hD z]
  exact SevenEighths.InverseMoment.ideal_coprime_mobius D _ (primaryGenerator_ne_zero_ideal D hD)

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

lemma cubic_admissible_quotient {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) :=
  cubic_admissible_of_dvd hI (CanonicalQuadraticSieve.idealQuotient_dvd hD)

lemma cubicRow_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    cubicRow I z = cubicRow D z * cubicRow (idealQuotient D I) z := by
  conv_lhs => rw [← CanonicalQuadraticSieve.idealQuotient_mul hDI]
  exact cubicRow_mul _ _ _

def cubicGcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0

theorem cubicGcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    cubicGcdTerm D cols a z j k =
      (star (cubicRow D z) * cubicRow D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (cubicRow (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (cubicRow (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [cubicGcdTerm, totalQuotient, ite_eq_left hj, ite_eq_left hk]
      rw [← CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, cubicRow_divisor_factor D _ hj,
          cubicRow_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [cubicGcdTerm, ite_eq_right hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [cubicGcdTerm, ite_eq_right hg]
    simp [hj]

theorem cubic_weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, cubicRow (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, cubicGcdTerm D cols a z j k) =
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [cubicGcdTerm, ite_true]
    · intro D hD hne
      exact ite_eq_right (Ne.symm hne)
    · exact fun h => (h (CanonicalQuadraticSieve.mem_gcdPool cols j k)).elim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => cubicRow (cols j) z * a j)

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0353

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.FullNorm
Source SHA256: 8d1cce620d9a82caeb4b7a2dfeb6e278a2f51029e3bad43656c64f8a35bbd38a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0354


namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementRange (M : ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌊M⌋₊).filter
    (fun z => z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)

lemma mem_elementRange (M : ℝ) (z : O) :
    z ∈ elementRange M ↔ z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_qNat_le
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Nat.le_floor h.2

def elementMatrix (M N : ℝ) : Matrix (elementRange M) (idealRange N) ℂ :=
  fun z J => cubicRow J.val z.val

def elementSieveNorm (M N : ℝ) : ℝ := squaredNorm (elementMatrix M N)

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma sieveNorm_le_elementSieveNorm (M N : ℝ) : sieveNorm M N ≤ elementSieveNorm M N := by
  apply element_family_squared_norm_le
    (fun I : idealRange M => primaryGenerator I.val) (fun J : idealRange N => J.val)
  · intro I J he
    exact Subtype.ext (primaryGenerator_inj_on_cubic_admissible
      (mem_idealRange.mp I.property).1 (mem_idealRange.mp J.property).1 he)
  · exact Subtype.val_injective
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1.2, by
      rw [(primaryGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1]
      exact (mem_idealRange.mp I.property).2⟩
  · intro J
    exact mem_idealRange.mp J.property

lemma elementSieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    elementSieveNorm M N ≤ elementSieveNorm M' N' := by
  apply element_family_squared_norm_le (fun z : elementRange M => z.val)
    (fun I : idealRange N => I.val) Subtype.val_injective Subtype.val_injective
  · intro z
    exact ⟨((mem_elementRange M z.val).mp z.property).1,
      ((mem_elementRange M z.val).mp z.property).2.trans hM⟩
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hN⟩

theorem element_coprime_bilinear_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (hN : 0 ≤ N)
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a b : n → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) (rows i) * a j) * (cubicRow (cols k) (rows i) * b k) else 0‖) ^ 2 ≤
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖b j‖ ^ 2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε cols cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    N N hN hN (fun j => (hcols j).2) (fun j => (hcols j).2)
    (fun i j => cubicRow (cols j) (rows i)) (fun i j => cubicRow (cols j) (rows i)) a b
  have hn := element_family_squared_norm_le rows cols hr hc M N hrows hcols
  have hfac : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _)
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (elementSieveNorm_nonneg _ _) hfac) (by positivity)

theorem elementSieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    elementSieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ elementRange M, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact ((mem_elementRange M z).mp hz).2
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, cubicRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    change aext J.val * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM (elementRange M) hR
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [aext, dite_eq_left J.property]
    rfl
  simp_rw [hinner] at he
  rw [hea, ← Finset.sum_coe_sort] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0354

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ExtractionOptimization
Source SHA256: dfa2eba96b842eb6fae28dd9f16a37cfb1e879c0a2b888bf29c7f8705b209081
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0355


namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma cube_scale_power (M T a : ℝ) (hT : 0 < T) (hTM : T ≤ M) (ha : (1/3 : ℝ) ≤ a) :
    (M/T)^(1/3 : ℝ) * T^a ≤ M^a := by
  have hM : 0 < M := hT.trans_le hTM
  have hbase : 1 ≤ M/T := (one_le_div hT).mpr hTM
  calc
    _ ≤ (M/T)^a * T^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hbase ha) (Real.rpow_nonneg hT.le _)
    _ = M^a := by
      rw [Real.div_rpow hM.le hT.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT a).ne']

lemma extracted_monomial_le (W U T a : ℝ) (hW : 1 ≤ W) (hU : 0 ≤ U)
    (hWT : W^2*U ≤ T) (ha : (1/2 : ℝ) ≤ a) : W*U^a ≤ T^a := by
  have hW0 : 0 ≤ W := by linarith
  have hw : W ≤ (W^2)^a := by
    rw [← Real.rpow_natCast_mul hW0]
    conv_lhs => rw [← Real.rpow_one W]
    exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num; linarith)
  calc
    _ ≤ (W^2)^a * U^a := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hU _)
    _ = (W^2*U)^a := (Real.mul_rpow (sq_nonneg _) hU).symm
    _ ≤ T^a := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) hU) hWT (by linarith)

lemma extracted_linear_le (W T : ℝ) (hW : 0 ≤ W) (hWT : W^3 ≤ T) :
    W ≤ T^(1/3 : ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hW 3) hWT (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast_mul hW] at hh
  norm_num at hh
  exact hh

lemma extraction_selected_shape (M N W U T ξ : ℝ) (hN : 0 ≤ N)
    (hW : 1 ≤ W) (hU : 0 ≤ U) (hT : 0 < T) (hTM : T ≤ M)
    (hWT : W^2*U ≤ T) (hWcube : W^3 ≤ T) (hξ : 1 ≤ ξ) :
    (M/T)^(1/3 : ℝ) * W * (U^ξ + N + (U*N)^(2/3 : ℝ)) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hM0 : 0 < M := hT.trans_le hTM
  have hH : 0 ≤ (M/T)^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp : (M/T)^(1/3 : ℝ)*W*U^ξ ≤ M^ξ := by
    calc
      _ = (M/T)^(1/3 : ℝ)*(W*U^ξ) := by ring
      _ ≤ (M/T)^(1/3 : ℝ)*T^ξ := mul_le_mul_of_nonneg_left
        (extracted_monomial_le W U T ξ hW hU hWT (by linarith)) hH
