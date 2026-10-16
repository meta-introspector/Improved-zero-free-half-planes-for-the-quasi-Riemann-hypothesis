import core.OAI04
-- import Mathlib.Algebra.Group.Pi.Units
-- import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- import Mathlib.Analysis.Analytic.IsolatedZeros
-- import Mathlib.Analysis.Analytic.Order
-- import Mathlib.Analysis.Analytic.Uniqueness
-- import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- import Mathlib.Analysis.Complex.CauchyIntegral
-- import Mathlib.Analysis.Complex.Convex
-- import Mathlib.Analysis.Complex.HalfPlane
-- import Mathlib.Analysis.Complex.Liouville
-- import Mathlib.Analysis.Complex.RealDeriv
-- import Mathlib.Analysis.MellinInversion
-- import Mathlib.Analysis.MellinTransform
-- import Mathlib.Analysis.Normed.Group.FunctionSeries
-- import Mathlib.Analysis.Normed.Ring.Finite
-- import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
-- import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
-- import Mathlib.Analysis.SpecialFunctions.SmoothTransition
-- import Mathlib.Data.ZMod.Basic
-- import Mathlib.Logic.Equiv.Fin.Basic
-- import Mathlib.MeasureTheory.Function.Floor
-- import Mathlib.MeasureTheory.Integral.IntegralEqImproper
-- import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
-- import Mathlib.NumberTheory.AbelSummation
-- import Mathlib.NumberTheory.LSeries.AbstractFuncEq
-- import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
-- import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
-- import Mathlib.NumberTheory.MulChar.Lemmas
-- import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
-- import Mathlib.RingTheory.Ideal.Norm.AbsNorm
-- import Mathlib.RingTheory.Ideal.Quotient.Operations
-- import Mathlib.Tactic.FieldSimp
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Tactic.Ring

/-! Pinned OAI dependency closure, consolidated without changing public namespaces.
Original module boundaries and hashes are preserved below. -/

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredEnergyUniform
Source SHA256: e7c351ed9334b81fd01c1fe72cdbd6df185510d14f0a16440066cc602002c416
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0781







namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_moving_radius_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_retained_moving_radius_window_order_uniform_types  om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsub:source⊆originalSource:=InverseMomentGlobalRetainedGates.geometrySource_subset p originalSource b X
  have hsource:ActualSecondSourceConditions p source:=
    ActualSecondSourceConditions.mono p (unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff) hsub
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    fun x hx=>unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff x (hsub hx)
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x (hsub hx)
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  have hupper:∀y,principalWindow om lo hi hlo hsupport negative t y≠0 → y≤b:=by
    intro y hy
    have hy':y∈Function.support om:=by
      rw [←principalWindow_support om lo hi hlo hsupport negative t]
      exact hy
    exact (hsupport hy').2.trans hhib
  rw [InverseMomentGlobalRetainedGates.original_retained_geometry_sum p hp hcop hg extra pool originalSource
    (globalPriorityWeight p hg negative Ψ m ray core w assigned a) negative Ψ₀ m slots assigned lists a
    (principalWindow om lo hi hlo hsupport negative t) X Y b hX hupper z]
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0781

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredRays
Source SHA256: 8f386e8e46af56bf21bf8064c0477bf12b10fd1d98a7509af9b4aca3366ca764
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0782


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_filtered_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_moving_radius (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0782

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredAggregate
Source SHA256: c30f12bb7c6002a082ef231f971376c13229ac3abbf30fef25cf060060f78766
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0783




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_filtered_aggregate
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_all_rays (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=>cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1<Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤H at hb
  change P*((32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
  calc
    _=(32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤(32*512)*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
    _=(32*512)*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0783

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredRaysUniform
Source SHA256: 7d2819476f4319f4982fb24bdd3ecbb2b2125cdeb4b10b46172f065046a73dce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0784




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_all_rays_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_moving_radius_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0784

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredAggregateUniform
Source SHA256: bc3bf81f2f007e702f58598ef0a416cad253e76aebb86d385c5519386e9803a0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0785






namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_aggregate_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_all_rays_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=>cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1<Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤H at hb
  change P*((32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
  calc
    _=(32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤(32*512)*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
    _=(32*512)*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0785

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesRadius
Source SHA256: 82e8cccf173029cb97e7a40f506f99e275c1d9a7994d37669ee2f212d5e22be9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0786


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def supportedRetainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  geometrySource p (retainedSource p extra original negative J lists pool cutoff) b X

lemma supported_subset (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    supportedRetainedSource p extra original negative J lists pool cutoff b X⊆
      retainedSource p extra original negative J lists pool cutoff := geometrySource_subset p _ b X

lemma supported_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ActualSecondSourceConditions p (supportedRetainedSource p extra original negative J lists pool cutoff b X) :=
  ActualSecondSourceConditions.mono p (retained_conditions p hp extra original hvalid hextra negative J lists pool cutoff)
    (supported_subset p extra original negative J lists pool cutoff b X)

lemma supported_frequency_ne_zero
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,x.second.frequency≠0 := by
  intro x hx
  exact unified_frequency_ne_zero p pool _ (fun _=>cutoff) x
    (supported_subset p extra original negative J lists pool cutoff b X hx)

lemma supported_uniform_frequency_gate
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
        (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L Y (Z^tau)) := by
  intro x hx
  exact ((mem_unifiedSource p pool _ _ x).mp
    (supported_subset p extra original negative J lists pool _ b X hx)).2.2.2.2

theorem supported_cell_row_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z M r ell V delta A B j t eta tau L b X : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)) b X
    (∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta (index p x))) ∧
    (∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d) := by
  intro source
  have hgates := actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
    hZ heta hbin hL0 hL (supported_uniform_frequency_gate p extra original negative J lists pool Z delta eta L _ tau b X)
  refine ⟨?_,actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ hgates⟩
  intro x hx
  exact hgates (index p x) x (Finset.mem_filter.mpr ⟨hx,rfl⟩)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0786

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesCaps
Source SHA256: d2a608df23c7a1125582e5aed7638f7a17c49327da17753624433b42033a1f5f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0787


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma uniform_radius_cap (G E : Finset ι) (hEG : E⊆G)
    (Z delta eta L Y tau Lcol LY : ℝ) (hZ : 0<Z) (hL : 0≤L) (hY : 0<Y)
    (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY) :
    uniformSecondRadius p Z delta eta G E L Y (Z^tau)≤
      Z^(delta+eta+2*Lcol+tau+LY) := by
  have hr : primeProductNorm p E/primeProductNorm p G≤1 :=
    (div_le_one (primeProductNorm_pos p hp G)).mpr (primeProductNorm_mono p hp hEG)
  have hr0 : 0≤primeProductNorm p E/primeProductNorm p G := by
    exact div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hs : (primeProductNorm p E/primeProductNorm p G)^2≤1 := pow_le_one₀ hr0 hr
  unfold uniformSecondRadius
  rw [div_eq_mul_inv]
  calc
    _ ≤ Z^(delta+eta)*1*(Z^Lcol)^2*Z^tau*Z^LY := by gcongr
    _ = _ := by
      rw [mul_one,←Real.rpow_mul_natCast hZ.le]
      repeat rw [←Real.rpow_add hZ]
      congr 1
      norm_num
      ring

lemma bare_frequency_norm_le (a k : O) (ha : a≠0) :
    ‖eisEmbedding k‖^2≤‖eisEmbedding (a*k)‖^2 := by
  have hh := element_norm_ge_one a ha
  rw [map_mul,norm_mul,mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) hh

include hp in

theorem supported_outer_caps
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X Lcol LY Lcap : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hY : 0<Y) (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY)
    (hgeom : b*X≤Z^Lcap) (hphysical : delta+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      ∀i,outerNorms p x i≤Z^Lcap := by
  intro x hx i
  have hret := supported_subset p extra original negative J lists pool _ b X hx
  have hm := (mem_unifiedSource p pool _ _ x).mp hret
  have hg : primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤Z^Lcap :=
    (geometrySource_gate p _ b X x hx).trans hgeom
  have hG : primeProductNorm p x.second.sourceCommon≤Z^Lcap :=
    (le_mul_of_one_le_right (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  have hV : primeProductNorm p x.second.overlap≤Z^Lcap :=
    (le_mul_of_one_le_left (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  fin_cases i
  · exact hG
  · exact (primeProductNorm_mono p hp hm.2.2.1).trans hG
  · exact hV
  · have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hm.2.2.2.2
    exact (bare_frequency_norm_le _ _ (actualSecondMultiplier_ne_zero p x)).trans
      (hb.2.trans ((uniform_radius_cap p hp _ _ hm.2.2.1 Z delta eta L Y tau Lcol LY
        (zero_lt_one.trans_le hZ) hL hY hLc hYi).trans
        (Real.rpow_le_rpow_of_exponent_le hZ hphysical)))

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0787

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesChildren
Source SHA256: 801f5ca16b5df2b74162044c2d563829c79f66d1c3dcb30f4cd1851e62a40fd0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0788


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma supported_original_property
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ)
    (F : CubeCoordinates ι→Finset ι→Finset ι→Ideal O→Prop)
    (hF : ∀y∈original,F y.cube y.firstCommon y.firstDivisor (sourceIdeal p y.quotientSupport)) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,
      F x.cube x.firstCommon x.firstDivisor x.quotient := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x
    (supported_subset p extra original negative J lists pool cutoff b X hx)
  rw [hb,hc,hd,hq]
  exact hF y hy

theorem supported_label_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤Z^(B+eta))
    (hJ : ∀y∈original,‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2≤Z^(j+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    (∀d,∀x∈cell p source d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d) ∧
    (∀d,∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d)) := by
  intro source
  have hc := supported_original_property p extra original negative J lists pool cutoff b X
    (fun _ C _ _=>primeProductNorm p C≤Z^(B+eta)) hC
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2≤Z^(j+eta)) hJ
  exact ⟨fun d x hx=>actual_cell_labels_cover p source d x hx,
    fun d=>actual_cell_squarefree_labels p hp source
      (supported_frequency_ne_zero p extra original negative J lists pool cutoff b X) d Z B j eta hZ hbin hc hj⟩

theorem supported_child_margins (hp : ∀i,p i≠0)
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b : ℝ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀y∈original,primeProductNorm p y.quotientSupport≤Z^(t+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p source d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
        (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro source d γ hγ
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b (Z^(r-A-B-t))
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hq := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun _ _ _ I=>(Ideal.absNorm I:ℝ)≤Z^(t+eta)) (by
      intro y hy
      simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hT y hy)
  exact actual_cell_triple_margins p hp hpr source hs hk d m hm
    Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ hb₁ hb₂ hq γ hγ

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0788

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesBudget
Source SHA256: 9b8331d59ce77b6f345daaeb60746d6204ddcae0f5eeee40c9f9199f1aa85380
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0789



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseInitialArithmetic InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

 theorem source_cell_exponent_cap {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (Z Lcap : ℝ) (hZ : 1<Z)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (d : BlockIndex) (hd : d∈keys p source) (i : Fin 4) :
    secondCellExponent Z d i≤Lcap := by
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hs : scales d i≤outerNorms p x i := by
    simpa only [one_mul,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx i).1
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [second_cell_scale_rpow Z d i hZ]
  exact hs.trans (hnorm x (cell_subset p source d hx) i)

theorem source_cell_mass_gate {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0)
    (Z Lcap ell Ractive j t eta eps pi : ℝ) (hZ : 1<Z) (hj : 0≤j) (heps : 0≤eps)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (hbudget : eps*(ell+Ractive/2+t+Lcap+11*eta/2)≤pi) :
    ∀d∈keys p source,eps*(secondCount ell Ractive j t
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro d hd
  have hg := source_cell_exponent_cap p hp source hk Z Lcap hZ hnorm d hd 0
  have htheta := secondCellExponent_nonneg Z d 1 hZ
  apply le_trans (mul_le_mul_of_nonneg_left (show
    secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2≤
      ell+Ractive/2+t+Lcap+11*eta/2 by unfold secondCount; linarith) heps) hbudget

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0789

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesRank
Source SHA256: 6412c4e54a12cf1b55928e219b10412fb4de033138ed105fc5b58a5d44e9f631
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0790


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem supported_row_rank_decrease (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z M ell A t V j eta shortCutoff : ℝ)
    (hZ : 1<Z) (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : shortCutoff≤ell+V) (hsmall : eta≤shortCutoff/16)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : ∀y∈original,Z^(j-eta)≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    ∀d∈keys p source,actualCellRowExponent Z M ell A t V j eta d+3*shortCutoff/2≤M := by
  intro source d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hxs := cell_subset p source d hx
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b X
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b X
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>Z^(j-eta)≤‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2) hJ
  exact actual_cell_row_decrease p hp source hs hk d x hx Z M ell A t V j eta shortCutoff
    hZ hA ht heta hbin hterminal hsmall (hb₁ x hxs) (hb₂ x hxs) (hj x hxs)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0790

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityEnergy
Source SHA256: 974798fec22a52890e3e7005e858d913dd2103468b21a6856552c4a3b64167de
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0791



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem whole_priority_retained_fixed_ray
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (firstCommon firstDivisor:Finset ι)
    (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector:Finset ι→ℂ)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
    (_hcube:cube.Admissible) (_hcommon:Disjoint firstCommon cube.support)
    (_hdivisor:firstDivisor⊆firstCommon∪cube.support)
    (_hold:∀D∈pool.powerset,selector D≠0 → ∀i,(old i).val∣
      sourceIdeal p cube.support*sourceIdeal p firstCommon*sourceIdeal p D)
    (_hextra:extra cube⊆cube.support),
    let source:=unifiedSource p pool
      (activeParents p extra pool cube firstCommon firstDivisor old selector negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y R L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀D∈pool.powerset,‖selector D‖≤1) →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    actual_priority_retained_bound (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool cube firstCommon firstDivisor old selector
    Ψ m ray core slots assigned lists a cutoff hcube hcommon hdivisor hold hextra source Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    hselector haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsource:ActualSecondSourceConditions p source:=
    active_conditions p hp extra pool cube firstCommon firstDivisor old selector hcube hcommon hdivisor
      hold hextra negative assigned lists cutoff
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    active_deleted_support p hinj extra pool cube firstCommon firstDivisor old selector hcube hcommon
      hdivisor hold hextra negative assigned lists cutoff
  have hw:∀x∈source,‖normalizedWeight p hg cube negative Ψ m selector ray core assigned a x‖≤1:=
    fun x hx=>normalizedWeight_norm p hg hinj extra pool cube firstCommon firstDivisor old selector
      negative Ψ m ray core assigned lists a haassigned hselector (fun D hD hD0=>hΨ _) cutoff x hx
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedWeight p hg cube negative Ψ m selector ray core assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  rw [source_sum_normalized p hg cube negative Ψ m selector ray core assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedWeight p hg cube negative Ψ m selector ray core assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedWeight p hg cube negative Ψ m selector ray core assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0791

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityRays
Source SHA256: 5019441e1caaa25beeb5e23debc4e30f02a45cac90c0102602b89cfab0e0bb5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0792


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem whole_priority_retained_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (firstCommon firstDivisor:Finset ι)
    (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector:Finset ι→ℂ)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
    (_hcube:cube.Admissible) (_hcommon:Disjoint firstCommon cube.support)
    (_hdivisor:firstDivisor⊆firstCommon∪cube.support)
    (_hold:∀D∈pool.powerset,selector D≠0 → ∀i,(old i).val∣
      sourceIdeal p cube.support*sourceIdeal p firstCommon*sourceIdeal p D)
    (_hextra:extra cube⊆cube.support),
    let source:=unifiedSource p pool
      (activeParents p extra pool cube firstCommon firstDivisor old selector negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y R L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀D∈pool.powerset,‖selector D‖≤1) →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    whole_priority_retained_fixed_ray (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool cube firstCommon firstDivisor old selector
    Ψ m ray core slots assigned lists a cutoff hcube hcommon hdivisor hold hextra source Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    hselector haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈source,sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool cube firstCommon firstDivisor old selector
      Ψ m ray core slots assigned lists a cutoff hcube hcommon hdivisor hold hextra z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hselector haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0792

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityCollapse
Source SHA256: 6b1cac27c33fb7f61b239c8d08ff4daf3c49fa57181103d67798edc6be79decd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0793




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem whole_assigned_source_original
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    (∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y))=
    ∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      H (parent p (fixedPoint cube C E old D)) := by
  rw [activeParents,←wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj,
    sum_activeFixedSource]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector D≠0
  · rw [ite_eq_left hs]
    simp only [fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
  · rw [ite_eq_right hs,priorityOuter_zero p hg cube negative Ψ m selector ray core D (not_ne_iff.mp hs)]
    simp

theorem whole_assigned_source_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    ‖∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y)‖≤
    ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖H (parent p (fixedPoint cube C E old D))‖ := by
  rw [whole_assigned_source_original p hg hinj]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0793

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityBranches
Source SHA256: 36b2206f0cf6045a27ba3166ae432f2e760486d276d772b013f62c06cd5164b1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0794


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

theorem whole_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D)=
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D)))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))) := by
  intro V Ψ₀ parents source
  rw [whole_priority_complex_slice p hp hg hcop hinj hc hpr pool cube C E extra old negative Ψ m
    slots assigned lists a selector om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  rw [fullPhysical_unified p hg hp hcop hinj extra pool]
  dsimp only
  rw [←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    ←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem whole_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D‖≤
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖) := by
  intro V Ψ₀ parents source
  rw [whole_priority_signed_branches p hg hp hcop hinj hc hpr extra pool cube C E old selector negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Finset ι→ℂ):
      ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
        (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*H D‖≤
      ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
        ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*‖H D‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D hD
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0794

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityBranches
Source SHA256: a09be139c40765b235b6b63014e70059e968d19282ffc419698dc4a0b84b82ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0795



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x))=
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)) := by
  intro V Ψ₀ parents source
  rw [global_priority_physical_source p hp hcop hg hinj hc hpr extra pool original negative Ψ m ray core w
    slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem global_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖) := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0795

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityMass
Source SHA256: b509b4d845c9d48d05f17c80a094bc157abdc6d7034849457b786cf6b1f5e60e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0796



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseSecondPrincipalCaller InversePrincipalEnergy FirstCauchyArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_weighted_branch (ε:ℝ)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(original:Finset (Source ι Jo))(extra:CubeCoordinates ι→Finset ι)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(w:Source ι Jo→ℂ)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀x∈original,‖w x‖≤1)→0≤B→
      ∀U:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→Source ι Jo→ℝ,
      (∀r core J,J∈slots.powerset→∀x∈original,0≤U r core J x)→
      (∀r core J,J∈slots.powerset→∀x∈original,U r core J x≤B)→
      (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,‖globalPriorityOuter p hg negative Ψ m r core w x‖*
          ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*U r core J x≤
      Cb*(4:ℝ)^slots.card*B*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  let Cr:ℝ:=Fintype.card (RayCharacter×RayCharacter)
  let Cc:ℝ:=Fintype.card FirstCoreIndex
  refine ⟨(32*512)*Cr*Cc*coefficientBound*Cm^2,by
    have hr:0<Cr:=by dsimp [Cr];exact_mod_cast Fintype.card_pos
    have hc:0<Cc:=by dsimp [Cc];exact_mod_cast Fintype.card_pos
    have:=coefficientBound_pos;positivity,?_⟩
  intro ι σ _ _ p hp _ hg hcop Jo original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB U hU0 hU
  let N:=fun x:Source ι Jo=>(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε)
  have hn(x:Source ι Jo):0≤N x:=Real.rpow_nonneg (primeProductNorm_pos p hp _).le _
  have hm(J:Finset σ)(hJ:J∈slots.powerset)(x:Source ι Jo):
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤Cm^2*N x:=by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (wholeExtractedSupport (fun x=>extra x.cube) negative x)
    have he:((primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^ε)^2=N x:=by
      dsimp [N]
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have hw'(r:RayCharacter×RayCharacter)(core:FirstCoreIndex)(x:Source ι Jo)(hx:x∈original):
      ‖globalPriorityOuter p hg negative Ψ m r core w x‖≤coefficientBound:=by
    rw [globalPriorityOuter,norm_mul]
    have ht:=priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) r core x.quotientSupport (by simp) (hΨ _)
    exact (mul_le_mul (hw x hx) ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,coefficientBound*(Cm^2*N x)*B:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro core hc
      apply Finset.sum_le_sum
      intro J hJ
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul (mul_le_mul (hw' r core x hx) (hm J hJ x) (sq_nonneg _) coefficientBound_pos.le)
        (hU r core J hJ x hx) (hU0 r core J hJ x hx) (mul_nonneg coefficientBound_pos.le (mul_nonneg (sq_nonneg Cm) (hn x)))
    _= _:=by
      have hsum:(∑x∈original,coefficientBound*(Cm^2*N x)*B)=
          coefficientBound*Cm^2*B*∑x∈original,N x:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros;ring
      rw [hsum]
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [←he]
      dsimp only [Cr,Cc,N]
      ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0796

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityMass
Source SHA256: 356787fd31d84edc8c42c2f529f8110392fa0a4d190d5239ea294ae7e86a2b8c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0797


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O"=>ActualEisensteinCubic.O

theorem whole_priority_weighted_branch (ε:ℝ) (hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → 0≤B →
      ∀U:(RayCharacter×RayCharacter)→Finset ι→FirstCoreIndex→Finset σ→ℝ,
      (∀r D core J,J∈slots.powerset → 0≤U r D core J) →
      (∀r D core J,J∈slots.powerset → U r D core J≤B) →
      (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative Ψ m D core‖*
          ∑J∈slots.powerset,‖primeMark J lists a
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*U r D core J ≤
      Cb*(4:ℝ)^slots.card*B*
        (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  refine ⟨((32*512:ℝ)^2*512)*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hcop pool b C extra negative Ψ m slots lists a selector B hslots ha hΨ hB U hU0 hU
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hm (J:Finset σ) (hJ:J∈slots.powerset) (D:Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*(primeProductNorm p (A∪D))^(2*ε) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij) (fun i hi=>ha i (hj hi)) (A∪D)
    have he:((primeProductNorm p (A∪D))^ε)^2=(primeProductNorm p (A∪D))^(2*ε):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^ε)^2:=pow_le_pow_left₀ (norm_nonneg _) hh 2
      _= _:=by rw [mul_pow,he]
  have hn (D:Finset ι) : 0≤primeProductNorm p (A∪D):=(primeProductNorm_pos p hp _).le
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hU r D core J hJ) (hU0 r D core J hJ) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hB))
    _= ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*B*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*B*512*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= _ := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [A]
      ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0797

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityParentBounds
Source SHA256: 89c3d464167a7f20b23e886640888f1539860b432653992a49aa18accc871511
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0798


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_subset {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (lists:σ→Finset ι) (y:SecondParentSource ι Jo) (i:σ):
    residualLists p negative (fun i=>lists i\extra y.cube) y i⊆lists i:=
by
  intro k hk
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).1

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_pairwise {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (slots assigned:Finset σ) (lists:σ→Finset ι) (y:SecondParentSource ι Jo)
    (hslots:(slots:Set σ).PairwiseDisjoint lists):
    ((slots\assigned:Finset σ):Set σ).PairwiseDisjoint (residualLists p negative (fun i=>lists i\extra y.cube) y):=by
  intro i hi j hj hij
  exact (hslots (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij).mono
    (parent_residual_lists_subset p extra negative lists y i)
    (parent_residual_lists_subset p extra negative lists y j)

theorem priority_zero_parent_uniform (ε:ℝ) (hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Y → (∀G E,0≤R G E) →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      ‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
        Y*(X*Real.exp M)^(1+ε):=by
  obtain ⟨s,C,hC,hbound⟩:=marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y t R hX hhi hY hR Jo y
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  have hz:∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈secondVariableCutoff p y R G E:=by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _
      (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) _ (hR G E)
  have hb:=hbound p hp hg hinj hcop (slots\assigned)
    (residualLists p negative (fun i=>lists i\extra y.cube) y) a hpair hcoeff ∅ pool Ψ hΨ
    (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y)
    (principalWindow om lo hi hlo hs negative t) rowMajorant X M Y hX hY
    (principalWindow_upper om lo hi hlo hs M hhi negative t) (secondVariableCutoff p y R) hz
    (fun _ _ _=>0) (by intros; simp)
  have hb':‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
      (principalWindow om lo hi hlo hs negative t) X Y R y‖≤_:=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb
  simpa only [Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero,mul_assoc] using hb'

theorem priority_tail_parent_uniform (Lcap tau saving:ℝ)(hLcap:0≤Lcap)(htau:0<tau):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y Z t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      (∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p y) G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving):=by
  obtain ⟨s,C,hC,hbound⟩:=InverseWholePriorityRapidTail.marked_rapid_tail Lcap tau saving hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y Z t R hX hhi hZ hY hscale hy hyi hx Jo y hR
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  exact hbound p hp hcop hg hinj hc pool Ψ hΨ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (primeSubsetGenerator_ne_zero _ _)
    (slots\assigned) _ a hpair hcoeff om rowMajorant lo hi hlo hs negative t X M Y Z R
    hX hhi hZ hY hscale hy hyi hx hR

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0798

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailCollapse
Source SHA256: 6c3409b80e5fb8e354c1992290552395e6137283d7828f3798b1b97cd5a0d1d6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0799



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

lemma tail_forget (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ)
    (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R
      (forgetAppended (Jo:=Jo) y)=
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y := rfl

theorem original_paired_tail (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ) :
    (∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y*priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y)=
    ∑x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R (parent p x) := by
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj]
  simp only [tail_forget]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
end OAIOriginalModule0799

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTail
Source SHA256: 93a7dd4c3198789fbbcf03c2b6ea5adde906da8f69890d51a12fe7af8fdb3fcc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0800



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_parent_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)
      (w : Source ι Jo→ℂ)(slots J : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      J⊆slots → (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := priority_tail_parent_uniform Lcap tau (saving+13*Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  obtain ⟨Cs,hCs,hmass⟩ := original_tail_mass Jmax
  have hCb : 0<coefficientBound := coefficientBound_pos
  refine ⟨s,coefficientBound*Cm^2*Ct*Cs,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
    hJ hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  let V := principalWindow om lo hi hlo hs negative height
  let Q := (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  let T := Ct*Q*Z^(-(saving+13*Lcap))
  have hT : 0≤T := by dsimp [T,Q];positivity
  have hΨ₀ : ∀u,‖Ψ₀ u‖≤1 := fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u)
  have hout (x : Source ι Jo) (hx : x∈source) :
      ‖globalPriorityOuter p hg negative Ψ m ray core w x‖≤coefficientBound := by
    rw [globalPriorityOuter,norm_mul]
    exact (mul_le_mul (hw x hx)
      (priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport
        (by simp) (hΨ _)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hm (x : Source ι Jo) :
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤
        Cm^2*primeProductNorm p (principalSupport extra negative x) := by
    have hh := hmark p hp hcop J lists a
      (fun i hi j hj hij=>hslots (hJ hi) (hJ hj) hij) (fun i hi=>ha i (hJ hi))
      (principalSupport extra negative x)
    have he : ((primeProductNorm p (principalSupport extra negative x))^(1/2:ℝ))^2=
        primeProductNorm p (principalSupport extra negative x) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      norm_num
    have hsupp : wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x := by
      simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
    rw [hsupp]
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have ht (x : Source ι Jo) (hx : x∈source) :
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖≤T := by
    simpa only [T,Q,mul_assoc] using htail p hp hg hinj hcop hc extra pool negative Ψ₀ m slots J lists a
      hslots ha hΨ₀ om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
      (parent p x) (hR x hx)
  have hmass₀ := hmass p hp hinj Jo hJo source Z Lcap hZ hLcap hsource hb₁ hb₂ hactive hcommon hquot extra negative hextra
  rw [original_paired_tail p hg hp hinj]
  calc
    _ ≤ ∑x∈source,‖globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖ := norm_sum_le _ _
    _ ≤ ∑x∈source,coefficientBound*(Cm^2*primeProductNorm p (principalSupport extra negative x))*T := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (mul_le_mul (hout x hx) (hm x) (sq_nonneg _) coefficientBound_pos.le)
        (ht x hx) (norm_nonneg _)
        (mul_nonneg hCb.le (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp _).le))
    _ = coefficientBound*Cm^2*T*(∑x∈source,primeProductNorm p (principalSupport extra negative x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ coefficientBound*Cm^2*T*(Cs*Z^(13*Lcap)) :=
      mul_le_mul_of_nonneg_left hmass₀ (by positivity)
    _ = _ := by
      have he : Z^(-(saving+13*Lcap))*Z^(13*Lcap)=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp only [T,Q]
      calc
        _ = coefficientBound*Cm^2*Ct*Cs*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^(-(saving+13*Lcap))*Z^(13*Lcap)) := by ring
        _ = _ := by rw [he]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
end OAIOriginalModule0800

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailAggregate
Source SHA256: eae2b18515136aff68911dd7781812b5b550660098b3335090c1e2a002f9b3ff
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0801


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_parent_tail_aggregate_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_rapid Jmax Lcap tau saving hLcap htau
  let N : ℝ := (Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)
  have hN : 0<N := by dsimp [N];positivity
  refine ⟨s,(32*512)*N*C,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  let B := C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hsum : (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)
      ≤N*(2:ℝ)^slots.card*B := by
    calc
      _ ≤ ∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_J∈slots.powerset,B := by
        apply Finset.sum_le_sum
        intro ray hr
        apply Finset.sum_le_sum
        intro core hc₀
        apply Finset.sum_le_sum
        intro J hJ
        exact hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
          (Finset.mem_powerset.mp hJ) hslots ha hΨ hw om lo hi hlo hs X M Y Z height R
          hX hhi hZ hY hscale hy hyi hXcap hsource hextra hb₁ hb₂ hactive hcommon hquot hR
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        dsimp [N]
        ring
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤(32*512)*(2:ℝ)^slots.card)).trans_eq
  have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by
    rw [←pow_mul,pow_mul']
    norm_num
  dsimp [B]
  calc
    _ = (32*512)*N*C*((2:ℝ)^slots.card)^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by ring
    _ = _ := by rw [he]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
end OAIOriginalModule0801

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailPhysical
Source SHA256: 503672b90464c775e23b4fe655bf92a267d97a6f9b1aea89c730d1ad96e6ee57
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0802


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_physical_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height kappa eta : ℝ)(R : Finset ι→Finset ι→ℝ),
      kappa+(9/2:ℝ)*eta≤Lcap →
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*((32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖))≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_aggregate_rapid Jmax Lcap tau (saving+Lcap) hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height kappa eta R hkappa hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have he : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^(kappa+(9/2:ℝ)*eta) := by
    rw [Real.rpow_add hz,Real.rpow_def_of_pos hz ((9/2:ℝ)*eta)]
    congr 2
    ring
  have hP : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))≤Z^Lcap := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ hkappa
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  calc
    _ ≤ Z^Lcap*(C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-(saving+Lcap))) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    _ = _ := by
      have he₂ : Z^Lcap*Z^(-(saving+Lcap))=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^Lcap*Z^(-(saving+Lcap))) := by ring
        _ = _ := by rw [he₂]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
end OAIOriginalModule0802

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityZero
Source SHA256: bd51829d4914f99a84a5e41234c342187d5d9da840ccfd1672ac0c7f0f654964
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0803



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
def globalPriorityZeroAggregate
    (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a V X Y R (parent p x)‖

theorem global_priority_zero_aggregate (ε:ℝ)(hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X→hi≤Real.exp M→1≤Y→(∀G E,0≤R G E)→
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative t) X Y R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Y*(X*Real.exp M)^(1+ε)*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=priority_zero_parent_uniform ε hε
  obtain ⟨Cb,hCb,hmass⟩:=global_priority_weighted_branch ε hε
  refine ⟨s,Cb*Cp,mul_pos hCb hCp,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y t R hX hhi hY hR
  let B:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
    Y*(X*Real.exp M)^(1+ε)
  have hB:0≤B:=by dsimp [B];positivity
  have hh:=hmass p hp hg hcop original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB
    (fun ray core J x=>‖priorityZeroParent p hg extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y R (parent p x)‖)
    (by intros;positivity)
    (fun ray core J hJ x hx=>hprincipal p hp hg hinj hcop extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a hslots ha
      (fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u))
      om lo hi hlo hs X M Y t R hX hhi hY hR (parent p x))
  convert hh using 1 <;> dsimp only [globalPriorityZeroAggregate,B] ; ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0803

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityZeroPhysical
Source SHA256: b9775c4627837080fde2500c2c00eeb28333e8613654eae5696458ad085af56d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0804


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_zero_physical (ε:ℝ)(hε:0<ε)(Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (Jo:ℕ),Jo≤Jmax→∀(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
      (original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)(negative:Bool)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (Z M r ell V delta A B Ractive j t eta tau window pi height:ℝ)(R:Finset ι→Finset ι→ℝ),
      1≤Z→0≤ell+eta→0≤B→0≤j→
      ε*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*ε*(2*ell+B+t+4*eta)≤pi+eta/2→
      (∀x∈original,SourceValid p x)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(B+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(t+eta))→
      (∀x∈original,extra x.cube⊆x.cube.support)→
      hi≤Real.exp window→1≤Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)→(∀G E,0≤R G E)→
      (Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative height) (Z^(r-A-B-t))
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+ε))*
        Z^(r+3*ell+V+17*eta+tau+pi):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=global_priority_zero_aggregate ε hε
  obtain ⟨Cm,hCm,hmass⟩:=original_physical_weighted_source Jmax dsmall hdsmall
  refine ⟨s,Cp*Cm,mul_pos hCp hCm,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs Z M r ell V delta A B Ractive j t eta tau window pi height R
    hZ hell hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot hextra hhi hY hR
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let P:=Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let Q:=Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2
  have hP:0≤P:=by dsimp [P];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have he:=mul_le_mul_of_nonneg_left (hprincipal p hp hg hinj hcop extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs (Z^(r-A-B-t)) window
    (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) height R (by positivity) hhi hY hR) hP
  have hm:=hmass p hp hinj Jo hJo original Z M r ell V delta A B Ractive j t eta tau ε window pi
    hZ hell hε.le hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot extra negative hextra
  have hsupp(x:Source ι Jo):wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x:=by
    simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
  simp_rw [hsupp] at he
  apply he.trans
  calc
    _=Q*(physicalPrincipalFactor Z M r ell V delta A B Ractive j t eta tau ε window*
      ∑x∈original,(primeProductNorm p (principalSupport extra negative x))^(2*ε)):=by
      dsimp [Q,P,physicalPrincipalFactor];ring
    _≤Q*(Cm*Real.exp (window*(1+ε))*Z^(r+3*ell+V+17*eta+tau+pi)):=mul_le_mul_of_nonneg_left hm hQ
    _= _:=by dsimp [Q];ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0804

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullBranches
Source SHA256: fe0d3af2cfaa7db311f942d12dcdddca0971b1bd27e2eb7cff9964a8080ef331
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0805




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_slice_full_tail
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖ := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (le_refl _))

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0805

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullAggregate
Source SHA256: 10b14980260cf99bdcb7de59f18fae315c2fbcac85630526182dcad175d3cee6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0806


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InverseMomentGlobalPriorityTail
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
def globalPriorityOriginalEnergy (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x)).re

def globalPriorityTailAggregate (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) original negative J lists,
      coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
      priorityTailParent p hg hp hinj extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
        m slots J lists a V X Y R y‖

theorem global_priority_three_branches
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t;
    globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y≤
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityRetainedAggregate p hg hp hcop extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityTailAggregate p hg hp hinj extra pool original w negative Ψ m slots lists a V X Y R:=by
  dsimp only
  unfold globalPriorityOriginalEnergy globalPriorityZeroAggregate globalPriorityRetainedAggregate globalPriorityTailAggregate
  rw [←mul_add,←mul_add]
  simp only [←Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro core hcore
  apply Finset.sum_le_sum
  intro J hJ
  have hb:=global_priority_slice_full_tail p hg hp hcop hinj hc hpr extra pool original w negative Ψ m
    ray core slots J lists a om lo hi hlo hs X t Y hX hY R
  dsimp only at hb
  rw [original_paired_tail p hg hp hinj]
  exact (Complex.re_le_norm _).trans hb
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0806

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredStep
Source SHA256: b948b583fa24a0ffced088bffb1b6a4f1b3d477f4d00e353999c9f652c241f0a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0807



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_filtered_physical_step
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_aggregate (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have hz:0<Z:=zero_lt_one.trans hZ
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have hzbound : _ ≤ Cz'*Z^(r+3*ell+V+17*eta+tau+pi):=hzn.trans (by dsimp [Cz'];gcongr)
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add hzbound hrbound) htbound)
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0807

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredStepUniform
Source SHA256: 1101460cf950ebc0db8de0e275e62524c2d604f6d5baa8a29068dda9470c5bbf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0808





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_physical_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_aggregate_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have hz:0<Z:=zero_lt_one.trans hZ
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have hzbound : _ ≤ Cz'*Z^(r+3*ell+V+17*eta+tau+pi):=hzn.trans (by dsimp [Cz'];gcongr)
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add hzbound hrbound) htbound)
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0808

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.FirstGlobalParents
Source SHA256: 334bd4adada7a8ca5aa6413398718862c0f6f726c48fbc53bd731626570e4881
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0809



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def ofOriginal (k : FirstOriginalOuter ι) : Source ι 0 where
  cube := k.1
  firstCommon := k.2.1
  firstDivisor := k.2.2
  quotientSupport := ∅
  oldAssigned := Fin.elim0

def toOriginal (x : Source ι 0) : FirstOriginalOuter ι :=
  ⟨x.cube,⟨x.firstCommon,x.firstDivisor⟩⟩

omit [DecidableEq ι] in
@[simp] theorem toOriginal_ofOriginal (k : FirstOriginalOuter ι) :
    toOriginal (ofOriginal k)=k := by cases k with | mk b k => cases k; rfl

omit [DecidableEq ι] in
@[simp] theorem toOriginal_fill (x : Source ι 0) (D : Finset ι) :
    toOriginal (fillFirstQuotient x D)=toOriginal x := rfl

omit [DecidableEq ι] in
theorem ofOriginal_injective : Function.Injective (ofOriginal (ι:=ι)) :=
  Function.LeftInverse.injective toOriginal_ofOriginal

omit [DecidableEq ι] in
theorem ofOriginal_toOriginal (x : Source ι 0) :
    ofOriginal (toOriginal x)=eraseFirstQuotient x := by
  apply Source.ext <;> try rfl
  exact funext (fun i=>Fin.elim0 i)

omit [DecidableEq ι] in

theorem fill_ofOriginal_injective : Function.Injective
    (fun q : FirstOriginalOuter ι × Finset ι=>fillFirstQuotient (ofOriginal q.1) q.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [toOriginal_fill,toOriginal_ofOriginal] using congrArg toOriginal h
  · exact congrArg Source.quotientSupport h

def originalOuterSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (Source ι 0) :=
  (firstOriginalOuter pool Q).image ofOriginal

theorem originalOuterSource_empty (pool : Finset ι) (Q : Finset (ι→₀ℕ)) :
    ∀x∈originalOuterSource pool Q,x.quotientSupport=∅ := by
  intro x hx
  obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
  rfl

theorem sum_originalOuterSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (H : Source ι 0→A) :
    (∑x∈originalOuterSource pool Q,H x)=∑k∈firstOriginalOuter pool Q,H (ofOriginal k) := by
  exact Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)

def originalSelector (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (x : Source ι 0) (D : Finset ι) : ℂ := selector (toOriginal x) D

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) (D : Finset ι) :
    originalSelector selector (ofOriginal k) D=selector k D := by
  simp only [originalSelector,toOriginal_ofOriginal]

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal_fun (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) : originalSelector selector (ofOriginal k)=selector k :=
  funext (originalSelector_ofOriginal selector k)

def originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) : Finset (Source ι 0) :=
  globalParentSource (originalOuterSource pool Q) pool (originalSelector selector)

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i

theorem originalParentSource_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,SourceValid p x := by
  intro x hx
  obtain ⟨k,hk,D,hD,hs,rfl⟩:=(mem_originalParentSource pool Q selector x).mp hx
  exact original_fill_valid p pool Q k hk D

theorem sum_originalParentSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→A) :
    (∑x∈originalParentSource pool Q selector,H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset.filter (fun D=>selector k D≠0),
        H (fillFirstQuotient (ofOriginal k) D) := by
  rw [originalParentSource,sum_globalParentSource _ _ _ (originalOuterSource_empty pool Q),
    sum_originalOuterSource]
  simp only [originalSelector_ofOriginal]

theorem signed_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,selector (toOriginal x) x.quotientSupport*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        selector k D*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem real_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℝ) :
    (∑x∈originalParentSource pool Q selector,‖selector (toOriginal x) x.quotientSupport‖*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        ‖selector k D‖*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem original_supports (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (k : FirstOriginalOuter ι)
    (hk : k∈firstOriginalOuter pool Q) :
    k.1.leftExponent∈Q ∧ k.1.rightExponent∈Q ∧
      k.1.support⊆pool ∧ k.2.1⊆pool ∧ k.2.2⊆pool := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  have hb' := (mem_reopenedCubeFamily Q k.1).mp hb
  have hs := reopenedCubeFamily_support pool Q hQ k.1 hb
  have hc : k.2.1⊆pool := (Finset.mem_powerset.mp hC).trans Finset.sdiff_subset
  refine ⟨hb'.1,hb'.2.1,hs,hc,?_⟩
  exact (Finset.mem_powerset.mp hE).trans (Finset.union_subset hc
    ((Finset.filter_subset _ _).trans hs))

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem original_principal_extra (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,
      cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit ⊆ x.cube.support := by
  intro x hx
  exact Finset.filter_subset _ _

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem original_parent_data (k : FirstOriginalOuter ι) (D : Finset ι) :
    (parent p (fillFirstQuotient (ofOriginal k) D)).cube=k.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstCommon=k.2.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstDivisor=k.2.2 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).quotient=sourceIdeal p D :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem original_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈assignedParents p (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (assignedParents p (originalParentSource pool Q selector) negative J lists) expansion) :=
  assigned_family_conditions p hp _ (originalParentSource_valid p pool Q selector)
    negative J lists expansion hE

theorem original_whole_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈wholeAssignedParents p
      (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit)
      (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (wholeAssignedParents p
        (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)
        (originalParentSource pool Q selector) negative J lists) expansion) :=
  whole_assigned_family_conditions p hp _ _ (originalParentSource_valid p pool Q selector)
    (original_principal_extra pool Q selector) negative J lists expansion hE

variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_priority_slice
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (ray : RayCharacter×RayCharacter)
    (core : FirstCoreIndex) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
      (priorityOuter p hg k.1 negative Ψ m (selector k) ray core D:ℂ)*
        H (fillFirstQuotient (ofOriginal k) D) := by
  have h:=global_original_priority_slice p hg (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) negative Ψ m ray core H
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

theorem original_second_energy_source
    (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (extra : CubeCoordinates ι→Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (om : ℝ→ℂ) (X t Y : ℝ) :
    (∑k∈firstOriginalOuter pool Q,
      firstWholePrioritySecondEnergy p hp hg hinj pool k.1 k.2.1 (extra k.1)
        negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
        slots lists a (selector k) om X t Y)=
    (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,
      ∑J∈slots.powerset,(∑x∈originalParentSource pool Q selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re := by
  have h:=global_second_energy_source p hg hp hinj (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) extra negative Ψ m
    slots lists a om X t Y
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

end SevenEighths.InverseFirstGlobalParents

end

end OAI
end OAIOriginalModule0809

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalCanonicalEnergy
Source SHA256: 9f1acef0dc3b7a6796e07fe1471c8af755782e264e79f2d8e7bf8bfba8c28a02
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0810




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_canonical_to_original_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑x∈outer,firstCanonicalSecondEnergy p hp hg hinj pool x.cube x.firstCommon
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      (fun U=>primeMark slots lists a (extra x.cube∪U)) (selector x) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool (globalParentSource outer pool selector)
      (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun x hx=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool x.cube x.firstCommon (extra x.cube)
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      slots lists a (selector x) om X t Y hY))
  exact le_of_eq (global_second_energy_source p hg hp hinj outer pool selector houter extra
    negative Ψ m slots lists a om X t Y)

theorem original_canonical_to_global_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈firstOriginalOuter pool Q,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalParents.originalParentSource pool Q selector)
      (fun x=>(‖selector (InverseFirstGlobalParents.toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun k hk=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool k.1 k.2.1 (extra k.1)
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      slots lists a (selector k) om X t Y hY))
  exact le_of_eq (InverseFirstGlobalParents.original_second_energy_source p hg hp hinj pool Q
    selector extra negative Ψ m slots lists a om X t Y)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0810

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps
Source SHA256: bc0154ed657cb8c68e1d91b17f3f1182180015cba16bec5f2d94f858698ca6f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0811




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def outerNorms (p : ι→O) (x : FirstOriginalOuter ι) : Fin 5→ℝ :=
  ![‖eisEmbedding (aLabel p x.1.support x.1.rightBit)‖^2,
    ‖eisEmbedding (aLabel p x.1.support x.1.leftBit)‖^2,
    primeProductNorm p x.2.1,
    ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2,
    primeProductNorm p (cubeActiveSupport x.1.support
      (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)]

def outerGate (p : ι→O) (k : SourceIndex) (x : FirstOriginalOuter ι) : Prop :=
  ∀i : Fin 5,dyadIndex (outerNorms p x i)=k i.castSucc

def outerCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :=
  (firstOriginalOuter pool Q).filter (outerGate p k)

def parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) :=
  (originalParentSource pool Q (fun x=>commonSelector p (selector x) l)).filter
    (fun x=>outerGate p k (toOriginal x))

theorem mem_parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (x : Source ι 0) : x∈parentCell p pool Q selector k l ↔
    ∃o∈outerCell p pool Q k,∃D∈pool.powerset,
      commonSelector p (selector o) l D≠0 ∧ fillFirstQuotient (ofOriginal o) D=x := by
  simp only [parentCell,outerCell,Finset.mem_filter,mem_originalParentSource]
  constructor
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hg⟩
    exact ⟨o,⟨ho,by simpa using hg⟩,D,hD,hs,rfl⟩
  · rintro ⟨o,⟨ho,hg⟩,D,hD,hs,rfl⟩
    exact ⟨⟨o,ho,D,hD,hs,rfl⟩,by simpa using hg⟩

def originalNorms (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) : Fin 6→ℝ :=
  sourceNorms (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2)
    (fun y=>y.2.2) x

lemma originalNorms_outer (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (i : Fin 5) : originalNorms p x i.castSucc=outerNorms p x.1 i := by
  fin_cases i <;> rfl

lemma originalNorms_frequency (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) :
    originalNorms p x 5=‖eisEmbedding x.2.2‖^2 := rfl

theorem sourceCell_outer (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    x.1∈outerCell p pool Q k := by
  obtain ⟨hs,hk⟩:=Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp hs).1,?_⟩
  intro i
  simpa only [sourceIndex,originalNorms_outer] using congrFun hk i.castSucc

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerNorms_ge_one (x : FirstOriginalOuter ι) : ∀i,1≤outerNorms p x i := by
  intro i
  fin_cases i
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · change 1≤‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) :
    ∀i,1≤originalNorms p x i := by
  have hf:=((mem_firstRetainedSource p labels x.1.1 Y x.2).mp (Finset.mem_sigma.mp hx).2).2
  have hn : x.2.2≠0 := (Finset.mem_erase.mp hf).1
  intro i
  fin_cases i
  · exact outerNorms_ge_one p hp x.1 0
  · exact outerNorms_ge_one p hp x.1 1
  · exact outerNorms_ge_one p hp x.1 2
  · exact outerNorms_ge_one p hp x.1 3
  · exact outerNorms_ge_one p hp x.1 4
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceCell_frequency (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    dyadScale (k 5)≤‖eisEmbedding x.2.2‖^2 ∧
      ‖eisEmbedding x.2.2‖^2≤2*dyadScale (k 5) := by
  have h:=sourceCell_ratios (originalNorms p) _ (source_norms_ge_one p hp pool Q labels Y) k x hx 5
  exact ⟨by simpa only [originalNorms_frequency,one_mul] using (le_div_iff₀ (dyadScale_pos _)).mp h.1,
    by simpa only [originalNorms_frequency] using (div_le_iff₀ (dyadScale_pos _)).mp h.2⟩

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerGate_dyads (k : SourceIndex) (x : FirstOriginalOuter ι) (hx : outerGate p k x) :
    ∀i : Fin 5,dyadScale (k i.castSucc)≤outerNorms p x i ∧
      outerNorms p x i≤2*dyadScale (k i.castSucc) := by
  intro i
  have h:=dyadIndex_bounds _ (outerNorms_ge_one p hp x i)
  rw [hx i] at h
  exact ⟨h.1,h.2.le⟩

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma commonSelector_norm (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤‖selector D‖ := by
  unfold commonSelector
  split_ifs <;> simp

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_common_dyads (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι)
    (hlive : commonSelector p selector l D≠0) :
    dyadScale l≤primeProductNorm p D ∧ primeProductNorm p D≤2*dyadScale l := by
  have he : dyadIndex (primeProductNorm p D)=l := by
    by_contra h
    exact hlive (by simp [commonSelector,h])
  have h:=dyadIndex_bounds _ (primeProductNorm_ge_one p hp D)
  rw [he] at h
  exact ⟨h.1,h.2.le⟩

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
lemma sourceIdeal_norm (D : Finset ι) : (Ideal.absNorm (sourceIdeal p D):ℝ)=primeProductNorm p D := by
  simp only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm]

omit [∀i,(Ideal.span {p i}).IsMaximal] in

theorem parentCell_cube_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z ell eta : ℝ)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  exact reopenedCubeFamily_cube_norms p Q _ hQ o.1
    ((mem_firstOriginalOuter pool Q o).mp (Finset.mem_filter.mp ho).1).1

def dyadicExponent (Z : ℝ) (n : ℕ) : ℝ := Real.logb Z (dyadScale n)

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta) (n : ℕ)
    (hq : dyadScale n≤q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤q ∧ q≤Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_norm_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (∀i : Fin 5,Z^dyadicExponent Z (k i.castSucc)≤outerNorms p (toOriginal x) i ∧
      outerNorms p (toOriginal x) i≤Z^(dyadicExponent Z (k i.castSucc)+eta)) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)=primeProductNorm p x.quotientSupport ∧
    Z^dyadicExponent Z l≤(Ideal.absNorm (parent p x).quotient:ℝ) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)≤Z^(dyadicExponent Z l+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  have hg := outerGate_dyads p hp k o (Finset.mem_filter.mp ho).2
  have hd := live_common_dyads p hp (selector o) l D hs
  simp only [toOriginal_fill,toOriginal_ofOriginal]
  refine ⟨fun i=>dyad_power_bounds Z eta _ hZ h2 _ (hg i),sourceIdeal_norm p D,?_⟩
  change Z^dyadicExponent Z l≤(Ideal.absNorm (sourceIdeal p D):ℝ) ∧
    (Ideal.absNorm (sourceIdeal p D):ℝ)≤Z^(dyadicExponent Z l+eta)
  rw [sourceIdeal_norm]
  exact dyad_power_bounds Z eta _ hZ h2 l hd

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_ideal_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (Z^dyadicExponent Z (k 2)≤primeProductNorm p x.firstCommon ∧
      primeProductNorm p x.firstCommon≤Z^(dyadicExponent Z (k 2)+eta)) ∧
    (Z^dyadicExponent Z (k 3)≤(Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ)≤Z^(dyadicExponent Z (k 3)+eta)) ∧
    (Z^dyadicExponent Z (k 4)≤(Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ)
        ≤Z^(dyadicExponent Z (k 4)+eta)) := by
  have h:=(parentCell_norm_bounds p hp pool Q selector k l Z eta hZ h2 x hx).1
  refine ⟨h 2,?_,?_⟩
  · simpa [sourceIdeal_norm,outerNorms,toOriginal,primeSubsetGenerator_norm_eq_productNorm] using h 3
  · simpa [sourceIdeal_norm,outerNorms,toOriginal] using h 4

def jNorm (p : ι→O) (x : FirstOriginalOuter ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.1.support (fun i=>x.1.leftExponent i+x.1.rightExponent i)
    x.1.leftBit x.1.rightBit)‖^2

def labelParentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :=
  (parentCell p pool Q selector k l).filter (fun x=>dyadIndex (jNorm p (toOriginal x))=j)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem labelParentCell_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈labelParentCell p pool Q selector k l j) :
    x∈parentCell p pool Q selector k l ∧
    Z^dyadicExponent Z j≤jNorm p (toOriginal x) ∧
      jNorm p (toOriginal x)≤Z^(dyadicExponent Z j+eta) := by
  obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hx
  have hn : 1≤jNorm p (toOriginal x) :=
    EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  have hd:=dyadIndex_bounds _ hn
  rw [hj] at hd
  exact ⟨hm,dyad_power_bounds Z eta _ hZ h2 j ⟨hd.1,hd.2.le⟩⟩

theorem raw_column_exponent (Z r : ℝ) (hZ : 1<Z) (a b c : ℕ) :
    Z^r/(dyadScale a*dyadScale b*dyadScale c)=
      Z^(r-dyadicExponent Z a-dyadicExponent Z b-dyadicExponent Z c) := by
  simp only [Real.rpow_sub (show 0<Z by linarith),rpow_dyadicExponent Z hZ]
  simp only [div_div]

theorem columnScales_exponents (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    columnScales k l (Z^r) (Z^r)=rawScales k l
      (Z^(r-dyadicExponent Z (k 0)-dyadicExponent Z (k 2)-dyadicExponent Z l))
      (Z^(r-dyadicExponent Z (k 1)-dyadicExponent Z (k 2)-dyadicExponent Z l)) := by
  simp only [columnScales,raw_column_exponent Z r hZ]

theorem columnScales_products (Z r : ℝ) (k : SourceIndex) (l : ℕ) :
    let s:=columnScales k l (Z^r) (Z^r)
    s 0*s 2*s 5*s 7=Z^r ∧ s 1*s 2*s 5*s 8=Z^r :=
  ⟨columnScales_left k l _ _,columnScales_right k l _ _⟩

theorem sourceCell_parent (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (l : ℕ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (D : Finset ι) (hD : D⊆pool) (hs : commonSelector p (selector x.1) l D≠0) :
    fillFirstQuotient (ofOriginal x.1) D∈parentCell p pool Q selector k l :=
  (mem_parentCell p pool Q selector k l _).mpr
    ⟨x.1,sourceCell_outer p pool Q labels Y k x hx,D,Finset.mem_powerset.mpr hD,hs,rfl⟩

theorem outerCell_eq_of_first_five (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k k' : SourceIndex) (h : ∀i : Fin 5,k i.castSucc=k' i.castSucc) :
    outerCell p pool Q k=outerCell p pool Q k' := by
  ext x
  simp only [outerCell, Finset.mem_filter, outerGate, h]

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_selector_norm_le_one (selector : Finset ι→ℂ)
    (hs : ∀D,‖selector D‖≤1) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤1 := (commonSelector_norm p selector l D).trans (hs D)

include hp in

theorem sourceCell_actual_ratios
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
    (selector C₁ C₂ : (Σ _ : FirstOriginalOuter ι,Ideal O×O)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j≠0) :
    ∀i,actualOuterRatios p (outerNorms p x.1 0) (outerNorms p x.1 1)
      (outerNorms p x.1 2) (outerNorms p x.1 4)
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  exact actual_original_cell_ratios p hp hg _ selector C₁ C₂
    (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2) (fun y=>y.2.2)
    (source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end SevenEighths.InverseFirstGlobalCaps

end

end OAI
end OAIOriginalModule0811

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveNorms
Source SHA256: babe58122fac6955b7a92b445c7c3feb4e481cff33a6583d5e3aeb3c4797d2a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0812



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_norm_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L B:ℝ)
    (hB:0≤B)(hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels:∀I∈labels,I≠0)(hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    (∀i:Fin 6,originalNorms p x i≤(![L,L,L,L*B^2,B^2,Y]:Fin 6→ℝ) i) ∧
      primeProductNorm p j.2.1≤L ∧ InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
  obtain ⟨ha₁,ha₂,hcommon,hquot⟩:=original_live_profile_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K L hW x hx j hn
  obtain ⟨ho,hfreq⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hb,hC,hD⟩:=(mem_firstOriginalOuter pool Q x.1).mp ho
  obtain ⟨hf,hrow⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hfreq
  have hcube:=reopenedCubeFamily_cube_norms p Q B hQ x.1.1 hb
  have hsup:=cube_whole_support_dyad p hp x.1.1 B hB hcube.1 hcube.2
  have hdiv:primeProductNorm p x.1.2.2≤L*B^2:=by
    calc
      _≤primeProductNorm p (x.1.2.1∪cubePrincipalSupport x.1.1.support x.1.1.leftExponent
          x.1.1.rightExponent x.1.1.leftBit x.1.1.rightBit):=
        primeProductNorm_mono p hp (Finset.mem_powerset.mp hD)
      _≤primeProductNorm p x.1.2.1*primeProductNorm p x.1.1.support:=by
        apply (primeProductNorm_union_le_mul p hp _ _).trans
        exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _))
          (primeProductNorm_pos p hp _).le
      _≤L*B^2:=mul_le_mul hcommon hsup (primeProductNorm_pos p hp _).le
        ((primeProductNorm_pos p hp _).le.trans hcommon)
  have hactive:activeNorm p x≤B^2:=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hsup
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hf)
  have hh0:x.2.2≠0:=(Finset.mem_erase.mp hrow).1
  have hh:=((mem_nonzeroChildFrequencyBall _ hE Y x.2.2).mp hrow).2
  have hfreqnorm:‖eisEmbedding x.2.2‖^2≤Y:=
    (element_norm_le_of_dvd (mul_ne_zero hE hh0) (dvd_mul_left x.2.2 _)).trans hh
  have hj:InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
    have hd:=jLabel_dvd_cube_product p x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
      x.1.1.leftBit x.1.1.rightBit x.1.1.support_pos
    have hnorm:=element_norm_le_of_dvd
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _)) hd
    simp only [map_mul,norm_mul,mul_pow] at hnorm
    exact hnorm.trans ((mul_le_mul hcube.1 hcube.2 (sq_nonneg _) hB).trans_eq (pow_two B).symm)
  refine ⟨?_,hquot,hj⟩
  intro i
  fin_cases i
  · exact ha₁
  · exact ha₂
  · exact hcommon
  · simpa [originalNorms,InverseMomentFirstChildWindows.sourceNorms,divisorElement,
      primeSubsetGenerator_norm_eq_productNorm] using hdiv
  · exact hactive
  · exact hfreqnorm

end SevenEighths.InverseMomentFirstLiveCaps

end

end OAI
end OAIOriginalModule0812

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicRadius
Source SHA256: 0247359a5e9876372c28df3c0be88908d89e816cf758e91f6597440397a14cc7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0813




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]

def firstDyadicExponent (Z x:ℝ):ℝ:=dyadicExponent Z (dyadIndex x)

theorem first_dyadic_bounds (Z eta x:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x):
    0≤firstDyadicExponent Z x ∧ Z^firstDyadicExponent Z x≤x ∧ x≤Z^(firstDyadicExponent Z x+eta):=by
  have hd:=dyadIndex_bounds x hx
  have he:=dyad_power_bounds Z eta x hZ hbin (dyadIndex x) ⟨hd.1,hd.2.le⟩
  refine ⟨?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [Real.rpow_zero,firstDyadicExponent,rpow_dyadicExponent Z hZ]
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

def firstDyadicRadius (p:ι→O)(b:CubeCoordinates ι)(C D:Finset ι)
    (Z M r ell V eta tau:ℝ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (firstDyadicExponent Z (primeProductNorm p D))
    (firstDyadicExponent Z (primeProductNorm p C))
    (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau)

def firstDyadicPhysicalCutoff (p:ι→O)(b:CubeCoordinates ι)(C:Finset ι)(I:Ideal O)
    (Z M r ell V eta tau:ℝ)(D:Finset ι):Finset O:=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (firstDyadicRadius p b C D Z M r ell V eta tau)

theorem first_dyadic_radius_global_cap
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι)(C D:Finset ι)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (h₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)):
    firstDyadicRadius p b C D Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hC:=first_dyadic_bounds Z eta (primeProductNorm p C) hZ hbin (primeProductNorm_ge_one p hp C)
  have hd:=first_dyadic_bounds Z eta (primeProductNorm p D) hZ hbin (primeProductNorm_ge_one p hp D)
  have hj:=first_dyadic_bounds Z eta (‖eisEmbedding (jLabel p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) hZ hbin
    (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _))
  have hs:=cube_whole_support_dyad p hp b (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) h₁ h₂
  have hn:primeProductNorm p D≤Z^(firstDyadicExponent Z (primeProductNorm p C)+2*ell+3*eta):=by
    calc
      _≤primeProductNorm p (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):=
        primeProductNorm_mono p hp hD
      _≤primeProductNorm p C*primeProductNorm p b.support:=
        (primeProductNorm_union_le_mul p hp _ _).trans
          (mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _)) (primeProductNorm_pos p hp _).le)
      _≤Z^(firstDyadicExponent Z (primeProductNorm p C)+eta)*(Z^(ell+eta))^2:=
        mul_le_mul hC.2.2 hs (primeProductNorm_pos p hp _).le (Real.rpow_nonneg hz.le _)
      _=_:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
        congr 1
        norm_num
        ring
  have hde:= (Real.rpow_le_rpow_left_iff hZ).mp (hd.2.1.trans hn)
  unfold firstDyadicRadius firstPhysicalHeight
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith [hC.1,hj.1]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0813

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicTail
Source SHA256: 5ad9cbe01a06abb11a15d247025496243daa3727c432178c2802c56d1ec6d259
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0814


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_first_dyadic_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
