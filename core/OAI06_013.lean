


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSummedBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
theorem actual_block_from_divisor_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀J:sectorPool D hD.1 S,(Ideal.absNorm (J:Ideal O):ℝ)≤Z^B) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₂/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨K,hK,hkernel⟩:=CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentSecondHarmonicBudget.actual_divisor_budget B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC0 hD hCD U A hτ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hk:=hkernel r hr η τ t S β C D hC0 hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor
    (fun L=>E₁/(Ideal.absNorm L:ℝ)) (fun L=>E₂/(Ideal.absNorm L:ℝ))
    (fun L=>div_nonneg hE₁ (Nat.cast_nonneg _)) (fun L=>div_nonneg hE₂ (Nat.cast_nonneg _))
    hleft hright
  have hs:=hZ.2 Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
    (fun J _=>(sectorPool_supported D hD.1 S J).1) (fun J _=>hn J) J₁ J₂ t E₁ E₂
  apply hk.trans
  calc
    _≤K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=mul_le_mul_of_nonneg_left hs hK
    _≤max 1 K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
          (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    _=_:=by ring

end SevenEighths.CenteredMomentSecondSummedBlock

end

end OAI
end OAIOriginalModule1843

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondOriginalChildren
Source SHA256: d3c865eca71de39746d2af5330b330e3e1623ae312efdd03a63f246e4bd21d90
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1844








namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondOriginalChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def core (s:Input ι) (C:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

omit [DecidableEq ι] in
lemma envelope_eq_core (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) :
    envelope s C L C0 Z δ E=core s C C0 Z δ E/(Ideal.absNorm L:ℝ):=by
  unfold envelope core;ring

def sourceRadial (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) (hH:0<H)
    (hΦ:∀z:O,0≤(Φ (normValue z/H)).re) : Radial :=
  ⟨keep,Φ,H,hH,fun z=>by simpa only [normValue_eq_embedding] using hΦ z⟩

theorem actual_block_from_original_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀J:sectorPool D hD.1 S,(Ideal.absNorm (J:Ideal O):ℝ)≤Z^B) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)) := by
  obtain ⟨Ce,hCe,hsource⟩:=actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩:=CenteredMomentSecondSummedBlock.actual_block_from_divisor_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ hn
    R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcore (G:Ideal O) (E:ℝ) (hE:0≤E):0≤core s G Ce Z δ E:=by
    unfold core
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (mul_nonneg (profileCost_nonneg s) hE))
      (mul_nonneg (mul_nonneg s.X₁_pos.le s.X₂_pos.le) (Finset.prod_nonneg (fun i _=>(s.P_pos i).le)))) (Nat.cast_nonneg _)
  apply hZ.2 r hr η τ t S β C D hC hD hCD U hτ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor (core s C Ce Z δ E₁) (core s D Ce Z δ E₂)
    (hcore C E₁ hE₁) (hcore D E₂ hE₂)
  · intro L hL hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=
      (CenteredMomentWholeDivisorShell.divisorPool_nonzero_norm Finset.univ
        (fun J:sectorPool D hD.1 S=>(J:Ideal O))
        (fun J _=>(sectorPool_supported D hD.1 S J).1) (Z^B) (fun J _=>hn J) L hL).2
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) C hC R0 seed L hsC hsf
      E₁ Z hE₁ hZ.1 hnC hNL J₁ (τ χ) v (hleft L hL hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh
  · intro L hL hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=
      (CenteredMomentWholeDivisorShell.divisorPool_nonzero_norm Finset.univ
        (fun J:sectorPool D hD.1 S=>(J:Ideal O))
        (fun J _=>(sectorPool_supported D hD.1 S J).1) (Z^B) (fun J _=>hn J) L hL).2
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) D hD R0 seed L hsD hsf
      E₂ Z hE₂ hZ.1 hnD hNL J₂ (τ χ) v (hright L hL hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh

end SevenEighths.CenteredMomentSecondOriginalChildren

end

end OAI
end OAIOriginalModule1844

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
Source SHA256: eb4b9e3b8780ce186feaa3000d5b183479b073c7ec17b2fcc4b39df4b5956b41
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1845



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceLowerSupport
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_product {ι:Type*} [Fintype ι] (v:Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct v):ℝ)=
      (∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ))*
      (Ideal.absNorm (v (Sum.inr 0)):ℝ)*(Ideal.absNorm (v (Sum.inr 1)):ℝ) := by
  simp only [finiteTupleProduct,map_prod,Nat.cast_prod,map_mul,Nat.cast_mul,Fintype.prod_sum_type,Fin.prod_univ_two]
  ring

 theorem profile_product_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0<P i) (ha:∀i,0≤a i) (ha₁:0≤a₁) (ha₂:0≤a₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤x)
    (hs₁:∀x,W₁ x≠0→a₁≤x) (hs₂:∀x,W₂ x≠0→a₂≤x)
    (v:Tuple ι) (hv:profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm (finiteTupleProduct v):ℝ) := by
  have hslot:∀i,Wslot i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/P i)≠0:=by
    intro i
    have hp: (∏j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _))).2
  have hrect:idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))≠0:=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  have hslots:(∏i,a i)*(∏i,P i)≤∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ):=by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun i _=>mul_nonneg (ha i) (hP i).le)
    intro i hi
    exact (le_div_iff₀ (hP i)).mp (hs i _ (hslot i))
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hplain:a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
      ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
    have hbranch (X Y:ℝ) (hX:0<X) (hY:0<Y) (hXY:X*Y=T)
        (hn:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X)*
          W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y)≠0) :
        a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
          ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
      have h1: a₁*X≤(Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ):=
        (le_div_iff₀ hX).mp (hs₁ _ (mul_ne_zero_iff.mp hn).1)
      have h2: a₂*Y≤(Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ):=
        (le_div_iff₀ hY).mp (hs₂ _ (mul_ne_zero_iff.mp hn).2)
      have hh:=mul_le_mul h1 h2 (mul_nonneg ha₂ hY.le) (Nat.cast_nonneg _)
      simp only [map_mul,Nat.cast_mul] at hh
      rw [←hXY]
      nlinarith
    unfold idealRectangle at hrect
    by_cases hx:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂)=0
    · have hy:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/Y₁)*
        W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y₂)≠0:=by
        intro hy
        exact hrect (by rw [hx,hy,sub_self])
      exact hbranch Y₁ Y₂ hY₁ hY₂ hYT hy
    · exact hbranch X₁ X₂ hX₁ hX₂ hXT hx
  have hT:0<T:=hXT ▸ mul_pos hX₁ hX₂
  have hp:=mul_le_mul hslots hplain (mul_nonneg (mul_nonneg ha₁ ha₂) hT.le)
    (Finset.prod_nonneg (fun _ _=>Nat.cast_nonneg _))
  rw [tuple_norm_product]
  have he:(∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)=
      ((∏i,a i)*(∏i,P i)*(a₁*a₂*T))/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))).mpr
  convert hp using 1 ; ring

 theorem profile_column_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0<P i) (ha:∀i,0≤a i) (ha₁:0≤a₁) (ha₂:0≤a₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤x)
    (hs₁:∀x,W₁ x≠0→a₁≤x) (hs₂:∀x,W₂ x≠0→a₂≤x)
    (S:Finset (Tuple ι)) (I:Ideal O)
    (hI:finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm I:ℝ) := by
  obtain ⟨v,hv,hv0,he⟩:=CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness S
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I hI
  have hh:=profile_product_lower R ν Wslot P a W₁ W₂ a₁ a₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP ha ha₁ ha₂ hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hXT hYT hs hs₁ hs₂ v hv0
  simpa only [he] using hh

end SevenEighths.CenteredMomentSourceLowerSupport

end

end OAI
end OAIOriginalModule1845

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceDyadicShell
Source SHA256: 1a850fe92f82fa875e305aff75b50bf0c45c92794643f2605dee1f8132e52369
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1846



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSourceDyadicShell
open CenteredMomentSectorLocalization CenteredMomentSourceLowerSupport
local notation "O" => ActualEisensteinCubic.O

lemma residual_window_bounds (C I:Ideal O) (hC:C≠0) (L U:ℝ) (n:ℤ)
    (hL:L≤(Ideal.absNorm (C*I):ℝ)) (hU:(Ideal.absNorm (C*I):ℝ)≤U)
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    L/(Ideal.absNorm C:ℝ)≤dyadicScale n ∧
      dyadicScale n≤4*U/(Ideal.absNorm C:ℝ) := by
  have hc:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=dyadicWeight_support n hw
  simp only [map_mul,Nat.cast_mul] at hL hU
  constructor
  · apply (div_le_iff₀ hc).mpr
    exact hL.trans (by nlinarith [hs.2])
  · apply (le_div_iff₀ hc).mpr
    nlinarith [hs.1]

lemma raw_window_lower (C I:Ideal O) (hC:C≠0) (a H:ℝ) (ha:0<a) (n:ℤ)
    (hL:a*H≤(Ideal.absNorm (C*I):ℝ))
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale n/a := by
  have hc:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=(dyadicWeight_support n hw).2.le
  simp only [map_mul,Nat.cast_mul] at hL
  apply (div_le_div_iff₀ hc ha).mpr
  nlinarith

end SevenEighths.CenteredMomentSourceDyadicShell

end

end OAI
end OAIOriginalModule1846

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows
Source SHA256: b56b8e69b01608cba8d04471acf65bcf000919e21eec35e1561a3fcd68a0f5f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1847



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceBlockWindows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

 theorem physicalBlock_column_witnesses (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃I:sectorPool C hC.1 S,∃J:sectorPool D hD.1 S,
      β (C*I)≠0 ∧ β (D*J)≠0 ∧
      dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)≠0 ∧
      dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ)≠0 := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hcoeff: (β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J)≠0:=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).1).2
    have hl:β (C*I)≠0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hcoeff).1).1
    have hr:β (D*J)≠0:=by
      intro hh
      exact hcoeff (by rw [hh,zero_mul,star_zero,mul_zero])
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact ⟨I,J,hl,hr,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2,(mul_ne_zero_iff.mp hw).2⟩
  · exact False.elim (hz rfl)

 theorem physicalBlock_scale_lower (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (a H:ℝ) (ha:0<a) (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    H/(Ideal.absNorm C:ℝ)≤dyadicScale (n 2)/a ∧
      H/(Ideal.absNorm D:ℝ)≤dyadicScale (n 3)/a := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  exact ⟨raw_window_lower C I hC.1 a H ha (n 2) (hlower _ hI) hwi,
    raw_window_lower D J hD.1 a H ha (n 3) (hlower _ hJ) hwj⟩

end SevenEighths.CenteredMomentSourceBlockWindows

end

end OAI
end OAIOriginalModule1847

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger
Source SHA256: 8763f9fe4eab238fbb14e9fe7684f53c6b2e7b9f2827fb22d36580304a078264
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1848


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSourceBlockWindows CenteredMomentSecondPhysicalCost
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing
open CenteredMomentSecondSectorFrequency CenteredMomentFirstWholeKernel
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem physicalBlock_effective_window (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K
      <dyadicScale (n 0) := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact (dyadicWeight_support (n 0)
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1).2
  · exact False.elim (hz rfl)

lemma logb_one_add_sixth (Z x:ℝ) (hZ:1<Z) (hx:0<x) :
    Real.logb Z x/6≤Real.logb Z (1+x) := by
  have hp:0≤Real.logb Z (1+x):=Real.logb_nonneg hZ (by linarith)
  have hm:=Real.logb_le_logb_of_le hZ hx (show x≤1+x by linarith)
  linarith

theorem scalar_log_ledger (Z c d g u v f p K H a k₀ h₀ A B:ℝ)
    (hZ:1<Z) (hc:0<c) (hd:0<d) (hg:0<g) (hu:0<u) (hv:0<v)
    (hf:0<f) (hp:0<p) (hK:0<K) (hH:0<H) (ha:0<a)
    (hk₀:0<k₀) (hh₀:0<h₀) (hA:0<A) (hB:0<B)
    (hk:K*g*v/(c*d)≤k₀) (hleft:a*H/c≤A) (hright:a*H/d≤B) :
    Real.logb Z (K*g/(Real.sqrt c*Real.sqrt d*u*Real.sqrt A*Real.sqrt B)*
      h₀^(1/6:ℝ)/(1+k₀*h₀/(A*B))*H/(c*d)*p/f^(1/3:ℝ))≤
      Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-
      (Real.logb Z c+Real.logb Z d-5*Real.logb Z g/6-Real.logb Z p+
        Real.logb Z u+Real.logb Z v/6+Real.logb Z f/3) := by
  have hklog:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos (mul_pos hK hg) hv) (mul_pos hc hd)) hk
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hdec:=logb_one_add_sixth Z (k₀*h₀/(A*B)) hZ (by positivity)
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) hv.ne',Real.logb_mul hK.ne' hg.ne',
    Real.logb_mul hc.ne' hd.ne'] at hklog
  rw [Real.logb_div (by positivity) hc.ne',Real.logb_mul ha.ne' hH.ne'] at hl
  rw [Real.logb_div (by positivity) hd.ne',Real.logb_mul ha.ne' hH.ne'] at hr
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul hk₀.ne' hh₀.ne',Real.logb_mul hA.ne' hB.ne'] at hdec
  simp (disch := positivity) only [Real.logb_div,
    Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos hh₀,
    Real.logb_rpow_eq_mul_logb_of_pos hf,
    logb_sqrt Z c hc,logb_sqrt Z d hd,logb_sqrt Z A hA,logb_sqrt Z B hB]
  linarith

def forcingNorm (C D:Ideal O) (U:Finset (CommonIndex C D)) : ℝ :=
  Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U))

def saving (C D:Ideal O) (U:Finset (CommonIndex C D)) (Z:ℝ) : ℝ :=
  Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
    5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
    Real.logb Z (Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
    Real.logb Z (forcingNorm C D U)/3

def centralPhysicalCost (C D:Ideal O) (U:Finset (CommonIndex C D))
    (K H:ℝ) (n:Fin 4→ℤ) : ℝ :=
  (1/H)*outerScalar C D K n*normalizer C D U*
    (dyadicScale (n 1))^(1/6:ℝ)/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
    (H^2/((C.absNorm:ℝ)*D.absNorm))*(Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)/
    (forcingNorm C D U)^(1/3:ℝ)

lemma common_product_pos (C D:Ideal O) (hC:Supported C) (V:Finset (CommonIndex C D)) :
    (0:ℝ)<Ideal.absNorm (∏P∈V,P.val) := by
  rw [map_prod,Nat.cast_prod]
  apply Finset.prod_pos
  intro P hP
  rw [←commonPrime_span C D hC P]
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (commonPrime_supported C D hC P).1)

theorem actual_physical_log_ledger (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0<K) (H a Z:ℝ) (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.logb Z (centralPhysicalCost C D U K H n)≤
      Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-saving C D U Z := by
  have hc:(0:ℝ)<C.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg:(0:ℝ)<Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hv:(0:ℝ)<Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hp:=common_product_pos C D hC Finset.univ
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hw:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hh: H/(C.absNorm:ℝ)*a≤dyadicScale (n 2):=(le_div_iff₀ ha).mp hw.1
    convert hh using 1; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hh: H/(D.absNorm:ℝ)*a≤dyadicScale (n 3):=(le_div_iff₀ ha).mp hw.2
    convert hh using 1; ring
  have hk:=physicalBlock_effective_window η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hk
  have hb:=scalar_log_ledger Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)
    (Ideal.absNorm (∏P∈U,P.val):ℝ)
    (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)
    (forcingNorm C D U) (Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)
    K H a (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
    hZ hc hd hg hu hv hf hp hK hH ha (dyadicScale_pos _) (dyadicScale_pos _)
    (dyadicScale_pos _) (dyadicScale_pos _) hk.le hl hr
  change _≤Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-saving C D U Z at hb
  convert hb using 1
  congr 1
  rw [centralPhysicalCost,normalizer,actual_partitionNormalizer C D hC,outerScalar]
  field_simp

lemma centralPhysicalCost_pos (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K H:ℝ) (hK:0<K) (hH:0<H) (n:Fin 4→ℤ) :
    0<centralPhysicalCost C D U K H n := by
  have hc:(0:ℝ)<C.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hu:=normalizer_pos C D hC U
  have hn0:=dyadicScale_pos (n 0)
  have hn1:=dyadicScale_pos (n 1)
  have hn2:=dyadicScale_pos (n 2)
  have hn3:=dyadicScale_pos (n 3)
  unfold centralPhysicalCost outerScalar
  positivity

theorem actual_physical_cost_bound (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0<K) (H a Z:ℝ) (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*Z^(-saving C D U Z) := by
  have hh:=actual_physical_log_ledger η t S β C D hC hD U R rows W K n hK H a Z hH ha hZ hlower hne
  apply (Real.logb_le_logb hZ (centralPhysicalCost_pos C D hC hD U K H hK hH n)
    (show 0<H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*Z^(-saving C D U Z) by positivity)).mp
  simp (disch := positivity) only [Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos hH,Real.logb_rpow_eq_mul_logb_of_pos hK,
    Real.logb_rpow_eq_mul_logb_of_pos ha,Real.logb_rpow (by linarith : 0<Z) hZ.ne']
  linarith

theorem actual_canonical_physical_cost (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (w:O) (hpart:canonicalPartition C D U w)
    (hcorr:idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0<K) (H a Z:ℝ) (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  have hs:=actual_second_ledger_lower C D hC hD hCD U w hpart Z hZ hcorr
  change (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3≤saving C D U Z at hs
  exact (actual_physical_cost_bound η t S β C D hC hD U R rows W K n hK H a Z hH ha hZ hlower hne).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity))

theorem physicalBlock_canonical_witness (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (hK:0<K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) ∧
      idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  have hn:=right_ne_zero_of_mul hne
  unfold normalizedBlock at hn
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  have hr:=left_ne_zero_of_mul hz
  have hpart:canonicalPartition C D U (nonunitFrequencyGenerator C D U*z):=by
    by_contra hp
    simp only [retainedScalar,canonicalPartitionScalar,hp,ite_false,zero_mul] at hr
    exact hr rfl
  refine ⟨z,hzr,hpart,?_⟩
  intro hc
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>CenteredMomentLogDyadic.logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)
    (by simpa only [mul_assoc] using hc)
  exact (right_ne_zero_of_mul hz) (by simpa only [sectorFrequency,F] using he)

theorem original_block_physical_cost (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0<K) (H a Z:ℝ) (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  obtain ⟨z,hz,hpart,hcorr⟩:=physicalBlock_canonical_witness η t S β C D hC hD hCD U R rows hrows W K hK n hne
  exact actual_canonical_physical_cost η t S β C D hC hD hCD U _ hpart hcorr R rows W K n
    hK H a Z hH ha hZ hlower hne

end SevenEighths.CenteredMomentSecondPhysicalLedger

end

end OAI
end OAIOriginalModule1848

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceSupportedTailUniform
Source SHA256: 0573649eccfe69cf5f1c82130ac595e3c0176a32d24179198cebbd3174559c6b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1849




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSupportedTailUniform
open ActualEisensteinCubic HeckeFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentFirstTailAggregate CenteredMomentFirstScale
open CenteredMomentSupportedTailAggregate CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem source_first_discarded_energy_bound {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j))
    (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (sΦ : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      ((∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤Real.exp HN*X) →
      (∀ I : supportedColumns (finiteColumns S),∀ J : supportedColumns (finiteColumns S),
        finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0 →
        finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0 →
        ∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s))
        Φ K Tsec Z ξ‖ ≤
      ((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        (Real.exp HN*X)^ε*K*(C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨D,hD,hmass⟩ := CenteredMomentSourceProfileMassUniform.profile_mass_uniform
    Wslot a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hWslot
  obtain ⟨sΦ,C,hC,htail⟩ := first_discarded_energy_bound Adec ε hε
  refine ⟨sΦ,D^2*C,mul_pos (sq_pos_of_pos hD) hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
    S Φ K X HN Tsec Z Csec ξ hK hXX hZ hCs hN hsec hthreshold
  let Dprofile := D*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hm := (finiteColumnCoefficient_mass S β).trans
    (hmass W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S)
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
      (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hNN (I : Ideal O) (_hI : I∈finiteColumns S)
      (hn : finiteColumnCoefficient S β I≠0) : (Ideal.absNorm I:ℝ)≤Real.exp HN*X := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      (fun j=>hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
      (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂)
      (fun j x hx=>(hsSlot j hx).2) (fun x hx=>(hs₁ hx).2)
      (fun x hx=>(hs₂ hx).2) v hv0
    rw [←he]
    exact hh.2.trans hN
  have ht := htail η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K X HN Tsec Z Csec ξ
    hK hXX hZ hCs hNN hsec hthreshold
  apply ht.trans
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2
  calc
    _ ≤ (Dprofile*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        (Real.exp HN*X)^ε*K*(C*sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hK.le
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by positivity) _)
    _ = _ := by dsimp [Dprofile]; ring

theorem source_second_discarded_energy_bound {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j))
    (Adec : ℕ) :
    ∃ (sΦ : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      ((∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤Real.exp HN*X) →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s))
        Φ K Tsec Z ξ‖ ≤
      ((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        K*(Real.exp HN*X)^2*(C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨D,hD,hmass⟩ := CenteredMomentSourceProfileMassUniform.profile_mass_uniform
    Wslot a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hWslot
  obtain ⟨sΦ,C,hC,htail⟩ := second_discarded_energy_bound Adec
  refine ⟨sΦ,D^2*C,mul_pos (sq_pos_of_pos hD) hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
    S Φ K X HN Tsec Z Csec ξ hK hXX hZ hCs hN hsec hthreshold
  let Dprofile := D*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hm := (finiteColumnCoefficient_mass S β).trans
    (hmass W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S)
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
      (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hNN (I : Ideal O) (_hI : I∈finiteColumns S)
      (hn : finiteColumnCoefficient S β I≠0) : (Ideal.absNorm I:ℝ)≤Real.exp HN*X := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      (fun j=>hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
      (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂)
      (fun j x hx=>(hsSlot j hx).2) (fun x hx=>(hs₁ hx).2)
      (fun x hx=>(hs₂ hx).2) v hv0
    rw [←he]
    exact hh.2.trans hN
  have ht := htail η t (finiteColumns S) (finiteColumnCoefficient S β) Φ K X HN Tsec Z Csec ξ
    hK hXX hZ hCs hNN hsec hthreshold
  apply ht.trans
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hm 2
  calc
    _ ≤ (Dprofile*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j))^2*
        K*(Real.exp HN*X)^2*(C*sΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsq hK.le
    _ = _ := by dsimp [Dprofile]; ring

end SevenEighths.CenteredMomentSourceSupportedTailUniform

end

end OAI
end OAIOriginalModule1849

/-! Original module: OAI.NumberTheory.DirichletL.PeriodicThetaRegularity
Source SHA256: 7589b5c6ec1711370690b5f13fa463df7d707721e88c732e6e8fce9bd20aafa5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1850


namespace OAI

noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.PeriodicThetaRegularity
open ThetaProduct EisensteinTheta HeckeTheta

theorem rectangularPair_f_continuous (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (rectangularPair a b u v hu hv).f (Ioi 0) :=
  (scaledEvenPair_f_continuous a u hu).mul (scaledEvenPair_f_continuous b v hv)

theorem pair_f_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (pair w).f (Ioi 0) := by
  have h : ContinuousOn (fun t => ∑ p : (Fin N × Fin N) × Fin 2,
      w p.1 * (parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2).f t)
      (Ioi 0) := by
    apply continuousOn_finsetSum
    intro p _
    exact continuousOn_const.mul
      (rectangularPair_f_continuous (xShift p.1.1 p.1.2 N p.2)
        (yShift p.1.2 N p.2) _ _ _ _)
  apply h.congr
  intro t _
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem theta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (theta w) (Ioi 0) :=
  (pair_f_continuous w).congr (fun _t ht => theta_eq_pair w ht)

theorem theta_locallyIntegrable {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    LocallyIntegrableOn (theta w) (Ioi 0) :=
  (theta_continuous w).locallyIntegrableOn measurableSet_Ioi

theorem theta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (r : ℝ) :
    (fun t => theta w t - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) := by
  apply ((pair w).hf_top r).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [theta_eq_pair w ht, pair_f₀]

theorem scaledTheta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) :
    ContinuousOn (fun t => theta w (A * t)) (Ioi 0) :=
  (theta_continuous w).comp (by fun_prop) (fun t ht => mul_pos hA ht)

theorem scaledTheta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) (r : ℝ) :
    (fun t => theta w (A * t) - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) :=
  rapid_rescale (theta w) (w (0,0)) (theta_rapid w) hA r

def primitivePair {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (A : ℝ) (hA : 0 < A) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ t : ℝ, 0 < t →
      theta w (A / t) = ε * (t : ℂ) * theta v (A * t)) : WeakFEPair ℂ where
  f := fun t => theta w (A * t)
  g := fun t => theta v (A * t)
  k := 1
  ε := ε
  f₀ := w (0,0)
  g₀ := v (0,0)
  hf_int := (scaledTheta_continuous w A hA).locallyIntegrableOn measurableSet_Ioi
  hg_int := (scaledTheta_continuous v A hA).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  h_feq t ht := by
    simpa only [mul_one_div, Real.rpow_one, smul_eq_mul] using hfeq t ht
  hf_top := scaledTheta_rapid w A hA
  hg_top := scaledTheta_rapid v A hA

end SevenEighths.PeriodicThetaRegularity

end

end OAI
end OAIOriginalModule1850

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedEuler
Source SHA256: efef8a8eb8e02a4eb79cece6b8faa8ddde74e4c802a037bbaf8765655d33c1c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1851



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open ActualEisensteinCubic ProbeEulerFinsupp ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedRowArray (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedRowArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : excludedRowArray S η u x w z 1=1 := by
  simp only [excludedRowArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]

lemma excludedRowArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedRowArray S η u x w z (a*b)=excludedRowArray S η u x w z a*excludedRowArray S η u x w z b := by
  simp only [excludedRowArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedRowPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedRowArray S η u x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedRowArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedRowArray S η u x w z (highIdeals v)=v.prod (excludedRowPrimeTerm S η u x w z) :=
  highArray_val_prod _ (excludedRowArray_one S hS η u x w z) (excludedRowArray_mul S hS η u x w z) v

lemma markedRowArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η u x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedRowArray S η u x w z (highIdeals v)=_
  rw [excludedRowArray_prod S hS]

theorem markedRowSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η u x w z) := by
  have h0 (P : PrimeIdeal) : excludedRowPrimeTerm S η u x w z P 0=1 := by
    simp only [excludedRowPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedRowArray_one S hS η u x w z
  have hs := (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedRowArray S η u x w z (highIdeals v)‖) at hs
  simp only [excludedRowArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedRowPrimeTerm S η u x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η u x w z := by
    simp only [←markedRowArray_val S hS T η u x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1851

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedLocal
Source SHA256: 71968b716bd08ee78f6557fc09bd0439b318ea0fabb8b4b1d86cb7f5b332d1f8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1852




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealRowMarkedLocalFactor (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*rowHighPrimeTerm η u x w z P ((e.val,l),(k,m))

lemma markedRowPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*rowHighPrimeTerm η u x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedRowPrimeTerm_tsum (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,completedValuationMark P b*rowHighPrimeTerm η u x w z P b)=
      idealRowMarkedLocalFactor η u P x w z := by
  have hs := (markedRowPrimeTerm_summable_norm η u P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*rowHighPrimeTerm η u x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedRowLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedRowPrimeTerm S η u x w z) P b)=
      if P∈T then idealRowMarkedLocalFactor η u P x w z else idealRowHighLocalFactor η u P.val x w z := by
  have he (b : HighValuation) : excludedRowPrimeTerm S η u x w z P b=rowHighPrimeTerm η u x w z P b := by
    simp only [excludedRowPrimeTerm,excludedRowArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,rowHighPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [ite_eq_left hPT]
    exact markedRowPrimeTerm_tsum η u P x w z hx hw hz
  · simp only [ite_eq_right hPT,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1852

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Valuation
Source SHA256: 0c57756bea7fad7ffc3201f6593bc119646fc1e1a560c0bf4afa8d621ffc57e4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1853



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification UniqueFactorizationMonoid
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def unitPart (u : FreeRow) (p : O) (hp : Prime p) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_spec (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=p^(multiplicity p u.val)*unitPart u p hp ∧ ¬p∣unitPart u p hp :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_coprime (u : FreeRow) (p : O) (hp : Prime p) : IsCoprime (unitPart u p hp) p :=
  (hp.irreducible.coprime_iff_not_dvd.mpr (unitPart_spec u p hp).2).symm

theorem unitPart_ne_zero (u : FreeRow) (p : O) (hp : Prime p) : unitPart u p hp≠0 := by
  intro he
  have hu := (unitPart_spec u p hp).1
  rw [he,mul_zero] at hu
  exact u.property.1 hu

theorem multiplicity_lt_six (u : FreeRow) (p : O) (hp : Prime p) : multiplicity p u.val<6 := by
  let P : Ideal O := Ideal.span {p}
  have hP0 : P≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  have hP : Prime P := Ideal.prime_of_isPrime hP0 (Ideal.isPrime_span_singleton_of_prime hp)
  have hb : (Ideal.span {unitPart u p hp}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (unitPart_ne_zero u p hp)
  have he : (Ideal.span {u.val}:Ideal O)=P^(multiplicity p u.val)*Ideal.span {unitPart u p hp} := by
    conv_lhs => rw [(unitPart_spec u p hp).1]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow]
  have hf := u.property.2 P
  rw [he,normalizedFactors_mul (pow_ne_zero _ hP0) hb,normalizedFactors_pow,
    normalizedFactors_irreducible hP.irreducible] at hf
  simp only [normalize_eq,Multiset.count_add,Multiset.count_nsmul,
    Multiset.count_singleton_self,mul_one] at hf
  omega

theorem canonical_decomposition (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=unitPart u p hp*p^(multiplicity p u.val) ∧
      IsCoprime (unitPart u p hp) p ∧ multiplicity p u.val<6 := by
  exact ⟨(unitPart_spec u p hp).1.trans (mul_comm _ _),unitPart_coprime u p hp,
    multiplicity_lt_six u p hp⟩

theorem idealRowHighLocalFactor_canonical (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hprimary : ConcretePrimeRowBridge.goodLambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (x w z : ℂ) :
    ProbePhysical.idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,
        ProbeEuler.sourceRowTerm p hp hg (ProbeRow.targetMonoid η p) (ProbeEuler.actualACube η p)
          (CompletedGauss.actualSextic (Ideal.span {p}) hg
            (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val) e.val l k m := by
  conv_lhs => rw [(canonical_decomposition u p hp).1]
  exact ProbePhysical.idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1853

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Character
Source SHA256: 18c683744028feae68304ad0e35349983a48a63cc607ea0f9bb8aa47a07a3ba5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1854





namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ProbePhysical
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rowMaskElement : O := 2*λ₀

theorem rowMaskElement_ne_zero : rowMaskElement≠0 :=
  mul_ne_zero (by norm_num) PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero

def rawRow (u : FreeRow) : Character := Classical.choose
  (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))

theorem rawRow_coeff (u : FreeRow) (I : Ideal O) :
    idealCoeff (rawRow u) I=idealCoeff (fixedSourcePrincipal ∅ (by simp)) I*
      idealRowHom (rowMaskElement^6*u.val) I := by
  have he := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2
  simpa only [one_pow,mul_one] using idealCoeff_eq_row _ (rawRow u) rowMaskElement 1 u.val he I

theorem outside_good_coprime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (P : PrimeIdeal) (hP : P.val∉S) :
    λ₀∉P.val ∧ IsCoprime P.val (Ideal.span {rowMaskElement}) := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have hn : P.val∉fixedBadPrimes := fun hh => hP (hbad hh)
  have hg := (prime_good_iff_not_bad P.val).mpr hn
  refine ⟨hg.1,?_⟩
  have hc := (prime_coprime_fixedProduct S hS P).mpr hP
  rw [IsCoprime.prod_right_iff] at hc
  have hLam : Ideal.span {λ₀}∈S := hbad (Finset.mem_insert_self _ _)
  have h2 : Ideal.span {(2 : O)}∈S := hbad (by simp [fixedBadPrimes])
  unfold rowMaskElement
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact (hc _ h2).mul_right (hc _ hLam)

theorem rawRow_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (P : PrimeIdeal) (hP : P.val∉S) :
    idealCoeff (rawRow u) P.val=idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [rawRow_coeff,fixedSourcePrincipal_prime]
  rw [ite_eq_right (by simp),one_mul]
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask rowMaskElement P.val hg,
    ite_eq_left hc,one_mul]

def rowCharacter (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Character :=
  (rawRow u).excludePrimes S hS

def sourceRowCoeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Ideal O→*₀ℂ where
  toFun I := highExclusion S hS I*idealRowHom u.val I
  map_zero' := by rw [(idealRowHom u.val).map_zero, mul_zero]
  map_one' := by rw [map_one,map_one,mul_one]
  map_mul' I J := by simp only [map_mul]; ring

theorem hom_eq_of_primes (f g : Ideal O→*₀ℂ) (h : ∀P : PrimeIdeal,f P.val=g P.val) : f=g := by
  ext I
  by_cases hI : I=0
  · subst I; rw [map_zero,map_zero]
  have hf := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq f)
  have hg := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq g)
  rw [←hf,←hg]
  change (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map f).prod)=
    (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map g).prod)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  exact h ⟨P,UniqueFactorizationMonoid.prime_of_normalized_factor P hP⟩

theorem rowCharacter_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=highExclusion S hS I*idealRowHom u.val I := by
  have he : idealCoeff (rowCharacter S hS u)=sourceRowCoeff S hS u := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=
      highExclusion S hS P.val*idealRowHom u.val P.val
    rw [excludedTarget_prime,highExclusion_prime]
    by_cases hP : P.val∈S
    · simp only [ite_eq_left hP,zero_mul]
    · simp only [ite_eq_right hP,one_mul]
      exact rawRow_prime_outside S hS hbad u P hP
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem target_inverseRow_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (P : PrimeIdeal) :
    idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=
      if P.val∈S then 0 else idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val) := by
  rw [excludedTarget_prime,idealCoeff_product,idealCoeff_inverse_conj]
  by_cases hP : P.val∈S
  · simp only [ite_eq_left hP]
  · rw [ite_eq_right hP,ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1854

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Euler
Source SHA256: a93ae1bc03e6175d2bb52bb5c0c2b9a13a3def143e955e79e9d311eecc54c7eb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1855


namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def targetRow (η : Character) (u : FreeRow) : Character := η.product (rawRow u).inverse

theorem rowCharacter_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-idealRowHom u.val P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (rowCharacter S hS u) s) := by
  apply LFunction_hasProd_outside (rowCharacter S hS u) S (idealRowHom u.val) _ s hs
  intro P
  rw [rowCharacter_coeff S hS hbad,highExclusion_prime]
  split_ifs <;> simp only [zero_mul,one_mul]

theorem targetRow_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-idealCoeff η P.val.val*starRingEnd ℂ (idealRowHom u.val P.val.val)*
        CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction ((targetRow η u).excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (fun P => idealCoeff η P*starRingEnd ℂ (idealRowHom u.val P))
    (target_inverseRow_coeff S hS hbad η u) s hs

def localCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

theorem localCorrection_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (markedIdealHighSeries S 1 η u.val x w z *
        (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ * (LFunction (rowCharacter S hS u) w)⁻¹ *
          LFunction ((targetRow η u).excludePrimes S hS) x) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hF := excludedIdealHighSeries_row_hasProd_outside S hS η u.val x w z hx hw hz
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz1).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1)
  have hW := (rowCharacter_hasProd S hS hbad u w hw1).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1)
  have hD := targetRow_hasProd S hS hbad η u x hx1
  have he := ((hF.mul hZ).mul hW).mul hD
  simpa only [localCorrection,inv_inv,div_eq_mul_inv] using he

theorem globalCorrection_multipliable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z) :=
  (localCorrection_hasProd S hS hbad η u x w z hx hw hz).multipliable

theorem high_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (rowCharacter S hS u) w /
        LFunction ((targetRow η u).excludePrimes S hS) x * globalCorrection S η u x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [globalCorrection,(localCorrection_hasProd S hS hbad η u x w z hx hw hz).tprod_eq]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1855

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Conductor
Source SHA256: 032beb68252aecb437238fb118c73c21df96bb234df16a2a509b05dacdbc2417
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1856



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

def conductorConstant : ℕ :=
  (Ideal.span {rowMaskElement}:Ideal O).absNorm*(Ideal.span {(72 : O)}:Ideal O).absNorm

theorem rawRow_conductor (u : FreeRow) :
    (rawRow u).modulus.absNorm≤conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  have hb := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).1
  change (rawRow u).modulus.absNorm≤_ at hb
  simpa [rowConductorBound,conductorConstant,fixedSourcePrincipal,HeckeRayFamily.character,
    Character.ofResidue] using hb

theorem rowCharacter_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).modulus.absNorm≤
      conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((rawRow u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (rawRow_conductor u)

theorem targetRow_conductor (η : Character) (u : FreeRow) :
    (targetRow η u).modulus.absNorm≤η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (O ⧸ (rawRow u).modulus) := Ring.HasFiniteQuotients.finiteQuotient (rawRow u).modulus_ne_bot
  change (η.modulus⊓(rawRow u).modulus).absNorm≤_
  calc
    _ ≤ η.modulus.absNorm*(rawRow u).modulus.absNorm :=
      FiniteConductor.absNorm_inf_le_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm (rawRow_conductor u)

theorem targetRow_excluded_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) :
    ((targetRow η u).excludePrimes S hS).modulus.absNorm≤
      η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((targetRow η u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (targetRow_conductor η u)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1856

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
Source SHA256: 410a50259ddcb26cd84c20045a67bafedd227ec94c04441e6faebee92902372b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1857



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem canonicalPrimePower_descent (P : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) :
    CenteredMomentCanonical.canonicalPrimePowerCharacter P hg hc x =
      (CompletedGauss.actualSextic P hg ^ c)
        (CenteredMomentCorrelation.primePowerReduction P hc x) := rfl

theorem idealRowHom_congr_radical (I : Ideal O) (x y : O)
    (hxy : x-y ∈ I.radical) : idealRowHom x I = idealRowHom y I := by
  by_cases hI : I = 0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _)
  rw [ite_eq_right hI, ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  have hle : I.radical ≤ P := hp.radical_le_iff.mpr
    (((Ideal.mem_normalizedFactors_iff hI).mp hP).2)
  unfold localRowValue
  split_ifs with hg
  · let : P.IsMaximal := hg.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

theorem radical_ne_bot (I : Ideal O) (hI : I ≠ ⊥) : I.radical ≠ ⊥ := by
  intro h
  exact hI (bot_unique (h ▸ I.le_radical))

theorem movingNumeratorRow_radical_periodic (r : O)
    (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}).radical
      (movingNumeratorRow r hr) := idealRowHom_congr_radical _

theorem actualPeriodicRow_radical_periodic (Ψ : O →* ℂ) (Q : Ideal O)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ : x-y ∈ Q := Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm : x-y ∈ Ideal.span {m} := Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72 : x-y ∈ Ideal.span {(72 : O)} := Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy : x-y ∈ (Ideal.span {r}).radical := Ideal.mul_le_right hxy
  change ((Ψ x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) *
      movingNumeratorRow r hr x =
    ((Ψ y * coprimalityMask m y) * numeratorBadTwist u a b r hr y) *
      movingNumeratorRow r hr y
  rw [hΨ x y hQ, coprimalityMask_periodic m x y hm,
    numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_radical_periodic r hr x y hrxy]

theorem rowTwist_radical_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _ (actualPeriodicRow (elementHom η) m u a b r hr)
    (actualPeriodicRow_radical_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((supported_span_iff n).mp hs).1 hn
  · exact rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_radical_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical) n) := by
  have hu := rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx hn
  have hle : η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r} ≤
      η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical :=
    Ideal.mul_mono_right (Ideal.span {r}).le_radical
  exact hu.map (Ideal.Quotient.factor hle)

theorem exists_row_character_radical (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * (Ideal.span {m}).absNorm *
        (Ideal.span {(72 : O)}).absNorm * (Ideal.span {f^4*z}).radical.absNorm ∧
      ∀ n : O, elementCoeff χ n = rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, _, _, _, _⟩ :=
    exists_actual_periodic_row (elementHom η) η.modulus η.modulus_ne_bot
      (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  change f^4*z = (u : O)*λ₀^a*(2 : O)^b*r at hx
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical
  have hM : M ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (radical_ne_bot _ hr.1)
  have hG := rowTwist_radical_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨HeckeRowClosure.rowCharacter M hM _ hG (rowTwist_unit η m f z), ?_, ?_⟩
  · change M.absNorm ≤ _
    have hfr : Ideal.span {f^4*z} ≤ (Ideal.span {r} : Ideal O) := by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
    have hF : (Ideal.span {f^4*z} : Ideal O).radical ≠ ⊥ :=
      radical_ne_bot _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz))
    let : Finite (O ⧸ (Ideal.span {f^4*z} : Ideal O).radical) :=
      Ring.HasFiniteQuotients.finiteQuotient hF
    have hn := FiniteConductor.absNorm_le_of_le (Ideal.radical_mono hfr)
    simpa only [M, map_mul] using Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn
        (rowTwist_nonzero_radical_unit η m f z n hmLam hm2 u a b r hx h)))

theorem periodic_sup (G : O →* ℂ) (I J : Ideal O)
    (hI : CanonicalCoefficientClass.FactorsModulo I G)
    (hJ : CanonicalCoefficientClass.FactorsModulo J G) :
    CanonicalCoefficientClass.FactorsModulo (I ⊔ J) G := by
  intro x y hxy
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxy
  calc
    G x = G (x-a) := hI _ _ (by convert ha using 1; ring)
    _ = G y := hJ _ _ (by convert hb using 1; linear_combination -hab)

theorem primitive_of_equal_elements (χ θ : Character)
    (hel : ∀ n : O, elementCoeff χ n = elementCoeff θ n) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ θ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  have hθ : CanonicalCoefficientClass.FactorsModulo θ.modulus (elementHom χ) := by
    intro x y hxy
    change elementCoeff χ x = elementCoeff χ y
    rw [hel x, hel y]
    exact elementHom_periodic θ x y hxy
  let M := χ.modulus ⊔ θ.modulus
  have hM : M ≠ ⊥ := fun h => χ.modulus_ne_bot (bot_unique (h ▸ le_sup_left))
  have hG := periodic_sup (elementHom χ) χ.modulus θ.modulus (elementHom_periodic χ) hθ
  have hu : ∀ u : Oˣ, elementHom χ (u : O) = 1 := fun u => χ.unit_trivial u
  let ρ := HeckeRowClosure.rowCharacter M hM (elementHom χ) hG hu
  have hr (n : O) : elementCoeff ρ n = elementCoeff χ n := by
    change elementCoeff (HeckeRowClosure.rowCharacter M hM _ hG hu) n = _
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · have hz : elementCoeff χ n = 0 := by
        by_contra hne
        have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hne
        exact hn (hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left)))
      exact hz.symm
  obtain ⟨ψ, hψ, hp, hn, hmask⟩ := exists_primitive_character ρ
  refine ⟨ψ, le_sup_left.trans hψ, hp, ?_, ?_⟩
  · let : Finite (O ⧸ θ.modulus) := Ring.HasFiniteQuotients.finiteQuotient θ.modulus_ne_bot
    exact hn.trans (FiniteConductor.absNorm_le_of_le (show θ.modulus ≤ M from le_sup_right))
  · intro I
    by_cases hI : I = 0
    · subst I
      simp only [map_zero, ite_self]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn0 : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
    have hre : idealCoeff ρ I = idealCoeff χ I := by
      rw [← hs, idealCoeff_span _ hn0, idealCoeff_span _ hn0, hr]
    by_cases hc : IsCoprime I χ.modulus
    · have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr (hs.symm ▸ hc)
      have huM : IsUnit (Ideal.Quotient.mk M n) :=
        hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left))
      have hcM : IsCoprime I M := hs ▸ (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp huM
      simpa only [hre, show ρ.modulus = M from rfl, hcM, hc, ite_true] using hmask I
    · rw [ite_eq_right hc]
      simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem rawRow_small_presentation (u : HeckeInverseAmplification.FreeRow) :
    ∃ θ : Character,
      θ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (ProbeHighRowFamily.rawRow u) n = elementCoeff θ n := by
  obtain ⟨θ, hn, he⟩ := exists_row_character_radical
    (ProbePhysical.fixedSourcePrincipal ∅ (by simp)) ProbeHighRowFamily.rowMaskElement 1 u.val
    ProbeHighRowFamily.rowMaskElement_ne_zero one_ne_zero u.property.1
    (dvd_mul_left _ _) (dvd_mul_right _ _)
  refine ⟨θ, ?_, ?_⟩
  · simpa [ProbeHighRowFamily.conductorConstant, ProbePhysical.fixedSourcePrincipal,
      HeckeRayFamily.character, Character.ofResidue] using hn
  · intro n
    have ho := (Classical.choose_spec
      (exists_row_character_with_conductor (ProbePhysical.fixedSourcePrincipal ∅ (by simp))
        ProbeHighRowFamily.rowMaskElement 1 u.val ProbeHighRowFamily.rowMaskElement_ne_zero
        one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n
    exact ho.trans (he n).symm

theorem rawRow_primitive_radical (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rawRow u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rawRow u) I =
        if IsCoprime I (ProbeHighRowFamily.rawRow u).modulus then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements _ θ he
  exact ⟨ψ, hle, hp, hb.trans hn, hmask⟩

theorem equal_elements_excludePrimes (χ θ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff θ n)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (n : O) :
    elementCoeff (χ.excludePrimes S hS) n = elementCoeff (θ.excludePrimes S hS) n := by
  have hc : IsCoprime (Ideal.span {n}) χ.modulus ↔ IsCoprime (Ideal.span {n}) θ.modulus := by
    have huχ : elementCoeff χ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) χ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    have huθ : elementCoeff θ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) θ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    rw [he n] at huχ
    exact huχ.symm.trans huθ
  simp only [Character.excludePrimes, elementCoeff_refineModulus,
    IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff, hc, he n]

def fixedConductorConstant (S : Finset (Ideal O)) : ℕ :=
  ProbeHighRowFamily.conductorConstant * (∏ P ∈ S, P).absNorm

theorem rowCharacter_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements
    (ProbeHighRowFamily.rowCharacter S hS u) (θ.excludePrimes S hS)
    (equal_elements_excludePrimes _ θ he S hS)
  refine ⟨ψ, hle, hp, hb.trans ?_, hmask⟩
  change (θ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

theorem prod_le_radical_prod_pow {ι : Type*} (T : Finset ι)
    (P : ι → Ideal O) (e : ι → ℕ) (he : ∀ i ∈ T, 1 ≤ e i) :
    (∏ i ∈ T, P i) ≤ (∏ i ∈ T, P i ^ e i).radical := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hei : e i ≠ 0 := by have := he i (Finset.mem_insert_self i T); omega
    have hpow : (P i ^ e i).radical = (P i).radical := Ideal.radical_pow (P i) hei
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Ideal.radical_mul, hpow]
    exact Ideal.mul_le_inf.trans (inf_le_inf (P i).le_radical
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj))))

theorem radical_norm_selected_deficit {ι : Type*} [Fintype ι]
    (I : Ideal O) (hI : I ≠ 0) (P : ι → Ideal O)
    (hP : ∀ i, Prime (P i)) (hdis : Function.Injective P)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (hdiv : ∀ i, P i ^ e i ∣ I) :
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i - 1) ≤ I.absNorm := by
  let (i : ι) : (P i).IsMaximal := (Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  have hcop : Pairwise (fun i j => IsCoprime (P i ^ e i) (P j ^ e j)) := by
    intro i j hij
    exact (Ideal.isCoprime_of_isMaximal (hdis.ne hij)).pow
  obtain ⟨B, hB⟩ := Fintype.prod_dvd_of_coprime hcop hdiv
  have hB0 : B ≠ 0 := by
    intro hz
    apply hI
    rw [hB, hz, mul_zero]
  have hsmall0 : (∏ i, P i) * B ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne_zero)) hB0
  have hsmall : (∏ i, P i) * B ≤ I.radical := by
    rw [hB, Ideal.radical_mul]
    exact Ideal.mul_le_inf.trans (inf_le_inf
      (prod_le_radical_prod_pow Finset.univ P e (fun i _ => he i)) B.le_radical)
  let : Finite (O ⧸ (∏ i, P i) * B) := Ring.HasFiniteQuotients.finiteQuotient hsmall0
  have hn := FiniteConductor.absNorm_le_of_le hsmall
  have hprod : (∏ i, P i) * (∏ i, P i ^ (e i-1)) = ∏ i, P i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (he i)
  calc
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
        ((∏ i, P i) * B).absNorm * (∏ i, P i ^ (e i-1)).absNorm := by
      simpa only [map_prod, map_pow] using Nat.mul_le_mul_right
        (∏ i, (P i).absNorm ^ (e i-1)) hn
    _ = I.absNorm := by
      rw [← map_mul]
      congr 1
      calc
        ((∏ i, P i) * B) * (∏ i, P i ^ (e i-1)) =
            ((∏ i, P i) * (∏ i, P i ^ (e i-1))) * B := by ring
        _ = I := by rw [hprod, ← hB]

theorem rowCharacter_primitive_selected_deficit (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          ψ.modulus.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hb := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => (by have := he i; omega)) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i-1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hb

theorem canonicalCRT_radical_congr {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x y : O)
    (hxy : x-y ∈ (∏ i, P i ^ e i).radical) :
    CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) x) =
      CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) y) := by
  rw [CenteredMomentCanonical.canonicalCRTCharacter_mk,
    CenteredMomentCanonical.canonicalCRTCharacter_mk]
  exact idealRowHom_congr_radical _ x y hxy

theorem fixedConductorConstant_pos (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : 0 < fixedConductorConstant S := by
  have hnorm (I : Ideal O) (hI : I ≠ 0) : 0 < I.absNorm :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  unfold fixedConductorConstant ProbeHighRowFamily.conductorConstant
  exact mul_pos (mul_pos
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr ProbeHighRowFamily.rowMaskElement_ne_zero))
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))))
    (hnorm _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))

theorem sourceRow_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, ProbePhysical.highExclusion S hS I * idealRowHom u.val I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hn, ?_⟩
  intro I
  rw [← ProbeHighRowFamily.rowCharacter_coeff S hS hbad u I]
  exact hm I

theorem rowCharacter_primitive_selected_div (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          (ψ.modulus.absNorm : ℝ) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) /
              ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
  obtain ⟨ψ, hle, hp, hm, hb⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hpos : 0 < ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hP i).ne_zero)
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast hb k P hP hdis e he hdiv

end SevenEighths.ProbeRowRadicalConductor

end

end OAI
end OAIOriginalModule1857

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedProduct
Source SHA256: fd52fd26a390c14a23ad75345a7dcf6fb3db68a30aa0a793aff726834fd8fa42
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1858



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

def markExclusions (S : Finset (Ideal O)) (T : Finset PrimeIdeal) : Finset (Ideal O) :=
  S∪T.image Subtype.val

theorem markExclusions_prime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · exact hS P hP
  · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property

@[simp] theorem mem_markExclusions (S : Finset (Ideal O)) (T : Finset PrimeIdeal) (P : PrimeIdeal) :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (h|⟨Q,hQ,he⟩)
    · exact Or.inl h
    · exact Or.inr ((Subtype.ext he : Q=P) ▸ hQ)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨P,h,rfl⟩

theorem markedRowSeries_eq_finite_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then idealRowMarkedLocalFactor η u P x w z else 1
  have hR : HasProd R (∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hP : P∈T
    · rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP)),
        selectedRowLocal_outside S hS T η u P (hT P hP) x w z hx hw hz,ite_eq_left hP]
      simp only [R,ite_eq_left hP,one_mul]
    · simp only [R,ite_eq_right hP,mul_one,markedLocal,one_mul]
      change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
      rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedRowSeries_hasProd S hS T η u x w z hx hw hz).unique he'

theorem markedRowSeries_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let S' := markExclusions S T
    let hS' := markExclusions_prime S hS T
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S' hS') (6*z)*LFunction (rowCharacter S' hS' u) w/
        LFunction ((targetRow η u).excludePrimes S' hS') x*globalCorrection S' η u x w z)*
        ∏P∈T,idealRowMarkedLocalFactor η u.val P x w z := by
  dsimp only
  rw [markedRowSeries_eq_finite_replacement S hS T hT η u.val x w z hx hw hz,
    high_L_factorization (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1858

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedNormalization
Source SHA256: 8bb1a2924f7a5291da818a139010492b9c9cd7ed2e2a20de1968c1151470df70
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1859


namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def localNormalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

theorem localCorrection_eq_normalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localCorrection η u P x w z=idealRowHighLocalFactor η u.val P.val x w z*
      localNormalization η u P x w z := by
  unfold localCorrection localNormalization
  ring

lemma lift_outside_hasProd (S : Finset (Ideal O)) (f : PrimeIdeal→ℂ) (a : ℂ)
    (h : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>f P.val) a) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else f P) a := by
  have hh := (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal | P.val∉S}) (f:=f)).mp h
  convert hh using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem localNormalization_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else localNormalization η u P x w z)
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x) := by
  apply lift_outside_hasProd
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz)
  have hW := (rowCharacter_hasProd S hS hbad u w hw).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw)
  have hD := targetRow_hasProd S hS hbad η u x hx
  simpa only [localNormalization,inv_inv,div_eq_mul_inv] using (hZ.mul hW).mul hD

theorem markedRowSeries_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z*
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x)=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hleft := (markedRowSeries_hasProd S hS T η u.val x w z hx hw hz).mul
    (localNormalization_hasProd S hS hbad η u x w z hx1 hw1 hz1)
  have hbase := lift_outside_hasProd (markExclusions S T) (fun P=>localCorrection η u P x w z) _
    (globalCorrection_multipliable (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).hasProd
  let R := fun P : PrimeIdeal=>if P∈T then markedLocalCorrection η u P x w z else 1
  have hR : HasProd R (∏P∈T,markedLocalCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,markedLocal T completedValuationMark (excludedRowPrimeTerm S η u.val x w z) P b)*
        (if P.val∈S then 1 else localNormalization η u P x w z)=
      (if P.val∈markExclusions S T then 1 else localCorrection η u P x w z)*R P := by
    by_cases hP : P∈T
    · rw [selectedRowLocal_outside S hS T η u.val P (hT P hP) x w z hx hw hz,
        ite_eq_left hP,ite_eq_right (hT P hP),ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP))]
      simp only [R,ite_eq_left hP,one_mul,markedLocalCorrection]
    · simp only [markedLocal,ite_eq_right hP,one_mul,R,mul_one]
      change (∑'b : HighValuation,markedIdealHighSummand S 1 η u.val x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*_=_
      rw [excludedRowHighLocalFactor S hS η u.val x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
      by_cases hPS : P.val∈S
      · simp only [ite_eq_left hPS,one_mul]
      · simp only [ite_eq_right hPS,localCorrection_eq_normalization]
  have hright := hbase.mul hR
  apply hleft.unique
  convert hright using 1
  · funext P
    exact heq P
  · rfl

theorem markedRowSeries_original_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [←markedRowSeries_normalized S hS hbad T hT η u x w z hx hw hz]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1859

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FiniteNormalization
Source SHA256: 35060fe8342a6893577fc091838a308603cacb5a1a8a44fcc84dae548ca23706
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1860


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def globalNormalization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
    (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x

theorem globalNormalization_finite_split (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    globalNormalization S hS η u x w z=
      globalNormalization (markExclusions S T) (markExclusions_prime S hS T) η u x w z*
        ∏P∈T,localNormalization η u P x w z := by
  have hleft := localNormalization_hasProd S hS hbad η u x w z hx hw hz
  have hbase := localNormalization_hasProd (markExclusions S T) (markExclusions_prime S hS T)
    (hbad.trans Finset.subset_union_left) η u x w z hx hw hz
  let R := fun P : PrimeIdeal=>if P∈T then localNormalization η u P x w z else 1
  have hR : HasProd R (∏P∈T,localNormalization η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hleft.unique
  convert hbase.mul hR using 1
  · funext P
    by_cases hP : P∈T
    · simp only [ite_eq_right (hT P hP),mem_markExclusions,hP,or_true,ite_true,R,ite_eq_left hP,one_mul]
    · simp only [mem_markExclusions,hP,or_false,R,ite_eq_right hP,mul_one]
  · rfl

theorem finite_replacement_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (g : PrimeIdeal→ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (markedIdealHighSeries (markExclusions S T) 1 η u.val x w z*∏P∈T,g P)*
      globalNormalization S hS η u x w z=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,g P*localNormalization η u P x w z := by
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  rw [globalNormalization_finite_split S hS hbad T hT η u x w z (by linarith) (by linarith) hz1,
    globalCorrection,(localCorrection_hasProd (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).tprod_eq,
    Finset.prod_mul_distrib,globalNormalization]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1860

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Unramified
Source SHA256: 7bcd7958c7f9f33e72a86fb0c48ea390d930a4272f0f7c612dde487e65f620a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1861



namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem localCorrection_coordinates (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u.val)
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z *
        (1-coordV Q z)*(1-coordW Q rho w)/(1-coordD Q (targetMonoid η p) rho x) := by
  dsimp only
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  unfold localCorrection coordV coordW coordD
  simp only [CubicEisenstein.fullIdealWeight,hP0,ite_false,Complex.ofReal_natCast]
  rw [idealCoeff_span η hp.ne_zero,idealRowHom_prime u.val (Ideal.span {p}) hg]
  rw [show -(6*z)=(-6 : ℂ)*z by ring]
  rfl

theorem localCorrection_unramified (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (hu : IsCoprime u.val p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      actualUnramifiedClosed η p u.val hg x w z := by
  rw [localCorrection_coordinates η u p hp hg]
  rw [idealRowHighLocalFactor_unramified η p hp hg hc hprimary hs u.val hu x w z hx hw hz]
  have hgeom := row_initial_geometric η p hp hg hc u.val hu x w z hx hw hz
  dsimp only at hgeom
  have hV := one_sub_ne_zero_of_norm_lt_one _ hgeom.1
  have hW := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.1
  have hD := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.2
  unfold actualUnramifiedClosed
  change _=unramifiedClosed _ _ (targetMonoid η p) _ x w z
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1861

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Ideal
Source SHA256: a9a8f8dc102822a4293979612b584be9325eb4a01c16147e2b3bdef627490b66
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1862



namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

theorem localCorrection_unramified_ideal (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by rw [hspan]; exact hcop)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

theorem localCorrection_outside_unramified (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (hP : P.val∉S) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z :=
  localCorrection_unramified_ideal η u P (outside_prime_supported S hbad P hP) hcop x w z hx hw hz

theorem localCorrection_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    localCorrection η u P x w z=
      idealRowHighLocalFactor η u.val P.val x w z*(1-CubicEisenstein.fullIdealWeight (6*z) P.val) := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  have hr : idealRowHom u.val P.val=0 := idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu
  simp only [localCorrection,hr,map_zero,mul_zero,zero_mul,sub_zero,mul_one,div_one]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1862

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Ramified
Source SHA256: 14578f8c697837766554b8785707efb24a5df290a387b83f3cfcc88f15a3da6f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1863




namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def ramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x w z (multiplicity p u.val)

theorem ramifiedCorrection_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (19/20 : ℝ)≤w.re) (hz : (33/200 : ℝ)≤z.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz _

theorem localCorrection_eq_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hPu : P.val∣Ideal.span {u.val})
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hdiv : p∣u.val := Ideal.span_singleton_le_span_singleton.mp
    (by rw [hspan]; exact Ideal.dvd_iff_le.mp hPu)
  have hj0 : multiplicity p u.val≠0 := ne_of_gt (multiplicity_pos_of_dvd hdiv
    (FiniteMultiplicity.of_prime_left hp u.property.1))
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  dsimp only at hgeom
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    have hpos : (0 : ℝ)<Ideal.absNorm (Ideal.span {p}) :=
      HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
    have he := evenRatio_eq_coordR _ hpos (actualACube η p) x z
    simp only [Complex.ofReal_natCast] at he
    rw [he]
    exact hgeom.2.1
  rw [localCorrection_ramified η u P hPu,←hspan,
    idealRowHighLocalFactor_canonical η u p hp hg.1 hg.2 hprimary hsp]
  have he := sourceRowSeries_ramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p) _ x w z hρ hgeom.1 hR
    hgeom.2.2.1 (multiplicity p u.val) hj0 (multiplicity_lt_six u p hp)
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  convert he using 1
  · simp only [sourceRowSeries,CubicEisenstein.fullIdealWeight,
      hP0,ite_false,Complex.ofReal_natCast,coordV]
    rw [show -(6*z)=(-6 : ℂ)*z by ring]
  · rfl

def ramifiedPrimes (S : Finset (Ideal O)) (u : FreeRow) : Finset PrimeIdeal :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).filter (fun P => P.val∉S)

theorem ramified_product_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1863

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Product
Source SHA256: 87d374b4ce7333ce7a602dfc626ee7667231fef148978221a6683ed301efafa4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1864


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

def unramifiedFactor (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

theorem unramifiedFactor_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedFactor η u P x w z-1‖≤globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply unramifiedClosed_open_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz

theorem unramifiedProduct_defect (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem unramifiedProduct_multipliable (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem unramifiedProduct_analytic_x (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>unramifiedProduct S η u x w z) {x : ℂ | 7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_x
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hz
  · intro P x hx
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem unramifiedProduct_analytic_w (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>unramifiedProduct S η u x w z) {w : ℂ | 9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_w
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
      · exact hz
  · intro P w hw
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem unramifiedProduct_analytic_z (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>unramifiedProduct S η u x w z) {z : ℂ | 4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ => if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [ite_eq_right h]
      apply unramifiedClosed_analytic_z
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
  · intro P z hz
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1864

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Continuation
Source SHA256: 611130c5828aba5c9fb5f604af8bd15ce55b8fba1d57e5ae61769a184a18091d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1865



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

lemma actualACube_norm_le (η : Character) (p : O) : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

theorem ramifiedCorrection_analytic_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | 7/8<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_analytic_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_analytic_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 4/25<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

theorem continuedCorrection_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro S hS η u x w z hx hw hz
  have hR := hbound S hS η u x w z hx hw hz
  have hU := unramifiedProduct_defect S hS.tail η u x w z hx (by linarith) (by linarith)
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1 : ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_analytic_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>continuedCorrection S hS η u x w z) {x : ℂ | 7/8<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_x S hS.tail η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) w z hz

theorem continuedCorrection_analytic_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>continuedCorrection S hS η u x w z) {w : ℂ | 9/10<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_w S hS.tail η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x z hx hz).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt _)

theorem continuedCorrection_analytic_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>continuedCorrection S hS η u x w z) {z : ℂ | 4/25<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_z S hS.tail η u x w hx hw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w hx

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1865

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Agreement
Source SHA256: d3fbdbeae80d4d075ef3a7a52e1714c71ae5e764aa921ac566bb1da8026173b0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1866


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow) : Finset {P : PrimeIdeal // P.val∉S} :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).subtype (fun P => P.val∉S)

theorem mem_ramifiedIndices (S : Finset (Ideal O)) (u : FreeRow)
    (P : {P : PrimeIdeal // P.val∉S}) : P∈ramifiedIndices S u ↔ P.val.val∣Ideal.span {u.val} := by
  simp only [ramifiedIndices,Finset.mem_subtype,SmoothMobiusCorrection.mem_primeSet,
    IdealMobiusDivisorSum.primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (show (Ideal.span {u.val}:Ideal O)≠0 from Ideal.span_singleton_eq_bot.not.mpr u.property.1),
    P.val.property,true_and]

def ramifiedFactor (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (P : {P : PrimeIdeal // P.val∉S}) (x w z : ℂ) : ℂ :=
  if P.val.val∣Ideal.span {u.val} then
    ramifiedCorrection η u P.val (outside_prime_supported S hS.bad P.val P.property) x w z else 1

theorem ramifiedFactor_hasProd (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    HasProd (fun P =>ramifiedFactor S hS η u P x w z) (ramifiedProduct S hS η u x w z) := by
  have he : (∏ P∈ramifiedIndices S u,ramifiedFactor S hS η u P x w z)=
      ramifiedProduct S hS η u x w z := by
    unfold ramifiedProduct
    apply Finset.prod_bij (fun P hP =>
      (⟨P.val,Finset.mem_filter.mpr ⟨Finset.mem_subtype.mp hP,P.property⟩⟩ : ramifiedPrimes S u))
    · intro P hP; exact Finset.mem_attach _ _
    · intro P hP Q hQ heq
      exact Subtype.ext (congrArg (fun R : ramifiedPrimes S u => R.val) heq)
    · intro P hP
      refine ⟨⟨P.val,(Finset.mem_filter.mp P.property).2⟩,?_,?_⟩
      · exact Finset.mem_subtype.mpr (Finset.mem_filter.mp P.property).1
      · rfl
    · intro P hP
      simp only [ramifiedFactor,ite_eq_left ((mem_ramifiedIndices S u P).mp hP)]
  rw [←he]
  apply hasProd_prod_of_ne_finset_one
  intro P hP
  exact ite_eq_right (fun hd => hP ((mem_ramifiedIndices S u P).mpr hd))

theorem supported_prime_coprime (P : PrimeIdeal) (hs : Supported P.val) (u : O)
    (hn : ¬P.val∣Ideal.span {u}) : IsCoprime P.val (Ideal.span {u}) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have he : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  have hnot : ¬p∣u := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←he,Ideal.span_singleton_le_span_singleton]
    exact hd
  rw [←he,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr hnot

theorem continuedCorrection_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCorrection S hS η u x w z=globalCorrection S η u x w z := by
  have hr := ramifiedFactor_hasProd S hS η u x w z
  have hu := (unramifiedProduct_multipliable S hS.tail η u x w z
    (by linarith) (by linarith) (by linarith)).hasProd
  have he := hr.mul hu
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ramifiedFactor S hS η u P x w z*unramifiedFactor η u P.val x w z=
        localCorrection η u P.val x w z := by
    have hs := outside_prime_supported S hS.bad P.val P.property
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simp only [ramifiedFactor,unramifiedFactor,ite_eq_left h,mul_one]
      exact (localCorrection_eq_ramified η u P.val hs h x w z hx hw hz).symm
    · simp only [ramifiedFactor,unramifiedFactor,ite_eq_right h,one_mul]
      exact (localCorrection_unramified_ideal η u P.val hs
        (supported_prime_coprime P.val hs u.val h) x w z hx hw hz).symm
  have hh : HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (continuedCorrection S hS η u x w z) := by
    simpa only [hlocal,continuedCorrection,unramifiedProduct] using he
  exact hh.tprod_eq.symm

theorem high_L_factorization_continued (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w /
        LFunction ((targetRow η u).excludePrimes S hS.prime) x*continuedCorrection S hS η u x w z := by
  rw [continuedCorrection_eq_initial S hS η u x w z hx hw hz]
  exact high_L_factorization S hS.prime hS.bad η u x w z hx hw hz

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1866

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstTail
Source SHA256: 6bdd82394b7156566a7413444aa3d5188dd0df400f8cbe3e662d980de0d1035d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1867



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

def firstPrimeDefectBound (eps : ℝ) (P : PrimeIdeal) : ℝ :=
  240*(P.val.absNorm : ℝ)^(-1-min eps (1/50:ℝ))

theorem firstPrimeDefectBound_nonneg (eps : ℝ) (P : PrimeIdeal) :
    0≤firstPrimeDefectBound eps P := by unfold firstPrimeDefectBound; positivity

theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
    Summable (firstPrimeDefectBound eps) := by
  have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    have hm : 0<min eps (1/50:ℝ) := lt_min heps (by norm_num)
    linarith
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
  unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp only [Complex.neg_re,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  congr 2
  ring

structure FirstTail (eps : ℝ) (S : Finset (Ideal O)) : Prop where
  positive : 0<eps
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤P.val.absNorm
  small : (∑' P : {P : PrimeIdeal // P.val∉S},firstPrimeDefectBound eps P.val)≤1/6

theorem FirstTail.summable {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val) :=
  (firstPrimeDefectBound_summable eps h.positive).subtype _

theorem FirstTail.half {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S)
    (P : {P : PrimeIdeal // P.val∉S}) : firstPrimeDefectBound eps P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>firstPrimeDefectBound_nonneg eps Q.val)
  linarith [h.small]

theorem exists_first_cutoff (eps : ℝ) (heps : 0<eps) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset (Ideal O),
      (∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S) → FirstTail eps S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (firstPrimeDefectBound eps))).2
    (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>P.val.absNorm))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>P.val.absNorm) hm).trans
      (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  refine ⟨heps,?_,?_⟩
  · intro P hP
    have hn : ¬P.val.absNorm≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>firstPrimeDefectBound_nonneg eps P.val) (fun _=>le_rfl)
      ((firstPrimeDefectBound_summable eps heps).subtype _)
      ((firstPrimeDefectBound_summable eps heps).subtype _)

theorem exists_both_source_exclusions (eps : ℝ) (heps : 0<eps)
    (S₀ : Finset (Ideal O)) (hp : ∀P∈S₀,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S₀) :
    ∃S : Finset (Ideal O),S₀⊆S ∧ SourceExclusions S ∧ FirstTail eps S := by
  obtain ⟨N₁,hN₁,hcut₁⟩ := exists_uniform_global_cutoff
  obtain ⟨N₂,hN₂,hcut₂⟩ := exists_first_cutoff eps heps
  let N := max N₁ N₂
  let S := S₀∪smallPrimeSet N
  have hpS : ∀P∈S,Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  have hcut : ∀P : PrimeIdeal,P.val.absNorm≤N → P.val∈S := by
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
  refine ⟨S,Finset.subset_union_left,⟨hpS,hbad.trans Finset.subset_union_left,?_⟩,?_⟩
  · exact hcut₁ S (fun P hP=>hcut P (hP.trans (le_max_left _ _)))
  · exact hcut₂ S (fun P hP=>hcut P (hP.trans (le_max_right _ _)))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1867

/-! Original module: OAI.NumberTheory.DirichletL.ParametersFixedSource
Source SHA256: 01fb197c3353d800ef80bc77d56ee3e27a09baab98f22c59ec23db235e901637
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1868




namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.Parameters
open ProbePhysical ProbeHighRowFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma fixed_bad_primes_prime : ∀ P∈fixedBadPrimes,Prime P := by
  intro P hP
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:O)≠0))
      twoIdeal_maximal.isPrime

theorem exists_fixed_source (e : ℝ) (he : 0<e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
    ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
      FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal) := by
  obtain ⟨S,hsub,hS,hfirst⟩ := exists_both_source_exclusions (4*e) (by positivity)
    (S₀∪fixedBadPrimes)
    (fun P hP => (Finset.mem_union.mp hP).elim (hS₀ P) (fixed_bad_primes_prime P))
    Finset.subset_union_right
  refine ⟨S,Finset.subset_union_left.trans hsub,hS,hfirst,?_⟩
  intro P hP
  exact (Ideal.isPrime_of_prime (hS.prime P hP)).isMaximal (hS.prime P hP).ne_zero

theorem exists_fixed_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w⊆Set.Ioo 1 2 ∧ tsupport w⊆Set.Ioi 0 ∧
    (∀x,0≤w x ∧ w x≤1) ∧ w≠0 ∧ (∀x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W⊆Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,W,hw,hc,hs,hb,hv,hn,he,hWn,hWs,hr,hp⟩ := exists_probe_window
  refine ⟨w,W,hw,hc,hs,?_,hb,hn,he,hWn,hWs,hr,hp⟩
  have hcl : tsupport w⊆Set.Icc 1 2 :=
    closure_minimal (hs.trans Set.Ioo_subset_Icc_self) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hcl hx).1
end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule1868

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstProduct
Source SHA256: 36590e3e214dde13bfd4f9016dc480732387be3c4bda7c246f8e562210bebeaf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1869


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedFactor_first_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_defect (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw) hS.half hS.small

theorem unramifiedProduct_first_multipliable (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1869

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstAnalytic
Source SHA256: 9adea125a5b73448e9f5c140691e7c99ca2e3f51dba25f3daaadce0c4177c20c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1870



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedProduct_first_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedProduct S η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (51/100:ℝ) (1+eps-w.re)<x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)<x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (51/100:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedProduct S η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(1/100:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(1/100:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedProduct S η u x w z) {z : ℂ | (17/50:ℝ)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=>if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [ite_eq_right h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (17/50:ℝ)<z.re at hz
      change (1/3:ℝ)<z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1870

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation
Source SHA256: f3c30b77cfc2cd3221c34dc6da38b954d5a048a596a3bcbd0c0277e3e5a7d686
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1871




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem ramifiedCorrection_first_analytic_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (1/3 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | 1/2<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_first_analytic_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2 : ℝ)≤x.re) (hz : (1/3 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_first_analytic_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : (1/2 : ℝ)≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 1/3<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

theorem ramifiedCorrection_first_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (51/100 : ℝ)≤x.re) (hw : -(1/100 : ℝ)≤w.re) (hz : (17/50 : ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_first_region_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz hxw _ (multiplicity_lt_six u p hp)

theorem ramified_product_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100 : ℝ)≤x.re → -(1/100 : ℝ)≤w.re → (17/50 : ℝ)≤z.re → 1≤x.re+w.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz hxw
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_first_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz hxw
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

theorem continuedCorrection_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      1+eps≤x.re+w.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_first_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro eps S hS hfirst η u x w z hx hw hz hxw
  have hR := hbound S hS η u x w z hx hw hz (by linarith [hfirst.positive])
  have hU := unramifiedProduct_first_defect eps S hfirst η u x w z hx hz hw hxw
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_first_analytic_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>continuedCorrection S hS η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_x eps S hfirst η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)).mono
  intro x hx
  change max (51/100:ℝ) (1+eps-w.re)<x.re at hx
  have hh := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
  change (1/2:ℝ)<x.re
  linarith

theorem continuedCorrection_first_analytic_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>continuedCorrection S hS η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_w eps S hfirst η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd (Complex.isOpen_re_gt _)

theorem continuedCorrection_first_analytic_z (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>continuedCorrection S hS η u x w z) {z : ℂ | (17/50:ℝ)<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_z eps S hfirst η u x w hx hw hxw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)).mono
  intro z hz
  change (17/50:ℝ)<z.re at hz
  change (1/3:ℝ)<z.re
  linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1871

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstNeighborhood
Source SHA256: 6f50ca4dbe9ee1aa32d1a25c8cc6da59b7f0ffc97b6313b65176be68f4462d9e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1872



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedFactor_first_neighborhood_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_neighborhood_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_neighborhood_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(3/200:ℝ)≤w.re) (hz : (27/80:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedProduct S η u x w z)
      {x : ℂ | max (101/200:ℝ) (1+eps-w.re)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (101/200:ℝ) (1+eps-w.re)<x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)<x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (101/200:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedProduct S η u x w z)
      {w : ℂ | max (-(3/200:ℝ)) (1+eps-x.re)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(3/200:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(3/200:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (101/200:ℝ)≤x.re) (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedProduct S η u x w z) {z : ℂ | (27/80:ℝ)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=>if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [ite_eq_right h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (27/80:ℝ)<z.re at hz
      change (1/3:ℝ)<z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1872

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Series
Source SHA256: d08bcfae4c8d44c9f0902c2867a43fa0da58127559241110e05754211ca8f044
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1873



namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
      continuedCorrection S hS η u x w z

theorem continuedSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx; linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx; linarith
  rw [continuedSeries,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    high_L_factorization_continued S hS η u x w z hx hw hz,div_eq_mul_inv]

theorem continuedSeries_differentiableAt_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)<x.re) (hbeta : HeckeZeroSupremum.beta<x.re)
    (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x =>continuedSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_analytic_x S hS η u w z hw hz) x hx).differentiableAt

theorem continuedSeries_differentiableAt_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)<w.re) (hz : (4/25 : ℝ)≤z.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w =>continuedSeries S hS η u x w z) w := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  exact (((LFunction_differentiableAt (rowCharacter S hS.prime u) hw0 hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_analytic_w S hS η u x z hx hz) w hw).differentiableAt

theorem continuedSeries_differentiableAt_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)<z.re)
    (hpole : 6*z≠1) :
    DifferentiableAt ℂ (fun z =>continuedSeries S hS η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.mul_re] at he
    linarith
  exact ((((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hpole)).comp z
    (differentiableAt_id.const_mul 6)).mul_const _).mul_const _).mul
      ((continuedCorrection_analytic_z S hS η u x w hx hw) z hz).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1873

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Origin
Source SHA256: 92338975365e40d1ddec35b9a0c980545f21916886432cb0127ea2ac4feb75e0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1874




namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def continuedHighSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

theorem continuedHighSeries_eq_series (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) (hw0 : w≠0) (hw1 : w≠1) :
    continuedHighSeries S hS η u x w z=continuedSeries S hS η u x w z := by
  rw [continuedHighSeries,HeckeOrigin.continued_eq _ hw0 hw1,continuedSeries]

theorem continuedHighSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedHighSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw; linarith
  rw [continuedHighSeries_eq_series S hS η u x w z hw0 hw1,
    continuedSeries_eq_initial S hS η u x w z hx hw hz]

theorem continuedHighSeries_first_differentiableAt_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : max (-(1/100:ℝ)) (1+eps-x.re)<w.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_first_analytic_w eps S hS hfirst η u x z hx hz) w hw).differentiableAt

theorem continuedHighSeries_first_differentiableAt_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hx : max (51/100:ℝ) (1+eps-w.re)<x.re)
    (hbeta : HeckeZeroSupremum.beta<x.re) :
    DifferentiableAt ℂ (fun x=>continuedHighSeries S hS η u x w z) x := by
  exact ((HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _).mul
    ((continuedCorrection_first_analytic_x eps S hS hfirst η u w z hw hz) x hx).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1874

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstBoundary
Source SHA256: 33f0229ec0e963c3ed443961e378fd5d943fa5719ecc471d796e1224c2ec32ec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1875



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem continuedCorrection_first_boundary_x (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun x=>continuedCorrection S hS η u x w z) x := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_x (eps/2) S hfirst
    η u w z (by linarith) (by linarith)) x (by change max (101/200:ℝ) (1+eps/2-w.re)<x.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)) x (by change (1/2:ℝ)<x.re; linarith)

theorem continuedCorrection_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun w=>continuedCorrection S hS η u x w z) w := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_w (eps/2) S hfirst
    η u x z (by linarith) (by linarith)) w (by change max (-(3/200:ℝ)) (1+eps/2-x.re)<w.re; exact max_lt (by linarith) (by linarith)))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact ((ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd
      (isOpen_univ : IsOpen (Set.univ : Set ℂ))) w (Set.mem_univ w)

theorem continuedCorrection_first_boundary_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun z=>continuedCorrection S hS η u x w z) z := by
  apply AnalyticAt.mul _ ((unramifiedProduct_first_neighborhood_analytic_z (eps/2) S hfirst
    η u x w (by linarith) (by linarith) (by linarith)) z (by change (27/80:ℝ)<z.re; linarith))
  apply Finset.analyticAt_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)) z (by change (1/3:ℝ)<z.re; linarith)

theorem continuedHighSeries_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    (continuedCorrection_first_boundary_w eps heps S hS hfirst η u x w z hx hw hz hxw).differentiableAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1875

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions
Source SHA256: c5a50d801a7bef905dd7a6d8c76fbdda27db8a4c53f4d7952233fee5ce18775e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1876



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical
local notation "O" => HeckeFamily.O

theorem correctionTail_mono {S T : Finset (Ideal O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  constructor
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>globalPrimeDefectBound_nonneg P.val)
      (fun _=>le_rfl) (globalPrimeDefectBound_summable.subtype _) hS.summable

theorem firstTail_mono {eps : ℝ} {S T : Finset (Ideal O)} (hS : FirstTail eps S) (hst : S⊆T) :
    FirstTail eps T := by
  let inc : {P : PrimeIdeal // P.val∉T}→{P : PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=>P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : PrimeIdeal // P.val∉S}=>R.val) h)
  refine ⟨hS.positive,?_,?_⟩
  · intro P hP
    exact hS.norm_four P (fun h=>hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>firstPrimeDefectBound_nonneg eps P.val)
      (fun _=>le_rfl) ((firstPrimeDefectBound_summable eps hS.positive).subtype _) hS.summable

theorem markedSourceExclusions (S : Finset (Ideal O)) (hS : SourceExclusions S) (T : Finset PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }

theorem marked_firstTail (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S) (T : Finset PrimeIdeal) :
    FirstTail eps (markExclusions S T) := firstTail_mono hS Finset.subset_union_left

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1876

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.RestoreCorrection
Source SHA256: a032269770291db813352ac13113f6d1c5e74e1a78698c3a01b4b191cd220a05
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1877




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def supportedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if hs : Supported P.val then
    if P.val∣Ideal.span {u.val} then ramifiedCorrection η u P hs x w z
    else idealUnramifiedCorrection η u P x w z
  else 1

def excludedCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∈S then 1 else supportedCorrection η u P x w z

theorem continuedCorrection_first_hasProd (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    HasProd (fun P : PrimeIdeal=>excludedCorrection S η u P x w z)
      (continuedCorrection S hS η u x w z) := by
  have hp := (ramifiedFactor_hasProd S hS η u x w z).mul
    (unramifiedProduct_first_multipliable eps S htail η u x w z hx hz hw hxw).hasProd
  have hsub : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      excludedCorrection S η u P.val x w z) (continuedCorrection S hS η u x w z) := by
    convert hp using 1
    · funext P
      have hs := outside_prime_supported S hS.bad P.val P.property
      simp only [excludedCorrection,ite_eq_right P.property,supportedCorrection,dite_eq_left hs,
        ramifiedFactor,unramifiedFactor]
      split_ifs <;> simp
    · rfl
  exact (Subtype.val_injective.hasProd_iff (fun P hP=>by
    have hm : P.val∈S := by
      by_contra hn
      exact hP ⟨⟨P,hn⟩,rfl⟩
    simp [excludedCorrection,hm])).mp hsub

theorem continuedCorrection_restore (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    continuedCorrection S hS η u x w z=
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
        ∏P∈T,supportedCorrection η u P x w z := by
  have hlarge := continuedCorrection_first_hasProd eps S hS htail η u x w z hx hz hw hxw
  have hsmall := continuedCorrection_first_hasProd eps (markExclusions S T)
    (markedSourceExclusions S hS T) (marked_firstTail eps S htail T)
    η u x w z hx hz hw hxw
  have hfinite : HasProd (fun P : PrimeIdeal=>if P∈T then supportedCorrection η u P x w z else 1)
      (∏P∈T,supportedCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T)
      (f:=fun P : PrimeIdeal=>if P∈T then supportedCorrection η u P x w z else 1)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hlarge.unique
  convert hsmall.mul hfinite using 1
  funext P
  simp only [excludedCorrection,mem_markExclusions]
  by_cases hp : P∈T
  · simp [hp,hT P hp]
  · simp [hp]

theorem continuedCorrection_restore_quotients (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re)
    (G : PrimeIdeal→ℂ) (hne : ∀P∈T,supportedCorrection η u P x w z≠0) :
    continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T,G P=continuedCorrection S hS η u x w z*
      ∏P∈T,G P/supportedCorrection η u P x w z := by
  rw [continuedCorrection_restore eps S hS htail T hT η u x w z hx hz hw hxw,
    Finset.prod_div_distrib]
  have hn : (∏P∈T,supportedCorrection η u P x w z)≠0 := Finset.prod_ne_zero_iff.mpr hne
  field_simp
end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1877

/-! Original module: OAI.NumberTheory.DirichletL.PrincipalMellinResidues
Source SHA256: 0363acf8efc10c765e7851f9030ae6fd80f82ce3917b194734d177d2bac3be24
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1878







namespace OAI

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace SevenEighths.PrincipalMellinResidues
open ProbePhysical

lemma inverse_vertical_continuous (c : ℝ) (hc : c≠0) :
    Continuous (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  have he := congrArg Complex.re h
  simp at he
  exact hc he

lemma inverse_vertical_truncated (c T : ℝ) (hc : c≠0) :
    (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) = (2*Real.arctan (T/c):ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) volume (-T) T :=
    (inverse_vertical_continuous c hc).intervalIntegrable (-T) T
  apply Complex.ext
  · have hh := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).re at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).re) =
        (fun t : ℝ => c/(c^2+t^2)) := by
      funext t
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [he, integral_div_sq_add_sq]
    simp [neg_div, Real.arctan_neg]
    ring
  · have hh := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).im at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).im) =
        (fun t : ℝ => -(t/(c^2+t^2))) := by
      funext t
      simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]
    rw [he, intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc]
    simp

lemma inverse_vertical_limit_pos (c : ℝ) (hc : 0<c) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (Real.pi:ℂ)) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne']
  have ht := Real.tendsto_arctan_atTop.comp (Filter.tendsto_id.atTop_div_const hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_vertical_limit_neg (c : ℝ) (hc : c<0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (-(Real.pi:ℂ))) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne]
  have ht := Real.tendsto_arctan_atBot.comp (Filter.tendsto_id.atTop_div_const_of_neg hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_horizontal_limit (a b p : ℝ) (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹‖ ≤ T⁻¹ * |b-a| from ?_) ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_inv]
    apply inv_anti₀ hT
    have h := Complex.abs_im_le_norm ((x:ℂ)+(ε*T)*I-p)
    simpa [abs_mul, hε, abs_of_pos hT] using h
  · simpa using (tendsto_inv_atTop_zero.mul_const |b-a|)

lemma dslope_eq_sub_pole {A F : ℂ → ℂ} {p z : ℂ} (hz : z≠p)
    (hF : F z = A z / (z-p)) :
    dslope A p z = F z - A p * (z-p)⁻¹ := by
  rw [dslope_of_ne A hz, slope, hF]
  simp only [smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

lemma dslope_vertical_truncated (A F : ℂ → ℂ) (p x T : ℝ) (hx : x≠p)
    (hF : ∀ z : ℂ, z.re = x → F z = A z / (z-p))
    (hi : Integrable (fun t : ℝ => F ((x:ℂ)+t*I))) :
    (∫ t : ℝ in -T..T, dslope A (p:ℂ) ((x:ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((x:ℂ)+t*I)) -
        A p * (∫ t : ℝ in -T..T, (((x-p:ℝ):ℂ)+t*I)⁻¹) := by
  have he (t : ℝ) : dslope A (p:ℂ) ((x:ℂ)+t*I) =
      F ((x:ℂ)+t*I) - A p * ((((x-p:ℝ):ℂ)+t*I)⁻¹) := by
    have hn : (x:ℂ)+t*I ≠ p := by
      intro h
      exact hx (by simpa using congrArg Complex.re h)
    have h := dslope_eq_sub_pole hn (hF _ (by simp))
    convert h using 1; push_cast; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable
    (((inverse_vertical_continuous (x-p) (sub_ne_zero.mpr hx)).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

lemma rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a≤b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a≤z.re ∧ z.re≤b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) -
      (∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a:ℂ)+(-T)*I) ((b:ℂ)+T*I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0:ℂ)-0+I*Vb-I*Va=0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I*Vb=I*Va by simpa using sub_eq_zero.mp hz)).symm

lemma horizontal_quotient_continuousOn (A : ℂ → ℂ) {a b p y : ℝ}
    (hab : a≤b) (hy : y≠0)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b}) :
    ContinuousOn (fun x : ℝ => A ((x:ℂ)+y*I) / ((x:ℂ)+y*I-p)) (uIcc a b) := by
  apply ContinuousOn.div
  · apply hA.continuousOn.comp (by fun_prop)
    intro x hx
    simpa [uIcc_of_le hab] using hx
  · fun_prop
  · intro x hx h
    have hh := congrArg Complex.im h
    exact hy (by simpa using hh)

lemma dslope_horizontal_limit (A F : ℂ → ℂ) {a b p : ℝ} (hab : a≤b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ε : ℝ) (hε : |ε|=1)
    (hlim : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, dslope A p ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
  have hl := hlim.sub ((inverse_horizontal_limit a b p ε hε).const_mul (A p))
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hy : ε*T≠0 := mul_ne_zero (by intro h; simp [h] at hε) hT.ne'
  have hn (x : ℝ) : (x:ℂ)+(ε*T)*I≠p := by
    intro h
    exact hy (by simpa using congrArg Complex.im h)
  have he (x : ℝ) (hx : x∈uIcc a b) := hF ((x:ℂ)+(ε*T)*I)
    (by have := (uIcc_of_le hab ▸ hx).1; simpa using this)
    (by have := (uIcc_of_le hab ▸ hx).2; simpa using this) (hn x)
  have hfi : IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(ε*T)*I)) volume a b := by
    apply ((horizontal_quotient_continuousOn A (p:=p) hab hy hA).congr ?_).intervalIntegrable
    intro x hx
    simpa using he x hx
  have hki : IntervalIntegrable (fun x : ℝ => ((x:ℂ)+(ε*T)*I-p)⁻¹) volume a b := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    exact hn x (sub_eq_zero.mp h)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hfi (hki.const_mul _)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (dslope_eq_sub_pole (hn x) (he x hx)).symm

theorem verticalIntegral_simple_pole (A F : ℂ → ℂ) {a b p : ℝ}
    (hap : a<p) (hpb : p<b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ha : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    verticalIntegral b F = verticalIntegral a F + A p := by
  have hab := hap.le.trans hpb.le
  have hnb : {z : ℂ | a≤z.re ∧ z.re≤b} ∈ 𝓝 (p:ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a<(p:ℂ).re ∧ (p:ℂ).re<b from ⟨hap,hpb⟩))
    intro z hz
    exact ⟨hz.1.le,hz.2.le⟩
  have hG := (Complex.differentiableOn_dslope hnb).mpr hA
  have haF := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbF := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have haG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((a:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((a:ℂ)+t*I)) - A p * (-(Real.pi:ℂ)))) := by
    simp_rw [dslope_vertical_truncated A F p a _ hap.ne
      (fun z hz => hF z (by simp [hz]) (by simpa [hz] using hab)
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hap.ne this)) ha]
    exact haF.sub ((inverse_vertical_limit_neg (a-p) (sub_neg.mpr hap)).const_mul (A p))
  have hbG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((b:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((b:ℂ)+t*I)) - A p * (Real.pi:ℂ))) := by
    simp_rw [dslope_vertical_truncated A F p b _ hpb.ne'
      (fun z hz => hF z (by simpa [hz] using hab) (by simp [hz])
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hpb.ne' this)) hb]
    exact hbF.sub ((inverse_vertical_limit_pos (b-p) (sub_pos.mpr hpb)).const_mul (A p))
  have hbotG := dslope_horizontal_limit A F hab hA hF (-1) (by norm_num)
    (by simpa using hbot)
  have htopG := dslope_horizontal_limit A F hab hA hF 1 (by norm_num)
    (by simpa using htop)
  have he := rectangle_limits (dslope A p) hab hG haG hbG
    (by simpa using hbotG) (by simpa using htopG)
  have he' : (∫ t : ℝ, F ((b:ℂ)+t*I)) =
      (∫ t : ℝ, F ((a:ℂ)+t*I)) + 2*(Real.pi:ℂ)*A p := by
    linear_combination -he
  unfold verticalIntegral
  rw [he']
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [mul_comm]

structure BoundaryControl (F : ℂ → ℂ) (a b : ℝ) : Prop where
  left : Integrable (fun t : ℝ => F ((a:ℂ)+t*I))
  right : Integrable (fun t : ℝ => F ((b:ℂ)+t*I))
  lower : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0)
  upper : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)

open HeckeFamily

theorem verticalIntegral_hecke (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0<a) (ha1 : a<1) (h1b : 1<b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤z.re ∧ z.re≤b})
    (hB : BoundaryControl (fun z => K z * LFunction χ z) a b) :
    verticalIntegral b (fun z => K z * LFunction χ z) =
      verticalIntegral a (fun z => K z * LFunction χ z) +
        K 1 * HeckeReciprocal.regularizedL χ 1 := by
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ z)
    (fun z => K z * LFunction χ z) ha1 h1b
    (hK.mul (HeckeOrigin.poleRemoved_entire χ).differentiableOn) ?_
    hB.left hB.right hB.lower hB.upper
  · simpa [HeckeOrigin.poleRemoved_one] using h
  · intro z hza hzb hzp
    have hz0 : z≠0 := by intro h; subst z; simp at hza; linarith
    have hz1 : z≠1 := by simpa using hzp
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    norm_num
    field_simp

theorem verticalIntegral_hecke_six (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0<a) (hap : a<1/6) (hpb : 1/6<b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤z.re ∧ z.re≤b})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) a b) :
    verticalIntegral b (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral a (fun z => K z * LFunction χ (6*z)) +
        K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 := by
  have hhol : Differentiable ℂ (fun z => HeckeOrigin.poleRemoved χ (6*z)) :=
    (HeckeOrigin.poleRemoved_entire χ).comp (differentiable_id.const_mul 6)
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ (6*z) / 6)
    (fun z => K z * LFunction χ (6*z)) hap hpb
    ((hK.mul hhol.differentiableOn).div_const 6) ?_
    hB.left hB.right hB.lower hB.upper
  · norm_num [HeckeOrigin.poleRemoved_one] at h ⊢
    exact h
  · intro z hza hzb hzp
    have hz0 : 6*z≠0 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      have : z.re=0 := by linarith
      linarith
    have hz1 : 6*z≠1 := by
      intro h
      apply hzp
      push_cast
      linear_combination h / 6
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    have hden : z-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hzp)
    push_cast
    field_simp

theorem source_w_shift (χ : Character) (K : ℂ → ℂ → ℂ) (z : ℂ) {cw : ℝ}
    (hcw : 1<cw)
    (hK : DifferentiableOn ℂ (fun w => K w z)
      {w : ℂ | 19/20≤w.re ∧ w.re≤cw})
    (hB : BoundaryControl (fun w => K w z * LFunction χ w) (19/20) cw) :
    verticalIntegral cw (fun w => K w z * LFunction χ w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction χ w) +
      K 1 z * HeckeReciprocal.regularizedL χ 1 :=
  verticalIntegral_hecke χ (fun w => K w z) (by norm_num) (by norm_num) hcw hK hB

theorem source_residue_z_shift (χ : Character) (K : ℂ → ℂ) {e : ℝ} (he : 0<e)
    (hK : DifferentiableOn ℂ K {z : ℂ | 33/200≤z.re ∧ z.re≤1/6+e})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) (33/200) (1/6+e)) :
    verticalIntegral (1/6+e) (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral (33/200) (fun z => K z * LFunction χ (6*z)) +
      K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 :=
  verticalIntegral_hecke_six χ K (by norm_num) (by norm_num) (by linarith) hK hB

lemma verticalIntegral_add (a : ℝ) (F G : ℂ → ℂ)
    (hF : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hG : Integrable (fun t : ℝ => G ((a:ℂ)+t*I))) :
