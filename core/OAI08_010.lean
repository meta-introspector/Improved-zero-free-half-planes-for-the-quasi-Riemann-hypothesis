Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2799






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hx (X:ℝ):X≤Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving (fun _=>hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=>le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSource

end

end OAI
end OAIOriginalModule2799

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly
Source SHA256: cabaa148a5c065cde2d3c792d8178bea5b027ca7a4f56aa092d57418fc129299
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2800


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssembly
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
lemma low_restrict (W:ℝ→ℂ)(bslot a b bΦ Bmask L L' Lslot lo hi Mcap d d' κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hZ:1≤Z)(hL:L'≤L)(hd:d≤d')(hC:0≤C)
    (h:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap d κ Z η₀ Q degree S C):
    PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L' Lslot lo hi
      Mcap d' κ Z η₀ Q degree S C:=by
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
  have hscale:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale) hcap hlow
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (by have hh:=diagonalControl_nonneg s.radial.profile;positivity)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0<d ∧ 0≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0<Cu ∧ 0<Cr ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap (min du dr) du κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) (min_le_left _ _) hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap (min du dr) dr κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) (min_le_right _ _) hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤s.width/4
  · left
    exact hzu.2 Lslot κ η₀ Q K hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 Lslot κ η₀ Q K hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.CenteredMomentEnergyPositiveHighAssembly

end

end OAI
end OAIOriginalModule2800

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
Source SHA256: e3e0f7f1e4f0d3bd963d6962f70f9026ba26d274767896c711ce4574b483ad62
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2801



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParameters
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma actual_width_le (hZ:1<Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1<Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤s.width:=by
  have hv:0<CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=>le_rfl)

omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤N)(hZ:1<Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0<s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=>le_rfl)
  have hconst:0≤Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst

end SevenEighths.CenteredMomentEnergyPositiveHighParameters

end

end OAI
end OAIOriginalModule2801

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission
Source SHA256: b970e995a4a232f42316d372f8f21f00b91d48509c04ee236da8e0d9fb5dd2e4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2802




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

theorem fixed_fields :
    (balancedSource).lower=aslot ∧ (balancedSource).upper=bslot ∧
    (balancedSource).b₁=b ∧ (balancedSource).b₂=b ∧
    (balancedSource).W₁=p.profile 0 ∧ (balancedSource).W₂=p.profile 1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧ (balancedSource).t=t ∧
    (∀i,(balancedSource).lo i=aslot) ∧ (∀i,(balancedSource).hi i=bslot) ∧
    (∀i,(balancedSource).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (∀i,(balancedSource).P i=Z^(w i)) := by
  repeat' constructor
  all_goals intro i;rfl

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=>le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

lemma exact_log_volume (hZ:1<Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem four_upper_scales (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    (balancedSource).X₁≤Z^L ∧ (balancedSource).X₂≤Z^L ∧
    (balancedSource).Y₁≤Z^L ∧ (balancedSource).Y₂≤Z^L := by
  have hp:0<Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
  have hxy:X₁*X₂≤volume balancedSource:=by
    change X₁*X₂≤X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

theorem four_lower_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem state_capacity_packet (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    1≤s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤s.width ∧
    volume balancedSource≤Z^s.width ∧ Real.logb Z (volume balancedSource)≤s.width ∧
    volume balancedSource≤Z^L ∧
    (s.puncture.absNorm:ℝ)≤Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI
end OAIOriginalModule2802

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded
Source SHA256: 394f0f27cf2d1604a89cdb3b167836746ef65187961d81a9bc015a2004ce0e8d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2803







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

open CenteredMomentEnergyPositiveHighSource

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e→ 0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving (fun _=>hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=>le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+e+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSourceBounded

end

end OAI
end OAIOriginalModule2803

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded
Source SHA256: 22da20ccb0e424e40f15bb58d17aaa7afb867e0e5bfe6d7705a4ea181216690a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2804




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBounded CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0<d ∧ 0≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0<Cu ∧ 0<Cr ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e→ 0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+e+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+e+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hLuUpper,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,max_le hLuUpper hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) le_rfl hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) le_rfl hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤s.width/4
  · left
    exact hzu.2 e Lslot κ η₀ Q K he hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 e Lslot κ η₀ Q K he hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBounded

end

end OAI
end OAIOriginalModule2804

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighBound
Source SHA256: 31f5f142cec0bc0cc6b5d008f5abdefbb2eddc3574dcc86fae407290a3eaddac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2805







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBounded CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

open CenteredMomentEnergyPositiveHighAssemblyBounded CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) →
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤
          Cmass*(p.control Smass)^2*(1+|t|+height)^Jmass*Z^(s.width+emass)) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|+height)^Jout*Z^(s.width+efinal) :=by
  obtain ⟨d,L,hd,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hstage⟩:=
    actual_high_source_split (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨L,hL,hLupper,Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,hbound⟩:=hstage degree S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=(profileBound Wslot hcSlot aslot bslot lo hi haslot hsSlot)^(2*Fintype.card α)
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Lslot κ η₀ Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ s hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z^(s.width+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z^(s.width+ej)≤F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej≤s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by dsimp [Jout];omega
  have hjr:Jr≤Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced|⟨hfour,hsource⟩
  · change _≤Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z^(s.width+e+ε) at hunbalanced
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        CenteredMomentAmplificationChildInput.volume inp≤Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
        (Fintype.card α) le_rfl U
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(s.width+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤c*P*A*F:=by
      calc
        _≤c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _≤c*P*A*F:=by
          calc
            _ = (c*P*A*(p.control U)^2*Z^(s.width+efinal))*1 := by ring
            _ ≤ (c*P*A*(p.control U)^2*Z^(s.width+efinal))*
                (1+|t|+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
            _ = c*P*A*F := by dsimp [F]; ring
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|+height)^Jout*Z^(s.width+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyPositiveHighBound

end

end OAI
end OAIOriginalModule2805

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound
Source SHA256: a912d66ac9d30b1d62b6993d6f060aa628c157f5c985e017cdc39b4866292055
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2806





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyPositiveHighBound CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyPositiveHighAssembly (low_restrict)
def PhysicalHighAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤state.width→
    5*state.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
    let inp:=balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂;
    (Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ/volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

def PositiveHighAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
    5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem actual_high_stage_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hrho:0<rho)(hε:0<ε)(hMcap:0≤Mcap)(hBmask:0≤Bmask)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(L Lslot κ e emass efinal:ℝ)(η₀:Character)(Q:Ideal O)(K Cphysical:ℝ),
      3/4≤κ→0≤e→0≤K→0≤Cphysical→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
        Lslot lo hi Mcap e κ Z η₀ Q degree S K→
      PhysicalHighAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ emass Z ha Ψ η₀ Q Smass Jmass Cphysical→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap efinal κ Z η₀ Q
        Jout U (Cfixed*(K+Cphysical+1)):=by
  have hfixed (T:Finset α):=actual_high_from_physical (α:=T) M H hH W aslot bslot lo hi
    haslot hWs hW a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε
    hMcap hBmask hbslot hεdiag hξ
  choose Lj hLj hLjcap Ψ hΨs hΨn hj using hfixed
  refine ⟨Ψ,hΨs,hΨn,?_⟩
  intro degree S Jmass Smass
  have hall (T:Finset α):=hj T degree S Jmass Smass
  choose Jj Uj Cj hCj hbound using hall
  let Jout:ℕ:=∑T:Finset α,Jj T
  let U:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset α):Jj T≤Jout:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hUU (T:Finset α):Uj T⊆U:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ T,hx⟩
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  have hevent:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro L Lslot κ e emass efinal η₀ Q K Cphysical hκ he hK hCphysical hefinal hmassFinal
    hdiagFinal htailFinal hlow hmass
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hlowT:=CenteredMomentEnergyLowBandSubtype.positiveLowAt_subtype (α:=α) M H hH T
    W bslot a b bΦ Bmask (Mcap+Bmask+rho/100) Lslot lo hi Mcap e κ Z η₀ Q degree S K hlow
  have hlowLj:=low_restrict (α:=T) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
    (Lj T) Lslot lo hi Mcap e e κ Z η₀ Q degree S K hZ1.le (hLjcap T) le_rfl hK hlowT
  have hphys:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo
    hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hh:=(hZ T).2 e emass efinal Lslot κ η₀ Q K Cphysical he hK hCphysical
    hefinal hmassFinal hdiagFinal htailFinal hlowLj θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ state hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcapacity hphys
  have hc:=hCC T
  have hp:=profile_control_mono p (hUU T)
  have hp0:=p.control_nonneg (Uj T)
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hpow:=pow_le_pow_right₀ hbase (hJJ T)
  have hd:=diagonalControl_nonneg state.radial.profile
  have hz:0≤Z:=zero_le_one.trans hZ1.le
  apply hh.trans
  gcongr

omit [Fintype α] [DecidableEq α] in
theorem positive_from_stages
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(J:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hold:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q J S C)
    (hlow:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C)
    (hhigh:PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hsmall:s.width≤ rho
  · exact hold T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hsmall p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hl:length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6
  · exact hlow T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity hl
  exact hhigh T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ (le_of_not_ge hsmall) hs
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity (le_of_not_ge hl)

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

end

end OAI
end OAIOriginalModule2806

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveLowBandSource
Source SHA256: 7c92ce7de0f562b727b4f00895600d2a94509793a84781db5ffdb0a708bf9aaa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2807




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PhysicalLowAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤state.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6→
    physicalMass (zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)
      state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ /
      volume (sourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical:ℝ),
      1/6≤κ→0≤Cphysical→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1))→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)):=by
  have hfixed (T:Finset α):=natural_low_source_bound (ι:=T) W hW aslot bslot lo hi
    a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ hMcap hεdiag hξ
  choose Ψ hΨs hΨn Cj hCj hbound using hfixed
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical hκ hCphysical he hsave hold hmass
  have hpositive:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cphysical+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidth
      p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    by_cases hsmall:state.width≤ rho
    · exact hold T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        state hQ hsmall p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
    have hp:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      state hQ (le_of_not_ge hsmall) hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    have hh:=(hZ T).2 M H hH η₀ θ w σ freq hw (fun i=>⟨hσlo i,hσhi i⟩)
      Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ (hcapacity.trans hwidth)
      S J Cphysical height e hCphysical hheight he hsave hp
    have hc:=hCC T
    have hd:=diagonalControl_nonneg state.radial.profile
    have hz:0≤Z:=zero_le_one.trans hZ1.le
    apply hh.trans
    gcongr
  exact ⟨hpositive,CenteredMomentEnergyLowBandEmpty.positive_low_zero (α:=α) M H hH
    W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J (insert (0,0) S)
    (Cfixed*(Cphysical+1)) hpositive⟩

end SevenEighths.CenteredMomentEnergyPositiveLowBandSource

end

end OAI
end OAIOriginalModule2807

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PositiveLowSourceControlled
Source SHA256: bc65de7ba401370cea07bbbe32a70c2770511de7b64d97c7bd2fe97e47ca8ce0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2808





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveLowBandSource (PhysicalLowAt)
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical Cprevious:ℝ),
      1/6≤κ→0≤Cphysical→0≤Cprevious→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J S Cprevious→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)+Cprevious) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)+Cprevious) :=by
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hbound⟩:=
    CenteredMomentEnergyPositiveLowBandSource.actual_low_stages_from_physical (α:=α) M H hH
      W hW aslot bslot lo hi a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ
      hMcap hεdiag hξ
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical Cprevious hκ hCphysical hCprevious he hsave hold hmass
  let Cm:=Cphysical+Cprevious/Cfixed
  have hdiv:0≤Cprevious/Cfixed:=div_nonneg hCprevious hCfixed.le
  have hCm:0≤Cm:=by dsimp [Cm];positivity
  have hcc:Cphysical≤Cm:=by dsimp [Cm];linarith
  have heq:Cfixed*(Cm+1)=Cfixed*(Cphysical+1)+Cprevious:=by
    dsimp [Cm]
    field_simp
    ; ring
  have hprev:Cprevious≤Cfixed*(Cm+1):=by
    rw [heq]
    have hh:0≤Cfixed*(Cphysical+1):=by positivity
    linarith
  have hold':PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cm+1)):=
    positiveAt_transport (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z
      a b bΦ Bmask L rho e η₀ Q J J S (insert (0,0) S) Cprevious (Cfixed*(Cm+1)) hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.subset_insert _ _)
      hCprevious hprev hold
  have hmass':PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
      a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cm:=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤Z:=zero_le_one.trans hZ.1.le
    apply hh.trans
    gcongr
  have hh:=hZ.2 Bmask L Lslot rho κ e η₀ Q S J Cm hκ hCm he hsave hold' hmass'
  simpa only [heq] using hh

end SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled

end

end OAI
end OAIOriginalModule2808

/-! Original module: OAI.NumberTheory.DirichletL.Energy.SourceInputReindexGates
Source SHA256: 7a4c485fd6ced54eeb2b4e5906baa43c21064ccca7cacd050f096da090f77d70
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2809






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSecondInputGates CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstChildProfileControl CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma mass_map (e : α≃β) (s : Input α) : mass (reindex e s)=mass s :=
  (controls_map e s).1

lemma nominal_map (e : α≃β) (s : Input α) (K : ℝ) :
    nominal (reindex e s) K=nominal s K := by
  unfold nominal
  rw [volume_map]

theorem ready_map (e : α≃β) (s : Input α) (R : Ideal O) (K Z ξ B : ℝ)
    (h : Ready s R K Z ξ B) : Ready (reindex e s) R K Z ξ B := by
  rcases h with ⟨hR0,hK,hV,hs0,hs,hq,hr,hn0,hn,hf0,hf⟩
  exact ⟨hR0,hK,by simpa only [volume_map] using hV,
    by simpa only [sourceRadius_map] using hs0,
    by simpa only [sourceRadius_map] using hs,hq,hr,
    by simpa only [nominal_map] using hn0,
    by simpa only [nominal_map] using hn,
    by simpa only [nominal_map] using hf0,
    by simpa only [nominal_map] using hf⟩

section Dictionary
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem matches_map (e : α≃β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (reindex e s) η₀
      (θ ∘ e.symm) (w ∘ e.symm) (σ ∘ e.symm) (freq ∘ e.symm) W bslot Z :=
  ⟨fun i I=>h.character (e.symm i) I,fun i y=>h.profile (e.symm i) y,
    fun i=>h.pool (e.symm i),fun i=>h.scale (e.symm i)⟩

theorem matches_child (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) W bslot Z :=
  ⟨fun i I=>h.character i.val I,fun i y=>h.profile i.val y,
    fun i=>h.pool i.val,fun i=>h.scale i.val⟩

omit [Fintype α] [Fintype β] in
theorem imageInput_matches (e : α↪β) (T : Finset α) (s : Input T) (η₀ : Character)
    (θ : T→RayQuotient.Characters M H) (w σ freq : T→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (imageInput e T s) η₀
      (θ ∘ (Finset.equivMap e T).symm) (w ∘ (Finset.equivMap e T).symm)
      (σ ∘ (Finset.equivMap e T).symm) (freq ∘ (Finset.equivMap e T).symm) W bslot Z :=
  matches_map M H hH (Finset.equivMap e T) s η₀ θ w σ freq W bslot Z h

omit [Fintype β] in
theorem allocatedImage_matches (e : α↪β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (allocatedImage e s C R B τ t) η₀
      (fun i=>θ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>w ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>σ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>freq ((Finset.equivMap e (liveIndices B.val)).symm i).val) W bslot Z :=
  imageInput_matches M H hH e (liveIndices B.val) (child s C R B τ t) η₀
    _ _ _ _ W bslot Z (matches_child M H hH s η₀ θ w σ freq W bslot Z h C R B τ t)
end Dictionary

theorem active_map (e : α≃β) (s : Input α) :
    activeInput (reindex e s)=reindex e (activeInput s) := rfl

lemma allocationLabels_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (allocationLabels s.pools C).image (tupleMap e)=
      allocationLabels (reindex e s).pools C := by
  unfold allocationLabels
  rw [←pools_map,Finset.image_image,Finset.image_image]
  congr 1

lemma actualAllocations_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (actualAllocations s.pools C).image (tupleMap e)=
      actualAllocations (reindex e s).pools C := by
  change ((allocationLabels s.pools C).filter (fun B=>finiteTupleProduct B=C)).image (tupleMap e)=
    (allocationLabels (reindex e s).pools C).filter (fun B=>finiteTupleProduct B=C)
  rw [←allocationLabels_map e s C,Finset.filter_image]
  simp only [tupleMap_product]

def allocationEquiv (e : α≃β) (s : Input α) (C : Ideal O) :
    actualAllocations s.pools C ≃ actualAllocations (reindex e s).pools C where
  toFun B := ⟨tupleMap e B.val,by
    rw [←actualAllocations_map]
    exact Finset.mem_image.mpr ⟨B.val,B.property,rfl⟩⟩
  invFun B := ⟨(tupleMap e).symm B.val,by
    have hh : B.val∈(actualAllocations s.pools C).image (tupleMap e) := by
      simpa only [actualAllocations_map e s C] using B.property
    obtain ⟨v,hv,hvB⟩:=Finset.mem_image.mp hh
    simpa only [←hvB,Equiv.symm_apply_apply] using hv⟩
  left_inv B := Subtype.ext ((tupleMap e).symm_apply_apply B.val)
  right_inv B := Subtype.ext ((tupleMap e).apply_symm_apply B.val)

@[simp] lemma allocationEquiv_val (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) :
    (allocationEquiv e s C B).val=tupleMap e B.val := rfl

def liveEquiv (e : α≃β) (B : Tuple α) : liveIndices B ≃ liveIndices (tupleMap e B) where
  toFun i := ⟨e i.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.symm_apply_apply] using (Finset.mem_filter.mp i.property).2⟩
  invFun j := ⟨e.symm j.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl]
      using (Finset.mem_filter.mp j.property).2⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

@[simp] lemma liveEquiv_val (e : α≃β) (B : Tuple α) (i : liveIndices B) :
    (liveEquiv e B i).val=e i.val := rfl

@[simp] lemma liveEquiv_symm_val (e : α≃β) (B : Tuple α)
    (j : liveIndices (tupleMap e B)) : ((liveEquiv e B).symm j).val=e.symm j.val := rfl

theorem child_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    reindex (liveEquiv e B.val) (child s C R B τ t)=
      child (reindex e s) C R (allocationEquiv e s C B) τ t := rfl

theorem child_mass_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      mass (child s C R B τ t) := by
  exact mass_map (liveEquiv e B.val) (child s C R B τ t)

theorem child_volume_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      volume (child s C R B τ t) := by
  exact volume_map (liveEquiv e B.val) (child s C R B τ t)

theorem child_normalized_map (e : α≃β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (reindex e s) C R seed (allocationEquiv e s C B) τ t W K=
      childNormalizedGaussSource s C R seed B τ t W K := by
  exact normalizedGaussSource_map (liveEquiv e B.val) (child s C R B τ t) (R*C) seed W K

theorem active_allocation_pullback (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val := by
  exact ⟨(allocationEquiv e (activeInput s) C).symm B,
    congrArg Subtype.val ((allocationEquiv e (activeInput s) C).apply_symm_apply B)⟩

omit [Fintype α] [Fintype β] in
theorem imageInput_ready (e : α↪β) (T : Finset α) (s : Input T)
    (R : Ideal O) (K Z ξ B : ℝ) (h : Ready s R K Z ξ B) :
    Ready (imageInput e T s) R K Z ξ B :=
  ready_map (Finset.equivMap e T) s R K Z ξ B h

omit [Fintype β] in
theorem allocatedImage_ready (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t K Z ξ bound : ℝ)
    (h : Ready (child s C R B τ t) (R*C) K Z ξ bound) :
    Ready (allocatedImage e s C R B τ t) (R*C) K Z ξ bound :=
  imageInput_ready e (liveIndices B.val) (child s C R B τ t) (R*C) K Z ξ bound h

omit [Fintype α] [Fintype β] in
lemma imageInput_mass (e : α↪β) (T : Finset α) (s : Input T) :
    mass (imageInput e T s)=mass s := mass_map (Finset.equivMap e T) s

omit [Fintype β] in
lemma allocatedImage_mass (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (allocatedImage e s C R B τ t)=mass (child s C R B τ t) :=
  imageInput_mass e (liveIndices B.val) (child s C R B τ t)

omit [Fintype β] in
lemma allocatedImage_volume (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (allocatedImage e s C R B τ t)=volume (child s C R B τ t) :=
  volume_map (Finset.equivMap e (liveIndices B.val)) (child s C R B τ t)

lemma source_fields_map (e : α≃β) (s : Input α) :
    (reindex e s).η=s.η ∧ (reindex e s).m=s.m ∧ (reindex e s).A=s.A ∧
    (reindex e s).t=s.t ∧ (reindex e s).W₁=s.W₁ ∧ (reindex e s).W₂=s.W₂ ∧
    (reindex e s).X₁=s.X₁ ∧ (reindex e s).X₂=s.X₂ ∧
    (reindex e s).Y₁=s.Y₁ ∧ (reindex e s).Y₂=s.Y₂ ∧
    (reindex e s).lower=s.lower ∧ (reindex e s).upper=s.upper ∧
    (reindex e s).plain₁=s.plain₁ ∧ (reindex e s).plain₂=s.plain₂ ∧
    (reindex e s).rows=s.rows ∧ (reindex e s).weight=s.weight := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem active_child_pullback (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) (τ : Character) (t : ℝ) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val ∧
      mass (child (activeInput (reindex e s)) C R B τ t)=
        mass (child (activeInput s) C R A τ t) ∧
      volume (child (activeInput (reindex e s)) C R B τ t)=
        volume (child (activeInput s) C R A τ t) ∧
      ∀(seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        childNormalizedGaussSource (activeInput (reindex e s)) C R seed B τ t W K=
          childNormalizedGaussSource (activeInput s) C R seed A τ t W K := by
  obtain ⟨A,hA⟩:=(allocationEquiv e (activeInput s) C).surjective B
  subst B
  exact ⟨A,rfl,child_mass_map e (activeInput s) C R A τ t,
    child_volume_map e (activeInput s) C R A τ t,
    fun seed W K=>child_normalized_map e (activeInput s) C R seed A τ t W K⟩

end SevenEighths.CenteredMomentEnergySourceInputReindexGates

end

end OAI
end OAIOriginalModule2809

/-! Original module: OAI.NumberTheory.DirichletL.Energy.StageMonotonicity
Source SHA256: b7ad89741fad2bfbb90b9c34ae9ddb52b9a45279ad2cf31c207518fd7bc67d56
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2810





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyStageMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentEnergyZeroGrowth
local notation "O"=>HeckeFamily.O

theorem zeroLowAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroLowAt Q a b radial mask L Mcap eps Z J S C):
    ZeroLowAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hlow
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hlow
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

theorem zeroGrowthAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroGrowthAt Q a b radial mask L Mcap eps Z J S C):
    ZeroGrowthAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(max s.width (length Z X₁+length Z X₂)+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(max s.width (length Z X₁+length Z X₂)+eps)≤Z^(max s.width (length Z X₁+length Z X₂)+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveLowAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveLowAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveLowAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlow
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

omit [Fintype α] [DecidableEq α] in
theorem positiveHighAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi rho Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' rho' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(hrho:rho≤rho')(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveHighAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi rho Mcap eps κ Z η₀ Q J S C):
    PositiveHighAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi rho' Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hrho.trans hwidthLo) (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlarge
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyStageMonotonicity

end

end OAI
end OAIOriginalModule2810

/-! Original module: OAI.NumberTheory.DirichletL.Energy.CappedSuccessorPacking
Source SHA256: 2724a7a6d99bec483ed730299e2288a6a1c6c281dae46929a53c8037f03bf43d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2811



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedSuccessorPacking
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem certified_from_stages
    (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (ez el eh:ℝ)
    (hez:ez≤stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (hel:el≤stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (heh:eh≤stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k)
    (hzero:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) ez Z J S C)
    (hlow:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1)) (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) el κ Z η₀ Q J S C)
    (hhigh:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        PositiveHighAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1)) (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) eh κ Z η₀ Q J S C):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0<reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hloss:stageLoss Mcap Bs ε k≤stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨Jold,Sold,hold⟩:=hold
  obtain ⟨Jz,Sz,hzero⟩:=hzero
  obtain ⟨Jl,Sl,hlow⟩:=hlow
  obtain ⟨Jh,Sh,hhigh⟩:=hhigh
  let J:=Jold+Jz+Jl+Jh
  let S:=Sold∪Sz∪Sl∪Sh
  have hJo:Jold≤J:=by dsimp [J];omega
  have hJz:Jz≤J:=by dsimp [J];omega
  have hJl:Jl≤J:=by dsimp [J];omega
  have hJh:Jh≤J:=by dsimp [J];omega
  have hSo:Sold⊆S:=by intro x hx;simp [S,hx]
  have hSz:Sz⊆S:=by intro x hx;simp [S,hx]
  have hSl:Sl⊆S:=by intro x hx;simp [S,hx]
  have hSh:Sh⊆S:=by intro x hx;simp [S,hx]
  refine ⟨J,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Coz,Cop,hCoz,hCop,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,hCz,hzero⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cl,hCl,hlow⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ch,hCh,hhigh⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
  let Cp:=Cop+Cl+Ch
  have hCp:0<Cp:=by dsimp [Cp];linarith
  have hCop':Cop≤Cp:=by dsimp [Cp];linarith
  have hCl':Cl≤Cp:=by dsimp [Cp];linarith
  have hCh':Ch≤Cp:=by dsimp [Cp];linarith
  refine ⟨Cz,Cp,hCz,hCp,?_⟩
  filter_upwards [hold,hzero,hlow,hhigh] with Z hold hz hl hh
  refine ⟨hold.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      Jz J Sz S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      hez hJz hSz hCz.le le_rfl hz
  · apply positive_from_stages (α:=α) M H hH W bslot _ _ _ _ _ _ _ _
      (bandWidth Mcap Bs ε k) _ _ κ Z η₀ Q J S Cp
    · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ η₀ Q Jold J Sold S Cop Cp hold.1.le
        hlower le_rfl le_rfl le_rfl hlength le_rfl hloss hJo hSo hCop.le hCop' hold.2.2
    · exact positiveLowAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ η₀ Q Jl J Sl S Cl Cp hold.1.le
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hel hJl hSl hCl.le hCl' hl
    · exact positiveHighAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ _ η₀ Q Jh J Sh S Ch Cp hold.1.le
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl heh hJh hSh hCh.le hCh' hh

end SevenEighths.CenteredMomentEnergyCappedSuccessorPacking

end

end OAI
end OAIOriginalModule2811

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroBalancedDictionary
Source SHA256: 9e7f93863d9e7e01feded2b466f706a5aedcb40ca8a64648212f5ebd271600d0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2812




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedDictionary
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyNaturalInputMatches
open CenteredMomentAmplificationChildInput CenteredMomentFirstSourceReduction
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "zeroInput"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem balanced_matches (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)
    (w σ freq:Fin 0→ℝ)(W:ℝ→ℂ)(bslot:ℝ):
    CenteredMomentAllocatedRayDictionary.Matches M H hH zeroInput η₀ θ w σ freq W bslot Z:=by
  constructor <;> intro i <;> exact Fin.elim0 i

theorem balanced_eq_positive_empty (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)
    (w σ freq:Fin 0→ℝ):
    zeroInput=CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
      (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
      (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
      s p ha t X₁ X₂ hX₁ hX₂:=by
  unfold CenteredMomentEnergyZeroReferencePhysical.balancedInput
    CenteredMomentEnergyPositiveHighSource.balancedInput input naturalInput naturalData completeInput
  congr 5 <;> exact Subsingleton.elim _ _

variable (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)(w σ freq:Fin 0→ℝ)
def positiveEmptyInput : Input (Fin 0):=
  CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
  (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
  (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
  s p ha t X₁ X₂ hX₁ hX₂

local notation "positiveInput"=>positiveEmptyInput M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq

lemma balanced_pools_eq : (zeroInput).pools=(positiveInput).pools:=
  congrArg Input.pools (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)

lemma balanced_normalized_gauss_eq (R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource zeroInput R seed W K=normalizedGaussSource positiveInput R seed W K:=
  congrArg (fun inp=>normalizedGaussSource inp R seed W K)
    (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)

lemma balanced_physical_mass_eq (R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass zeroInput R seed m A Φ K Z₀ ξ=physicalMass positiveInput R seed m A Φ K Z₀ ξ:=
  congrArg (fun inp=>physicalMass inp R seed m A Φ K Z₀ ξ)
    (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)

lemma balanced_current_source :
    (zeroInput).η=s.character ∧ (zeroInput).m=s.mask ∧ (zeroInput).t=t ∧
    (zeroInput).X₁=X₁ ∧ (zeroInput).X₂=X₂ ∧
    (zeroInput).Y₁=comparisonFirst Z s.width ∧
    (zeroInput).Y₂=comparisonSecond Z s.width X₁ X₂:=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem declared_capacity (hZ:1<Z):
    let Mdecl:=max s.width (length Z X₁+length Z X₂);
    Real.logb Z (volume zeroInput)≤Mdecl ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width ∧
    volume zeroInput≤Z^Mdecl:=by
  have hlog (X:ℝ)(hX:0<X):Real.logb Z X≤length Z X:=by
    rw [CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX]
    exact le_max_right _ _
  have hV:Real.logb Z (volume zeroInput)≤length Z X₁+length Z X₂:=by
    rw [CenteredMomentEnergyZeroReferencePhysical.balanced_volume,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact add_le_add (hlog X₁ hX₁) (hlog X₂ hX₂)
  have hdecl:=hV.trans (le_max_right s.width (length Z X₁+length Z X₂))
  refine ⟨hdecl,CenteredMomentEnergyPositiveHighParameters.actual_width_le s hZ,
    CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos zeroInput)).mp hdecl

theorem balanced_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)):
    Z^(s.width/4)≤(zeroInput).X₁ ∧ Z^(s.width/4)≤(zeroInput).X₂ ∧
    Z^(s.width/4)≤(zeroInput).Y₁ ∧ Z^(s.width/4)≤(zeroInput).Y₂:=by
  have h:=CenteredMomentEnergyOriginalHighReflectionSymmetric.balanced_four_scale_gates
    Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

lemma declared_capacity_upper (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal):
    max s.width (length Z X₁+length Z X₂)≤max Mcap (2*Lgoal):=by
  have hlen (X:ℝ)(hcap:X≤Z^Lgoal):length Z X≤Lgoal:=by
    unfold length
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mpr
      (max_le (Real.one_le_rpow hZ.le hL) hcap)
  exact max_le_max hs (by linarith [hlen X₁ hc₁,hlen X₂ hc₂])

end SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

end

end OAI
end OAIOriginalModule2812

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroBalancedAdmission
Source SHA256: b376d49d6288252bb1f60ff759035e9f84d3f63f8b7d5bf37f91453d32520919
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2813



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedAdmission
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyReferenceState CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyOriginalProfileControl CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "inp"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem fixed_fields :
    (inp).lower=1 ∧ (inp).upper=1 ∧
    (inp).b₁=b ∧ (inp).b₂=b ∧
    (inp).W₁=p.profile 0 ∧ (inp).W₂=p.profile 1 ∧
    (∀i,(inp).lo i=1) ∧ (∀i,(inp).hi i=1) ∧
    (∀i,(inp).M i≤1) ∧ Fintype.card (Fin 0)=0 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,by simp⟩
  all_goals intro i; exact Fin.elim0 i

lemma lower_product : 0<a*a ∧ (∏i,(inp).lo i)*a*a=a*a := by
  exact ⟨mul_pos ha ha,by simp⟩

lemma profile_control (S:Finset (ℕ×ℕ)) :
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (p.control (insert (0,0) S))^2 := by
  simpa using plain_control_sq_le inp p S 0 1 (by norm_num)
    (by simp) (fun i=>Fin.elim0 i)

lemma source_factor (hZ:1<Z) :
    sourceFactor inp a a s.radial.scale≤
      (Real.exp (Real.log 4)*fixedPresentationCost/(a*a))*Z^s.width := by
  have hK:0<s.radial.scale:=s.radial.scale_pos
  have hh:=source_factor_le inp 0 1 a s.radial.scale (by norm_num) ha hK
    (by simp) (fun i=>Fin.elim0 i)
  simp only [pow_zero,one_mul] at hh
  have hcap:=CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ
  have hc:0≤Real.exp (Real.log 4)*fixedPresentationCost/(a*a):=by
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le fixedPresentationCost_pos.le)
      (mul_pos ha ha).le
  apply hh.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hcap hc

theorem four_upper_scales (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    (inp).X₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).X₂≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₂≤Z^(max Mcap (2*Lgoal)) := by
  have hLg:Lgoal≤max Mcap (2*Lgoal):=by linarith [le_max_right Mcap (2*Lgoal)]
  have hp:0<Z:=zero_lt_one.trans hZ
  have hquarter:0≤s.width/4:=div_nonneg s.width_nonneg (by norm_num)
  have hY₁:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le hquarter
  refine ⟨hc₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),
    hc₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),?_,?_⟩
  · change Z^(s.width/4)≤_
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [s.width_nonneg,le_max_left Mcap (2*Lgoal)]
  · change X₁*X₂/comparisonFirst Z s.width≤_
    calc
      _≤X₁*X₂:=div_le_self (mul_pos hX₁ hX₂).le hY₁
      _≤Z^Lgoal*Z^Lgoal:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_pos_of_pos hp _).le
      _=Z^(2*Lgoal):=by rw [←Real.rpow_add hp];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_right _ _)

theorem capacity_packet (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    let Mdecl:=max s.width (length Z X₁+length Z X₂)
    0≤Mdecl ∧ Mdecl≤max Mcap (2*Lgoal) ∧
    volume inp≤Z^Mdecl ∧ volume inp≤Z^(max Mcap (2*Lgoal)) ∧
    1≤s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width := by
  have hd:=CenteredMomentEnergyZeroBalancedDictionary.declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hu:=CenteredMomentEnergyZeroBalancedDictionary.declared_capacity_upper s X₁ X₂ Mcap Lgoal hZ hL hs hc₁ hc₂
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨s.width_nonneg.trans (le_max_left _ _),hu,hd.2.2.2,
    hd.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hu),hr.1,hr.2.1,hd.2.1,hd.2.2.1⟩

end SevenEighths.CenteredMomentEnergyZeroBalancedAdmission

end

end OAI
end OAIOriginalModule2813

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthHighBound
Source SHA256: 09eb74be3fdb4b88d07720c1e08af8b13f6622d768d88bdaead64e0d0fb41bd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2814







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyOriginalProfileControl
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

lemma low_restrict (Q:Ideal O)(a b bΦ Bmask L L' Mcap e Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(K:ℝ)(hZ:1≤Z)(hL:L'≤L)
    (h:ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K):
    ZeroLowAt Q a b bΦ Bmask L' Mcap e Z degree S K:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hL
  exact h s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hp) (hc₂.trans hp) hl

theorem actual_high_from_physical
    (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroLowAt Q a b bΦ Bmask (Mcap+Bmask+rho/100) Mcap e Z degree S K→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B→
      5*s.width/6≤length Z X₁+length Z X₂→
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
          Cmass*(p.control Smass)^2*(1+|t|)^Jmass*
            Z^(max s.width (length Z X₁+length Z X₂)+emass))→
      s.plainEnergy p t X₁ X₂≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^Jout*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuCap,hLu,hLuCap,huStage⟩:=
    CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirCap,hLr,hLrCap,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrStage⟩:=
    CenteredMomentEnergyZeroReferencePhysicalBounded.actual_positive_source_entry
      a b bΦ rho ε Mcap Bmask B εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Uu,Cu,hCu,huBound⟩:=huStage S
  obtain ⟨Jr,Ur,Cr,hCr,hrBound⟩:=hrStage S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=1
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=by norm_num [P]
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [huBound,hrBound] with Z hZu hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂ hvolume hlarge
  dsimp only
  intro hphysical
  let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
  have hlowU:=low_restrict Q a b bΦ Bmask _ Lu Mcap e Z degree S K hZ.1.le hLuCap hlow
  have hlowR:=low_restrict Q a b bΦ Bmask _ Lr Mcap e Z degree S K hZ.1.le hLrCap hlow
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|:=by exact le_add_of_nonneg_right (abs_nonneg t)
  let Mout:ℝ:=max s.width (length Z X₁+length Z X₂)
  have hwm:s.width≤Mout:=le_max_left _ _
  let F:ℝ:=(p.control U)^2*(1+|t|)^Jout*Z^(Mout+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|)^jj*Z^(s.width+ej)≤F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (add_le_add hwm hej)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by dsimp [Jout];omega
  have hjr:Jr≤Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    have hCuC : Cu ≤ Cfixed := by
      dsimp only [Cfixed]
      linarith only [hCr, hD, hT]
    exact mul_le_mul hCuC (by linarith only [hCmass])
      (by linarith only [hK]) hCfixed.le
  by_cases hshort:min (length Z X₁) (length Z X₂)≤s.width/4
  · have hunbalanced:=hZu.2 e Q degree K he hK hlowU s hQ hwidthLo hwidth
      p t X₁ X₂ hX₁ hX₂ hshort hlarge
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hfour':=balanced_four_scale_gates Z s.width X₁ X₂ hZ.1 (hrho.trans_le hwidthLo)
      hX₁ hX₂ (le_of_not_ge hshort)
    have hfour:Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂:=
      ⟨hfour'.1,hfour'.2.1,hfour'.2.2.1,hfour'.2.2.2.1⟩
    rcases hZ.2 e Q degree K he hK hlowR s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂
      hvolume hlarge with hzero|hsource
    · rw [hzero]
      positivity
    have hmass:=hphysical hfour
    have hmEnv:(p.control Smass)^2*(1+|t|)^Jmass*Z^(Mout+emass)≤F:=by
      have hp:=profile_control_mono p hm
      have hp0:=p.control_nonneg Smass
      have hj:=pow_le_pow_right₀ hbase hjm
      have hx:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show Mout+emass≤Mout+efinal by linarith only [hmassFinal])
      dsimp [F]
      gcongr
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        (X₁*X₂)≤Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=plain_control_sq_le inp p U 0 1 (by norm_num) (by simp) (by intro i;exact Fin.elim0 i)
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [P,Finset.insert_eq_of_mem h00,one_pow,one_mul] using hc
    have hheight1:1≤(1+|t|)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(Mout+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by have hh:=hwm;unfold NaturalState.width at hh;linarith only [hh, hx, s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤c*P*A*F:=by
      calc
        _≤c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤c*(P*(p.control U)^2)*A*Z^(Mout+efinal):=by gcongr;exact hscalePower x hx
        _≤c*P*A*F:=by
          dsimp [F]
          nlinarith only [mul_nonneg (show 0≤c*P*A*(p.control U)^2*Z^(Mout+efinal) by positivity)
            (sub_nonneg.mpr hheight1)]
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu, hCr, hD, hT, hK, hCmass, mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|)^Jout*Z^(Mout+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyZeroGrowthHighBound

end

end OAI
end OAIOriginalModule2814

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysicalReindex
Source SHA256: 8721624ee0484f62d2259156f940137828eb63faa1ebeae494246bbed6a1f706
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2815



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentSourceInputReindex
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstRetainedNorm CenteredMomentAmplificationChildInput
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α β:Type*}[Fintype α][Fintype β]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
local instance : DecidableEq (β⊕Fin 2):=Classical.decEq _

lemma physical_mass_map (e:α≃β)(s:Input α)(R seed:Ideal O)(m A:O)
    (Ψ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass (reindex e s) R seed m A Ψ K Z ξ=physicalMass s R seed m A Ψ K Z ξ:=by
  have hc:coefficient (reindex e s) R seed=coefficient s R seed:=by
    simpa only [CenteredMomentFirstAmplificationChoice.OriginalData.beta,
      CenteredMomentFirstAmplificationChoice.OriginalData.profile,original,coefficient]
      using coefficient_map e s R seed
  have hp:CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools)=
      CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools):=by
    rw [←pools_map e s,CenteredMomentSourceMass.finiteColumns,Finset.image_image]
    congr 1
    funext v
    exact tupleMap_product e v
  have hv:CenteredMomentExceptionalAmplitudePair.volume (reindex e s).toData=
      CenteredMomentExceptionalAmplitudePair.volume s.toData:=volume_map e s
  have hs (T:Finset (Ideal O))(C D:Ideal O)
      (hC:CanonicalQuadraticSieve.Supported C)(hD:CanonicalQuadraticSieve.Supported D)
      (t X:ℝ):
      sectorMass (reindex e s) R seed m A t T C D hC hD Ψ K X Z ξ=
      sectorMass s R seed m A t T C D hC hD Ψ K X Z ξ:=by
    unfold sectorMass
    rw [sourceRadius_map e s]
    simp only [hc, show (reindex e s).η=s.η from rfl]
  let sumAt (T:Finset (Ideal O))(t X:ℝ):ℝ:=
    ∑p:CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns T) (CenteredMomentSourceRow.supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).1
        (CenteredMomentFirstSectorTransform.commonLabels_supported T p).2 Ψ K X Z ξ
  have hl:physicalMass (reindex e s) R seed m A Ψ K Z ξ=
      sumAt (CenteredMomentActiveSource.activeSource
        (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset (reindex e s).pools))
        (coefficient (reindex e s) R seed)) s.t
        (CenteredMomentExceptionalAmplitudePair.volume (reindex e s).toData):=by
    unfold physicalMass
    dsimp only
    exact Finset.sum_congr rfl (fun p _=>hs _ _ _ _ _ _ _)
  rw [hl]
  rw [hc,hp,hv]
  rfl

def emptyEquiv (α:Type*)[Fintype α]:Fin 0≃(∅:Finset α):=Equiv.equivOfIsEmpty _ _

variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def emptyBalanced (α:Type*)[Fintype α]:Input (∅:Finset α):=
  reindex (emptyEquiv α)
    (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)

lemma empty_balanced_mass (R seed:Ideal O)(m A:O)(Ψ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α) R seed m A Ψ K Z₀ ξ=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        R seed m A Ψ K Z₀ ξ:=
  physical_mass_map (emptyEquiv α) _ R seed m A Ψ K Z₀ ξ

lemma empty_balanced_volume : volume (emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α)=X₁*X₂:=by
  rw [emptyBalanced,volume_map,CenteredMomentEnergyZeroReferencePhysical.balanced_volume]

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex

end

end OAI
end OAIOriginalModule2815

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthSource
Source SHA256: 3d7dab36a6386b055984d67b36ed13cd687d7318773a89de538e5c691141edb4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2816


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSource
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

def PhysicalGrowthAt (Q:Ideal O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)

theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hLB:2*L≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z Jout U (Cfixed*(K+Cmass+1))→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hold hlow hmass
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hCout:0≤Cfixed*(K+Cmass+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hsmall:s.width≤ rho
  · exact zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z Jout U
      (Cfixed*(K+Cmass+1)) hCout hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤Cfixed*(K+Cmass+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤Z^B:=by
    calc
      _≤Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤Cfixed:=by dsimp [Cfixed];linarith
  apply hh.trans
  rw [Real.norm_eq_abs]
  gcongr

end SevenEighths.CenteredMomentEnergyZeroGrowthSource

end

end OAI
end OAIOriginalModule2816

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthSourceControlled
Source SHA256: e9f2da58bfc4baa59cde685497097a5ac3a25791e3761ae58701827bbc88c390
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2817


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroGrowthSource (PhysicalGrowthAt)

theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hLB:2*L≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass Cprevious:ℝ),
      0≤e→0≤K→0≤Cmass→0≤Cprevious→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z degree S Cprevious→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+Cprevious+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass Cprevious he hK hCm hCp hef hmf hdf htf hold hlow hmass
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hCout:0≤Cfixed*(K+Cmass+Cprevious+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  by_cases hsmall:s.width≤ rho
  · have hh:=zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z degree S
      Cprevious hCp hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ (show 1≤1+‖t‖ by linarith [norm_nonneg t]) hj
    have hcoeff:Cprevious≤Cfixed*(K+Cmass+Cprevious+1):=by
      dsimp [Cfixed]
      nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    gcongr
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤Cfixed*(K+Cmass+Cprevious+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤Z^B:=by
    calc
      _≤Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤Cfixed:=by dsimp [Cfixed];linarith
  have hcoefFull:Ch*(K+Cmass+1)≤Cfixed*(K+Cmass+Cprevious+1):=
    mul_le_mul hcoeff (by linarith) (by positivity) hCfixed.le
  have hfront:=mul_le_mul_of_nonneg_right hcoefFull
    (show 0≤diagonalControl s.radial.profile*(p.control Uh)^2*(1+|t|)^Jh*
      Z^(max s.width (length Z X₁+length Z X₂)+efinal) by positivity)
  have hmid:s.plainEnergy p t X₁ X₂≤
      Cfixed*(K+Cmass+Cprevious+1)*diagonalControl s.radial.profile*(p.control Uh)^2*
        (1+|t|)^Jh*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
    apply hh.trans
    convert hfront using 1 <;> ring
  apply hmid.trans
  rw [Real.norm_eq_abs]
  gcongr

end SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled

end

end OAI
end OAIOriginalModule2817

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
Source SHA256: afd183e7797123bc80cca56d358954d9e3499be0191d2b89f39368f50a5f8e47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2818



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainRelativeClass
open HeckeFamily CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance:IsPrincipalIdealRing O:=IsCyclotomicExtension.Rat.three_pid K
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma ray_identity (θ:RayQuotient.Characters M H)(I:Ideal O)
    (hI:I∈RayQuotient.identityClass M H):
    idealCoeff (HeckeRayQuotient.character M H hH θ) I=1:=by
  rcases hI with ⟨hI,a,ha,u,hu,huH⟩
  rw [HeckeRayQuotient.idealCoeff_character]
  change IdealCharacter.ofResidue M θ (RayQuotient.character_unitInvariant M H hH θ) I=1
  rw [IdealCharacter.ofResidue_of_generator M θ _ hI ha,←hu]
  exact (RayOrthogonality.mem_characters_iff H θ).mp θ.property u huH

lemma relative_pool (η₀:Character)(θ:RayQuotient.Characters M H)(b P:ℝ)
    (I:Ideal O)(hI:I∈primePool M H b P):
    idealCoeff (relativeCharacter M H hH η₀ θ) I=idealCoeff η₀.inverse I:=by
  rw [relativeCharacter_ideal,ray_identity M H hH θ I (Finset.mem_filter.mp hI).2.2,one_mul]

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem positive_row (η η₀:Character)(θ:ι→RayQuotient.Characters M H)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→Ideal O→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*β i I) P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P t X₁ X₂:=by
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [relative_pool M H hH η₀ (θ i) (b i) (P i) I hI]

omit [DecidableEq ι] in
theorem energy_eq (η η₀:Character)(θ:ι→RayQuotient.Characters M H)(m A:O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→Ideal O→ℂ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*β i I) P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row M H hH η η₀ θ m A z W₁ W₂ b P β t X₁ X₂]

end SevenEighths.CenteredMomentDetectorPlainRelativeClass

end

end OAI
end OAIOriginalModule2818

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState
Source SHA256: 6bfb18da7d39d66ce4da3699c5acdd5d686a0b754af1d54e7263da5ea1e90276
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2819




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open HeckeFamily HeckeDetectorRawFiber CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainStateDictionary
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O

def allowance (δ m:ℝ):ℝ:=δ+max 0 (2*m-1)

lemma allowance_nonneg (δ m:ℝ)(hδ:0≤δ):0≤allowance δ m:=
  add_nonneg hδ (le_max_left _ _)

lemma padded_width (δ m:ℝ):1+allowance δ m=max 1 (2*m)+δ:=by
  unfold allowance
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right (by linarith:0≤2*m-1)]
    ring
  · rw [max_eq_left (le_of_not_ge hm),max_eq_left (by linarith:2*m-1≤0)]
    ring

lemma padded_modulus (η:Character)(U δ m:ℝ)(hU:1≤U)
    (hη:(η.modulus.absNorm:ℝ)≤U^δ):
    (η.modulus.absNorm:ℝ)≤U^(allowance δ m):=
  hη.trans (Real.rpow_le_rpow_of_exponent_le hU (le_add_of_nonneg_right (le_max_left _ _)))

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T heightAllowance:ℝ}{i:ℕ}

def state (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState U 0 bΦ:=
  initialState η Q Φ bΦ U (allowance δ F.m) hU (allowance_nonneg _ _ hδ) hs hp
    (padded_modulus η U δ F.m hU hη)

omit [NeZero M] in
theorem actual_scale_gates (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ εcap:ℝ)
    (hU:1<U)(hδ:0≤δ)(hε:ε≤εcap)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):
    let s:=state F η Q Φ bΦ δ hU.le hδ hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+δ ∧
    s.width≤max 1 (1+150*εcap)+δ ∧
    1≤U^F.m ∧ length U (U^F.m)=F.m ∧
    2*length U (U^F.m)≤s.width ∧ U^F.m≤U^(1/2+75*εcap):=by
  dsimp only
  have hm:=F.lengths hU
  have hmcap:F.m≤1/2+75*εcap:=by linarith [hm.2.2.1]
  have hscale:1≤U^F.m:=Real.one_le_rpow hU.le hm.2.2.2.2
  have hlen:length U (U^F.m)=F.m:=by
    rw [length,max_eq_right hscale]
    exact Real.logb_rpow (zero_lt_one.trans hU) hU.ne'
  have hw:(state F η Q Φ bΦ δ hU.le hδ hs hp hη).width=max 1 (2*F.m)+δ:=padded_width δ F.m
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,hw,?_,hscale,hlen,?_,?_⟩
  · rw [hw]
    exact add_le_add (max_le_max le_rfl (by linarith)) le_rfl
  · rw [hw,hlen]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right hδ)
  · exact Real.rpow_le_rpow_of_exponent_le hU.le hmcap

omit [NeZero M] in
theorem actual_source_eq (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (state F η Q Φ bΦ δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=
  retainedSourceEnergy_empty_eq_plainEnergy F η Q Φ bΦ (allowance δ F.m)
    hU (allowance_nonneg _ _ hδ) hs hp (padded_modulus η U δ F.m hU hη) j k σ t

end SevenEighths.CenteredMomentDetectorPlainUnmarkedState

end

end OAI
end OAIOriginalModule2819

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacitySource
Source SHA256: f6a029a6917d90762b176e121dd8d8ec6d72f32b0ee89889ba6548e1af82c454
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2820





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem frozen_reduction_log (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (Z:ℝ)(hZ:1<Z)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0):
    Real.logb Z (rawReduction B.val s.P)-Real.logb Z (C.absNorm:ℝ)≤
      -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower) := by
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have ha:0<min 1 s.lower:=lt_min zero_lt_one s.lower_pos
  have hh:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower s.upper s.lower_pos s.slot_support hne).1
  have hl:=Real.logb_le_logb_of_le hZ (mul_pos (pow_pos ha _) hr) hh
  rw [Real.logb_mul (pow_pos ha _).ne' hr.ne',Real.logb_pow] at hl
  nlinarith

theorem inherited_affine_parent (s:Input ι)(C _R:Ideal O)(B:actualAllocations s.pools C)
    (Z κ M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤M := by
  have hp:=CenteredMomentEnergyInputParentCapacity.input_affine_capacity s Z κ M hZ hcap
  have hs:=CenteredMomentAllocatedChildCapacity.common_slot_logs_le s C B Z hZ hP
  have hh:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0):
    Real.logb Z (volume (child s C R0 B τ t)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ t S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (child s C R0 B τ t)) a Z (cost*(τ.modulus.absNorm:ℝ)) n
    (mul_pos hcost hq) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  rw [common_volume] at hg
  rw [Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  rw [common_volume]
  linarith

theorem actual_error_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(child s C R0 B τ t).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (child s C R0 B τ t).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=twice_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacitySource

end

end OAI
end OAIOriginalModule2820

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedActiveCapacitySource
Source SHA256: 9a3b6d57e4e6759901998d0bfedb30488679aca2efef366f6509d8885ab0474d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2821






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput

theorem active_error_volume (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)=
      volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [errorInput,child_volume _ Q hQ k hslot,active_volume,common_volume]
  ring

theorem actual_active_error_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

theorem actual_active_error_source_shift_right (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(D₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference_right υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource

end

end OAI
end OAIOriginalModule2821

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedActiveAffine
Source SHA256: a5e106bd8a2cec8a0990818acb668de47ee988e8c7b0b7170d0f14f81929a641
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2822


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedActiveAffine
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentFirstAnnularInput CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAmplifiedActiveCapacitySource CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem active_error_slot_logs_le (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      ∑i,Real.logb Z (s.P i) := by
  have hp : ∀i,1≤(activeInput (child s C R B τ t)).P i := fun i=>hP i.val
  have hs := common_slot_logs_le (activeInput (child s C R B τ t)) (Q^k) Bp Z hZ hp
  exact hs.trans (common_slot_logs_le s C B Z hZ hP)

theorem active_error_parent_affine (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z κ M : ℝ) (hZ : 1<Z) (hκ : 1/6≤κ) (hP : ∀i,1≤s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M) :
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤M := by
  have hh := input_affine_capacity s Z κ M hZ hcap
  have hs := active_error_slot_logs_le s C R B τ t Q k Bp υ v Z hZ hP
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0≤6*κ-1)
  linarith

theorem active_error_raw_affine (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v Z κ M : ℝ) (hZ : 1<Z) (hκ : 1/6≤κ) (hP : ∀i,1≤s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M) :
    Real.logb Z (volume (errorInput s C R B τ t Q k Bp υ v))+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      M-Real.logb Z (rawReduction B.val s.P)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ) := by
  have hh := active_error_parent_affine s C R B τ t Q k Bp υ v Z κ M hZ hκ hP hcap
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hq : 0<(Q.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  rw [active_error_volume s C R B τ t Q hQ k hslot Bp υ v,
    Real.logb_div (volume_pos s).ne' (mul_pos hr (pow_pos hq k)).ne',
    Real.logb_mul hr.ne' (pow_pos hq k).ne',Real.logb_pow]
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedActiveAffine

end

end OAI
end OAIOriginalModule2822

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon
Source SHA256: 84efcfb743ae1d807ab42f4939495b122a373ebe025861e4d83dcf84bfa163a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2823



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentSourceLiveColumn
open CenteredMomentSecondCapacitySourceShift CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondNonexceptionalScalar
open CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalCost CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentAllocatedChildCapacity CenteredMomentFirstScale
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def envelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

def ratioPenalty (n:Fin 4→ℤ):ℝ:=
  max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

lemma envelope_pos (qref:ℝ)(hq:0<qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):0<envelopeRef qref C D U n:=by
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hu:=CenteredMomentSecondPhysicalLedger.common_product_pos C D hC U
  have hv:=norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hn:=dyadicScale_pos (n 1)
  unfold envelopeRef
  positivity

lemma adjusted_log (Z qref:ℝ)(hq:0<qref)(C D:Ideal O)(hC:Supported C)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    Real.logb Z (adjustedEnvelopeRef qref C D U n)=
      Real.logb Z (envelopeRef qref C D U n)+Real.logb Z (ratioPenalty n):=by
  exact Real.logb_mul (envelope_pos qref hq C D hC U n).ne'
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'

theorem common_raw_reference_shift (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools C)(hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) C R0 B υ t hB
  have hc:=norm_pos C hC.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s C R0 B υ t)) hu
  have hb:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) C R0 B)=volume (child s C R0 B υ t):=rfl
  rw [he]
  linarith

theorem common_raw_reference_shift_right (s:Input ι)(υ:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (B:actualAllocations s.pools D)(hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference_right υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) D R0 B υ t hB
  have hc:=norm_pos D hD.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s D R0 B υ t)) hu
  have hb:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) D R0 B)=volume (child s D R0 B υ t):=rfl
  rw [he]
  linarith

theorem actual_width_le_reference {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→Character}
    (hf:Family η C D hC hD U τ)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤qref)(hZ:1<Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z ((τ χ).modulus.absNorm:ℝ)+Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (envelopeRef qref C D U n) := by
  have hqpos:=norm_pos (τ χ).modulus (τ χ).modulus_ne_bot
  have he:=family_child_envelope hf t S β R rows W K hK n hne χ
  have hb:childEnvelope η C D U n≤envelopeRef qref C D U n:=by
    unfold childEnvelope envelopeRef
    gcongr
    exact (dyadicScale_pos _).le
  have hh:=Real.logb_le_logb_of_le hZ (mul_pos hqpos (dyadicScale_pos _)) (he.trans hb)
  rwa [Real.logb_mul hqpos.ne' (dyadicScale_pos _).ne'] at hh

end SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

end

end OAI
end OAIOriginalModule2823

/-! Original module: OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
Source SHA256: 70d2a04389f6f3fdeb654f1b558adfd1006794cf9d2bda2d1edf7038222961a1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2824





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedChildWidth
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplifiedActiveCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondRadicalBudget
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstScale CenteredMomentAmplifiedChildWidth
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι]
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ) := by
  intro x hx
  by_cases h:0≤x
  · exact (ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

theorem actual_ball_witness (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z≠0 ∧ ballProfile (normValue z/dyadicScale (n 1))=1 := by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  refine ⟨z,hz0,ballProfile_one _ (div_nonneg (normValue_pos z hz0).le (dyadicScale_pos _).le) ?_⟩
  exact (div_le_one (dyadicScale_pos _)).mpr (dyadicRows_norm rows n z hz).2.le

def geometry (N:ℕ)(b:ℝ):ℝ := (b^N)^2

lemma geometry_pos (N:ℕ)(b:ℝ)(hb:1≤b):0<geometry N b := by
  unfold geometry
  exact sq_pos_of_pos (pow_pos (zero_lt_one.trans_le hb) _)

lemma main_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t K:ℝ)(hK:0<K)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    nominal (child s C R B τ t) K≤geometry N b*((volume s/(C.absNorm:ℝ))^2/K) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hC:=CenteredMomentAmplificationChildSourceCaps.norm_ge_one C (allocation_ne s C B)
  have hh:0≤volume s/(C.absNorm:ℝ):=div_nonneg (volume_pos s).le (by positivity)
  have hv':volume (child s C R B τ t)≤b^N*(volume s/(C.absNorm:ℝ)):=by simpa only [mul_div_assoc] using hv
  have hp:volume (child s C R B τ t)^2≤(b^N)^2*(volume s/(C.absNorm:ℝ))^2:=by
    nlinarith [volume_pos (child s C R B τ t),mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma error_volume_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))(υ:Character)(v:ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hq:0≤(Q.absNorm:ℝ)^k:=pow_nonneg (Nat.cast_nonneg _) _
  have hh:=div_le_div_of_nonneg_right hv hq
  rw [common_volume] at hh
  rw [active_error_volume s C R B τ t Q hQ k hslot Bp υ v]
  convert hh using 1 <;> ring

lemma error_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ:Character)(v K:ℝ)(hK:0<K) :
    nominal (errorInput s C R B τ t Q k Bp υ v) K≤
      geometry N b*((volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K) := by
  have hv:=error_volume_cap N b hb s hc hs C R B τ t hne Q hQ k hslot Bp υ v
  have hh:0≤volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_nonneg (volume_pos s).le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
  have hp:volume (errorInput s C R B τ t Q k Bp υ v)^2≤
      (b^N)^2*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2:=by
    nlinarith [volume_pos (errorInput s C R B τ t Q k Bp υ v),
      mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

lemma restored_nominal_eq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ:Character)(v K:ℝ) :
    nominal (restoredError s C R B τ t Q k Bp υ v) K=
      nominal (errorInput s C R B τ t Q k Bp υ v) K := by
  unfold nominal
  rw [restoredError_volume s C R B τ t Q hQ k hslot Bp υ v,
    active_error_volume s C R B τ t Q hQ k hslot Bp υ v]

def mainRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):ℝ :=
  mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve

def errorRadius (C D:Ideal O)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):ℝ :=
  errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V))
    (Real.logb Z (C.absNorm:ℝ)) σ δ reserve p k

lemma mainRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ):
    mainRadius C D E K V Z σ δ reserve=
      mainCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [mainRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

lemma errorRadius_eq (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))(K V Z σ δ reserve:ℝ)(p:O)(k:ℕ):
    errorRadius C D E K V Z σ δ reserve p k=
      errorCommonRadius Z (Real.logb Z ((commonPart D C).absNorm:ℝ))
        (nominalLog C D (∏P∈E,P.val) K V Z)
        (Real.logb Z ((commonPart C D).absNorm:ℝ)) σ δ reserve p k := by
  rw [commonPart_eq_left C D hC.1 hCD,commonPart_eq_left D C hD.1 hCD.symm]
  simp only [errorRadius,nominalLog,primeSubsetGenerator,span_idealGenerator]

def threshold (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):ℝ :=
  fixedWidthThreshold 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ

lemma threshold_gt_one (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ):1<threshold N b σ hb hσ :=
  (fixedWidthThreshold_spec 2 (geometry N b) σ (by norm_num) (geometry_pos N b hb) hσ).1

theorem main_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family τ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock τ t S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (child s C R B τ t) (mainRadius C D E K (volume s) Z σ δ reserve)) Z ξ)
      rows W (mainRadius C D E K (volume s) Z σ δ reserve) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  let L:=mainRadius C D E K (volume s) Z σ δ reserve
  have hL:0<L:=by unfold L mainRadius mainCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=mainRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve
  have hscale:=main_nominal_cap N b hb s hc hs C R B τ t L hL hB
  have hhscale:nominal (child s C R B τ t) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm:ℝ))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness τ t S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=main_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod hf t S β rows W
    (nominal (child s C R B τ t) L) (geometry N b) ξ (nominal_pos _ L hL)
    (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

theorem error_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=0∨k=5∨k=6)
    (hslot:∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^(k+1)))
    (υ:Character)(χ₀:RayCharacter)(v:ℝ)
    (hN:υ.modulus.absNorm≤radicalBound (childCharacter τ χ₀) fixedBadMask p (errorMovingExponent k))
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→Character)
    (hf:Family υ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v)
        (errorRadius C D E K (volume s) Z σ δ reserve p (k+1))) Z ξ)
      rows W (errorRadius C D E K (volume s) Z σ δ reserve p (k+1)) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  have hQ:Ideal.span {p}≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  let L:=errorRadius C D E K (volume s) Z σ δ reserve p (k+1)
  have hL:0<L:=by unfold L errorRadius errorCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=errorRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve p (k+1)
  have hscale:=error_nominal_cap N b hb s hc hs C R B τ t hB (Ideal.span {p}) hQ (k+1) hslot Bp υ v L hL
  have hpn:((Ideal.span {p}).absNorm:ℝ)=normValue p:=rfl
  have hhscale:nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm*(normValue p)^(k+1)))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD,hpn] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness υ v S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=error_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod υ χ₀ p hp k hk hN hf v S β rows W
    (nominal (errorInput s C R B τ t (Ideal.span {p}) (k+1) Bp υ v) L) (geometry N b) ξ
    (nominal_pos _ L hL) (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith

end SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

end

end OAI
end OAIOriginalModule2824

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
Source SHA256: 9f4ec00b57274a1c3afbe71bc47bff1fd70be3101c039055c26c4f40cd3c37fe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2825






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentFirstAmplifiedActiveAffine CenteredMomentFirstAmplifiedActiveCapacitySource
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

def sourceReserve {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):ℝ :=
  max (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
    min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
    Real.logb Z fixedPresentationCost-Real.logb Z cost+
    Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
    (Fintype.card α:ℝ)*Real.logb Z (max 1 childInput.upper)) 0

lemma sourceReserve_nonneg {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):0≤sourceReserve s childInput C D Z delta reserve cost a :=
  le_max_right _ _

lemma common_affine (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)
    (Z κ A M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hp:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M):
    A+(6*κ-1)*(∑i:liveIndices B.val,Real.logb Z (s.P i.val))≤M := by
  have hs:=common_slot_logs_le s C B Z hZ hP
  have hm:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_admission (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (child s C R0 B τ t).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (child s C R0 B τ t).ν (child s C R0 B τ t).W (child s C R0 B τ t).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=child s C R0 B τ t;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*(sigma/3)+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ):=mul_pos hcost hq
  have hf:=inherited_affine_parent s C R0 B Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(child s C R0 B τ t).P i:=fun i=>hP i.val
  have hparent:=common_affine (child s C R0 B τ t) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (child s C R0 B τ t) υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ))-
      Real.logb Z (volume (child s C R0 B τ t))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
  rw [common_volume,Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

theorem actual_active_error_admission (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).ν (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).W (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*errorRemoval p Z k+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k):=by positivity
  have hf:=active_error_parent_affine s C R0 B τ t (Ideal.span {p}) k Bp υ v Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P i:=fun i=>hP i.val.val
  have hparent:=common_affine (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

theorem actual_width_admission {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→Character}
    (hf:CenteredMomentSecondExceptionalFamily.Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤qref)(hZ:1<Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)-
      Real.logb Z (envelopeRef qref C D U n)≤0 := by
  have hh:=actual_width_le_reference hf t S β R rows W K hK n hne qref Z hq hZ χ
  linarith

lemma common_preVolume_height (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ υ:Character)(v t:ℝ):
    preVolume (commonData (withHeight s τ v) C R B)=
      preVolume (commonData (withHeight s υ t) C R B) := rfl

end SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

end

end OAI
end OAIOriginalModule2825

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
Source SHA256: a577224a4f7a3686cb064d6030689b82ad1790f4a515725368b51aa908279cd2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2826


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidReserve
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstPhysicalSource CenteredMomentSecondCanonicalScalar CenteredMomentFirstScale
open CenteredMomentSecondRadicalBudget
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def fixedNumerator (N:ℕ)(lower upper cost0 a0:ℝ):ℝ :=
  (N:ℝ)*|Real.log (min 1 lower)|+(N:ℝ)*|Real.log (max 1 upper)|+
    |Real.log fixedPresentationCost|+|Real.log cost0|+
    |Real.log (4/((fixedFactor:ℝ)*a0^2))|

lemma fixedNumerator_nonneg (N:ℕ)(lower upper cost0 a0:ℝ):
    0≤fixedNumerator N lower upper cost0 a0 := by unfold fixedNumerator;positivity

theorem source_reserve_bound (N:ℕ)(lower upper cost0 a0:ℝ)
    (hlower:0<lower)(hcost0:0<cost0)(ha0:0<a0)
    {ι α:Type*}[Fintype ι][Fintype α](s:Input ι)(input:Input α)
    (hn:Fintype.card ι≤N)(hnc:Fintype.card α≤N)
    (hl:lower≤s.lower)(hu:input.upper≤upper)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(Z delta reserve cost a:ℝ)
    (hZ:1<Z)(hd:0≤delta)(hr:0≤reserve)(hc:cost0≤cost)(ha:a0≤a):
    sourceReserve s input C D Z delta reserve cost a≤
      delta+reserve+fixedNumerator N lower upper cost0 a0/Real.log Z := by
  have hz:=Real.log_pos hZ
  have hN:(0:ℝ)≤N:=Nat.cast_nonneg _
  have hnc:(Fintype.card α:ℝ)≤N:=by exact_mod_cast hnc
  have hno:(Fintype.card ι:ℝ)≤N:=by exact_mod_cast hn
  have hmin:=Real.logb_le_logb_of_le hZ (lt_min zero_lt_one hlower) (min_le_min_left 1 hl)
  have hmin0:0≤-Real.logb Z (min 1 lower):=by
    have hh:=Real.logb_le_logb_of_le hZ (lt_min zero_lt_one hlower) (min_le_left 1 lower)
    rw [Real.logb_one] at hh
    linarith
  have hlow: -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)≤(N:ℝ)*(-Real.logb Z (min 1 lower)):=by
    have hh:=mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤_)
    have hh':=mul_le_mul_of_nonneg_right hno hmin0
    nlinarith
  have hmax:=Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 input.upper))
    (max_le_max_left 1 hu)
  have hmax0:0≤Real.logb Z (max 1 upper):=Real.logb_nonneg hZ (le_max_left _ _)
  have hupp:(Fintype.card α:ℝ)*Real.logb Z (max 1 input.upper)≤(N:ℝ)*Real.logb Z (max 1 upper):=
    (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnc hmax0)
  have hcost:=Real.logb_le_logb_of_le hZ hcost0 hc
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have ha':0<a:=ha0.trans_le ha
  have hfrac:4/((fixedFactor:ℝ)*a^2)≤4/((fixedFactor:ℝ)*a0^2):=by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ ha0.le ha'.le |>.mpr ha) hf.le
  have harg:=Real.logb_le_logb_of_le hZ (by positivity:0<4/((fixedFactor:ℝ)*a^2)) hfrac
  have hCN:(1:ℝ)≤C.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hDN:(1:ℝ)≤D.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hcommon:0≤min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ)):=
    le_min (Real.logb_nonneg hZ hCN) (Real.logb_nonneg hZ hDN)
  have habs:
      (N:ℝ)*(-Real.logb Z (min 1 lower))+(N:ℝ)*Real.logb Z (max 1 upper)-
        Real.logb Z fixedPresentationCost-Real.logb Z cost0+
        Real.logb Z (4/((fixedFactor:ℝ)*a0^2))≤fixedNumerator N lower upper cost0 a0/Real.log Z:=by
    simp only [Real.logb]
    rw [show (N:ℝ)*(-(Real.log (min 1 lower)/Real.log Z))+
      (N:ℝ)*(Real.log (max 1 upper)/Real.log Z)-Real.log fixedPresentationCost/Real.log Z-
      Real.log cost0/Real.log Z+Real.log (4/((fixedFactor:ℝ)*a0^2))/Real.log Z=
      ((N:ℝ)*(-Real.log (min 1 lower))+(N:ℝ)*Real.log (max 1 upper)-
        Real.log fixedPresentationCost-Real.log cost0+Real.log (4/((fixedFactor:ℝ)*a0^2)))/Real.log Z by ring]
    apply (div_le_div_iff_of_pos_right hz).mpr
    have h1:=mul_le_mul_of_nonneg_left (neg_le_abs (Real.log (min 1 lower))) hN
    have h2:=mul_le_mul_of_nonneg_left (le_abs_self (Real.log (max 1 upper))) hN
    unfold fixedNumerator
    linarith [neg_le_abs (Real.log fixedPresentationCost),neg_le_abs (Real.log cost0),
      le_abs_self (Real.log (4/((fixedFactor:ℝ)*a0^2)))]
  unfold sourceReserve
  apply max_le
  · linarith
  · exact add_nonneg (add_nonneg hd hr) (div_nonneg (fixedNumerator_nonneg _ _ _ _ _) hz.le)

theorem eventually_source_reserve (N:ℕ)(lower upper cost0 a0 theta:ℝ)
    (hlower:0<lower)(hcost0:0<cost0)(ha0:0<a0)(htheta:0<theta):
    ∃Z0:ℝ,1<Z0 ∧ ∀Z:ℝ,Z0≤Z→
      ∀{ι α:Type*}[Fintype ι][Fintype α],∀(s:Input ι)(input:Input α),
      Fintype.card ι≤N→Fintype.card α≤N→lower≤s.lower→input.upper≤upper→
      ∀(C D:Ideal O),C≠0→D≠0→∀delta reserve cost a:ℝ,
      0≤delta→0≤reserve→cost0≤cost→a0≤a→
      sourceReserve s input C D Z delta reserve cost a≤delta+reserve+theta := by
  let L:=fixedNumerator N lower upper cost0 a0
  have hL:0≤L:=fixedNumerator_nonneg _ _ _ _ _
  let Z0:=Real.exp (1+L/theta)
  have hZ0:1<Z0:=Real.one_lt_exp_iff.mpr (by positivity)
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZZ ι α _ _ s input hn hnc hl hu C D hC hD delta reserve cost a hd hr hc ha
  have hZ:1<Z:=hZ0.trans_le hZZ
  have hlog:=Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hsmall:L/Real.log Z≤theta:=by
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hh:(L/theta)*theta≤(Real.log Z)*theta:=
      mul_le_mul_of_nonneg_right (by linarith) htheta.le
    rw [div_mul_cancel₀ _ htheta.ne'] at hh
    linarith
  have hb:=source_reserve_bound N lower upper cost0 a0 hlower hcost0 ha0 s input
    hn hnc hl hu C D hC hD Z delta reserve cost a hZ hd hr hc ha
  exact hb.trans (by change delta+reserve+L/Real.log Z≤_;linarith)

theorem eventually_actual_amplified_reserves (N:ℕ)(lower upper cost0 a0 theta:ℝ)
    (hlower:0<lower)(hcost0:0<cost0)(ha0:0<a0)(htheta:0<theta):
    ∃Z0:ℝ,1<Z0 ∧ ∀Z:ℝ,Z0≤Z→
      ∀{ι:Type*}[Fintype ι],∀s:Input ι,
      Fintype.card ι≤N→lower≤s.lower→s.upper≤upper→
      ∀(C D R:Ideal O),C≠0→D≠0→∀B:actualAllocations s.pools C,
      ∀(τ:Character)(t delta reserve cost a:ℝ),
      0≤delta→0≤reserve→cost0≤cost→a0≤a→
      sourceReserve s (child s C R B τ t) C D Z delta reserve cost a≤delta+reserve+theta ∧
      ∀(Q:Ideal O)(k:ℕ)
        (Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
        (υ:Character)(v:ℝ),
        sourceReserve s (errorInput s C R B τ t Q k Bp υ v) C D Z delta reserve cost a≤
          delta+reserve+theta := by
  obtain ⟨Z0,hZ0,hbound⟩:=eventually_source_reserve N lower upper cost0 a0 theta
    hlower hcost0 ha0 htheta
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZZ ι _ s hn hl hu C D R hC hD B τ t delta reserve cost a hd hr hc ha
  have hchild:Fintype.card (liveIndices B.val)≤N:=(live_card_le B.val).trans hn
  refine ⟨hbound Z hZZ s (child s C R B τ t) hn hchild hl hu C D hC hD
    delta reserve cost a hd hr hc ha,?_⟩
  intro Q k Bp υ v
  have herr:Fintype.card (liveIndices Bp.val)≤N:=(live_card_le Bp.val).trans hchild
  exact hbound Z hZZ s (errorInput s C R B τ t Q k Bp υ v) hn herr hl hu C D hC hD
    delta reserve cost a hd hr hc ha

end SevenEighths.CenteredMomentFirstAmplifiedPaidReserve

end

end OAI
end OAIOriginalModule2826

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
Source SHA256: 21f0c7cbd78787d7e7f70f69e933d8f1705f2f250d17015ae1e42422f7e89169
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2827




namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
namespace SevenEighths.CenteredMomentRelativeCapacityRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem relative_slots_uniform {ι:Type*}[Fintype ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,1≤C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤(ν i).modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀σ t v V:ℝ,lo≤σ → σ≤hi → 0≤V → |v|≤V →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) P)
        (fun I=>idealCoeff (ν i) I*annularWeight (W i) P σ v I) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  choose degree C hC hb using fun i=>natural_character_slot_bound M H hH (W i) (a i) (b i)
    (ha i) (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let Ctotal:ℝ:=1+∑i,C i
  have hCtotal:1≤Ctotal:=by
    have hsum:=Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(hC i).le)
    dsimp [Ctotal];linarith
  have hCi (i:ι):C i≤Ctotal:=by
    have hsum:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Ctotal];linarith
  refine ⟨∑i,degree i,Ctotal,hCtotal,?_⟩
  intro ν
  have hev:∀ᶠZ:ℝ in atTop,∀i:ι,_ := Filter.eventually_all.mpr (fun i=>hb i (ν i))
  obtain ⟨Zbase,hbase⟩:=eventually_atTop.mp hev
  refine ⟨max 2 Zbase,lt_max_of_lt_left (by norm_num),?_⟩
  intro i Z P hZ hP hPcap η z hz F hcond Q hQM hQν hex σ t v V hσ hσhi hV hv
  have hZ0:Zbase≤Z:=(le_max_right _ _).trans hZ
  have hZp:0<Z:=lt_of_lt_of_le (by norm_num:0<(2:ℝ)) ((le_max_left _ _).trans hZ)
  refine (hbase Z hZ0 i P hP hPcap η z hz F hcond Q hQM hQν hex σ t v hσ hσhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul (hCi i) _ (by positivity) (zero_le_one.trans hCtotal)
  calc
    _≤(1+|t|+V)^(degree i):=pow_le_pow_left₀ (by positivity) (by linarith) _
    _≤_:=pow_le_pow_right₀ (by linarith [abs_nonneg t])
      (Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i))

theorem actual_relative_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → (∀i,Q≤(ν i).modulus) → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*annularWeight (W i) (P i) (σ i) (freq i) I
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,hC,hbound⟩:=relative_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,pow_pos (zero_lt_one.trans_le hC) _,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  let excess:=CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w excess κ mesh (le_max_right _ _) hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,CenteredMomentLiveCapacity.remaining_capacity J R hR w n₁ n₂ width κ hpay,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQν hex σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
  dsimp only
  have hZ1:1≤Z:=hZ₀.le.trans hZ
  have hZp:0<Z:=zero_lt_one.trans_le hZ1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hZ1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) (Z^(w i)))
      (fun I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))‖^2≤
      B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hZ1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hwcap i)) η z hz F hcond Q hQM (hQν i) hex
      (σ i) t (freq i) V (hσ i) (hσhi i) hV (hfreq i)
    rw [←Real.rpow_mul hZp.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η fixedBadMask 1 z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i)))
    (fun i I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hZp w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(excess/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hZ1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hZp.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
