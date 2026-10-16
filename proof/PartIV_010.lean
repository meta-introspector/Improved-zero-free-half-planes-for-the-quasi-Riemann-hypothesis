    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤ Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hx (X:ℝ):X≤ Z^(length Z X):=by
    rw [length, CenteredMomentEnergyBands.length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=> Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤ Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
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
    (ι:=α) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving (fun _=> hbslot) ha (by linarith) hM hεdiag hξ
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
      (p.support 0) (p.support 1) (fun _=> le_rfl) s.puncture s.radial s.radial_support
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
end SevenEighths.CenteredMomentEnergyPositiveHighSourceIVNF

end

end OAI

end ExtendedModule19


end NFModule72

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters -/
section NFModule73
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters -/
section ExtendedModule20

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParametersIVNF
open CenteredMomentEnergyPositiveHighParameters hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV hiding balanced_four_scale_gates energy_swap original_unbalanced_from_low
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentEnergyReferenceLivePowerIV hiding original_reference_power_live
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePowerIVNF CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSourceIVNF CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetricIVNF
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma actual_width_le (hZ:1< Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1< Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤ Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤ s.width:=by
  have hv:0< CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1< Z)(hwidth:0< s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤ N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=> le_rfl)

omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤ N)(hZ:1< Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0< s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=> le_rfl)
  have hconst:0≤ Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst

end SevenEighths.CenteredMomentEnergyPositiveHighParametersIVNF

end

end OAI

end ExtendedModule20


end NFModule73

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission -/
section NFModule74
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission -/
section ExtendedModule21

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmissionIVNF
open CenteredMomentEnergyPositiveBalancedAdmission hiding exact_log_volume fixed_fields fixed_lower_product four_lower_scales four_upper_scales state_capacity_packet
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV hiding balanced_four_scale_gates energy_swap original_unbalanced_from_low
open CenteredMomentEnergyPositiveHighParametersIV hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentEnergyReferenceLivePowerIV hiding original_reference_power_live
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePowerIVNF CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSourceIVNF CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetricIVNF
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParametersIVNF
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

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤ N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=> le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

lemma exact_log_volume (hZ:1< Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem four_upper_scales (κ L:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ L) :
    (balancedSource).X₁≤ Z^L ∧ (balancedSource).X₂≤ Z^L ∧
    (balancedSource).Y₁≤ Z^L ∧ (balancedSource).Y₂≤ Z^L := by
  have hp:0< Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=> hw i))
  have hxy:X₁*X₂≤ volume balancedSource:=by
    change X₁*X₂≤ X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤ Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤ Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

theorem four_lower_scales (hZ:1< Z)(hwidth:0< s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem state_capacity_packet (κ L:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ L) :
    1≤ s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤ s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤ s.width ∧
    volume balancedSource≤ Z^s.width ∧ Real.logb Z (volume balancedSource)≤ s.width ∧
    volume balancedSource≤ Z^L ∧
    (s.puncture.absNorm:ℝ)≤ Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmissionIVNF

end

end OAI

end ExtendedModule21


end NFModule74

/- No-floor source OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters -/
section NFModule75
/- BEGIN OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters -/
section ExtendedModule22

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstSourceParametersIVNF
open CenteredMomentEnergyFirstSourceParameters hiding columnLoss columnLoss_physical eventually_actual_four_fit maskEpsilon parameter_gates ready_budget_final sourceEpsilon source_cap_mono

open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤ Bschedule)(ht:0≤ ts)(hem:0≤ em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤ M)(hA:0≤ A)(hB:0≤ B)
    (hκ:(13/18:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0< sigma ∧ sigma≤1 ∧ 0< r/4 ∧ r/4≤ sigma/4 ∧ r/4≤1 ∧
      0< sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0< maskEpsilon M B ε ∧ 0< mesh M B κ ε ∧
      mesh M B κ ε≤ sigma/12 ∧ 0≤ sigma/12 ∧ sigma/12< sigma/6 ∧
      0<2*sigma+1 ∧ 0≤ A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤ amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0< sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤ reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤ M)(hA:0≤ A)(_hP:0≤ P)(hB:0≤ B)(hready:readyBudget A P≤ B)
    (hκ:(13/18:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤ stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤ columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤ M)(hB:0≤ Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤ Bmask):
    readyBudget A P≤ CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤ count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤ CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end SevenEighths.CenteredMomentEnergyFirstSourceParametersIVNF

end

end OAI

end ExtendedModule22


end NFModule75

/- No-floor source OAI.NumberTheory.DirichletL.Energy.NaturalLowPhysical -/
section NFModule76
/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalLowPhysical -/
section ExtendedModule23

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowPhysicalIVNF
open CenteredMomentEnergyNaturalLowPhysical hiding actual_natural_low_physical
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyFirstSourceParametersIV hiding columnLoss columnLoss_physical eventually_actual_four_fit maskEpsilon parameter_gates ready_budget_final sourceEpsilon source_cap_mono
open CenteredMomentEnergyPositiveBalancedAdmissionIV hiding exact_log_volume fixed_fields fixed_lower_product four_lower_scales four_upper_scales state_capacity_packet
open CenteredMomentEnergyPositiveHighParametersIV hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParametersIVNF CenteredMomentEnergyPositiveBalancedAdmissionIVNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIVNF
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_natural_low_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(1/50:ℝ)≤κ)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLbase:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤2*max Lgoal Mparent+r/4:=by positivity
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalLowPhysicalNF.actual_low_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  let inp:=zeroSourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=(both_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂).2
  have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
    hw hκsmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent≤2*max Lgoal Mparent+r/4:=by linarith
  have hu1:inp.X₁≤ Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2:inp.X₂≤ Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hlowV:Real.logb Z (volume inp)≤5*state.width/6:=
    (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyNaturalLowPhysicalIVNF

end

end OAI

end ExtendedModule23


end NFModule76

/- No-floor source OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionBounded -/
section NFModule77
/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionBounded -/
section ExtendedModule24

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionBoundedIVNF
open CenteredMomentEnergyOriginalHighReflectionBounded hiding original_high_power
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionOriginalIV hiding original_high_from_low
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginalIVNF CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_high_from_low (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hxiM:xi≤ s.width/15:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumcap:(∑i,w i)≤ Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionBoundedIVNF

end

end OAI

end ExtendedModule24


end NFModule77

/- No-floor source OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetricBounded -/
section NFModule78
/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetricBounded -/
section ExtendedModule25

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIVNF
open CenteredMomentEnergyOriginalHighReflectionSymmetricBounded hiding original_unbalanced_from_low
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionBoundedIV hiding original_high_power
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV hiding balanced_four_scale_gates energy_swap original_unbalanced_from_low
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionBoundedIVNF
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyOriginalHighReflectionSymmetricIVNF

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIVNF

end

end OAI

end ExtendedModule25


end NFModule78

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly -/
section NFModule79
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly -/
section ExtendedModule26

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyIVNF
open CenteredMomentEnergyPositiveHighAssembly hiding actual_high_source_split low_restrict
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV hiding balanced_four_scale_gates energy_swap original_unbalanced_from_low
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceIVNF CenteredMomentEnergyOriginalHighReflectionSymmetricIVNF
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] [DecidableEq α] in
lemma low_restrict (W:ℝ→ℂ)(bslot a b bΦ Bmask L L' Lslot lo hi Mcap d d' κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hZ:1≤ Z)(hL:L'≤ L)(hd:d≤ d')(hC:0≤ C)
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
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0< d ∧ 0≤ L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0< Cu ∧ 0< Cr ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
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
  · exact (show 0≤ Lu by linarith).trans (le_max_left _ _)
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
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
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
end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyIVNF

end

end OAI

end ExtendedModule26


end NFModule79

/- No-floor source OAI.NumberTheory.DirichletL.Energy.ReferenceRobustBounded -/
section NFModule80
/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceRobustBounded -/
section ExtendedModule27

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustBoundedIVNF
open CenteredMomentEnergyReferenceRobustBounded hiding original_reference_power_robust
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyReferenceRobustOriginalIV hiding original_reference_from_low_robust
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginalIVNF CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-rho/100≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_reference_from_low_robust (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi (rho/100) saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by positivity) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hxiM:xi+8*(rho/100)/5≤ s.width/15:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hg:=CenteredMomentEnergyLiveClippingDefectIVNF.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤ Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyReferenceRobustBoundedIVNF

end

end OAI

end ExtendedModule27


end NFModule80

/- No-floor source OAI.NumberTheory.DirichletL.Energy.ReferenceLiveBounded -/
section NFModule81
/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceLiveBounded -/
section ExtendedModule28

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLiveBoundedIVNF
open CenteredMomentEnergyReferenceLiveBounded hiding original_reference_power_live
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyReferenceRobustOriginalIV hiding original_reference_from_low_robust
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginalIVNF CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=
    CenteredMomentEnergyReferenceRobustBoundedIVNF.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefectIVNF.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases CenteredMomentEnergyLiveClippingDefectIVNF.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=CenteredMomentEnergyLiveClippingDefectIVNF.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.CenteredMomentEnergyReferenceLiveBoundedIVNF

end

end OAI

end ExtendedModule28


end NFModule81

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded -/
section NFModule82
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded -/
section ExtendedModule29

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundedIVNF
open CenteredMomentEnergyPositiveHighSourceBounded hiding actual_positive_source_entry
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentEnergyReferenceLiveBoundedIV hiding original_reference_power_live
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLiveBoundedIVNF CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

open CenteredMomentEnergyPositiveHighSourceIVNF

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e→ 0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
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
    (ι:=α) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving (fun _=> hbslot) ha (by linarith) hM hεdiag hξ
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
      (p.support 0) (p.support 1) (fun _=> le_rfl) s.puncture s.radial s.radial_support
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
end SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundedIVNF

end

end OAI

end ExtendedModule29


end NFModule82

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded -/
section NFModule83
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded -/
section ExtendedModule30

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBoundedIVNF
open CenteredMomentEnergyPositiveHighAssemblyBounded hiding actual_high_source_split
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIV hiding original_unbalanced_from_low
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV hiding balanced_four_scale_gates energy_swap original_unbalanced_from_low
open CenteredMomentEnergyPositiveHighAssemblyIV hiding actual_high_source_split low_restrict
open CenteredMomentEnergyPositiveHighSourceBoundedIV hiding actual_positive_source_entry
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceIVNF (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetricIVNF (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBoundedIVNF CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIVNF
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveHighAssemblyIVNF (low_restrict)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0< d ∧ 0≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0< Cu ∧ 0< Cr ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e→ 0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
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
  · exact (show 0≤ Lu by linarith).trans (le_max_left _ _)
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
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
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
end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBoundedIVNF

end

end OAI

end ExtendedModule30


end NFModule83

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighBound -/
section NFModule84
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighBound -/
section ExtendedModule31

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBoundIVNF
open CenteredMomentEnergyPositiveHighBound hiding actual_high_from_physical
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIV hiding original_unbalanced_from_low
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV hiding balanced_four_scale_gates energy_swap original_unbalanced_from_low
open CenteredMomentEnergyPositiveHighAssemblyBoundedIV hiding actual_high_source_split
open CenteredMomentEnergyPositiveHighAssemblyIV hiding actual_high_source_split low_restrict
open CenteredMomentEnergyPositiveHighParametersIV hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentEnergyPositiveHighSourceBoundedIV hiding actual_positive_source_entry
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentEnergyReferenceStateIV hiding balanced_reference_geometry balanced_reflection_margins comparisonFirst comparisonSecond comparison_positive comparison_same_product comparison_second_power effectiveRadial effectiveState effective_character_cap effective_character_nonprincipal effective_row_norm radialEnergy_effective
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceIVNF (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetricIVNF (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBoundedIVNF CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIVNF
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveHighAssemblyIVNF (low_restrict)

open CenteredMomentEnergyPositiveHighAssemblyBoundedIVNF CenteredMomentEnergyPositiveHighParametersIVNF
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤ e→0≤ K→0≤ Cmass→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
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
  have hP:0≤ P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0≤ D:=by dsimp [D];positivity
  have hT:0≤ T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0< Cfixed:=by dsimp [Cfixed];positivity
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
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z^(s.width+efinal)
  have hF:0≤ F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤ Jout)(hej:ej≤ efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z^(s.width+ej)≤ F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej≤ s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤ Jout:=by dsimp [Jout];omega
  have hjr:Jr≤ Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤ Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤ Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced|⟨hfour,hsource⟩
  · change _≤ Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z^(s.width+e+ε) at hunbalanced
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤ Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        CenteredMomentAmplificationChildInput.volume inp≤ Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤ P*(p.control U)^2:=by
      have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
        (Fintype.card α) le_rfl U
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤ efinal):s.radial.scale*Z^x≤ Z^(s.width+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤ A)(hx:x≤ efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
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
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤ Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤ Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
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

end SevenEighths.CenteredMomentEnergyPositiveHighBoundIVNF

end

end OAI

end ExtendedModule31


end NFModule84

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound -/
section NFModule85
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound -/
section ExtendedModule32

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundIVNF
open CenteredMomentEnergyPositiveHighSourceBound hiding PhysicalHighAt PositiveHighAt actual_high_stage_from_physical positive_from_stages
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyPositiveHighAssemblyIV hiding actual_high_source_split low_restrict
open CenteredMomentEnergyPositiveHighBoundIV hiding actual_high_from_physical
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentSecondHeightFamily
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveHighSourceIVNF (balancedInput)
open CenteredMomentEnergyPositiveHighBoundIVNF CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyPositiveHighAssemblyIVNF (low_restrict)
def PhysicalHighAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0< a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤ hi,
    0≤ height→(∀i,|freq i|≤ height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,
    X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    5*state.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
    let inp:=balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂;
    (Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ/volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

def PositiveHighAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤ hi)→
    0≤ height→(∀i,|v i|≤ height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ rho≤ s.width→s.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0< X₁→0< X₂→X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=> primePool M H bslot (Z^(w i)))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem actual_high_stage_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (hrho:0< rho)(hε:0<ε)(hMcap:0≤ Mcap)(hBmask:0≤ Bmask)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(L Lslot κ e emass efinal:ℝ)(η₀:Character)(Q:Ideal O)(K Cphysical:ℝ),
      13/18≤κ→0≤ e→0≤ K→0≤ Cphysical→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
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
  have hCfixed:0< Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤ Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset α):Jj T≤ Jout:=Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ T)
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
  have hz:0≤ Z:=zero_le_one.trans hZ1.le
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

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundIVNF

end

end OAI

end ExtendedModule32


end NFModule85

/- No-floor source OAI.NumberTheory.DirichletL.Energy.NaturalLowStage -/
section NFModule86
/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalLowStage -/
section ExtendedModule33

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowStageIVNF
open CenteredMomentEnergyNaturalLowStage hiding actual_low_from_bands
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyFirstSourceParametersIV hiding columnLoss columnLoss_physical eventually_actual_four_fit maskEpsilon parameter_gates ready_budget_final sourceEpsilon source_cap_mono
open CenteredMomentEnergyNaturalLowPhysicalIV hiding actual_natural_low_physical
open CenteredMomentEnergyPositiveBalancedAdmissionIV hiding exact_log_volume fixed_fields fixed_lower_product four_lower_scales four_upper_scales state_capacity_packet
open CenteredMomentEnergyPositiveHighParametersIV hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParametersIVNF CenteredMomentEnergyPositiveBalancedAdmissionIVNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIVNF
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyNaturalLowPhysicalIVNF CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_from_bands
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)(hΦ:2≤ bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(1/50:ℝ)≤κ)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uout:Finset (ℕ×ℕ),∃Jout:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi Mparent
        (physicalLoss Mglobal B ε k) κ Z η₀ Q Jout Uout (C*(C₀+C₁+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (physicalLoss Mglobal B ε k) Z Jout Uout (C*(C₀+C₁+1)) :=by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hmarg:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hbΦ:0< bΦ:=by linarith
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hentry⟩:=
    CenteredMomentEnergyPositiveLowSourceControlled.actual_low_stages_from_physical (α:=α)
      M H hH W hW.continuous aslot bslot lo hi a b bΦ Mparent (r/4) (r/4)
      (2*amplification ε+1) haslot hWs hbslot ha hb hbΦ hMp (by positivity) (by positivity)
  obtain ⟨U,J,hphysical⟩:=actual_natural_low_physical (α:=α) M H hH W hW aslot bslot lo hi a b bΦ
    haslot hWs hbslot ha hb Mglobal A B Bmask Mparent Mchild Lgoal Lslot Mchild κ ε k
    hMg hA hB hBm hMp hMc hL hLs hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  let Umerge:=S∪U
  let Jmerge:=degree+J
  have hS:S⊆Umerge:=Finset.subset_union_left
  have hU:U⊆Umerge:=Finset.subset_union_right
  have hdeg:degree≤ Jmerge:=Nat.le_add_right _ _
  have hJ:J≤ Jmerge:=Nat.le_add_left _ _
  have halower:a/max 1 b≤ a:=by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    nlinarith [le_max_left (1:ℝ) b]
  have hlen:Lgoal≤2*max Lgoal Mparent+r/4:=by
    have hh:=le_max_left Lgoal Mparent
    linarith
  refine ⟨insert (0,0) Umerge,Jmerge,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphys⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let Cout:=Cfixed*(Cp+1)+1
  have hCout:0< Cout:=by dsimp [Cout];positivity
  refine ⟨Cout,hCout,?_⟩
  filter_upwards [hentry,hphys] with Z he hp
  refine ⟨hp.1,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
  have hzsmall:=zeroAt_transport (internalQ Q η₀)
    (a/max 1 b) b bΦ Bmask _ Mchild εchild Z
    (a/max 1 b) b 2 0 _ Mchild εchild degree degree S S C₀ C₀ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₀ le_rfl hzero
  have hpsmall:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    (a/max 1 b) b 2 0 _ Mchild εchild η₀ Q degree degree S S C₁ C₁ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hpos
  have hold:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    a b bΦ Bmask Lgoal Mchild (physicalLoss Mglobal B ε k) η₀ Q
    degree Jmerge S Umerge C₁ C₁ hp.1.le halower le_rfl le_rfl le_rfl hlen le_rfl
    (hell.trans hmarg.2.1) hdeg hS hC₁ le_rfl hpos
  have hm:=hp.2 εchild C₀ C₁ hell hC₀ hC₁ hzsmall hpsmall
  have hm':PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
      a b bΦ Bmask Lgoal Lslot Mchild Mparent κ (r/4) (physicalLoss Mglobal B ε k)
      Z ha Ψ η₀ Q Umerge Jmerge (Cp*(C₀+C₁+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hm T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤ Z:=zero_le_one.trans hp.1.le
    have hcontrol:=profile_control_mono p hU
    have hc0:=p.control_nonneg U
    have hheight1:1≤1+|t|+height:=by linarith [abs_nonneg t]
    apply hh.trans
    gcongr
  have hsave:-(2*amplification ε+1)≤ physicalLoss Mglobal B ε k:=by
    have hs:0< amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
    linarith [hmarg.1]
  have hout:=he.2 Bmask Lgoal Lslot Mchild κ (physicalLoss Mglobal B ε k) η₀ Q Umerge Jmerge
    (Cp*(C₀+C₁+1)) C₁ hκsmall (by positivity) hC₁ hmarg.2.2.1 hsave hold hm'
  have hC:Cfixed*(Cp*(C₀+C₁+1)+1)+C₁≤ Cout*(C₀+C₁+1):=by
    dsimp [Cout]
    nlinarith [mul_nonneg hCfixed.le hC₀,mul_nonneg hCfixed.le hC₁]
  constructor
  · exact CenteredMomentEnergyStageMonotonicity.positiveLowAt_transport (α:=α) M H hH W bslot
      a b bΦ Bmask Lgoal Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) η₀ Q Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.1
  · exact CenteredMomentEnergyStageMonotonicity.zeroLowAt_transport (internalQ Q η₀)
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.2

end SevenEighths.CenteredMomentEnergyNaturalLowStageIVNF

end

end OAI

end ExtendedModule33


end NFModule86

/- No-floor source OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction -/
section NFModule87

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInductionNF
open CenteredMomentEnergyCappedWidthInduction hiding CertifiedBand actual_child_band bandWidth bandWidth_le bandWidth_le_schedule bandWidth_nonneg bandWidth_terminal certified_floor certified_terminal
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyWidthFloor hiding actual_joint_floor
open CenteredMomentEnergyWidthInduction hiding CertifiedBand certified_floor certified_terminal child_length child_support lengthAt lowerAt lowerAt_pos remaining
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBandsNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyWidthFloorNF CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySourceNF
local notation "O"=> HeckeFamily.O

open CenteredMomentEnergyWidthInductionNF (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

def bandWidth (M B ε:ℝ)(k:ℕ):ℝ:=min M (width M B ε k)
lemma bandWidth_le (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤ M:=min_le_left _ _
lemma bandWidth_le_schedule (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤ width M B ε k:=min_le_right _ _
lemma bandWidth_nonneg (M B ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hε:0<ε)(k:ℕ):
    0≤ bandWidth M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.1
  have hs:0< amplification ε:=(bounds M B 0 ε hM hB (by norm_num) hε).1
  unfold bandWidth width
  positivity
lemma bandWidth_terminal (M B ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hε:0<ε):
    bandWidth M B ε (count M ε)=M:=by
  have hh: M< width M B ε (count M ε):=
    (bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.2.2.2.2.2.1
  exact min_eq_left hh.le
lemma actual_child_band (M B ε parent child:ℝ)(hε:0<ε)(k:ℕ)
    (hp:parent≤ bandWidth M B ε (k+1))(hc:child≤ parent-amplification ε/2):
    child≤ bandWidth M B ε k:=by
  have hs:0< amplification ε:=lt_min (by norm_num) (by positivity)
  apply le_min
  · have hh:=hp.trans (bandWidth_le M B ε (k+1));linarith
  · exact child_band M B ε parent child k (hp.trans (bandWidth_le_schedule M B ε (k+1))) hc

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤ M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0< a)(hb:0≤ b)(hrad:0< radial)(hmask:0≤ Bmask)(hMcap:0≤ Mcap)
    (hκ0:0≤κ)(hε:0<ε)(hbeta:(1/50:ℝ)≤κ)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have ha0:=lowerAt_pos a b Mcap ε ha 0
  obtain ⟨degree,S,Czero,Cpositive,hCzero,hCpositive,hfloor⟩:=
    actual_joint_floor (α:=α) M H hH Mcap Bs κ ε hMcap hBs hκ0 hε W aslot bslot
      haslot hWs hW (lowerAt a b Mcap ε 0) b radial Bmask (lengthAt Mcap Bmask L ε 0)
      lo hi ha0 hb hrad hmask hbeta hκ
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM _ _ _
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hfloor η₀] with Z hZ
  have hh:=hZ.2 Q hQM
  have hloss:loss Mcap Bs ε 0≤ stageLoss Mcap Bs ε 0:=by
    unfold stageLoss
    linarith
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hh.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hh.2

omit [Fintype α] [DecidableEq α] in
theorem certified_terminal (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hmask:0≤ Bmask)(hMcap:0≤ Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤ M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1< Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  obtain ⟨hs,hs1,hse,hr,hm,hmm,hκm,h20,hcover,hloss⟩:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have he:stageLoss Mcap Bs ε (count Mcap ε)≤ε:=by
    have hh:=stageLoss_final Mcap Bs κ ε hMcap hBs hκ0 hε (count Mcap ε) le_rfl
    linarith
  obtain ⟨degree,S,hbound⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCzero,hCpositive,hcert⟩:=hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hcert] with Z hZ
  have hz:=hZ.2.1
  have hp:=hZ.2.2
  simp only [lowerAt,lengthAt,remaining,Nat.sub_self,CenteredMomentEnergyProfiles.lower,range] at hz hp
  have hterminal:=bandWidth_terminal Mcap Bs ε hMcap hBs hε
  change bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (count Mcap ε)=Mcap at hterminal
  rw [hterminal] at hz hp
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hz
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hp

end SevenEighths.CenteredMomentEnergyCappedWidthInductionNF

end

end OAI

end NFModule87

/- No-floor source OAI.NumberTheory.DirichletL.Energy.CappedLowStage -/
section NFModule88
/- BEGIN OAI.NumberTheory.DirichletL.Energy.CappedLowStage -/
section ExtendedModule34

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedLowStageIVNF
open CenteredMomentEnergyCappedLowStage hiding actual_capped_low
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyCappedWidthInduction hiding CertifiedBand actual_child_band bandWidth bandWidth_le bandWidth_le_schedule bandWidth_nonneg bandWidth_terminal certified_floor certified_terminal
open CenteredMomentEnergyWidthInduction hiding CertifiedBand certified_floor certified_terminal child_length child_support lengthAt lowerAt lowerAt_pos remaining
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBandsNF
open CenteredMomentEnergyCappedWidthInductionNF CenteredMomentEnergyWidthInductionNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyCappedRequests CenteredMomentEnergySourceCapSchedule
open CenteredMomentNaturalFixedRaySourceNF
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_capped_low
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0< aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤ bslot)
    (ha:0< a)(hb:0≤ b)(hrad:2≤ radial)(hmask:0≤ Bmask)(hMcap:0≤ Mcap)
    (hκ:(13/18:ℝ)≤κ)(hε:0<ε)(hbeta:(1/50:ℝ)≤κ)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(k:ℕ)(hk:k< count Mcap ε)
    (hold:CenteredMomentEnergyCappedWidthInductionNF.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:Character,∀Q:Ideal O,Q≤ M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C :=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Ag:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1))
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap ε)
  have hAg:0≤ Ag:=by dsimp [Ag];positivity
  have hMp:0≤ Mp:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε (k+1)
  have hMc:0≤ Mc:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε k
  have hMpCap:Mp≤ Mcap:=bandWidth_le Mcap Bs ε (k+1)
  have hMpAg:Mp≤ Ag:=by dsimp [Ag];linarith
  have hLnext:0≤ lengthAt Mcap Bmask L ε (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0≤ Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hκ0:0≤κ:=by linarith
  have hbounds:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have hmesh:0≤ fineMesh Mcap Bmask L κ ε:=hbounds.2.2.2.2.1.le
  have hr:0< reserve Mcap Bs ε:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs ε/4≤1:=by
    have hh:reserve Mcap Bs ε≤ amplification ε/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask≤ Bs:=
    readyBudget_le_schedule Mcap Bmask L ε Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤ Mc:=parent_drop Mcap Bs ε hε k
  have hlength:2*max Lreq Mp+reserve Mcap Bs ε/4≤ lengthAt Mcap Bmask L ε k:=
    previous_admits Mcap Bmask L ε Mp (reserve Mcap Bs ε/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap ε k hk
  obtain ⟨degree,S,hold⟩:=hold
  obtain ⟨U,J,hstage⟩:=CenteredMomentEnergyNaturalLowStageIVNF.actual_low_from_bands
    (α:=α) M H hH W hW aslot bslot lo hi (lowerAt a b Mcap ε (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap ε ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L κ ε) κ ε k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hκ hbeta hκbeta hε
    le_rfl hdrop degree S
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,Cp,hCz,hCp,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cs,hCs,hstage⟩:=hstage η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cs*(Cz+Cp+1),by positivity,?_⟩
  filter_upwards [hold,hstage] with Z hold hs
  have hz:=hold.2.1
  have hp:=hold.2.2
  rw [hsupport] at hz hp
  have hz':ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) Mc (stageLoss Mcap Bs ε k) Z degree S Cz:=
    zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cp Cp hold.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  exact ⟨hs.1,hs.2 (stageLoss Mcap Bs ε k) Cz Cp le_rfl hCz.le hCp.le hz' hp'⟩

end SevenEighths.CenteredMomentEnergyCappedLowStageIVNF

end

end OAI

end ExtendedModule34


end NFModule88

/- No-floor source OAI.NumberTheory.DirichletL.Energy.CanonicalHighSource -/
section NFModule89

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighSourceNF
open CenteredMomentEnergyCanonicalHighSource hiding actual_original_left_high_column
open CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands allocated_pair pair scale scale_cap scale_pos
open CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands
open CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power front_mono
open CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power
open CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands
open CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source
open CenteredMomentEnergyCanonicalHighColumn hiding actual_admitted_subsets_high_column
open CenteredMomentEnergyCanonicalLiveBound hiding LiveChild actual_live_canonical_child_bands energy_zero_of_not_live
open CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column inherited_height_split source_mass_cap
open CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source
open CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source
open CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBoundNF CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSourceNF CenteredMomentEnergyCanonicalCommonPaidNF
open CenteredMomentEnergyCanonicalReferencePaidNF CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClippedNF CenteredMomentEnergyAllocatedHomogeneousNF
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBandsNF
open CenteredMomentEnergyAllocatedPaidNF CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBoundNF CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReferenceNF CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniformNF CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPowerNF CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers
open CenteredMomentEnergyCanonicalLowColumnNF CenteredMomentEnergyCanonicalHighColumnNF CenteredMomentFirstNonexceptionalLocalWeightSum

theorem actual_original_left_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(1/50:ℝ)≤κ)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤ A)(hPcap:0≤ Pcap)(heta:eta< sigma/6)(hPrimeLoss:0< primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤ Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0< Ccolumn ∧ ∃Z₀:ℝ,1< Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ eta) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤ Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀_hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.left ∨ τ=F.right →
    ∀K:ℝ,1≤ K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤ sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤ A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤ Mdecl →
    Z^(Mwidth/4)≤ src.X₁ → Z^(Mwidth/4)≤ src.X₂ →
    Z^(Mwidth/4)≤ src.Y₁ → Z^(Mwidth/4)≤ src.Y₂ →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_high_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=CenteredMomentEnergyFirstTwoSeedAdmission.eventually_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ t
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1< Z:=hZbase.trans_le hZbaseLe
  have hZpos:0< Z:=zero_lt_one.trans hZ
  have hK:0< K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤ A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤ Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤ Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤ Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=> by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤ x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤ x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedC:seed0∣C:=hcols.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=> by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hNC:(C.absNorm:ℝ)≤ Z^(A+1):=hcols.2.2.2.2.2.1.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤ Z^Bseed:=by
    calc
      _≤ sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤ sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤ Z^(A+1):=hradius.1
      _≤ Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  have hmod:τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}:=by
    rcases hτ with rfl|rfl
    · exact F.left_modulus
    · exact F.right_modulus
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies τ
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E})
        K (volume src)) Z ξ:=by simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedC
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=> n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock false B t hB
  refine ⟨?_,?_⟩
  · have hmReady:Ready (child src C R0 B τ t) (R0*C)
        (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z (32*1) ξ) reserve)
        Z ξ (readyBudget A Pcap):=hm.1
    simpa only [mul_one] using hmReady
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hpdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun I hI=>(hpdata I hI).1)
      (fun I hI=>(hpdata I hI).2.1) prime.val prime.property
    let input:=child src C R0 B τ t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=> w j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hseparate z (fun j=> hweta j.val)
        (fun j=> hmatch.scale j.val) hsupp (original input (R0*C) seed).active_slot
        (fun j I hI=> input.prime j I ((original input (R0*C) seed).active_subset _ hI))
        _ (hpdata _ hd.2.1).1 (hpdata _ hd.2.1).2.2.1
    have hk:errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by
      have hi:=errorIndex_cases i;omega
    have hrad:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun i=> n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock false B t seed hB M H fixedBadPrimes (Finset.Subset.refl _)
      prime.val prime.property (errorIndex i+1) hk hcop Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hrad)
    rcases he with hdead|hlive
    · exact Or.inl hdead.1
    · have hr:Ready (errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
          (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t)
          ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
          (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z (32*1) ξ) reserve prime.val (errorIndex i+1))
          Z ξ (readyBudget A Pcap):=hlive.1
      exact Or.inr (by simpa only [mul_one] using hr)

end SevenEighths.CenteredMomentEnergyCanonicalHighSourceNF

end

end OAI

end NFModule89

/- No-floor source OAI.NumberTheory.DirichletL.Energy.CanonicalHighPhysical -/
section NFModule90

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighPhysicalNF
open CenteredMomentEnergyCanonicalHighPhysical hiding actual_high_physical
open CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands allocated_pair pair scale scale_cap scale_pos
open CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands
open CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power front_mono
open CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power
open CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands
open CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source
open CenteredMomentEnergyCanonicalLiveBound hiding LiveChild actual_live_canonical_child_bands energy_zero_of_not_live
open CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column inherited_height_split source_mass_cap
open CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source
open CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source
open CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBoundNF CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSourceNF CenteredMomentEnergyCanonicalCommonPaidNF
open CenteredMomentEnergyCanonicalReferencePaidNF CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClippedNF CenteredMomentEnergyAllocatedHomogeneousNF
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBandsNF
open CenteredMomentEnergyAllocatedPaidNF CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBoundNF CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReferenceNF CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniformNF CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPowerNF CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers
open CenteredMomentEnergyCanonicalLowColumnNF CenteredMomentFirstNonexceptionalLocalWeightSum

theorem actual_high_physical
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(1/50:ℝ)≤κ)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤ A)(hPcap:0≤ Pcap)(heta:eta< sigma/6)(hPrimeLoss:0< primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤ Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0< lowerProduct):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cphysical:ℝ,0< Cphysical ∧ ∃Z₀:ℝ,1< Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ eta) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    lowerProduct≤(∏i,src.lo i)*a*a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤ Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤ K →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤ A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤ Mdecl →
    Z^(Mwidth/4)≤ src.X₁ → Z^(Mwidth/4)≤ src.X₂ →
    Z^(Mwidth/4)≤ src.Y₁ → Z^(Mwidth/4)≤ src.Y₂ →
    (∀j:Fin 4,
      CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
          (frequencyLoss Z 32 ξ+reserve+θsource)/6+θclip/3+κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨UL,JL,hleft⟩:=CenteredMomentEnergyCanonicalHighSourceNF.actual_original_left_high_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  obtain ⟨UR,JR,hright⟩:=CenteredMomentEnergyCanonicalRightSourceColumnNF.actual_original_right_high_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  have hphysical (T:Finset α):=CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) JL JR (fun i=>|highs i.val|) (max 1 b) (max 1 b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  let Cmass:ℝ:=1+∑T:Finset α,Cp T
  have hCmass:0< Cmass:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
    dsimp [Cmass];linarith
  have hCpCap (T:Finset α):Cp T≤ Cmass:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
      (Finset.mem_univ T)
    dsimp [Cmass];linarith
  refine ⟨UL∪UR,2*(JL+JR),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CL,hCL,ZL,hZL,hleft⟩:=hleft η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CR,hCR,ZR,hZR,hright⟩:=hright η₀ Q hQM hQ0 hQt hQ72
  have hmL:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JL
  have hmR:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JR
  let Cm:ℝ:=Cmass*(CL+CR)*(1+CenteredMomentSecondWindowBudget.profileMoment JL)*
    (1+CenteredMomentSecondWindowBudget.profileMoment JR)
  have hCm:0< Cm:=by dsimp [Cm];positivity
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hp
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp hall
  refine ⟨Cm,hCm,max Zp (max ZL ZR),lt_of_lt_of_le hZL
    ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ hfit
  have hZL':ZL≤ Z:=(le_max_left _ _).trans ((le_max_right _ _).trans hZZ)
  have hZR':ZR≤ Z:=(le_max_right _ _).trans ((le_max_right _ _).trans hZZ)
  have hZ:1< Z:=hZL.trans_le hZL'
  have hz:0< Z:=zero_lt_one.trans hZ
  have hK:0< K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤ Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤ Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→a≤ x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→a≤ x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
    (delta+reserve+θsource)/6+θclip/3+κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let FL:=CL*(C₀+C₁+1)*(p.control UL)^2*(1+height)^JL
  let FR:=CR*(C₀+C₁+1)*(p.control UR)^2*(1+height)^JR
  let Fcap:ℝ:=(CL+CR)*(C₀+C₁+1)*(p.control (UL∪UR))^2*(1+height)^(JL+JR)
  let frontL:=FL*Z^(deficit+base)
  let frontR:=FR*Z^(deficit+base)
  have hfrontL:0≤ frontL:=by dsimp [frontL,FL];positivity
  have hfrontR:0≤ frontR:=by dsimp [frontR,FR];positivity
  have hFcap:0≤ Fcap:=by dsimp [Fcap];positivity
  have hcontrol (S₁:Finset (ℕ×ℕ))(hs:S₁⊆UL∪UR):p.control S₁≤ p.control (UL∪UR):=by
    unfold Profiles.control
    exact mul_le_mul
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hFL:FL≤ Fcap:=by
    dsimp [FL,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UL
    · exact hcontrol UL Finset.subset_union_left
    · linarith
    · omega
  have hFR:FR≤ Fcap:=by
    dsimp [FR,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UR
    · exact hcontrol UR Finset.subset_union_right
    · linarith
    · omega
  have hcoeff (F:ℝ)(hF:F≤ Fcap)(j:Fin 4):
      (F*Z^(deficit+base))*Z^(powers j)≤ Fcap*Z^(deficit+ell):=by
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul hF (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (Real.rpow_nonneg hz.le _) hFcap
    have hh:powers j+base≤ ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z JL JR
        (fun j=> frontL*Z^(powers j)) (fun j=> frontR*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hleft T θ Z hZL' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.left (Or.inl rfl)
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ v
      simpa only [frontL,FL,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hright T θ Z hZR' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.right rfl
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ v
      simpa only [frontR,FR,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=> by rw [hhiSrc]) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    a a K haPlain haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=> ell) (fun _=> ell)
    (fun j=> frontL*Z^(powers j)) (fun j=> frontR*Z^(powers j)) hFcap
    (fun j=> mul_nonneg hfrontL (Real.rpow_nonneg hz.le _))
    (fun j=> mul_nonneg hfrontR (Real.rpow_nonneg hz.le _))
    (hcoeff FL hFL) (hcoeff FR hFR) (fun _=> le_rfl)
    (fun _=> le_rfl) (fun lab E _ n hne=> hcols lab E n hne)
  have hconst:Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
      CenteredMomentSecondWindowBudget.profileMoment JR≤ Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
    · linarith
  have hheightProduct:(1+height)^(JL+JR)*(1+|src.t|)^(JL+JR)≤
      (1+|src.t|+height)^(2*(JL+JR)):=by
    have heq:(1+|src.t|+height)^(2*(JL+JR))=
        (1+|src.t|+height)^(JL+JR)*(1+|src.t|+height)^(JL+JR):=by
      rw [show 2*(JL+JR)=(JL+JR)+(JL+JR) by omega]
      exact pow_add _ _ _
    rw [heq]
    apply mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
          CenteredMomentSecondWindowBudget.profileMoment JR)*(C₀+C₁+1)*
          (p.control (UL∪UR))^2*((1+height)^(JL+JR)*(1+|src.t|)^(JL+JR))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalHighPhysicalNF

end

end OAI

end NFModule90

/- No-floor source OAI.NumberTheory.DirichletL.Energy.PositiveHighPhysical -/
section NFModule91
/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighPhysical -/
section ExtendedModule35

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighPhysicalIVNF
open CenteredMomentEnergyPositiveHighPhysical hiding actual_positive_high_physical
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyFirstSourceParametersIV hiding columnLoss columnLoss_physical eventually_actual_four_fit maskEpsilon parameter_gates ready_budget_final sourceEpsilon source_cap_mono
open CenteredMomentEnergyPositiveBalancedAdmissionIV hiding exact_log_volume fixed_fields fixed_lower_product four_lower_scales four_upper_scales state_capacity_packet
open CenteredMomentEnergyPositiveHighParametersIV hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentEnergyPositiveHighSourceBoundIV hiding PhysicalHighAt PositiveHighAt actual_high_stage_from_physical positive_from_stages
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSourceIVNF CenteredMomentEnergyPositiveHighSourceBoundIVNF
open CenteredMomentEnergyPositiveHighParametersIVNF CenteredMomentEnergyPositiveBalancedAdmissionIVNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIVNF
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_positive_high_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(1/50:ℝ)≤κ)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalHighAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLphys:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalHighPhysicalNF.actual_high_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (max Lgoal Mparent) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b)]
    with Z hZZ hfit hclipPow
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlarge
  dsimp only
  intro hfour
  let inp:=balancedInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=balanced_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hu:=four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
    hZ hw hκ hcapacity (hstate.trans (le_max_right _ _))
  have hp:=fixed_lower_product M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl le_rfl hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  rw [ht] at hh
  dsimp only [inp,r] at hh
  have hN1:((1:Ideal O).absNorm:ℝ)=1:=by norm_num
  simpa only [hN1,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyPositiveHighPhysicalIVNF

end

end OAI

end ExtendedModule35


end NFModule91

/- No-floor source OAI.NumberTheory.DirichletL.Energy.NaturalHighStage -/
section NFModule92
/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalHighStage -/
section ExtendedModule36

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalHighStageIVNF
open CenteredMomentEnergyNaturalHighStage hiding actual_high_stage
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyFirstSourceParametersIV hiding columnLoss columnLoss_physical eventually_actual_four_fit maskEpsilon parameter_gates ready_budget_final sourceEpsilon source_cap_mono
open CenteredMomentEnergyPositiveBalancedAdmissionIV hiding exact_log_volume fixed_fields fixed_lower_product four_lower_scales four_upper_scales state_capacity_packet
open CenteredMomentEnergyPositiveHighParametersIV hiding actual_conductor_scale actual_width_le balanced_actual_four_scales balanced_control balanced_log_volume balanced_source_cost
open CenteredMomentEnergyPositiveHighSourceBoundIV hiding PhysicalHighAt PositiveHighAt actual_high_stage_from_physical positive_from_stages
open CenteredMomentEnergyPositiveHighSourceIV hiding actual_positive_source_entry balancedInput balanced_matches balanced_volume balanced_volume_bound
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySourceNF CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSourceIVNF CenteredMomentEnergyPositiveHighSourceBoundIVNF
open CenteredMomentEnergyPositiveHighParametersIVNF CenteredMomentEnergyPositiveBalancedAdmissionIVNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIVNF
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_high_stage
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hrho:0< rho)(hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(1/50:ℝ)≤κ)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(lowDegree:ℕ)(Slow:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→0≤ Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      CenteredMomentEnergyReferenceLowBands.PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask
        (Mparent+Bmask+rho/100) Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z η₀ Q
        lowDegree Slow Clow→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi rho Mparent
        (reflectedLoss Mglobal B ε k) κ Z η₀ Q J U (C*(C₀+C₁+Clow+1)) := by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hb:0≤ b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hr4:0< r/4:=by positivity
  have hs:0< amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
  obtain ⟨Ψ,hΨs,hΨn,hstage⟩:=actual_high_stage_from_physical (α:=α) M H hH
    W hW.continuous aslot bslot lo hi a b bΦ rho r Mparent Bmask (r/4) (r/4)
    (2*amplification ε+1) haslot hWs hbslot ha hlo hhi hbΦ hrho hr hMp hBm hr4 hr4
  obtain ⟨Up,Jp,hphysical⟩:=CenteredMomentEnergyPositiveHighPhysicalIVNF.actual_positive_high_physical
    (α:=α) M H hH W hW aslot bslot lo hi a b bΦ haslot hWs hbslot ha hb
    Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε k hMg hA hB hBm hMp hMc hL hLs
    hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  obtain ⟨J,U,Cf,hCf,hstageZ⟩:=hstage lowDegree Slow Jp Up
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphysZ⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cf*(Cp+1),by positivity,?_⟩
  filter_upwards [hstageZ,hphysZ] with Z hstageNow hphysicalNow
  refine ⟨hphysicalNow.1,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hzero hpos hlow
  have hp:=hphysicalNow.2 εchild C₀ C₁ hchild hC₀ hC₁ hzero hpos
  have hm:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hmass:0≤ Cp*(C₀+C₁+1):=by positivity
  have hh:=hstageNow.2 Lgoal Lslot κ (physicalLoss Mglobal B ε k)
    (physicalLoss Mglobal B ε k) (reflectedLoss Mglobal B ε k) η₀ Q
    Clow (Cp*(C₀+C₁+1)) hκ hm.1.le hClow hmass
    (by exact le_rfl) hm.2.2.2.1 (hm.2.2.1.trans hm.2.2.2.1)
    (by have hpos:=hm.1.le.trans hm.2.2.2.1;linarith only [hpos,hs]) hlow hp
  have hconst:Cf*(Clow+Cp*(C₀+C₁+1)+1)≤(Cf*(Cp+1))*(C₀+C₁+Clow+1):=by
    have hh:0≤ Cp*Clow:=mul_nonneg hCp.le hClow
    nlinarith only [mul_nonneg hCf.le hh,mul_nonneg hCf.le hC₀,mul_nonneg hCf.le hC₁]
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge
  apply (hh T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge).trans
  have hd:=diagonalControl_nonneg state.radial.profile
  have hp0:=p.control_nonneg U
  have hz:0≤ Z:=zero_le_one.trans hphysicalNow.1.le
  gcongr

end SevenEighths.CenteredMomentEnergyNaturalHighStageIVNF

end

end OAI

end ExtendedModule36


end NFModule92

/- No-floor source OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysical -/
section NFModule93
/- BEGIN OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysical -/
section ExtendedModule37

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalIVNF
open CenteredMomentEnergyZeroGrowthPhysical hiding actual_growth_physical
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyCanonicalHighPhysical hiding actual_high_physical
open CenteredMomentEnergyFirstSourceParametersIV hiding columnLoss columnLoss_physical eventually_actual_four_fit maskEpsilon parameter_gates ready_budget_final sourceEpsilon source_cap_mono
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSecondHeightFamily
open CenteredMomentEnergyState CenteredMomentEnergyBandsNF
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyZeroGrowthPhysicalReindex CenteredMomentSourceInputReindex
open CenteredMomentEnergyZeroBalancedAdmission CenteredMomentEnergyZeroBalancedDictionary
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstSourceParametersIVNF CenteredMomentEnergyFirstLiveAdmission
open CenteredMomentEnergyCanonicalHighPhysicalNF CenteredMomentEnergyZeroGrowthSource
open CenteredMomentEnergyStageMargins CenteredMomentNaturalFixedRaySourceNF
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceReduction
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_growth_physical
    (Wslot:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Lchild Mparent Mchild
      Mschedule Bschedule ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hLs:0≤ Lslot)(hκ:(13/18:ℝ)≤κ)
    (hbeta:(1/50:ℝ)≤κ)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0< a)(hb:0≤ b)(hBmask:0≤ Bmask)(hLgoal:0≤ Lgoal)(hLchild:0≤ Lchild)
    (hMparent:0≤ Mparent)(hMchild:0≤ Mchild)(hMschedule:0≤ Mschedule)(hBschedule:0≤ Bschedule)
    (hε:0<ε)(hcap: max Mparent (2*Lgoal)≤ Lchild)
    (hready:readyBudget (max Mparent (2*Lgoal)) Bmask≤ Bschedule)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z→
    ∀(k:ℕ)(εchild C₀ C₁ rho:ℝ),εchild≤ stageLoss Mschedule Bschedule ε k→
      0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalGrowthAt (internalQ Q η₀) a b bΦ Bmask Lgoal rho Mparent
        (reserve Mschedule Bschedule ε/4) (physicalLoss Mschedule Bschedule ε k)
        Z ha Ψ Uprofile Jheight (C*(C₀+C₁+1)):=by
  let A:=max Mparent (2*Lgoal)
  let r:=reserve Mschedule Bschedule ε
  have hA:0≤ A:=hMparent.trans (le_max_left _ _)
  obtain ⟨hsigma,hsigma1,hr,hxiSigma,hxi1,hes,hes1,hem,hmesh,hmeshEta,heta0,heta,hSaving,hSeed⟩:=
    parameter_gates Mschedule A Bschedule κ ε hMschedule hA hBschedule hκ hε
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have ha2:0< a^2:=sq_pos_of_pos ha
  obtain ⟨U,J,hphysical⟩:=actual_high_physical (α:=α) M H hH
    Wslot aslot bslot Mchild Lslot (r/4) lo hi κ a b 1
    (maskEpsilon Mschedule Bschedule ε) (by norm_num) hem ha hb
    Lchild hLchild degree S haslot hWs hW hMchild hLs hr hκsmall hbeta hκbeta
    0 1 1 (a^2) (r/4) (by norm_num) (by norm_num) ha2 hr
    (fun _=>1) (fun _=>1) (fun _=> by norm_num)
    (sourceEpsilon Mschedule A Bschedule ε) (r/4) (r/4) (A+1) (r/4)
    (2*amplification ε+1) hes hr hr hr
    (amplification ε) hsigma hxiSigma A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBmask heta hr hsigma1 hxi1 hr hes1 le_rfl (fun _=>Ψ) (r/4) (a*a)
    hr (mul_pos ha ha)
  have hfit:=eventually_actual_four_fit Mschedule A Bmask Bschedule κ ε
    hMschedule hA hBmask hBschedule hready hκ hε
  have hclip:∀ᶠZ:ℝ in atTop,1< Z ∧ Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<2*(r/4) by linarith)))
        (max 1 b*max 1 b)] with Z hZ hz
    exact ⟨hZ,(Real.logb_le_iff_le_rpow hZ (mul_pos
      (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hz⟩
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Zbase,hZbase,hphysical⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Znum,hZnum⟩:=Filter.eventually_atTop.mp (hfit.and hclip)
  refine ⟨C,hC,max Zbase Znum,hZbase.trans_le (le_max_left _ _),?_⟩
  intro Z hZZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpos
  have hZbaseLe:Zbase≤ Z:=(le_max_left _ _).trans hZZ
  have hn:=hZnum Z ((le_max_right _ _).trans hZZ)
  have hZ:1< Z:=hn.1.1
  intro s hQ hsLower hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hlarge
  dsimp only
  intro hfour
  let src:=emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α
  let θ:(∅:Finset α)→RayQuotient.Characters M H:=fun i=> isEmptyElim i
  have hmatch:CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ
      (fun _=>0) (fun _=>0) (fun _=>0) Wslot bslot Z:=by
    constructor <;> intro i <;> exact isEmptyElim i
  have hupper:=four_upper_scales s p ha t X₁ X₂ hX₁ hX₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hu:Z^A≤ Z^Lchild:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  have hgate:=declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hdecl:=declared_capacity_upper s X₁ X₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hK:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  have hbound:=hphysical ∅ θ Z hZbaseLe εchild C₀ C₁ hC₀ hC₁ hzero hpos
    (fun _=>0) (fun _=>0) (fun _=>0) 0 (mesh Mschedule Bschedule κ ε) hmesh.le
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i) (by norm_num)
    (fun i=> isEmptyElim i) src hmatch
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i) (by simp) le_rfl le_rfl
    hb hb (le_max_right _ _) (le_max_right _ _) (by simp)
    s.puncture 1 s.puncture_ne_zero s.puncture_bound squarefree_one one_ne_zero
    s.radial.scale hK.1 p rfl rfl
    (hupper.1.trans hu) (hupper.2.1.trans hu) (hupper.2.2.1.trans hu) (hupper.2.2.2.trans hu)
    (max s.width (length Z X₁+length Z X₂)) s.width (r/4)
    (columnLoss Mschedule Bschedule ε k) hr.le hdecl
    (by
      change length Z X₁+length Z X₂+6*κ*(∑i:(∅:Finset α),(0:ℝ))≤_
      simpa only [Finset.sum_const_zero,mul_zero,add_zero] using
        le_max_right s.width (length Z X₁+length Z X₂))
    (hgate.2.1.trans (le_max_left _ _)) hgate.2.1 (by linarith)
    hn.2.2 (by simp [lowerFactor]) (le_max_left _ _)
    hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hn.1.2 k εchild hchild)
  rw [show physicalMass src s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4)=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4) from
        empty_balanced_mass s p ha t X₁ X₂ hX₁ hX₂ _ _ _ _ _ _ _ _] at hbound
  rw [show volume src=X₁*X₂ from empty_balanced_volume s p ha t X₁ X₂ hX₁ hX₂] at hbound
  have heq:max s.width (length Z X₁+length Z X₂)+columnLoss Mschedule Bschedule ε k+r/4=
      max s.width (length Z X₁+length Z X₂)+physicalLoss Mschedule Bschedule ε k:=by
    dsimp only [r]
    rw [add_assoc,columnLoss_physical]
  simpa only [map_one,Nat.cast_one,div_one,add_zero,
    show (src).t=t from rfl,heq] using hbound

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalIVNF

end

end OAI

end ExtendedModule37


end NFModule93

/- No-floor source OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage -/
section NFModule94
/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage -/
section ExtendedModule38

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalZeroStageIVNF
open CenteredMomentEnergyNaturalZeroStage hiding actual_zero_stage
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily CenteredMomentEnergyBandsNF CenteredMomentEnergyState
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentNaturalFixedRaySourceNF
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_zero_stage
    (W:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Mparent Mchild
      Mschedule Bschedule ε rho:ℝ)(k:ℕ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hLs:0≤ Lslot)(hκ:(13/18:ℝ)≤κ)
    (hbeta:(1/50:ℝ)≤κ)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:2≤ bΦ)(hBmask:0≤ Bmask)(_hLgoal:0≤ Lgoal)
    (hMparent:0≤ Mparent)(hMchild:0≤ Mchild)(hMschedule:0≤ Mschedule)(hBschedule:0≤ Bschedule)
    (hε:0<ε)(hrho:0< rho)(hrhoChild:rho≤ Mchild)
    (hdrop:Mparent-amplification ε/2≤ Mchild):
    ∃d Lgrow Llow:ℝ,0< d ∧ d≤1 ∧ 0< Lgrow ∧ Lgoal≤ Lgrow ∧
      Lgrow=max Lgoal (Mparent+Bmask+2*d)+1 ∧
      Llow=max Lgrow (Mparent+Bmask+rho/100) ∧
      Llow≤ max Lgoal (Mparent+Bmask+rho/100+2)+1 ∧
    ∀Lchild:ℝ,0≤ Lchild→max Mparent (2*Lgrow)≤ Lchild→
      readyBudget (max Mparent (2*Lgrow)) Bmask≤ Bschedule→
    ∀degree degreeLow:ℕ,∀S Slow:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mschedule Bschedule ε k→
      0≤ C₀→0≤ C₁→0≤ Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Llow Mparent
        (physicalLoss Mschedule Bschedule ε k) Z degreeLow Slow Clow→
      ZeroAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (stageLoss Mschedule Bschedule ε (k+1)) Z J U (C*(Clow+C₀+C₁+1)):=by
  let r:=reserve Mschedule Bschedule ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).2.2.2.1
  have hb:0≤ b:=by linarith
  have hrad:0< bΦ:=by linarith
  obtain ⟨d,Lgrow,hd,hd1,hLg,hgoal,hLexact,hLupper,hsharp⟩:=
    CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
      a b bΦ r Mparent Bmask Lgoal ha hlo hhi hrad hr hMparent hBmask
  let Llow:=max Lgrow (Mparent+Bmask+rho/100)
  refine ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,rfl,?_,?_⟩
  · apply max_le
    · apply hLupper.trans
      exact add_le_add (max_le_max (le_refl Lgoal)
        (show Mparent+Bmask+2≤ Mparent+Bmask+rho/100+2 by linarith only [hrho])) (le_refl (1:ℝ))
    · have hh:=le_max_right Lgoal (Mparent+Bmask+rho/100+2)
      linarith
  intro Lchild hLc hcap hready degree degreeLow S Slow
  obtain ⟨Ψ,hsΨ,hnΨ,hgrowth⟩:=
    CenteredMomentEnergyZeroGrowthSourceControlled.actual_growth_from_physical
      a b bΦ rho r Mparent Bmask (2*Lgrow) Lgrow (r/4) (r/4) (2*amplification ε+1)
      ha hlo hhi hrad hrho hr hMparent hBmask (by positivity) le_rfl (by positivity) (by positivity)
  obtain ⟨Smass,Jmass,hphysical⟩:=
    CenteredMomentEnergyZeroGrowthPhysicalIVNF.actual_growth_physical (α:=α) M H hH
      W aslot bslot Lslot lo hi κ a b bΦ Bmask Lgrow Lchild Mparent Mchild Mschedule Bschedule ε
      haslot hWs hW hLs hκ hbeta hκbeta ha hb hBmask hLg.le hLc hMparent hMchild
      hMschedule hBschedule hε hcap hready hdrop Ψ degree S
  obtain ⟨Jgrowth,Ugrowth,Cgrowth,hCg,hgrowth⟩:=hgrowth (degree+degreeLow) (S∪Slow) Jmass Smass
  obtain ⟨J,U,Csharp,hCs,hsharp⟩:=hsharp Ugrowth
  refine ⟨J,U,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cmass,hCm,Zmass,hZm,hmass⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let C:=Csharp*(Cgrowth*(Cmass+2)+1)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_ge_atTop Zmass,hgrowth,hsharp] with Z hZmZ hg hs
  have hZ:1< Z:=hZm.trans_le hZmZ
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hz hp hl
  have hmarg:=margins Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε k
  have hpLoss:0≤ physicalLoss Mschedule Bschedule ε k:=hmarg.1.le
  have hrLoss:0≤ reflectedLoss Mschedule Bschedule ε k:=hpLoss.trans hmarg.2.2.2.1
  have hlength:Lgrow≤ Lchild:=by linarith [le_max_right Mparent (2*Lgrow)]
  have hap:a/max 1 b≤ a:=div_le_self ha.le (le_max_left _ _)
  have hzero:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ 2 0 _ _ _
    degree degree S S C₀ C₀ hZ.le le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) hC₀ le_rfl hz
  have hpositive:=positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
    _ _ 2 0 _ _ _ η₀ Q degree degree S S C₁ C₁ hZ.le
    le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hp
  have hmassNow:=hmass Z hZmZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpositive
  have hprevious:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z a b bΦ Bmask Lgrow rho
    (reflectedLoss Mschedule Bschedule ε k) degree (degree+degreeLow) S (S∪Slow) C₀ C₀
    hZ.le hap le_rfl le_rfl le_rfl hlength hrhoChild
    (hchild.trans (hmarg.2.1.trans hmarg.2.2.2.1)) (Nat.le_add_right _ _)
    Finset.subset_union_left hC₀ le_rfl hz
  have hlow:=zeroLowAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    degreeLow (degree+degreeLow) Slow (S∪Slow) Clow Clow hZ.le
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_add_left _ _)
    Finset.subset_union_right hClow le_rfl hl
  have hgrowthNow:=hg.2 (physicalLoss Mschedule Bschedule ε k)
    (physicalLoss Mschedule Bschedule ε k) (reflectedLoss Mschedule Bschedule ε k)
    (internalQ Q η₀) Clow (Cmass*(C₀+C₁+1)) C₀ hpLoss hClow (by positivity) hC₀
    (by unfold reflectedLoss;exact le_rfl) hmarg.2.2.2.1
    (hmarg.2.2.1.trans hmarg.2.2.2.1)
    (by have hh:= (bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).1
        linarith only [hrLoss,hh]) hprevious hlow hmassNow
  have hfinal:=hs.2 (reflectedLoss Mschedule Bschedule ε k) (internalQ Q η₀) Jgrowth
    (Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)) hrLoss (by positivity) hgrowthNow
  rw [reflected_then_zero] at hfinal
  have hfront:Csharp*(Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)+1)≤ C*(Clow+C₀+C₁+1):=by
    have hinner:Clow+Cmass*(C₀+C₁+1)+C₀+1≤(Cmass+2)*(Clow+C₀+C₁+1):=by
      nlinarith [mul_nonneg hCm.le hClow]
    calc
      _≤ Csharp*(Cgrowth*((Cmass+2)*(Clow+C₀+C₁+1))+(Clow+C₀+C₁+1)):=by
        gcongr
        linarith
      _=_:=by dsimp [C];ring
  exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    J J U U _ _ hZ.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) (by positivity) hfront hfinal

end SevenEighths.CenteredMomentEnergyNaturalZeroStageIVNF

end

end OAI

end ExtendedModule38


end NFModule94

/- No-floor source OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor -/
section NFModule95
/- BEGIN OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor -/
section ExtendedModule39

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessorIVNF
open CenteredMomentEnergyCappedAnalyticSuccessor hiding actual_successor
open CenteredMomentEnergyBands hiding PositiveAt ZeroAt exists_positive_bottom length length_nonneg zeroAt_of_zeroBound
open CenteredMomentEnergyCappedWidthInduction hiding CertifiedBand actual_child_band bandWidth bandWidth_le bandWidth_le_schedule bandWidth_nonneg bandWidth_terminal certified_floor certified_terminal
open CenteredMomentEnergyPositiveHighBoundIV hiding actual_high_from_physical
open CenteredMomentEnergyWidthInduction hiding CertifiedBand certified_floor certified_terminal child_length child_support lengthAt lowerAt lowerAt_pos remaining
open CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound natural_relative_twists source_physical_slot_bound
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBandsNF
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyPositiveHighBoundIVNF
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInductionNF (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInductionNF
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyStageMonotonicity
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyCappedRequests
open CenteredMomentEnergySourceCapSchedule CenteredMomentNaturalFixedRaySourceNF
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_successor
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ:(13/18:ℝ)≤κ)(hε:0<ε)
    (hbeta:(1/50:ℝ)≤κ)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (k:ℕ)(hk:k< count Mcap ε)
    (hold:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let ac:=lowerAt a b Mcap ε (k+1)
  let Lc:=lengthAt Mcap Bmask L ε (k+1)
  let Lp:=lengthAt Mcap Bmask L ε k
  let Lreq:=requestLength Mcap Bmask Lc
  let A:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let r:=reserve Mcap Bs ε
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
  have hκ0:0≤κ:=by linarith
  have hb:0≤ b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε).2.2.2.1
  have hr1:r/4≤1:=by
    have hh:=bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε
    have hrs:r≤ amplification ε/100:=min_le_left _ _
    linarith [hh.2.1]
  have hMp:0≤ Mp:=bandWidth_nonneg Mcap Bs ε hMcap.le hBs hε _
  have hMc:0< Mc:=band_positive Mcap Bs ε hMcap hBs hε k
  have hMpM:Mp≤ Mcap:=bandWidth_le _ _ _ _
  have hMcM:Mc≤ Mcap:=bandWidth_le _ _ _ _
  have hac:0< ac:=lowerAt_pos a b Mcap ε ha _
  have haca:ac≤ a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
  have haclo:ac≤1/4:=haca.trans hlo
  have hLc:0≤ Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hLp:0≤ Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask hLc
  have hreqFinal:Lreq≤ range Mcap Bmask L (count Mcap ε):=
    request_le_final Mcap Bmask L ε hMcap.le hmask k hk
  have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)
  have hA:0≤ A:=by dsimp [A];positivity
  have hMA:Mp≤ A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)]
  have hready:readyBudget A Bmask≤ Bs:=
    readyBudget_le_schedule Mcap Bmask L ε A Bmask hMcap.le hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤ Mc:=parent_drop Mcap Bs ε hε k
  have hmesh:0≤ fineMesh Mcap Bmask L κ ε:=
    (fineMesh_pos Mcap Bmask L κ ε hMcap.le hmask hκ0 hε).le
  have hsupport:lowerAt a b Mcap ε k=ac/max 1 b:=child_support a b Mcap ε k hk
  have hrequest:2*max Lreq Mp+r/4≤ Lp:=previous_admits Mcap Bmask L ε Mp (r/4)
    hMcap.le hmask hMpM hr1 k hk
  have hhighL:max Lc Mp≤ Lp:=by
    have hh:max Lc Mp≤ Lreq:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
    have hg:0≤ max Lreq Mp:=hreq.1.trans (le_max_left _ _)
    have hx:=le_max_left Lreq Mp
    linarith
  have href:Mp+Bmask+Mc/100≤ Lreq:=by
    have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hmask hMpM hMcM (by norm_num)
    exact (le_max_right _ _).trans hh
  obtain ⟨Jold,Sold,hprev⟩:=hold
  obtain ⟨Slow,Jlow,hlow⟩:=CenteredMomentEnergyCappedLowStageIVNF.actual_capped_low (α:=α) M H hH
    W aslot bslot a b radial Bmask L lo hi Mcap κ ε hW haslot hWs hbslot ha hb hrad
    hmask hMcap.le hκ hε hbeta hκbeta k hk ⟨Jold,Sold,hprev⟩
  obtain ⟨Uhigh,Jhigh,hhigh⟩:=CenteredMomentEnergyNaturalHighStageIVNF.actual_high_stage (α:=α) M H hH
    W hW aslot bslot lo hi ac b radial haslot hWs hbslot hac haclo hhi (by linarith)
    Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L κ ε) Mc κ ε k hMc hMcap.le hA hBs hmask
    hMp hMc.le hLc hmesh hMA hready hκ hbeta hκbeta hε le_rfl hdrop Jold Sold Jlow Slow
  obtain ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,hLlow,hLupper,hzeroStage⟩:=
    CenteredMomentEnergyNaturalZeroStageIVNF.actual_zero_stage (α:=α) M H hH
      W aslot bslot (fineMesh Mcap Bmask L κ ε) lo hi κ ac b radial Bmask Lc Mp Mc Mcap Bs ε Mc k
      haslot hWs hW hmesh hκ hbeta hκbeta hac haclo hhi hrad hmask hLc hMp hMc.le hMcap.le hBs
      hε hMc le_rfl hdrop
  have hLlowReq:Llow≤ Lreq:=by
    rw [hLlow,hLexact]
    exact actual_contours Mcap Bmask Lc Mp Mc d hMcap.le hmask hMpM hMcM hd1
  have hLgrowLow:Lgrow≤ Llow:=by rw [hLlow];exact le_max_left _ _
  have hLgrowReq:Lgrow≤ Lreq:=hLgrowLow.trans hLlowReq
  have hzeroCap:max Mp (2*Lgrow)≤ Lp:=by
    have hm:Mp≤ Lreq:=hMpM.trans hreq.2.2
    have hh:=le_max_left Lreq Mp
    apply max_le <;> linarith
  have hzeroReady:readyBudget (max Mp (2*Lgrow)) Bmask≤ Bs:=by
    have hc:max Mp (2*Lgrow)≤ A:=by
      apply max_le
      · exact hMA
      · dsimp [A];linarith
    apply le_trans _ hready
    unfold readyBudget
    linarith
  obtain ⟨Jzero,Uzero,hzero⟩:=hzeroStage Lp hLp hzeroCap hzeroReady Jold Jlow Sold Slow
  have hmarg:=margins Mcap Bs κ ε hMcap.le hBs hκ0 hε k
  apply CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages (α:=α) M H hH
    W bslot a b radial Bmask L lo hi Mcap κ ε ha hmask hMcap.le hκ0 hε k
    (stageLoss Mcap Bs ε (k+1)) (physicalLoss Mcap Bs ε k) (reflectedLoss Mcap Bs ε k)
    le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 ⟨Jold,Sold,hprev⟩
  · refine ⟨Jzero,Uzero,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Cz,hCz,hzeroZ⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Cz*(Clow+C₀+C₁+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hzeroZ] with Z hp hl hz
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hlowRestricted:=zeroLowAt_transport (internalQ Q η₀)
      ac b radial Bmask Lreq Mp (physicalLoss Mcap Bs ε k) Z
      ac b radial Bmask Llow Mp (physicalLoss Mcap Bs ε k) Jlow Jlow Slow Slow Clow Clow
      hp.1.le le_rfl le_rfl le_rfl le_rfl hLlowReq le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.2
    exact hz.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzz hpp hlowRestricted
  · refine ⟨Jlow,Slow,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Clow,hClow,?_⟩
    filter_upwards [hlowZ] with Z hl
    exact positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask Lc Mp (physicalLoss Mcap Bs ε k) η₀ Q Jlow Jlow Slow Slow Clow Clow
      hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
  · refine ⟨Jhigh,Uhigh,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Ch,hCh,hhighZ⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Ch*(C₀+C₁+Clow+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hzSmall:=zeroAt_transport (internalQ Q η₀)
      (ac/max 1 b) b radial Bmask Lp Mc (stageLoss Mcap Bs ε k) Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k)
      Jold Jold Sold Sold C₀ C₀ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₀.le le_rfl hzz
    have hpSmall:=positiveAt_transport (α:=α) M H hH W bslot
      (ac/max 1 b) b radial Bmask Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k) κ Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k) η₀ Q
      Jold Jold Sold Sold C₁ C₁ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₁.le le_rfl hpp
    have hlRestricted:=positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs ε k) η₀ Q
      Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    exact hh.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessorIVNF

end

end OAI

end ExtendedModule39


end NFModule95

/- No-floor source OAI.NumberTheory.DirichletL.Energy.CertifiedExistence -/
section NFModule96
/- BEGIN OAI.NumberTheory.DirichletL.Energy.CertifiedExistence -/
section ExtendedModule40

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistenceIVNF
open CenteredMomentEnergyCertifiedExistence hiding certified_bands terminal_certificate
open CenteredMomentEnergyCappedAnalyticSuccessorIV hiding actual_successor
open CenteredMomentEnergyCappedWidthInduction hiding CertifiedBand actual_child_band bandWidth bandWidth_le bandWidth_le_schedule bandWidth_nonneg bandWidth_terminal certified_floor certified_terminal
open HeckeFamily CenteredMomentEnergyCappedWidthInductionNF
open CenteredMomentEnergyCappedAnalyticSuccessorIVNF CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(13/18:ℝ)≤κ)(hε:0<ε)
    (hbeta:(1/50:ℝ)≤κ)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∀k:ℕ,k≤ count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k< count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(_hrad:0< radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(13/18:ℝ)≤κ)(hε:0<ε)
    (hbeta:(1/50:ℝ)≤κ)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε hbeta hκ _ le_rfl

end SevenEighths.CenteredMomentEnergyCertifiedExistenceIVNF

end

end OAI

end ExtendedModule40


end NFModule96

#print axioms OAI.SevenEighths.CenteredMomentEnergyCertifiedExistenceIVNF.terminal_certificate

end PartIVBlock19

/- BEGIN consolidated variable_moments/UnrestrictedMoments.lean -/
section PartIVBlock20

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Filter
open OAI OAI.SevenEighths
variable [RHIVProbe.Geometry] [RHIVProbe.FullMomentParameter]
namespace RHZeroFreeExtension.AnalyticHigh.IV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyCappedWidthInduction

theorem unrestricted_kappa_terminal_certificate {gap : ℝ} (D : HighData gap)
    (F : SourceData D) (hOld : HeckeZeroSupremum.beta≤(1+RHIVProbe.fullMomentKappa)/2)
    (bPhi : ℝ) (hbPhi : 0< bPhi) :
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 RHIVProbe.fullMomentKappa (D.t/4)
      (count 2 (D.t/4)) := by
  apply CenteredMomentEnergyCertifiedExistenceIVNF.terminal_certificate (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=> conj (F.W x)) 1 2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 RHIVProbe.fullMomentKappa (D.t/4)
  · norm_num
  · intro x hx
    have hh : x∈Function.support (F.W:ℝ→ℂ) := by
      change conj (F.W x)≠0 at hx
      change F.W x≠0
      intro hz
      exact hx (by rw [hz];simp)
    exact F.complex_support hh
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbPhi
  · norm_num
  · norm_num
  · exact RHIVProbe.full_moment_range.1
  · exact div_pos D.t_pos (by norm_num)
  · linarith [RHIVProbe.full_moment_range.1]
  · linarith

theorem unrestricted_source_moments {gap : ℝ} (hgap : 0< gap) {D : HighData gap} (F : SourceData D)
    (counts : ProbeFinalAssembly.IVRawCountParameters F.modulus ⊤ D.t)
    (hOld : HeckeZeroSupremum.beta≤(1+RHIVProbe.fullMomentKappa)/2)
    (hfine : ∀j,D.ell j≤ IVFullProbeFinalAssemblyCertifiedBands.detectorMesh gap D.t/200) :
    ∃J : ℝ,0≤ J ∧ ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧
      ∀τ : ℝ,0<τ→τ≤1→∀ᶠZ : ℝ in atTop,
        FullSourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨hp,hz⟩ := IVFullProbeFinalAssemblyCertifiedBands.plain_inputs F (by
    intro bPhi hbPhi
    simpa only [IVFullCenteredMomentDetectorPlainMomentParameters.kappaPlain,
      IVFullCenteredMomentDetectorPlainMomentParameters.stageError] using
      unrestricted_kappa_terminal_certificate D F hOld bPhi hbPhi)
  exact IVFullProbeFinalAssemblyCertifiedBands.source_moments F counts
    (IVFullProbeFinalAssemblyCertifiedBands.detectorMesh gap D.t)
    (IVFullProbeFinalAssemblyCertifiedBands.detectorMesh_pos hgap D.t_pos) hfine hp hz
end RHZeroFreeExtension.AnalyticHigh.IV
end
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.unrestricted_kappa_terminal_certificate
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.unrestricted_source_moments

end PartIVBlock20

/- BEGIN consolidated ParameterDecimals.lean -/
section PartIVBlock21

namespace CombineV22.ParameterDecimals
open CombineV22Optimality

/-- A refined exact isolating interval, used to certify all displayed decimals. -/
theorem xiInf_refined_bracket :
    (388583354266034666797427/10^24 : ℝ) < xiInf ∧
    xiInf < (388583354266034666797428/10^24 : ℝ) := by
  have hlmem : (388583354266034666797427/10^24 : ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> norm_num
  have humem : (388583354266034666797428/10^24 : ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> norm_num
  have hlp : 0 < cubic (388583354266034666797427/10^24) := by norm_num [cubic]
  have hup : cubic (388583354266034666797428/10^24) < 0 := by norm_num [cubic]
  constructor
  · by_contra hn
    have hc := (cubic_nonpos_iff _ hlmem).2 (le_of_not_gt hn)
    linarith
  · have he := (cubic_nonpos_iff _ humem).1 (le_of_lt hup)
    apply lt_of_le_of_ne he
    intro heq
    rw [← heq, cubic_xiInf] at hup
    linarith

theorem boundary_refined_bracket :
    (874957019420098946128603/10^24 : ℝ) < boundary xiInf ∧
    boundary xiInf < (874957019420098946128605/10^24 : ℝ) := by
  have hb := xiInf_refined_bracket
  have hd := boundary_den_pos xiInf_mem
  unfold boundary
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [hb.1]
  · apply (div_lt_iff₀ hd).2
    nlinarith [hb.2]

/-- The displayed 18 decimal places of the limiting moment parameter. -/
theorem kappa_decimal_bracket :
    (749914038840197892/10^18 : ℝ) < kap xiInf ∧
    kap xiInf < (7499140388401978925/10^19 : ℝ) := by
  rw [root_fixed_point]
  constructor <;> linarith [boundary_refined_bracket.1,boundary_refined_bracket.2]

/-- The displayed 18 decimal places of the limiting length parameter. -/
theorem ell_decimal_bracket :
    (166838588986270882/10^18 : ℝ) < Uniform.ell xiInf ∧
    Uniform.ell xiInf < (1668385889862708825/10^19 : ℝ) := by
  rw [AlgebraicParameters.ell_boundary_relation _ xiInf_mem_small]
  constructor <;> linarith [boundary_refined_bracket.1,boundary_refined_bracket.2]

private def bp (x : ℝ) : ℝ := 53835237*x^3+381756141*x^2+94706196*x-17602208
private lemma bp_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : bp x ≤ bp y := by
  have h2 : x^2 ≤ y^2 := pow_le_pow_left₀ hx hxy 2
  have h3 : x^3 ≤ y^3 := pow_le_pow_left₀ hx hxy 3
  unfold bp
  linarith

/-- The displayed 18 decimal places of the limiting small-prime parameter.
The upper half-unit certificate also certifies rounding, not only truncation. -/
theorem b_decimal_bracket :
    (123405685419541002/10^18 : ℝ) < Uniform.b xiInf ∧
    Uniform.b xiInf < (1234056854195410025/10^19 : ℝ) := by
  have hb0 : 0 ≤ Uniform.b xiInf := by
    linarith [Uniform.b_positive_lower _ xiInf_mem_small]
  have hr : bp (Uniform.b xiInf) = 0 := AlgebraicParameters.b_root
  have hl : bp (123405685419541002/10^18) < 0 := by norm_num [bp]
  have hu : 0 < bp (1234056854195410025/10^19) := by norm_num [bp]
  constructor
  · by_contra hn
    have hm := bp_monotone hb0 (le_of_not_gt hn)
    linarith
  · by_contra hn
    have hm := bp_monotone (by norm_num : (0:ℝ) ≤ 1234056854195410025/10^19) (le_of_not_gt hn)
    linarith

#print axioms xiInf_refined_bracket
#print axioms boundary_refined_bracket
#print axioms kappa_decimal_bracket
#print axioms ell_decimal_bracket
#print axioms b_decimal_bracket
end CombineV22.ParameterDecimals

end PartIVBlock21

/- BEGIN consolidated probe/FinalConclusions.lean -/
section PartIVBlock22

/-! Final statements about the actual L-functions. No moment, count, probe,
comparison-saving or improved zero-free hypothesis is an input. -/
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
namespace CombineV22
noncomputable section
open OAI.SevenEighths HeckeFamily
open CombineV22Optimality

abbrev limitingBoundary : ℝ := boundary xiInf

theorem one_step (t : ℝ) (ht : t ∈ Set.Icc (38858/100000:ℝ) (38859/100000:ℝ))
    (hk : kap t ≤ (3/4:ℝ)) (hOld : HeckeZeroSupremum.beta ≤ (1+kap t)/2) :
    HeckeZeroSupremum.beta ≤ boundary t := by
  have htu : Uniform.InInterval t := ht
  have hk' : Uniform.kappa t ≤ (3/4:ℝ) := by
    rw [← EndpointGeometry.optimality_kappa]; exact hk
  letI : RHIVProbe.Geometry := EndpointGeometry.geometry t htu
  letI : RHIVProbe.HighGeometry := EndpointGeometry.highGeometry t htu
  letI : RHIVProbe.MomentParameter := EndpointGeometry.momentParameter t htu hk'
  letI : RHIVProbe.CountGeometry := EndpointGeometry.countGeometry t htu hk'
  have hp : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2 := by
    change HeckeZeroSupremum.beta ≤ (1+Uniform.kappa t)/2
    rw [← EndpointGeometry.optimality_kappa]
    exact hOld
  have h := RHZeroFreeExtension.AnalyticHigh.IV.beta_le_of_previous_bound hp
  change HeckeZeroSupremum.beta ≤ @RHIVProbe.boundary (EndpointGeometry.geometry t htu) at h
  rw [EndpointGeometry.physical_boundary t htu] at h
  rw [EndpointGeometry.optimality_boundary]
  exact h

/-- Every displayed finite bootstrap iterate is an actual family bound. -/
theorem bootstrap_finite_bounds (n : ℕ) :
    HeckeZeroSupremum.beta ≤ (1+Iteration.K n)/2 ∧
    HeckeZeroSupremum.beta ≤ Iteration.Bseq n :=
  Iteration.finite_bounds HeckeZeroSupremum.beta
    RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths one_step n

theorem beta_star_le : HeckeZeroSupremum.beta ≤ limitingBoundary :=
  conditional_bootstrap_limit HeckeZeroSupremum.beta
    RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths one_step

theorem limitingBoundary_positive : 0 < limitingBoundary := by
  have hx := xiInf_mem_small.1
  change 0 < (18*xiInf+7)/(18*xiInf+9)
  apply div_pos <;> linarith

theorem hecke_nonzero (chi : Character) (s : ℂ) (hs : limitingBoundary < s.re)
