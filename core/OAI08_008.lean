
/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowDirect
Source SHA256: 1f0c284e89c06104bb13e2bf99df783f1443333d5ce3ae7ccfc3699e9cf3623f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2732


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowDirect
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceLowChild

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem direct_child_from_low
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤Bmask)(ha:0<a)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hfreq:∀i,|freq i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤s.width)
    (hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      W₁ X₁ 0 t*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>t+freq i)
    0 (|t|+height) (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (independentProfiles ha W₁ W₂ hs₁ hs₂ t t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hsmall)
  rw [independent_child_ray_energy s ha W₁ W₂ hs₁ hs₂ F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>Wslot)
    (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _) t t t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowDirect

end

end OAI
end OAIOriginalModule2732

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowEmpty
Source SHA256: 43f216d3c5e39eceec0479cb8975aeebf9f157f8cdb28b237ba00750f8a9ecb9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2733


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α][IsEmpty α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem zero_low_positive_empty
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)(hC:0≤C)
    (h:ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C):
    PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hsmall
  have hh:=h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (by simpa using hsmall)
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid]
  apply hh.trans
  have hp:(1+‖t‖)^degree≤(1+|t|+height)^degree:=by
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.norm_eq_abs]
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by unfold diagonalControl;positivity))
    (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)

end SevenEighths.CenteredMomentEnergyReferenceLowEmpty

end

end OAI
end OAIOriginalModule2733

/-! Original module: OAI.NumberTheory.DirichletL.Energy.LowBandEmpty
Source SHA256: 8896d452b4b3b0652931286d139b8ec5867defb6e3153accea92a7e4b3c8360d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2734


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLowBandEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positive_low_zero
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C):
    ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  let T:Finset α:=∅
  let θ:T→RayQuotient.Characters M H:=fun i=>False.elim (Finset.notMem_empty _ i.property)
  let w:T→ℝ:=fun _=>0
  have hcap:length Z X₁+length Z X₂+6*κ*(∑i:T,w i)≤s.width:=by
    simp only [T,w,Finset.sum_const_zero,mul_zero,add_zero]
    linarith [s.width_nonneg]
  have hl:length Z X₁+length Z X₂+(∑i:T,w i)≤5*s.width/6:=by
    simpa only [w,Finset.sum_const_zero,add_zero] using hsmall
  have hh:=h T θ w w w t 0 (fun _=>le_rfl)
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property)) le_rfl
    (fun _=>by simp [w]) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hl
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (w i) (w i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [T,energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid] at hh
  simpa only [add_zero,Real.norm_eq_abs] using hh

end SevenEighths.CenteredMomentEnergyLowBandEmpty

end

end OAI
end OAIOriginalModule2734

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowMoments
Source SHA256: 86f9e080b522b94493a5428b320d38860b70092f1c2ac3b7a1940592fb9e2a55
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2735



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceLowChild CenteredMomentEnergyReferenceLowControl
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem reflected_child_uniform_from_low
    (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(Wslot:ℝ→ℂ)(bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(C:ℝ)(_hC:0≤C)
    (_hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (_hB:0≤Bmask)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (_hw:∀i,0≤w i)(_hwL:∀i,w i≤Lslot)(_hσlo:∀i,lo≤σ i)(_hσhi:∀i,σ i≤hi)
    (_hheight:0≤height)(_hfreq:∀i,|freq i|≤height)
    (s:NaturalState Z Bmask bΦ)(_hQ:s.fixedModulus=internalQ Q η₀)(_hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(_hX₁:0<X₁)(_hX₂:0<X₂)(_hc₁:X₁≤Z^L)(_hc₂:X₂≤Z^L)
    (_hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤s.width)
    (_hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6),
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n) :=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S degree
  refine ⟨n,T,D,hD,?_⟩
  intro Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q C hC hlow hB
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsW
    j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hsmall
  have hh:=reflected_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κ Z η₀ Q degree S C hlow hB ha hlo hhi F θ w σ freq t height hw hwL
    hσlo hσhi hheight hfreq s hQ hs Wshort hsW j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂
    hcapacity hsmall
  have hb:=hd Wshort hsW j k v t height hheight
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 <;> ring

end SevenEighths.CenteredMomentEnergyReferenceLowMoments

end

end OAI
end OAIOriginalModule2735

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflection
Source SHA256: 4b7d3f665e014bf5e254ff904b33a32b7bf194219324a41e7283c5b37ae707ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2736




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLowReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowMoments CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem reference_from_low
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Wslot:ℝ→ℂ)(bslot Bmask L Lslot lo hi Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤Bmask →
      ∀(F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤s.width →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+(∑i∈F,w i)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=reflected_child_uniform_from_low (α:=α) M H hH a b ha hlo hhi degree S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only
  apply hZ.2 Bmask s Wlong Wshort hsLong hsShort α F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t)
    (fun i=>Z^(w i)) t along bshort _ hlength
  · have hz:0<Z:=zero_lt_one.trans hZ.1
    have hd:0≤diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
    positivity
  · intro v j k x hx
    have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
    exact hchild Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q K hK hlow hBmask
      F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsShort
      j k v (Real.exp x) (Z^bshort) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
      (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hL))
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbshort)
      (by linarith [hwindow.1]) (by linarith [hwindow.1])

end SevenEighths.CenteredMomentEnergyReferenceLowReflection

end

end OAI
end OAIOriginalModule2736

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError
Source SHA256: ace17d30582fefef9c052be6f7a85ef90ecd50c0925cd7dd11c82418b7714c99
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2737



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLowReflectionError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowMoments CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyReferenceLowReflection CenteredMomentEnergyReferenceLowError
theorem reference_from_low_with_error
    (Fmax:Finset α)(Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask L Lslot Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤Bmask →
      ∀(F:Finset α),F⊆Fmax → ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤s.width →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+(∑i∈F,w i)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^bshort)*∏i∈F,Z^(w i) :=by
  obtain ⟨Cerr,hCerr,herr⟩:=relative_slot_error Fmax Wslot aslot bslot lo hi b haslot hsSlot hcSlot
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low (α:=α) M H hH
    a b bΦ epsilon xi saving Lreflect ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cerr,hC,mul_pos hD hCerr,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask
    F hF θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only
  have hh:=hZ.2 Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only at hh
  have he:=herr F hF Wshort (fun x hx=>(hsShort hx).2)
    (naturalCharacter s.character) (fun i=>relativeCharacter M H hH η₀ (θ i))
    (fun i=>primePool M H bslot (Z^(w i))) (fun i=>Z^(w i)) σ freq t
    (Z^bshort) s.radial.scale s.radial.profile (effectiveState s).radial.keep
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) s.radial.scale_pos
    (fun i _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    (fun i _=>hσlo i) (fun i _=>hσhi i)
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1) s.radial.nonneg
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hcoeff:0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
      (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving):=by positivity
  apply hh.trans
  apply add_le_add le_rfl
  convert mul_le_mul_of_nonneg_left he hcoeff using 1 ; ring

end SevenEighths.CenteredMomentEnergyReferenceLowReflectionError

end

end OAI
end OAIOriginalModule2737

/-! Original module: OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect
Source SHA256: 2976bdb1d6a1497f4e3f72a09cb53792dde3bcf5e96c79b8ed72263978e8a5da
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2738




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLiveClippingDefect
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_support_witness (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X : ℝ) (h : rowTwistedSum η m A z W t X ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold rowTwistedSum
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · subst I
        rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
      · rw [hn I hI, mul_zero]
    _ = 0 := tsum_zero

theorem rowTwistedSum_support_scale (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b)
    (h : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b * X := by
  obtain ⟨I, hI, hW⟩ := rowTwistedSum_support_witness η m A z W t X h
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hn.trans ((div_le_iff₀ hX).mp (hs hW))

variable {ι : Type*} [Fintype ι]

theorem positiveSlotRow_support_scales (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  exact ⟨rowTwistedSum_support_scale η m A z W₁ t X₁ b hX₁ hs₁
      (left_ne_zero_of_mul hp),
    rowTwistedSum_support_scale η m A z W₂ t X₂ b hX₂ hs₂
      (right_ne_zero_of_mul hp)⟩

theorem positiveSlotRow_profiles_scales (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  exact positiveSlotRow_support_scales η m A z _ _ S β P t X₁ X₂ b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) h

theorem length_le_raw_add_endpoint (Z X b : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hs : 1 ≤ b * X) : length Z X ≤ Real.logb Z X + Real.logb Z (max 1 b) := by
  have hB : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hc : max 1 X ≤ max 1 b * X := by
    apply max_le
    · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) b) hX.le
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left (1 : ℝ) X)) hc
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  simpa [length, add_comm] using hh

theorem total_clipping_defect (Z X₁ X₂ b : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hs₁ : 1 ≤ b * X₁) (hs₂ : 1 ≤ b * X₂) :
    length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
      2 * Real.logb Z (max 1 b) := by
  have h1 := length_le_raw_add_endpoint Z X₁ b hZ hX₁ hs₁
  have h2 := length_le_raw_add_endpoint Z X₂ b hZ hX₂ hs₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  linarith

theorem endpoint_threshold (b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      2 * Real.logb Z (max 1 b) ≤ δ := by
  let Z₀ := Real.exp (1 + 2 * Real.log (max 1 b) / δ)
  have hb : 0 ≤ Real.log (max 1 b) := Real.log_nonneg (le_max_left _ _)
  have he : 0 < 1 + 2 * Real.log (max 1 b) / δ := by positivity
  have hZ₀ : 1 < Z₀ := Real.one_lt_exp_iff.mpr he
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ
  have hZ : 1 < Z := hZ₀.trans_le hZZ
  have hlog := Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hbound : 2 * Real.log (max 1 b) ≤ δ * Real.log Z := by
    have hh : 2 * Real.log (max 1 b) / δ ≤ Real.log Z := by linarith
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  rw [Real.logb, ← mul_div_assoc]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr hbound

theorem profiles_uniform_defect (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ (η : Character) (m A z : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0 →
        length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ δ := by
  obtain ⟨Z₀, hZ₀, hh⟩ := endpoint_threshold b δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  exact (total_clipping_defect Z X₁ X₂ b (hZ₀.trans_le hZZ) hX₁ hX₂ h1 h2).trans (hh Z hZZ)

theorem total_clipping_defect_nonneg (Z X₁ X₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) := by
  have h1 := Real.logb_le_logb_of_le hZ hX₁ (le_max_right (1 : ℝ) X₁)
  have h2 := Real.logb_le_logb_of_le hZ hX₂ (le_max_right (1 : ℝ) X₂)
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  dsimp only [length]
  linarith

theorem positiveSlotRow_zero_or_defect (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ Z : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases hrow : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
    exact Or.inr ⟨total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂,
      total_clipping_defect Z X₁ X₂ b hZ hX₁ hX₂ h1 h2⟩

theorem energy_support_witness (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : CenteredMomentInductionEnergy.energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≠ 0) :
    ∃ z : O, keep z ∧ positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold CenteredMomentInductionEnergy.energy
  calc
    _ = ∑' _z : O, (0 : ℝ) := by
      apply tsum_congr
      intro z
      by_cases hk : keep z
      · simp only [ite_eq_left hk, hn z hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      · simp only [ite_eq_right hk]
    _ = 0 := tsum_zero

theorem energy_zero_or_defect (η : Character) (m A : O) (t : ℝ)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ Z : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
        S β P X₁ X₂ keep Φ K = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases h : CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
      S β P X₁ X₂ keep Φ K = 0
  · exact Or.inl h
  · obtain ⟨z, _, hz⟩ := energy_support_witness η m A t _ _ S β P X₁ X₂ keep Φ K h
    exact Or.inr ((positiveSlotRow_zero_or_defect η m A z p S β P t X₁ X₂ Z hZ hX₁ hX₂).resolve_left hz)

theorem raw_gates_of_defect (Z M X₁ X₂ ell κ e : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hdefect : length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ e)
    (hlarge : 5*M/6 ≤ length Z X₁ + length Z X₂ + ell)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*ell ≤ M) :
    5*M/6-e ≤ Real.logb Z (X₁ * X₂)+ell ∧
      Real.logb Z (X₁ * X₂)+ell+(6*κ-1)*ell ≤ M := by
  have hnonneg := total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂
  constructor <;> nlinarith

theorem robust_slot_budgets (M total ell kappa defect : ℝ)
    (hell : 0 ≤ ell) (hk : 3/4 ≤ kappa)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M) :
    ell ≤ M/21+2*defect/7 ∧ (6*kappa-1)*ell ≤ M/6+defect := by
  have hkell : 7/2*ell ≤ (6*kappa-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M xi defect : ℝ) (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hreserve : xi+11*defect/7 ≤ M/14) : defect ≤ M := by
  linarith

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hk : 3/4 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (hreserve : xi+11*defect/7 ≤ M/14) :
    15*M/28-9*defect/7 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hb⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (_hs : 0 ≤ short) (hsM : short ≤ M/4)
    (_hell : 0 ≤ ell) (_hz : 0 ≤ z) (hze : z ≤ ell) (hk : 3/4 ≤ kappa)
    (he : ell ≤ M/21+2*defect/7)
    (hbudget : (6*kappa-1)*ell ≤ M/6+defect)
    (hxi : 0 ≤ xi) (hdefect : 0 ≤ defect) (hdefectM : defect ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+xi)) :
    0 < along ∧ reflected+short+z ≤ 16*M/21+xi+4*defect/7 ∧
      reflected+short+6*kappa*z ≤ 13*M/14+xi+11*defect/7 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*kappa-1)*z ≤ M/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ M/21+2*defect/7 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M xi defect short reflected z kappa : ℝ)
    (hd : 0 ≤ defect) (hreserve : xi+11*defect/7 ≤ M/14)
    (ht : reflected+short+z ≤ 16*M/21+xi+4*defect/7)
    (hc : reflected+short+6*kappa*z ≤ 13*M/14+xi+11*defect/7) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*kappa*z ≤ M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hk : 3/4 ≤ kappa)
    (hxi : 0 ≤ xi) (hd : 0 ≤ defect)
    (hreserve : xi+11*defect/7 ≤ M/14)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4)
    (href : reflected ≤ max 0 (M-along+xi)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*kappa*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧
      reflected+short+6*kappa*z ≤ M) := by
  obtain ⟨he,hbudget⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*kappa)
    nlinarith
  · obtain ⟨hapos, ht, hc⟩ := robust_reflected_low M short along ell z kappa xi defect reflected
      hM hs hsM hell hz hze hk he hbudget hxi hd
      (robust_defect_le_width M xi defect hM hxi hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨hapos, robust_reflected_low_admissible M xi defect short reflected z kappa hd hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀M : ℝ, M₀ ≤ M →
      M₀/56+11*(M₀/56)/7 ≤ M/14 := by
  constructor
  · positivity
  · intro M hM
    linarith

open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacity

theorem robust_deleted_reference_cases (Z M X₁ X₂ ell z κ ξ e reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 3/4 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+11*e/7 ≤ M/14)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I)
    (href : reflected ≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+ξ)) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let long := length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+long+z ≤ 5*M/6 ∧ short+long+6*κ*z ≤ M) ∨
    (0 < Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ∧
      reflected+short+z ≤ 16*M/21+ξ+4*e/7 ∧
      reflected+short+6*κ*z ≤ 13*M/14+ξ+11*e/7) := by
  dsimp only
  have hb := robust_balanced_long_nonneg M (Real.logb Z (X₁*X₂)) ell κ ξ e
    hM hell hκ hξ hlarge hcap hreserve
  have hpos := comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hlog : Real.logb Z (comparisonSecond Z M X₁ X₂) = Real.logb Z (X₁*X₂)-M/4 := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hY : 1 ≤ comparisonSecond Z M X₁ X₂ := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hn₂ := product_norm_ge_one D₂ hD₂
  have hlongpos := div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort := deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0 := length_nonneg Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ)) hZ
  have hlong : length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ≤
      Real.logb Z (X₁*X₂)-M/4 := by
    rw [← hlog]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _)) (max_le hY (div_le_self hpos.2.le hn₂))
  by_cases hlo : length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ))+
      length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hkc := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · apply Or.inr
    obtain ⟨hellbound, hslot⟩ := robust_slot_budgets M (Real.logb Z (X₁*X₂)) ell κ e
      hell hκ hlarge hcap
    apply robust_reflected_low M _ _ ell z κ ξ e reflected hM hshort0 hshort hell hz hze hκ
      hellbound hslot hξ he (robust_defect_le_width M ξ e hM hξ hreserve) _ href
    rw [← CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

theorem robust_deleted_reference_window (Z M X₁ X₂ ell z κ ξ e : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 3/4 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+11*e/7 ≤ M/14)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
    (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
      length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
      length Z (Real.exp x)+short+6*κ*z ≤ M) := by
  dsimp only
  let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))
  rcases robust_deleted_reference_cases Z M X₁ X₂ ell z κ ξ e (max 0 (M-along+ξ))
    hZ hM hX₁ hX₂ hell hz hze hκ hξ he hreserve hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, ?_⟩
    intro x hx
    have hh := CenteredMomentEnergyReferenceLowWindow.reflection_window_length Z
      (max 0 (M-along+ξ)) x hZ (le_max_left _ _) hx
    have hb := robust_reflected_low_admissible M ξ e _ (max 0 (M-along+ξ)) z κ
      he hreserve h.2.1 h.2.2
    constructor <;> linarith [hh.1]

theorem live_profiles_reference_window (a b M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ e ξ Z₀ : ℝ, 0 < e ∧ 0 < ξ ∧ 1 < Z₀ ∧
      ∀ (Z M : ℝ), Z₀ ≤ Z → M₀ ≤ M →
      ∀ (η : Character) (m A u : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ ell z κ : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ ell →
        0 ≤ z → z ≤ ell → 3/4 ≤ κ →
        5*M/6 ≤ length Z X₁+length Z X₂+ell →
        length Z X₁+length Z X₂+6*κ*ell ≤ M →
      ∀ (D₁ D₂ : Finset (Ideal O)), (∀ I ∈ D₁, Prime I) → (∀ I ∈ D₂, Prime I) →
      positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
      (let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
       let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
       (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
        short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
       (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
         length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
         length Z (Real.exp x)+short+6*κ*z ≤ M)) := by
  have he : 0 < M₀/56 := by positivity
  obtain ⟨Z₀, hZ₀, hdefect⟩ := profiles_uniform_defect (ι := ι) a b (M₀/56) he
  refine ⟨M₀/56, M₀/56, Z₀, he, he, hZ₀, ?_⟩
  intro Z M hZZ hMM η m A u p S β P t X₁ X₂ ell z κ hX₁ hX₂ hell hz hze hκ hlarge hcap D₁ D₂ hD₁ hD₂
  by_cases hrow : positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · apply Or.inr
    have hZ := hZ₀.trans_le hZZ
    obtain ⟨hl, hc⟩ := raw_gates_of_defect Z M X₁ X₂ ell κ (M₀/56) hZ hX₁ hX₂
      (hdefect Z hZZ η m A u p S β P t X₁ X₂ hX₁ hX₂ hrow) hlarge hcap
    exact robust_deleted_reference_window Z M X₁ X₂ ell z κ (M₀/56) (M₀/56)
      hZ (hM₀.le.trans hMM) hX₁ hX₂ hell hz hze hκ he.le he.le
      ((robust_fixed_slack M₀ hM₀).2 M hMM) hl hc D₁ D₂ hD₁ hD₂

end SevenEighths.CenteredMomentEnergyLiveClippingDefect

end

end OAI
end OAIOriginalModule2738

/-! Original module: OAI.NumberTheory.DirichletL.Energy.DeletedRobustGeometry
Source SHA256: 2037b3c8eb49c9fdc5c8a4d805efd7ce64237ae6ca70ac4d50e1ef9dd265636d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2739



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyDeletedRobustGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyLiveClippingDefect
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(he:0≤e)(hreserve:xi+11*e/7≤s.width/14)
    (hlarge:5*s.width/6-e≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):= by
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hb := robust_balanced_long_nonneg s.width (Real.logb Z (X₁*X₂)) ell κ xi e
    s.width_nonneg hell hκ hxi hlarge hcap hreserve
  have hy₁ : 1 ≤ comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  have hy₂ : 1 ≤ comparisonSecond Z s.width X₁ X₂ := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hbase hZ.ne']
  have hd₁ := divisor_reflection_range s hZ Mcap _ hwidth hy₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap _ hwidth hy₂ D₂ hD₂
  dsimp only at hd₁ hd₂
  rw [hf] at hd₁
  rw [hl] at hd₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  have hlog₁ := Real.logb_nonneg hZ hn₁
  have hlog₂ := Real.logb_nonneg hZ hn₂
  have hMcap : 0 ≤ Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 ≤ L := by linarith
  have hslot : 0 ≤ (6*κ-1)*ell := mul_nonneg (by linarith) hell
  dsimp only
  refine ⟨hd₁.2.2, hd₂.2.2, by linarith, by linarith [s.width_nonneg],
    by linarith, hd₂.2.1, max_le hLc (by linarith [hd₂.1]), ?_⟩
  have hp₁ : ∀ I ∈ D₁, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₁ hi)
  have hp₂ : ∀ I ∈ D₂, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₂ hi)
  let along := Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
  have halong : Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏ P ∈ D₂, P).absNorm : ℝ)) = along := by
    rw [← hd₂.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  rcases robust_deleted_reference_cases Z s.width X₁ X₂ ell z κ xi e (max 0 (s.width-along+xi))
    hZ s.width_nonneg hX₁ hX₂ hell hz hze hκ hxi he hreserve hlarge hcap D₁ D₂ hp₁ hp₂
    (by rw [halong]) with hc | hc
  · exact Or.inl (by simpa only [hd₁.2.2, hd₂.2.2] using hc)
  · apply Or.inr
    have hh := robust_reflected_low_admissible s.width xi e _ (max 0 (s.width-along+xi)) z κ
      he hreserve hc.2.1 hc.2.2
    simpa only [hd₁.2.2] using hh

end SevenEighths.CenteredMomentEnergyDeletedRobustGeometry

end

end OAI
end OAIOriginalModule2739

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionDeleted
Source SHA256: 18b5206ff1a4ad49e0618cbec9654f83e598561d5c3830c266f065f030e92430
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2740




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem deleted_original_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=Real.logb Z (X₁/((∏I∈D₁,I).absNorm:ℝ))
  let along:=Real.logb Z (X₂/((∏I∈D₂,I).absNorm:ℝ))
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=>hw i)
  have hg:=actual_deleted_gates s hZ.1 (by linarith) hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=>hw i)) hsum hsumle hκ hxi.le hxiM hshort hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=>Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeleted

end

end OAI
end OAIOriginalModule2740

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionOriginal
Source SHA256: e1db9eb81af6631eca0ac3546f58a29cbe876fff64e06a70b68ea7164147778c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2741



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyOriginalHighReflectionDeleted CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_high_from_low
    (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=>bslot) (fun _=>Bslot) (fun _=>hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_original_from_low (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hX₁
  · exact hX₂
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal

end

end OAI
end OAIOriginalModule2741

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
Source SHA256: 3f18bae0e325a27898553735564f63b4b382d4de6546bff5d5afd26f24781d77
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2742


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma control_mono {S T:Finset (ℕ×ℕ)}(h:S⊆T)(W:𝓢(ℝ,ℂ)):
    sourceControl S W≤sourceControl T W:=Seminorm.le_def.mp (Finset.sup_mono h) W

theorem reference_envelopes (a b:ℝ)(ha:0<a)
    (S T Slong:Finset (ℕ×ℕ))(degree n nlong:ℕ)(Cref Dchild Dref:ℝ)
    (hCr:0<Cref)(hDc:0<Dchild)(hDr:0<Dref):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t height:ℝ,0≤height →
      let E:=C*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J;
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*(1+|t|+height)^degree≤E ∧
      Cref*Dchild*(sourceControl Slong W₂)^2*(sourceControl T W₁)^2*
        (1+‖t‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)≤E ∧
      Dref*(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
        (1+‖t‖)^(2*nlong)≤E:=by
  obtain ⟨na,Ta,Ca,hCa,hprof⟩:=independent_profile_control a b ha S
  let U:=((Ta∪T)∪Slong)∪{(0,0)}
  let J:=degree+4*na+2*n+2*nlong
  let C:=1+Ca^2*2^(4*na)+Cref*Dchild+Dref
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨J,U,C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only
  let H:=1+|t|+height
  let A:=sourceControl U W₁*sourceControl U W₂
  have hH:1≤H:=by dsimp only [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hA:0≤A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have haU:Ta⊆U:=by intro x hx;simp [U,hx]
  have hTU:T⊆U:=by intro x hx;simp [U,hx]
  have hlU:Slong⊆U:=by intro x hx;simp [U,hx]
  have hzU:(0,0)∈U:=by simp [U]
  have hz:(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁≤sourceControl U W₁:=
    Seminorm.le_def.mp (Finset.le_sup hzU) W₁
  have hp:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S≤Ca*A*(2*H)^(2*na):=by
    apply (hprof W₁ W₂ hs₁ hs₂ t t).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hCa.le
      exact mul_le_mul (control_mono haU W₁) (control_mono haU W₂)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · apply pow_le_pow_left₀ (by positivity)
      dsimp only [H]
      simp only [Real.norm_eq_abs]
      linarith [abs_nonneg t]
    · positivity
    · positivity
  have hd:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S^2*H^degree≤
      (Ca^2*2^(4*na))*A^2*H^J:=by
    have hsq:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
    have hmul:=mul_le_mul_of_nonneg_right hsq (pow_nonneg hH0 degree)
    have hid:(Ca*A*(2*H)^(2*na))^2*H^degree=
        (Ca^2*2^(4*na))*A^2*H^(degree+4*na):=by
      rw [mul_pow,mul_pow,←pow_mul,show (2*na)*2=4*na by omega,mul_pow,pow_add]
      ring_nf
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (by positivity))
  have hm:(sourceControl Slong W₂)^2*(sourceControl T W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul (control_mono hTU W₁) (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have he:(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (apply_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul hz (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheightpow:(1+‖t‖)^(2*nlong)≤H^(2*nlong):=by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    simp only [Real.norm_eq_abs]
    linarith
  have hcm: Cref*Dchild≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hce:Dref≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hcd:Ca^2*2^(4*na)≤C:=by dsimp only [C];nlinarith
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg A)) (pow_nonneg hH0 J)),?_,?_⟩
  · calc
      _=(Cref*Dchild)*((sourceControl Slong W₂)^2*(sourceControl T W₁)^2)*
          ((1+‖t‖)^(2*nlong)*H^(degree+2*n)):=by ring
      _≤C*A^2*(H^(2*nlong)*H^(degree+2*n)):=by gcongr
      _≤C*A^2*H^J:=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (sq_nonneg A))
        rw [←pow_add]
        exact pow_le_pow_right₀ hH (by dsimp only [J];omega)
  · calc
      _=Dref*((sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2)*(1+‖t‖)^(2*nlong):=by ring
      _≤C*A^2*H^(2*nlong):=by gcongr
      _≤C*A^2*H^J:=mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (mul_nonneg hC.le (sq_nonneg A))

end SevenEighths.CenteredMomentEnergyReferenceProfileBudget

end

end OAI
end OAIOriginalModule2742

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionBounded
Source SHA256: e8667278d9355dae0f7f372d86bfd478f04ac0f6d2aca0ab3c27dfd72744f75e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2743




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
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
  have hxiM:xi≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumcap:(∑i,w i)≤Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionBounded

end

end OAI
end OAIOriginalModule2743

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionPower
Source SHA256: 205516f6343f3e600ac9734a52547915804a43b3355d3f27c1d78066af85b68c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2744




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_high_from_low (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hxiM:xi≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumcap:(∑i,w i)≤Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower

end

end OAI
end OAIOriginalModule2744

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
Source SHA256: 119005d30ab4de4c2dd2cac2cba4662c7606ed27ac28ae3aad3ff73cddbcce69
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2745


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionPower
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

omit [DecidableEq α] in
lemma energy_swap (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₂ W₁ pool β P X₂ X₁ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      positiveSlotRow η m A z W₂ W₁ pool β P t X₂ X₁:=by
    unfold positiveSlotRow
    rw [mul_comm X₁ X₂]
    ring
  rw [hh]

theorem balanced_four_scale_gates (Z width X₁ X₂:ℝ)(hZ:1<Z)(hwidth:0<width)
    (hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:width/4≤min (length Z X₁) (length Z X₂)):
    Z^(width/4)≤X₁ ∧ Z^(width/4)≤X₂ ∧
    Z^(width/4)≤comparisonFirst Z width ∧
    Z^(width/4)≤comparisonSecond Z width X₁ X₂ ∧
    length Z X₁+length Z X₂=Real.logb Z (X₁*X₂):=by
  have h₁:width/4≤length Z X₁:=hshort.trans (min_le_left _ _)
  have h₂:width/4≤length Z X₂:=hshort.trans (min_le_right _ _)
  have hraw (X:ℝ)(hX:0<X)(h:width/4≤length Z X):
      length Z X=Real.logb Z X ∧ width/4≤Real.logb Z X:=by
    have he:=CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX
    have hp:0<Real.logb Z X:=by
      by_contra hn
      rw [he,max_eq_left (le_of_not_gt hn)] at h
      linarith
    refine ⟨he.trans (max_eq_right hp.le),?_⟩
    rwa [he,max_eq_right hp.le] at h
  obtain ⟨he₁,hr₁⟩:=hraw X₁ hX₁ h₁
  obtain ⟨he₂,hr₂⟩:=hraw X₂ hX₂ h₂
  refine ⟨?_,?_,le_refl _,?_,?_⟩
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₁] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₁
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₂] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₂
  · rw [comparison_second_power Z width X₁ X₂ hZ hX₁ hX₂,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [he₁,he₂,Real.logb_mul hX₁.ne' hX₂.ne']

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      min (length Z X₁) (length Z X₂)≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric

end

end OAI
end OAIOriginalModule2745

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetricBounded
Source SHA256: 7007d81a940fd698e9405a203c4b855aa25de4ad2d4c4281758d8257ecdc6f93
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2746



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionBounded
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyOriginalHighReflectionSymmetric

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      min (length Z X₁) (length Z X₂)≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
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

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded

end

end OAI
end OAIOriginalModule2746

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceRobustDeletedEnergy
Source SHA256: b5e385d3e4e294539bf46139cbc8d4e94ffe9711d0e2517ff1d0c1111d449aa4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2747




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem deleted_energy_from_low_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hdefect:0≤defect)(hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi+11*defect/7≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-defect≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (comparisonFirst Z s.width/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (comparisonSecond Z s.width X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=s.width/4-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=>hw i)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi defect hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=>hw i)) hsum hsumle hκ hxi.le hdefect hxiM hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=>Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergy

end

end OAI
end OAIOriginalModule2747

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceRobustOriginal
Source SHA256: 88a8fce7fa21f4516b649cd44b075a37ce12d8d8eb2e221296147d742b9345f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2748



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyReferenceRobustDeletedEnergy CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_reference_from_low_robust
    (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hdefect:0≤defect)(hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi+11*defect/7≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-defect≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=>bslot) (fun _=>Bslot) (fun _=>hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_energy_from_low_robust (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi defect saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hdefect hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hp:=comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.CenteredMomentEnergyReferenceRobustOriginal

end

end OAI
end OAIOriginalModule2748

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceRobustBounded
Source SHA256: 06796591611908e4d485b5ac6bc20b2fc616670dddb12e7a760f9f492afa38ec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2749




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-rho/100≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
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
  have hxiM:xi+11*(rho/100)/7≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hg:=CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyReferenceRobustBounded

end

end OAI
end OAIOriginalModule2749

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLiveBounded
Source SHA256: 586dfed838534c762c773fc4b5c2f17a8ca69c8f9a72a5e0dd23794d674eec55
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2750


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLiveBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=
    CenteredMomentEnergyReferenceRobustBounded.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.CenteredMomentEnergyReferenceLiveBounded

end

end OAI
end OAIOriginalModule2750

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceRobustPower
Source SHA256: dfab782560e99e50261982732ef0bfa91a66da08fbd50536192b20a89ea9088c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2751




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-rho/100≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_reference_from_low_robust (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi (rho/100) saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by positivity) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hxiM:xi+11*(rho/100)/7≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hg:=CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyReferenceRobustPower

end

end OAI
end OAIOriginalModule2751

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLivePower
Source SHA256: 22bc9abd7a8eb9e14a61c98b9f39961d3e18d797d2b0fa6e35cd53a9859e8741
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2752


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLivePower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=
    CenteredMomentEnergyReferenceRobustPower.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.CenteredMomentEnergyReferenceLivePower

end

end OAI
end OAIOriginalModule2752

/-! Original module: OAI.NumberTheory.DirichletL.Energy.Reindex
Source SHA256: 25310975852db2f8766251fc321f54ec2093dffb9e22ffabf12b37053cb27fdc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2753


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

variable {α β:Type*}[Fintype α][Fintype β]

lemma positive_reindex (e:α≃β)(η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=>CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex (e:α≃β)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

omit [Fintype α] [Fintype β] in
theorem energy_subset_map (e:α↪β)(T:Finset α)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i:T=>pool (e i)) (fun i:T=>coeff (e i))
      (fun i:T=>P (e i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i)
      (fun i:T.map e=>P i) X₁ X₂ keep Φ K:=
  energy_reindex (Finset.equivMap e T) η m A W₁ W₂
    (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i) (fun i:T.map e=>P i)
    t X₁ X₂ keep Φ K

end SevenEighths.CenteredMomentEnergyReindex

end

end OAI
end OAIOriginalModule2753

/-! Original module: OAI.NumberTheory.DirichletL.Energy.BandSubtypeTransport
Source SHA256: 9c074a60508d92e60c260eccc45b320be81eaa7822265665ef6b7f0050b67155
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2754



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandSubtypeTransport
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [Fintype β] in
theorem positiveAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
  let E : T≃T.map e := Finset.equivMap e T
  let θ' : T.map e→RayQuotient.Characters M H := θ∘E.symm
  let w' : T.map e→ℝ := w∘E.symm
  let σ' : T.map e→ℝ := σ∘E.symm
  let v' : T.map e→ℝ := v∘E.symm
  have hsum : (∑i:T.map e,w' i)=∑i:T,w i := E.symm.sum_comp w
  have hh := h (T.map e) θ' w' σ' v' t height
    (fun i=>hw (E.symm i)) (fun i=>hwL (E.symm i))
    (fun i=>hσlo (E.symm i)) (fun i=>hσhi (E.symm i))
    hheight (fun i=>hv (E.symm i)) s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
    (by rw [hsum];exact hcapacity)
  have he := energy_reindex E s.character s.mask 1 (p.profile 0) (p.profile 1)
    (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
    (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
    (fun i:T.map e=>Z^(w' i)) t X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have he' : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>primePool M H bslot (Z^(w i)))
      (fun (i:T) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:T=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
      (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
      (fun i:T.map e=>Z^(w' i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
    simpa only [Function.comp_def,θ',w',σ',v',Equiv.symm_apply_apply] using he
  exact he'.le.trans hh

omit [Fintype α] in
theorem positiveAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h

end SevenEighths.CenteredMomentEnergyBandSubtypeTransport

end

end OAI
end OAIOriginalModule2754

/-! Original module: OAI.NumberTheory.DirichletL.Energy.LowBandSubtype
Source SHA256: 2707765c65f63f5cd5a1c057513ea04c252f09517b3d4e1f43a7fdbb7253ae6c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2755



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLowBandSubtype
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentEnergyReferenceLowBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [Fintype β] in
theorem positiveLowAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  let E : T≃T.map e := Finset.equivMap e T
  let θ' : T.map e→RayQuotient.Characters M H := θ∘E.symm
  let w' : T.map e→ℝ := w∘E.symm
  let σ' : T.map e→ℝ := σ∘E.symm
  let v' : T.map e→ℝ := v∘E.symm
  have hsum : (∑i:T.map e,w' i)=∑i:T,w i := E.symm.sum_comp w
  have hh := h (T.map e) θ' w' σ' v' t height
    (fun i=>hw (E.symm i)) (fun i=>hwL (E.symm i))
    (fun i=>hσlo (E.symm i)) (fun i=>hσhi (E.symm i))
    hheight (fun i=>hv (E.symm i)) s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
    (by rw [hsum];exact hcapacity) (by rw [hsum];exact hlow)
  have he := energy_reindex E s.character s.mask 1 (p.profile 0) (p.profile 1)
    (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
    (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
    (fun i:T.map e=>Z^(w' i)) t X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have he' : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>primePool M H bslot (Z^(w i)))
      (fun (i:T) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:T=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
      (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
      (fun i:T.map e=>Z^(w' i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
    simpa only [Function.comp_def,θ',w',σ',v',Equiv.symm_apply_apply] using he
  exact he'.le.trans hh

omit [Fintype α] in
theorem positiveLowAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveLowAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h

end SevenEighths.CenteredMomentEnergyLowBandSubtype

end

end OAI
end OAIOriginalModule2755

/-! Original module: OAI.NumberTheory.DirichletL.Energy.WidthFloor
Source SHA256: 07b986deee8865483d88ae68ceaba4b0385ba5f397c012db0752bb1872caec7d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2756



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthFloor
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

private lemma control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(h:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_joint_floor (Mcap B κ ε:ℝ)(hMcap:0≤Mcap)(hB:0≤B)
    (hκ0:0≤κ)(hε:0<ε)
    (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L lo hi:ℝ)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        ZeroAt (internalQ Q η₀) a b bΦ Bmask L (width Mcap B ε 0)
          (loss Mcap B ε 0) Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
          (width Mcap B ε 0) (loss Mcap B ε 0) κ Z η₀ Q degree S Cpositive:=by
  have hs:=bounds Mcap B κ ε hMcap hB hκ0 hε
  have hr:=hs.2.2.2.1
  have hm:=hs.2.2.2.2.1
  obtain ⟨Jzero,Szero,Czero,hCzero,hzero⟩:=exists_zero_floor
    a b bΦ Bmask (reserve Mcap B ε) ha hb hbΦ hmask hr
  obtain ⟨Jpositive,Spositive,Cpositive,hCpositive,hpositive⟩:=exists_positive_bottom (α:=α)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
      (reserve Mcap B ε) κ ha hb hbΦ hmask hr hm.le hbeta hκ
  refine ⟨Jzero+Jpositive,Szero∪Spositive,Czero,Cpositive,hCzero,hCpositive,?_⟩
  intro η₀
  filter_upwards [hpositive η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q hQM
  rw [width_zero,loss_zero]
  constructor
  · intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ _ _
    have hh:=hzero (internalQ Q η₀) Z hZ.1.le s hQ hwidth p t X₁ X₂ hX₁ hX₂
    have hp:=control_mono p (Finset.subset_union_left (s₁:=Szero) (s₂:=Spositive))
    have hpn:=p.control_nonneg Szero
    have hpU:=p.control_nonneg (Szero∪Spositive)
    have hd:=diagonalControl_nonneg s.radial.profile
    have ht:(1+‖t‖)^Jzero≤(1+‖t‖)^(Jzero+Jpositive):=
      pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right _ _)
    apply hh.trans
    gcongr
    exact Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _
  · intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hwidth
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    have hh:=hZ.2 Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv
      s hQ hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    have hp:=control_mono p (Finset.subset_union_right (s₁:=Szero) (s₂:=Spositive))
    have hpn:=p.control_nonneg Spositive
    have hpU:=p.control_nonneg (Szero∪Spositive)
    have hd:=diagonalControl_nonneg s.radial.profile
    have ht:(1+|t|+height)^Jpositive≤(1+|t|+height)^(Jzero+Jpositive):=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.le_add_left _ _)
    apply hh.trans
    gcongr
    exact Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _

end SevenEighths.CenteredMomentEnergyWidthFloor

end

end OAI
end OAIOriginalModule2756

/-! Original module: OAI.NumberTheory.DirichletL.Energy.WidthInduction
Source SHA256: 3b11106f78348cc5fcb220b14ddcb0336324fc16042b40e1b19ca19c0f7d7e35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2757





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

def remaining (M ε:ℝ)(k:ℕ):ℕ:=count M ε-k
def lowerAt (a b M ε:ℝ)(k:ℕ):ℝ:=CenteredMomentEnergyProfiles.lower a b (remaining M ε k)
def lengthAt (M B L ε:ℝ)(k:ℕ):ℝ:=range M B L (remaining M ε k)

lemma lowerAt_pos (a b M ε:ℝ)(ha:0<a)(k:ℕ):0<lowerAt a b M ε k:=
  CenteredMomentEnergyProfiles.lower_pos a b ha _

lemma child_support (a b M ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lowerAt a b M ε k=lowerAt a b M ε (k+1)/max 1 b:=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lowerAt,he,CenteredMomentEnergyProfiles.lower]

lemma child_length (M B L ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lengthAt M B L ε k=step M B (lengthAt M B L ε (k+1)):=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lengthAt,he,range]

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (width Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (width Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0<a)(hb:0≤b)(hrad:0<radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ0:0≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
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
  have hloss:loss Mcap Bs ε 0≤stageLoss Mcap Bs ε 0:=by
    unfold stageLoss
    linarith
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      le_rfl le_rfl hloss le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hh.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hloss le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hh.2

omit [Fintype α] [DecidableEq α] in
theorem certified_terminal (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
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
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) hcover.le he le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hz
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl (le_max_right _ _) hcover.le he le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hp

end SevenEighths.CenteredMomentEnergyWidthInduction

end

end OAI
end OAIOriginalModule2757

/-! Original module: OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
Source SHA256: d1817f2122c48f2b9f9954cc564eef59b119d2f1b467343b4ad9b78604b825d6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2758





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

def bandWidth (M B ε:ℝ)(k:ℕ):ℝ:=min M (width M B ε k)
lemma bandWidth_le (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤M:=min_le_left _ _
lemma bandWidth_le_schedule (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤width M B ε k:=min_le_right _ _
lemma bandWidth_nonneg (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)(k:ℕ):
    0≤bandWidth M B ε k:=by
  have hr:0<reserve M B ε:=(bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.1
  have hs:0<amplification ε:=(bounds M B 0 ε hM hB (by norm_num) hε).1
  unfold bandWidth width
  positivity
lemma bandWidth_terminal (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε):
    bandWidth M B ε (count M ε)=M:=by
  have hh: M<width M B ε (count M ε):=
    (bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.2.2.2.2.2.1
  exact min_eq_left hh.le
lemma actual_child_band (M B ε parent child:ℝ)(hε:0<ε)(k:ℕ)
    (hp:parent≤bandWidth M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤bandWidth M B ε k:=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  apply le_min
  · have hh:=hp.trans (bandWidth_le M B ε (k+1));linarith
  · exact child_band M B ε parent child k (hp.trans (bandWidth_le_schedule M B ε (k+1))) hc

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive

theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0<a)(hb:0≤b)(hrad:0<radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ0:0≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
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
  have hloss:loss Mcap Bs ε 0≤stageLoss Mcap Bs ε 0:=by
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
    (hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
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

end SevenEighths.CenteredMomentEnergyCappedWidthInduction

end

end OAI
end OAIOriginalModule2758

/-! Original module: OAI.NumberTheory.DirichletL.Energy.CappedBandTransport
Source SHA256: b4985987719271c32dea8d31a11940810019d25bb6fa0d645f71603b99534657
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2759


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedBandTransport
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma saturated_successor (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (hsaturated:bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k=Mcap)
    (h:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε k):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0<reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hwidth:bandWidth Mcap Bs ε (k+1)≤bandWidth Mcap Bs ε k:=by
    rw [hsaturated]
    exact bandWidth_le _ _ _ _
  have hloss:stageLoss Mcap Bs ε k≤stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨degree,S,hcert⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCz,hCp,hbound⟩:=hcert η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCz,hCp,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le hlower le_rfl le_rfl le_rfl
      hlength hwidth hloss le_rfl (Finset.Subset.refl _) hCz.le le_rfl hZ.2.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      hlower le_rfl le_rfl le_rfl hlength hwidth hloss le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hZ.2.2

end SevenEighths.CenteredMomentEnergyCappedBandTransport

end

end OAI
end OAIOriginalModule2759

/-! Original module: OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport
Source SHA256: 5e61fd581589a817d306fa8b14fe53d8a236d8a8d5d60aacdbae64d39b2547fe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2760


namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedRadialTransport
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyBandMonotonicity
local notation "O" => HeckeFamily.O
variable {α : Type*}
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem certified_radial_mono (W : ℝ → ℂ)
    (bslot a b radialOld radialNew Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (hrad : radialNew ≤ radialOld)
    (h : CertifiedBand (α := α) M H hH W bslot a b radialOld Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH W bslot a b radialNew Bmask L lo hi Mcap κ ε k := by
  obtain ⟨degree, S, hbound⟩ := h
  refine ⟨degree, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero, Cpositive, hCzero, hCpositive, hcert⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero, Cpositive, hCzero, hCpositive, ?_⟩
  filter_upwards [hcert] with Z hZ
  refine ⟨hZ.1, ?_, ?_⟩
  · exact zeroAt_transport _ _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl hrad le_rfl
      le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hZ.2.1
  · exact positiveAt_transport (α := α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl hrad le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hZ.2.2

theorem certified_from_max_two (W : ℝ → ℂ)
    (bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (h : CertifiedBand (α := α) M H hH W bslot a b (max 2 radial)
      Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k :=
  certified_radial_mono (α := α) M H hH W bslot a b (max 2 radial) radial
    Bmask L lo hi Mcap κ ε k (le_max_right _ _) h

end SevenEighths.CenteredMomentEnergyCappedRadialTransport

end

end OAI
end OAIOriginalModule2760

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowth
Source SHA256: 39558bb2c411f95b0b56234f5bf42971120f4b1bc0236373487fe0abb3487261
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2761


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowth
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands QuadraticInitialBound
local notation "O" => HeckeFamily.O

def ZeroGrowthAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = Q → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ,
    0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.plainEnergy p t X₁ X₂ ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + ‖t‖) ^ degree *
        Z ^ (max s.width (length Z X₁ + length Z X₂) + ε)

lemma zeroGrowth_of_zeroAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ZeroAt Q a b bΦ Bmask L M ε Z degree S C) :
    ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  apply (h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
  have he : s.width + ε ≤ max s.width (length Z X₁ + length Z X₂) + ε := by
    linarith [le_max_left s.width (length Z X₁ + length Z X₂)]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one he)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC
    (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _)

lemma zeroGrowth_on_capacity (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (h : ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = Q) (hs : s.width ≤ M)
    (p : Profiles a b) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hcapacity : length Z X₁ + length Z X₂ ≤ s.width) :
    s.plainEnergy p t X₁ X₂ ≤ C * diagonalControl s.radial.profile *
      (p.control S) ^ 2 * (1 + ‖t‖) ^ degree * Z ^ (s.width + ε) := by
  simpa only [max_eq_left hcapacity] using
    h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂

theorem exists_zero_growth_floor (a b bΦ Bmask L ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hbΦ : 0 < bΦ) (hmask : 0 ≤ Bmask)
    (hε : 0 < ε) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Q : Ideal O, ∀ Z : ℝ, 1 ≤ Z →
        ZeroGrowthAt Q a b bΦ Bmask L (ε / 16) ε Z degree S C := by
  obtain ⟨degree, S, C, hC, hf⟩ := exists_zero_floor a b bΦ Bmask ε ha hb hbΦ hmask hε
  refine ⟨degree, S, C, hC, ?_⟩
  intro Q Z hZ
  exact zeroGrowth_of_zeroAt Q a b bΦ Bmask L (ε / 16) ε Z degree S C hC.le
    (zeroAt_of_zeroBound Q a b bΦ Bmask L (ε / 16) ε Z 1 degree S C (hf Q) hZ)

end SevenEighths.CenteredMomentEnergyZeroGrowth

end

end OAI
end OAIOriginalModule2761

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceChild
Source SHA256: b009ff48b6cb77d4f153d401aeb8dd07887c3b833cd93f8c1cfce4779d9bc9f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2762


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

lemma independent_energy {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (hB:0≤Bmask)(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    (unitBudgetState s hB).plainEnergy (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂:=by
  have hh:=independent_child_energy s ha W₁ W₂ hs₁ hs₂ (∅:Finset (Fin 0))
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t₁ t₂ X₁ X₂ hX₁ hX₂ (by simp)
  simpa only [Finset.prod_empty,mul_one,energy,NaturalState.plainEnergy,
    CenteredMomentRetainedEnergy.positiveSlotRow,Fintype.prod_empty,
    unitBudgetState,unpuncturedState,NaturalState.mask,effectiveState,effectiveRadial] using hh

theorem independent_from_low
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hsmall:length Z X₁+length Z X₂≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(s.width+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_low
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hsmall:length Z X₁+length Z X₂≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(s.width+ε):=by
  have hh:=independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end SevenEighths.CenteredMomentEnergyZeroReferenceChild

end

end OAI
end OAIOriginalModule2762

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthChild
Source SHA256: 6c15f6ce702a46828557c0397d93ecafd789c935168e45de6409c77d0536b16a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2763



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

theorem independent_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    :
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    :
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  have hh:=independent_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthChild

end

end OAI
end OAIOriginalModule2763

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceGeometry
Source SHA256: 8a4210c78f9f00f0fa8b7b9271ea12ed28f8b04fcfe4c00373686f9f37c2cdf6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2764



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroReferenceGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
local notation "O"=>HeckeFamily.O

lemma low_or_reflected (M short along xi:ℝ)(hM:0≤M)(hs:short≤M/4)(_hxi:0≤xi)
    (hxiM:xi≤M/6):
    max 0 short+max 0 along≤5*M/6 ∨
      (0<along ∧ max 0 (M-along+xi)+max 0 short≤5*M/6):=by
  have hs0:max 0 short≤M/4:=max_le (by linarith) hs
  by_cases hl:max 0 short+max 0 along≤5*M/6
  · exact Or.inl hl
  · right
    have halong:0<along:=by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn)] at hl
      linarith
    refine ⟨halong,?_⟩
    rw [max_eq_right halong.le] at hl
    rcases le_total 0 (M-along+xi) with hh|hh
    · rw [max_eq_right hh]
      linarith
    · rw [max_eq_left hh]
      linarith

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hxi:0≤xi)(hxiM:xi≤s.width/6)
    (hlarge:s.width/4≤Real.logb Z (X₁*X₂))
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ -Bmask≤along ∧
    s.width≤Mcap+Bmask+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((along≤L ∧ length Z (Z^short)+length Z (Z^along)≤5*s.width/6) ∨
      (0<along ∧ max 0 (s.width-along+xi)+length Z (Z^short)≤5*s.width/6)):=by
  dsimp only
  have hZ0:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁
  have hl₂:=Real.logb_nonneg hZ hn₂
  have hu₂:Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn₂)).mpr hc₂
  have hM:=s.width_nonneg
  have hL0:0≤L:=by linarith
  have he₁:Z^(s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ))=
      comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ):=by
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' (zero_lt_one.trans_le hn₁)]
    rfl
  have he₂:Z^(Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ))=
      comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
    rw [Real.rpow_sub hZ0,Real.rpow_sub hZ0,
      Real.rpow_logb hZ0 hZ.ne' (mul_pos hX₁ hX₂),
      Real.rpow_logb hZ0 hZ.ne' (zero_lt_one.trans_le hn₂)]
    rfl
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,by linarith,
    max_le hL0 (by linarith),?_⟩
  have hlen (v:ℝ):length Z (Z^v)=max 0 v:=by
    rcases le_total 0 v with hv|hv
    · rw [length, max_eq_right (Real.one_le_rpow hZ.le hv),
        Real.logb_rpow hZ0 hZ.ne',max_eq_right hv]
    · rw [length,max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le hv),
        Real.logb_one,max_eq_left hv]
  simp only [hlen]
  rcases low_or_reflected s.width
    (s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ))
    (Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ))
    xi hM (by linarith) hxi hxiM with hd|hr
  · refine Or.inl ⟨?_,hd⟩
    have hh₁:=le_max_right (0:ℝ)
      (Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ))
    have hh₂:=le_max_left (0:ℝ) (s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ))
    linarith
  · exact Or.inr hr

end SevenEighths.CenteredMomentEnergyZeroReferenceGeometry

end

end OAI
end OAIOriginalModule2764

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceMoments
Source SHA256: 882b51f9be861f1272da6c28113179dfea5c3fe290d5219151f1b573b279b854
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2765



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroReferenceChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    length Z X₁+length Z X₂≤5*s.width/6 →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hh:=reflected_from_low a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroReferenceMoments

end

end OAI
end OAIOriginalModule2765

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceReflection
Source SHA256: 0ad39eb829c6ad85de6dcb3f2b780f3a2c499f3325c50316d48717dd05f52622
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2766




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyZeroReferenceMoments CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
local notation "O"=>HeckeFamily.O

theorem reference_from_low
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask L Mcap ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K → 0≤Bmask →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+ε);
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t)
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=reflected_uniform a b ha hlo hhi S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap ε Q degree K hK hlow hBmask s hQ hs
    Wlong Wshort hsLong hsShort t along bshort hlength hL hbshort hsmall
  dsimp only
  have hh:=hZ.2 Bmask s Wlong Wshort hsLong hsShort (Fin 0) ∅
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t along bshort
    (K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+ε)) hlength
  simp only [Finset.prod_empty,mul_one] at hh
  apply hh
  · have hz:0<Z:=zero_lt_one.trans hZ.1
    have hd:0≤diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
    positivity
  · intro v j k x hx
    have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
    exact hchild bΦ Bmask L Mcap ε Z Q degree K hK hlow hBmask s hQ hs Wshort hsShort
      j k v t (Real.exp x) (Z^bshort) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
      (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hL))
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbshort)
      (by linarith [hwindow.1])

end SevenEighths.CenteredMomentEnergyZeroReferenceReflection

end

end OAI
end OAIOriginalModule2766

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceDeleted
Source SHA256: d8559bcbd381660252a8c6ed430804f4c8aed6139b0e5d86dbaa099bc69c4b54
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2767




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyZeroReferenceGeometry CenteredMomentEnergyZeroReferenceReflection
open CenteredMomentEnergyZeroReferenceError CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
local notation "O"=>HeckeFamily.O

theorem deleted_from_low (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤s.width/6 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀t X₁ X₂:ℝ,0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (comparisonFirst Z s.width/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (comparisonSecond Z s.width X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)):=by
  obtain ⟨Ce,hCe,he⟩:=short_energy_bound b
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Ce,hC,mul_pos hD hCe,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM W₁ W₂ hs₁ hs₂ t X₁ X₂ hX₁ hX₂ hlarge D₁ hD₁ D₂ hD₂
  let short:=s.width/4-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ xi hs hL
    hX₁ hX₂ hxi.le hxiM hlarge D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=independent_from_low a b bΦ Bmask L Mcap ε Z Q degree S K hlow hBmask ha
      s hQ hs W₁ W₂ hs₁ hs₂ t t (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hd.1) hd.2
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Mcap ε Q degree K hK hlow hBmask s hQ hs
      W₂ W₁ hs₂ hs₁ t along short hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2
    dsimp only at hh
    have he₁:=he W₁ (fun x hx=>(hs₁ hx).2) (fun z=>naturalCharacter s.character z)
      t (Z^short) s.radial.scale s.radial.profile (effectiveState s).radial.keep
      (Real.rpow_pos_of_pos hZpos _) s.radial.scale_pos s.radial.nonneg
    have hswap:(fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t)=
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · calc
        _≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          (Ce*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4)):=by
          gcongr
          exact he₁.trans (by
            gcongr
            · exact hZ.1.le
            · exact hg.2.2.1)
        _=_:=by ring

end SevenEighths.CenteredMomentEnergyZeroReferenceDeleted

end

end OAI
end OAIOriginalModule2767

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceOriginal
Source SHA256: 1814d66c3ff288e67a3e8d309048d9664171dde5e2f53e4aab4fbc4bbce4f6cf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2768



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyZeroReferenceDeleted
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O

theorem original_from_low (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤s.width/6 →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4))):=by
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_from_low
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ε Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hp:=comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith)
    (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
    t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) _ 0
  · simp
  · simp
  · simp
  · simp
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_zero] using
      hZ.2 ε Q degree K hK hlow s hQ hs hxiM (p.profile 0) (p.profile 1)
        (p.support 0) (p.support 1) t X₁ X₂ hX₁ hX₂ hlarge D₁ hD₁ D₂ hD₂

end SevenEighths.CenteredMomentEnergyZeroReferenceOriginal

end

end OAI
end OAIOriginalModule2768

