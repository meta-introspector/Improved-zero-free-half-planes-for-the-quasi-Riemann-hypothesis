theorem actual_error_weight (p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(k:ℕ)
    (hk:k=1 ∨ k=6 ∨ k=7):
    localErrorCost p (k-1)≤Z^(-errorMoving p Z k):=by
  have hn:1≤normValue p:=normValue_ge_one p hp
  have hnpos:0<normValue p:=normValue_pos p hp
  have he:Z^(-(Real.logb Z (normValue p)))=(normValue p)⁻¹:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hnpos]
  rcases hk with rfl|rfl|rfl
  · simpa [localErrorCost,errorMoving,normValue] using he.ge
  · norm_num only [Nat.reduceSub,localErrorCost,errorMoving,ite_true,neg_zero,Real.rpow_zero]
    change (1-(normValue p)⁻¹)^2≤1
    have hi:0≤(normValue p)⁻¹:=inv_nonneg.mpr hnpos.le
    have hu:(normValue p)⁻¹≤1:=inv_le_one_of_one_le₀ hn
    nlinarith
  · simpa [localErrorCost,errorMoving,normValue] using he.ge

end SevenEighths.CenteredMomentFirstMixedNormalization

end

end OAI
end OAIOriginalModule2236

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
Source SHA256: 12044cf80f4564f2efb1c221d797ae122398a774a8624e95cb58b51f36cf427c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2237





namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentFixedRayInducingTransport CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def relativeCharacter (η₀ : Character) (θ : RayQuotient.Characters M H) : Character :=
  (HeckeRayQuotient.character M H hH θ).product η₀.inverse

lemma relativeCharacter_ideal (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (relativeCharacter M H hH η₀ θ) I=
      idealCoeff (HeckeRayQuotient.character M H hH θ) I*idealCoeff η₀.inverse I :=
  idealCoeff_product _ _ _

lemma relativeCharacter_norm (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal O) :
    ‖idealCoeff (relativeCharacter M H hH η₀ θ) I‖≤1 := idealCoeff_norm_le_one _ _

lemma relativeCharacter_modulus (η₀ : Character) (θ : RayQuotient.Characters M H) :
    (relativeCharacter M H hH η₀ θ).modulus.absNorm≤M.absNorm*η₀.modulus.absNorm :=
  HeckePrimeScale.product_modulus_bound _ _

lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal O) (hQM : Q≤M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη

lemma excluded_product_ideal (χ ν : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I*idealCoeff ν I=idealCoeff (excluded (χ.product ν) R) I := by
  rw [excluded_ideal χ R hR,excluded_ideal (χ.product ν) R hR,idealCoeff_product]
  split_ifs <;> simp

lemma sector_element {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (n : O) :
    elementCoeff (F.character.product (relativeCharacter M H hH η₀ θ)) n=
      rowTwist (elementHom (η.product (relativeCharacter M H hH η₀ θ))) fixedBadMask 1 z n := by
  simpa only [one_mul] using CenteredMomentDetectorDictionary.product_row_presentation η F.character
    (relativeCharacter M H hH η₀ θ) fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) n

theorem sector_fixedQ_iff (η η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q R : Ideal O) (z : O) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (hR : R≠0) (hz : z≠0) :
    FixedInducingRow (η.product (relativeCharacter M H hH η₀ θ)) Q
      (fixedBadMask*idealGenerator R) 1 z ↔
    FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z :=
  fixedInducingRow_product_iff η (relativeCharacter M H hH η₀ θ) Q
    (fixedBadMask*idealGenerator R) 1 z
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R hR)) one_ne_zero hz
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _))

theorem sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤M) (hQη : Q≤η₀.modulus) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentRayNonprincipal.actual_row_twist_nonprincipal η F.character
    (relativeCharacter M H hH η₀ θ) Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)
    (relativeCharacter_fixedQ M H hH η₀ θ Q hQM hQη) hbase

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2237

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorProfile
Source SHA256: 5648950eb7c0b420fabf94f0867ece8135a6da9c92695666c4ea5e0b4198978c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2238



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles CenteredMomentDetectorDictionary
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentHeckeVolume
open CenteredMomentMask QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma detectorSchwartz_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (detectorSchwartz reverse n σ t:ℝ→ℂ)⊆Set.Icc (1/4) (9/4) := by
  intro x hx
  change detectorSchwartz reverse n σ t x≠0 at hx
  rw [detectorSchwartz_apply] at hx
  exact detector_profile_support reverse n σ (orientedFrequency reverse t) hx

def detectorNormProfile (reverse : Bool) (n : ℕ) (σ t h : ℝ) : 𝓢(ℝ,ℂ) :=
  normPowerProfile (detectorSchwartz reverse n σ t) (1/4) (9/4) (by norm_num)
    (detectorSchwartz_support reverse n σ t) ((detectorSchwartz reverse n σ t).smooth ⊤) h

lemma orientedFrequency_add_height (reverse : Bool) (t h : ℝ) :
    orientedFrequency reverse (t+orientedFrequency reverse h)=orientedFrequency reverse t+h := by
  cases reverse <;> simp [orientedFrequency] ; ring

theorem detectorNormProfile_eq (reverse : Bool) (n : ℕ) (σ t h : ℝ) :
    detectorNormProfile reverse n σ t h=
      detectorSchwartz reverse n σ (t+orientedFrequency reverse h) := by
  ext x
  rw [detectorNormProfile,normPowerProfile_apply,detectorSchwartz_apply,detectorSchwartz_apply,
    orientedFrequency_add_height]
  unfold twistProfile
  by_cases hw : orientedProfile reverse ((logProfile^[n]) positiveAnnular) x=0
  · simp only [hw,zero_mul,mul_zero]
  · have hx : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
      ((oriented_detector_log_support reverse n) hw).1
    calc
      _=orientedProfile reverse ((logProfile^[n]) positiveAnnular) x*
          ((x:ℂ)^(Complex.I*h)*(x:ℂ)^(-HeckeDyadic.shift σ (orientedFrequency reverse t))) := by ring
      _=orientedProfile reverse ((logProfile^[n]) positiveAnnular) x*
          (x:ℂ)^(Complex.I*h-HeckeDyadic.shift σ (orientedFrequency reverse t)) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2; unfold HeckeDyadic.shift; push_cast; ring

theorem detectorNormProfile_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2 → ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorNormProfile reverse n σ t h)≤
        C*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorSchwartz_uniform S
  refine ⟨J,C,hC,?_⟩
  intro reverse n hn σ hσ t h
  rw [detectorNormProfile_eq]
  apply (hbound reverse n hn σ hσ (t+orientedFrequency reverse h)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  have he : ‖orientedFrequency reverse h‖=‖h‖ := by cases reverse <;> simp [orientedFrequency]
  have hh:=norm_add_le t (orientedFrequency reverse h)
  rw [he] at hh
  linarith

theorem detector_volumeControl_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀χ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      volumeControl Q χ (detectorNormProfile reverse n σ t h)≤C*Z^ε*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,A,hA,hprofile⟩:=detectorNormProfile_uniform pvSeminorms
  obtain ⟨D,hD,hdiv⟩:=polynomial_mask_divisor_bound ε B hε hB
  refine ⟨J,?_⟩
  intro Q
  let mass : ℝ:=Nat.card (O⧸Ideal.span {fixedPeriod Q})
  let K : ℝ:=D*mass*pvConstant*A
  have hmass : 0≤mass:=Nat.cast_nonneg _
  have hK : 0≤K:=by dsimp [K];exact mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hA.le
  refine ⟨1+K,by linarith,?_⟩
  intro Z hZ χ hχ reverse n hn σ hσ t h
  have herr : volumeControl Q χ (detectorNormProfile reverse n σ t h)≤
      (D*Z^ε)*(mass*(pvConstant*(A*(1+‖t‖+‖h‖)^J))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hχ)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hprofile reverse n hn σ hσ t h) pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · positivity
  calc
    _≤(D*Z^ε)*(mass*(pvConstant*(A*(1+‖t‖+‖h‖)^J))) := herr
    _=K*Z^ε*(1+‖t‖+‖h‖)^J := by dsimp [K];ring
    _≤(1+K)*Z^ε*(1+‖t‖+‖h‖)^J := by gcongr;linarith

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2238

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceAllocatedProfile
Source SHA256: c62ccec48857971efbad1ffd113919accb457d184ec4b77019e43fe336ad4ace
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2239



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredMomentDetectorDictionary CenteredMomentAllocatedNaturalSource
open CenteredMomentRetainedProfile CenteredMomentLattice CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation QuadraticInitialBound EisensteinSchwartzPoisson

def detectorPlain (reverse : Bool) (n : ℕ) (σ t : ℝ) : Plain where
  W := detectorSchwartz reverse n σ t
  a := 1/4
  b := 9/4
  a_pos := by norm_num
  support := detectorSchwartz_support reverse n σ t
  smooth := (detectorSchwartz reverse n σ t).smooth ⊤

theorem detectorPlain_profile_apply (reverse : Bool) (n : ℕ) (σ t U : ℝ)
    (hU : 0<U) (h x : ℝ) :
    (detectorPlain reverse n σ t).profile U hU h x =
      if 1≤U*(9/4) then
        (x:ℂ)^(Complex.I*h)*detectorSchwartz reverse n σ t (clipDilation U*x)
      else 0 := by
  by_cases hr : 1≤U*(9/4)
  · have hr' : 1 ≤ U * (detectorPlain reverse n σ t).b := hr
    rw [Plain.profile_retained _ U hU h hr',retainedProfile_apply,ite_eq_left hr]
    rfl
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr),ite_eq_right hr]
    rfl

theorem detectorPlain_profile_support (reverse : Bool) (n : ℕ) (σ t U : ℝ)
    (hU : 0<U) (h : ℝ) :
    Function.support ((detectorPlain reverse n σ t).profile U hU h:ℝ→ℂ)⊆
      Set.Icc (1/9) (9/4) := by
  by_cases hr : 1≤U*(9/4)
  · rw [Plain.profile_retained _ U hU h hr]
    have hs:=retainedProfile_support _ _ _ (detectorPlain reverse n σ t).a_pos
      (detectorPlain reverse n σ t).support (detectorPlain reverse n σ t).smooth U hU hr h
    norm_num [detectorPlain] at hs ⊢
    exact hs
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr)]
    simp

theorem detectorPlain_profile_seminorm (S : Finset (ℕ×ℕ))
    (reverse : Bool) (n : ℕ) (σ t U : ℝ) (hU : 0<U) (h : ℝ) :
    S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((detectorPlain reverse n σ t).profile U hU h)≤
      (9/4:ℝ)^(S.sup Prod.snd)*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorNormProfile reverse n σ t h) := by
  by_cases hr : 1≤U*(9/4)
  · rw [Plain.profile_retained _ U hU h hr]
    have hc:=clipDilation_le (9/4) U hU hr
    norm_num at hc
    have hb:=normPowerProfile_dilated_finite (detectorSchwartz reverse n σ t)
      (1/4) (9/4) (9/4) (clipDilation U) (by norm_num) (by norm_num)
      (clipDilation_ge_one U hU) hc (detectorSchwartz_support reverse n σ t)
      ((detectorSchwartz reverse n σ t).smooth ⊤) h S
    simpa only [detectorPlain,retainedProfile,detectorNormProfile,
      max_eq_right (by norm_num : (1:ℝ)≤9/4)] using hb
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr),map_zero]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)

theorem detectorPlain_profile_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h U : ℝ,∀hU : 0<U,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((detectorPlain reverse n σ t).profile U hU h)≤
        C*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorNormProfile_uniform S
  refine ⟨J,(9/4:ℝ)^(S.sup Prod.snd)*C,mul_pos (by positivity) hC,?_⟩
  intro reverse n hn σ hσ t h U hU
  exact (detectorPlain_profile_seminorm S reverse n σ t U hU h).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (hbound reverse n hn σ hσ t h) (show 0≤(9/4:ℝ)^(S.sup Prod.snd) by positivity)))

theorem detectorPlain_volumeControl_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal HeckeFamily.O,∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀χ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h U : ℝ,∀hU : 0<U,
      volumeControl Q χ ((detectorPlain reverse n σ t).profile U hU h)≤
        C*Z^ε*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,hbound⟩:=detector_volumeControl_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q
  obtain ⟨C,hC,hbound⟩:=hbound Q
  refine ⟨(9/4:ℝ)^(pvSeminorms.sup Prod.snd)*C,mul_pos (by positivity) hC,?_⟩
  intro Z hZ χ hχ reverse n hn σ hσ t h U hU
  by_cases hr : 1≤U*(9/4)
  · rw [Plain.profile_retained _ U hU h hr]
    have hv:=retained_volumeControl_le Q χ (detectorSchwartz reverse n σ t) (1/4) (9/4)
      (by norm_num) (detectorSchwartz_support reverse n σ t)
      ((detectorSchwartz reverse n σ t).smooth ⊤) U hU hr h
    have hv' : volumeControl Q χ (retainedProfile (detectorPlain reverse n σ t).W
        (detectorPlain reverse n σ t).a (detectorPlain reverse n σ t).b
        (detectorPlain reverse n σ t).a_pos (detectorPlain reverse n σ t).support
        (detectorPlain reverse n σ t).smooth U hU hr h)≤
        (9/4:ℝ)^(pvSeminorms.sup Prod.snd)*volumeControl Q χ (detectorNormProfile reverse n σ t h) := by
      simpa only [detectorPlain,detectorNormProfile,max_eq_right (by norm_num : (1:ℝ)≤9/4)] using hv
    exact hv'.trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (hbound Z hZ χ hχ reverse n hn σ hσ t h)
      (show 0≤(9/4:ℝ)^(pvSeminorms.sup Prod.snd) by positivity)))
  · rw [Plain.profile_zero _ U hU h (lt_of_not_ge hr)]
    simp only [volumeControl,pvControl,map_zero,mul_zero]
    positivity

theorem allocated_detector_profiles_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀α : Type,∀_ : Fintype α,∀_ : DecidableEq α,
      ∀D : Ideal HeckeFamily.O,
      ∀a : CenteredMomentDivisorAllocation.Allocation D (Finset.univ : Finset (α⊕Fin 2)),
      ∀reverse : Fin 2→Bool,∀n : Fin 2→ℕ,(∀j,n j≤2) →
      ∀σ : Fin 2→ℝ,(∀j,σ j∈Set.Icc (0:ℝ) 1) →
      ∀t X : Fin 2→ℝ,∀hX : ∀j,0<X j,∀h : ℝ,∀j : Fin 2,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        ((detectorPlain (reverse j) (n j) (σ j) (t j)).profile
          (rawScale D a (X j) j) (rawScale_pos D a (X j) (hX j) j) h)≤
        C*(1+‖t 0‖+‖t 1‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorPlain_profile_uniform S
  refine ⟨J,C,hC,?_⟩
  intro α _ _ D a reverse n hn σ hσ t X hX h j
  apply (hbound (reverse j) (n j) (hn j) (σ j) (hσ j) (t j) h
    (rawScale D a (X j) j) (rawScale_pos D a (X j) (hX j) j)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  fin_cases j <;> dsimp <;> linarith [abs_nonneg (t 0),abs_nonneg (t 1)]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2239

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceAllocatedErrorMass
Source SHA256: 2fc3e1642f7a7d76a88aa891fbec90aaa3a1dfa2860d0df4f70b006717f70930
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2240




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open CenteredMomentOriginalReflectionErrorMass
local notation "O" => HeckeFamily.O

theorem naturalSlot_ideal_bound (χ : Character) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (b M P : ℝ) (hM : 0≤M) (hP : 0<P)
    (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool β P‖≤(128*max 1 b*M)*Real.sqrt P := by
  let f : Ideal O→ℂ:=fun I=>if I∈pool then idealCoeff χ I*β I else 0
  have hf0 : f 0=0:=by simp only [f,idealCoeff_zero,zero_mul,ite_self]
  have hf : ∀I,‖f I‖≤M := by
    intro I
    by_cases hi : I∈pool
    · simp only [f,ite_eq_left hi,norm_mul]
      exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hβ I hi) (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    · simpa only [f,ite_eq_right hi,norm_zero] using hM
  have hsup : ∀I,f I≠0 → (I.absNorm:ℝ)≤max 1 b*P := by
    intro I hi
    have hm : I∈pool:=by by_contra hn;exact hi (by simp only [f,ite_eq_right hn])
    have hb : β I≠0:=by intro hz;exact hi (by simp only [f,ite_eq_left hm,hz,mul_zero])
    exact (hs I hm hb).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hP.le)
  have he : (∑'I:Ideal O,f I)=∑I∈pool,idealCoeff χ I*β I := by
    rw [tsum_eq_sum (s:=pool) (fun I hi=>by simp only [f,ite_eq_right hi])]
    exact Finset.sum_congr rfl (fun I hi=>by simp only [f,ite_eq_left hi])
  have hh:=norm_tsum_ideal_ball f (max 1 b*P) M (by positivity) hM hf0 hf hsup
  rw [he] at hh
  unfold naturalSlot
  rw [←inverse_half_power P hP.le]
  apply normalized_linear_bound P _ hP
  convert hh using 1 ; ring

theorem naturalSlot_height_bound (χ : Character) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (b M P t : ℝ) (hM : 0≤M) (hP : 0<P)
    (hp : ∀I∈pool,Prime I) (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool (heightCoefficient β t) P‖≤(128*max 1 b*M)*Real.sqrt P := by
  apply naturalSlot_ideal_bound χ pool _ b M P hM hP
  · intro I hi
    rw [heightCoefficient_norm _ _ _ (hp I hi).ne_zero]
    exact hβ I hi
  · intro I hi hn
    exact hs I hi (left_ne_zero_of_mul hn)

theorem natural_remaining_sq_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort Bshort b M*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (hM j (hT hj)) (hP j hj) (hβ j hj) (hs j hj)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort Bshort b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hT (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort*Bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ errorConstant F bshort Bshort b M*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
    _ = _ := by ring

lemma allocated_profile_supnorm :
    ∃n : ℕ,∃A : ℝ,0<A ∧ ∀reverse : Bool,∀k : ℕ,k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h U : ℝ,∀hU : 0<U,∀x : ℝ,
      ‖(detectorPlain reverse k σ t).profile U hU h x‖≤A*(1+‖t‖+‖h‖)^n := by
  obtain ⟨n,A,hA,hb⟩:=detectorPlain_profile_uniform {(0,0)}
  refine ⟨n,A,hA,?_⟩
  intro reverse k hk σ hσ t h U hU x
  apply (SchwartzMap.norm_le_seminorm ℝ ((detectorPlain reverse k σ t).profile U hU h) x).trans
  simpa using hb reverse k hk σ hσ t h U hU

lemma errorConstant_height {α : Type*} (F : Finset α) (bshort A : ℝ) (b M : α→ℝ)
    (w : ℝ) (hw : 1≤w) :
    errorConstant F bshort (A*w) b M≤errorConstant F bshort A b M*w^2 := by
  unfold errorConstant
  have hh : 1+(128*max 1 bshort*(A*w))^2≤(1+(128*max 1 bshort*A)^2)*w^2 := by
    nlinarith [sq_nonneg (w-1)]
  calc
    _≤((1+(128*max 1 bshort*A)^2)*w^2)*∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      mul_le_mul_of_nonneg_right hh (Finset.prod_nonneg (fun _ _=>by positivity))
    _=_ := by ring

theorem allocated_natural_error_point {α : Type*} (F : Finset α) (b M : α→ℝ)
    (hM : ∀j∈F,0≤M j) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀T : Finset α,T⊆F →
      ∀reverse : Bool,∀k : ℕ,k≤2 → ∀σ∈Set.Icc (0:ℝ) 1,
      ∀t h U : ℝ,∀hU : 0<U,∀χ : Character,
      ∀pool : α→Finset (Ideal O),∀β : α→Ideal O→ℂ,∀P freq : α→ℝ,
      ∀X omega : ℝ,0<X → (∀j∈T,0<P j) →
      (∀j∈T,∀I∈pool j,Prime I) → (∀j∈T,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      ‖polynomial χ false ((detectorPlain reverse k σ t).profile U hU h) X 0 omega*
        ∏j∈T,naturalSlot χ (pool j) (heightCoefficient (β j) (freq j)) (P j)‖^2≤
      C*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n) := by
  obtain ⟨n,A,hA,hprofile⟩:=allocated_profile_supnorm
  refine ⟨n,errorConstant F (9/4) A b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT reverse k hk σ hσ t h U hU χ pool β P freq X omega hX hP hp hβ hs
  let w : ℝ:=(1+‖t‖+‖h‖)^n
  have hw : 1≤w:=one_le_pow₀ (by linarith [norm_nonneg t,norm_nonneg h] : (1:ℝ)≤1+‖t‖+‖h‖)
  have hh:=natural_remaining_sq_bound F T hT ((detectorPlain reverse k σ t).profile U hU h)
    (9/4) (A*w) b M (by positivity) hM (hprofile reverse k hk σ hσ t h U hU)
    (fun x hx=>(detectorPlain_profile_support reverse k σ t U hU h hx).2)
    χ pool (fun j=>heightCoefficient (β j) (freq j)) P X omega hX hP
    (by intro j hj I hi;rw [heightCoefficient_norm _ _ _ (hp j hj I hi).ne_zero];exact hβ j hj I hi)
    (by intro j hj I hi hn;exact hs j hj I hi (left_ne_zero_of_mul hn))
  apply hh.trans
  have hc:=mul_le_mul_of_nonneg_right (errorConstant_height F (9/4) A b M w hw)
    (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
  have hw2 : w^2=(1+‖t‖+‖h‖)^(2*n) := by
    dsimp only [w]
    rw [←pow_mul,Nat.mul_comm n 2]
  rw [hw2] at hc
  convert hc using 1 <;> ring

theorem allocated_natural_radial_error_mass {α : Type*} (F : Finset α) (b M : α→ℝ)
    (hM : ∀j∈F,0≤M j) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀T : Finset α,T⊆F →
      ∀reverse : Bool,∀k : ℕ,k≤2 → ∀σ∈Set.Icc (0:ℝ) 1,
      ∀t h U : ℝ,∀hU : 0<U,∀χ : O→Character,
      ∀pool : O→α→Finset (Ideal O),∀β : O→α→Ideal O→ℂ,∀freq : O→α→ℝ,
      ∀P : α→ℝ,∀omega : O→ℝ,∀X K : ℝ,∀Φ : 𝓢(ℝ,ℂ),
      0<X → (∀j∈T,0<P j) → 0<K →
      (∀z j,j∈T → ∀I∈pool z j,Prime I) →
      (∀z j,j∈T → ∀I∈pool z j,‖β z j I‖≤M j) →
      (∀z j,j∈T → ∀I∈pool z j,β z j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      let R:=fun z:O=>polynomial (χ z) false ((detectorPlain reverse k σ t).profile U hU h) X 0 (omega z)*
        ∏j∈T,naturalSlot (χ z) (pool z j) (heightCoefficient (β z j) (freq z j)) (P j)
      Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2) ∧
      (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)≤
        C*diagonalControl Φ*max 1 K*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n) ∧
      ∀E:Finset O,(∑z∈E,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)≤
        C*diagonalControl Φ*max 1 K*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n) := by
  obtain ⟨n,C,hC,hpoint⟩:=allocated_natural_error_point F b M hM
  refine ⟨n,C,hC,?_⟩
  intro T hT reverse k hk σ hσ t h U hU χ pool β freq P omega X K Φ hX hP hK hp hβ hs R
  let A:=C*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n)
  have hA : 0≤A:=by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC.le hX.le) (Finset.prod_nonneg (fun j hj=>(hP j hj).le))) (by positivity)
  have hr (z:O):‖R z‖^2≤A:=hpoint T hT reverse k hk σ hσ t h U hU (χ z)
    (pool z) (β z) P (freq z) X (omega z) hX hP (hp z) (hβ z) (hs z)
  have hsum:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right A)
  have hb:(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)≤
      C*diagonalControl Φ*max 1 K*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n):=by
    calc
      _≤∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*A:=hsum.tsum_le_tsum
        (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
        ((radial_norm_summable Φ K hK).mul_right A)
      _=(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*A:=tsum_mul_right
      _≤(diagonalControl Φ*max 1 K)*A:=
        mul_le_mul_of_nonneg_right (radial_weight_lattice_bound_all Φ K hK) hA
      _=_:=by dsimp [A];ring
  refine ⟨hsum,hb,?_⟩
  intro E
  exact (sum_le_hasSum E (fun z _=>mul_nonneg (norm_nonneg _) (sq_nonneg _)) hsum.hasSum).trans hb

theorem radialEnergy_le_absolute_mass (R : O→ℂ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hPhi : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hs : Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)) :
    CenteredMomentOriginalRadialComparison.radialEnergy R keep Φ K≤
      ∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
  let f:=fun z:O=>if keep z then ‖R z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hn (z:O):0≤f z:=by dsimp only [f];split_ifs;exact mul_nonneg (sq_nonneg _) (hPhi z);exact le_rfl
  have hb (z:O):f z≤‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
    dsimp only [f]
    split_ifs
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Complex.re_le_norm (Φ (‖eisEmbedding z‖^2/K))) (sq_nonneg ‖R z‖)
    · positivity
  exact (Summable.of_nonneg_of_le hn hb hs).tsum_le_tsum hb hs

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2240

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCancellation
Source SHA256: 302ba7a28bcfc5aec782d9e8f75848d21e8d28d4bfd46b32e5f8492366e7fff3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2241


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles CenteredMomentDetectorDictionary
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open ConcretePrimeRowBridge CenteredMomentHeckeVolume
local notation "O" => HeckeFamily.O

lemma detectorSchwartz_norm_zero_height (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    ‖detectorSchwartz reverse n σ t x‖=‖detectorSchwartz reverse n σ 0 x‖ := by
  rw [detectorSchwartz_apply,detectorSchwartz_apply]
  unfold twistProfile
  by_cases hw : orientedProfile reverse ((logProfile^[n]) positiveAnnular) x=0
  · simp only [hw,zero_mul]
  · have hx : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
      ((oriented_detector_log_support reverse n) hw).1
    simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.neg_re,
      HeckeDyadic.shift_re]

lemma detectorSchwartz_absolute :
    ∃A : ℝ,0<A ∧ ∀reverse : Bool,∀n : ℕ,n≤2 → ∀σ∈Set.Icc (0:ℝ) 1,∀t x : ℝ,
      ‖detectorSchwartz reverse n σ t x‖≤A := by
  obtain ⟨J,A,hA,hbound⟩:=detectorSchwartz_uniform {(0,0)}
  refine ⟨A,hA,?_⟩
  intro reverse n hn σ hσ t x
  rw [detectorSchwartz_norm_zero_height]
  apply (SchwartzMap.norm_le_seminorm ℝ (detectorSchwartz reverse n σ 0) x).trans
  simpa using hbound reverse n hn σ hσ 0

theorem detector_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η χ ψ : Character,(χ.modulus.absNorm:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ → ∀m A z : O,goodLambda∣m → (2:O)∣m →
      (∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        twistedIdealSum χ (detectorSchwartz r₁ j σ₁ t₁) h X₁*twistedIdealSum χ (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        twistedIdealSum χ (detectorSchwartz r₁ j σ₁ t₁) h Y₁*twistedIdealSum χ (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩:=detector_volumeControl_uniform ε B hε hB
  obtain ⟨A0,hA0,habs⟩:=detectorSchwartz_absolute
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hvolume⟩:=hJ Q
  refine ⟨4608*C*A0,by positivity,?_⟩
  intro Z hZ η χ ψ hχ hQψ hind m A z hml hm2 hrow r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E:=volumeControl Q χ (detectorNormProfile r₁ j σ₁ t₁ h)+
    volumeControl Q χ (detectorNormProfile r₂ k σ₂ t₂ h)
  let H:=1+‖t₁‖+‖t₂‖+‖h‖
  have hH : 0≤H:=by dsimp [H];positivity
  have hp₁ : (1+‖t₁‖+‖h‖)^J≤H^J := pow_le_pow_left₀ (by positivity) (by dsimp [H];linarith [abs_nonneg t₂]) J
  have hp₂ : (1+‖t₂‖+‖h‖)^J≤H^J := pow_le_pow_left₀ (by positivity) (by dsimp [H];linarith [abs_nonneg t₁]) J
  have hE : E≤2*C*Z^ε*H^J := by
    have h₁:=(hvolume Z hZ χ hχ r₁ j hj σ₁ hσ₁ t₁ h).trans
      (mul_le_mul_of_nonneg_left
        hp₁
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
    have h₂:=(hvolume Z hZ χ hχ r₂ k hk σ₂ hσ₂ t₂ h).trans
      (mul_le_mul_of_nonneg_left
        hp₂
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
    dsimp only [E]
    linarith
  have hraw:=actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
    (1/4) (9/4) (1/4) (9/4) A0 A0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hA0.le hA0.le (detectorSchwartz_support _ _ _ _) (detectorSchwartz_support _ _ _ _)
    ((detectorSchwartz r₁ j σ₁ t₁).smooth ⊤) ((detectorSchwartz r₂ k σ₂ t₂).smooth ⊤)
    (habs r₁ j hj σ₁ hσ₁ t₁) (habs r₂ k hk σ₂ hσ₂ t₂)
    h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hn:=CenteredMoment.normalized_centered_saving _ T L (128*((9/4)*A0+(9/4)*A0)) E hT hraw
  have hr : 0≤Real.sqrt T/L:=div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _≤4*E*(128*((9/4)*A0+(9/4)*A0))*(Real.sqrt T/L) := hn
    _≤4*(2*C*Z^ε*H^J)*(128*((9/4)*A0+(9/4)*A0))*(Real.sqrt T/L) := by
      gcongr
    _=_ := by dsimp [H];ring

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2241

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorSlots
Source SHA256: 8077be47cabb4a7b99e1e179da7ae3199a2625332e4c4206caebec122f6ed587
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2242


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile CenteredMomentHeckeVolume
local notation "O" => HeckeFamily.O

 theorem detector_row_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩:=detector_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩:=fixedInducingRow_controlled η Q m A z hm hA hz hml hm2 hex
  have hχnorm : (χ.modulus.absNorm:ℝ)≤Z^B :=
    (show (χ.modulus.absNorm:ℝ)≤rowConductorBound η m 1 (A*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A z hml hm2 hrow r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

theorem detector_slots_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀S : ι→Finset (Ideal O),∀β : ι→Ideal O→ℂ,∀p b M : ι→ℝ,
      (∀i,0<p i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀P∈S i,‖β i P‖≤M i) → (∀i,∀P∈S i,β i P≠0 → (P.absNorm:ℝ)≤b i*p i) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
        S β p h X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,p i)/L) := by
  obtain ⟨J,hJ⟩:=detector_row_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι inst Z hZ η m A z hm hA hz hml hm2 hcond hex S β p b M hp hb hM hβ hN
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) h‖≤(128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) h (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) h)
    (fun i=>128*b i*M i) p (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J) T L
    (by positivity) hT hL (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2242

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCapped
Source SHA256: 428990df3a2e1ee6249b102a286b637042fffd322730afe6b59630e5382a58e6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2243



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile CenteredMomentHeckeVolume
open CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O

theorem detector_capped_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_row_rectangle_uniform ε B hε hB
  obtain ⟨A0,hA0,habs⟩:=detectorSchwartz_absolute
  let D : ℝ:=2*(128*(9/4)*A0)*(128*(9/4)*A0)
  have hD : 0≤D:=by dsimp [D];positivity
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩:=hJ Q hQ
  refine ⟨C+D,by positivity,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : 0≤Z^ε:=Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    exact (hcancel Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hpow) (by positivity))
        (div_nonneg (Real.sqrt_nonneg _) hL.le))
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have ha:=normalized_rectangle_absolute η m A z
      (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
      (9/4) (9/4) A0 A0 (by norm_num) (by norm_num) hA0.le hA0.le
      (fun x hx=>(detectorSchwartz_support r₁ j σ₁ t₁ hx).2)
      (fun x hx=>(detectorSchwartz_support r₂ k σ₂ t₂ hx).2)
      (habs r₁ j hj σ₁ hσ₁ t₁) (habs r₂ k hk σ₂ hσ₂ t₂)
      h X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    calc
      D≤C+D:=le_add_of_nonneg_left hC.le
      _≤(C+D)*Z^ε:=le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
      _≤(C+D)*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J:=le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by linarith [norm_nonneg t₁,norm_nonneg t₂,norm_nonneg h]))

theorem detector_capped_slots_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀S : ι→Finset (Ideal O),∀β : ι→Ideal O→ℂ,∀p b M : ι→ℝ,
      (∀i,0<p i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀P∈S i,‖β i P‖≤M i) → (∀i,∀P∈S i,β i P≠0 → (P.absNorm:ℝ)≤b i*p i) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
        S β p h X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,p i)/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_capped_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι inst Z hZ η m A z hm hA hz hml hm2 hcond hex S β p b M hp hb hM hβ hN
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) h‖≤(128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) h (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) h)
    (fun i=>128*b i*M i) p (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J) T (max 1 L)
    (by positivity) hT (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2243

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorCapped
Source SHA256: 2fb1d04237e5a4e48b9afe589e43a42b842712962d55e57ed33ff353b11e60df
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2244



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorCapped
open HeckeFamily CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open ConcretePrimeRowBridge CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O

theorem actual_detector_allocated_capped (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂) X₁ X₂ Y₁ Y₂ T‖≤
      C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,hJ⟩:=detector_capped_slots_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (ι:=liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentAllocatedDetectorCapped

end

end OAI
end OAIOriginalModule2244

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocatedDetectorAmplitude
Source SHA256: fa9ce867620d3e61439f5ebbac5aeadc057e7527c5c0fd3fc323a7ea67bcfb13
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2245



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorAmplitude
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedDetectorCapped CenteredMomentDetectorDictionary
open ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def amplitude (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    allocatedRectangle s.η s.m s.A z s.t s.slots s.coefficient D a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def slotControl (s:Data ι):ℝ:=
  (∏i,s.M i)*(∏i,max 1 (128*max 0 (s.hi i)*s.M i))

omit [DecidableEq ι] in
lemma slotControl_nonneg (s:Data ι):0≤slotControl s:=by
  unfold slotControl
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>(zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _)))

lemma slot_product_bound (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    (∏i∈frozenIndices D a,s.M i)*(∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i)≤slotControl s:=by
  have hf:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hl:(∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i)≤∏i,max 1 (128*max 0 (s.hi i)*s.M i):=by
    have he := Finset.prod_coe_sort (liveIndices D a) (fun i:ι=>128*max 0 (s.hi i)*s.M i)
    rw [he]
    apply (Finset.prod_le_prod₀ (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
      (zero_le_one.trans (s.M_ge_one i))) (fun i _=>le_max_right 1 _)).trans
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _ _=>le_max_left _ _)
  exact mul_le_mul hf hl (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))

omit [DecidableEq ι] in
lemma coefficient_support (s:Data ι) (i:ι) (I:Ideal O) (hI:s.coefficient i I≠0):
    (Ideal.absNorm I:ℝ)≤max 0 (s.hi i)*s.P i:=by
  have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=right_ne_zero_of_mul hI
  exact (div_le_iff₀ (s.P_pos i)).mp ((s.support i hw).2.trans (le_max_right _ _))

theorem actual_allocated_amplitude (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),1<Z → (∀i,1≤s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ r:ℝ,s.W₁=detectorSchwartz r₁ j σ₁ t₁ → s.W₂=detectorSchwartz r₂ k σ₂ t₂ →
      Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,hJ⟩:=actual_detector_allocated_capped ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ s Z hZ hP z hm hA hz hml hm2 hcond hex D a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap ι Z hZ s.η s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end SevenEighths.CenteredMomentAllocatedDetectorAmplitude

end

end OAI
end OAIOriginalModule2245

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
Source SHA256: 6760a1977d0b627cf843aa1603f6e5c2bcaa5ee36685447f2278949393e3ef2f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2246



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

structure Tests where
  reverse : Fin 2→Bool
  index : Fin 2→ℕ
  index_le : ∀j,index j≤2
  sigma : Fin 2→ℝ
  sigma_mem : ∀j,sigma j∈Set.Icc (0:ℝ) 1
  height : Fin 2→ℝ

def Tests.profile (p:Tests) (i:Fin 2):𝓢(ℝ,ℂ):=
  detectorSchwartz (p.reverse i) (p.index i) (p.sigma i) (p.height i)

def Tests.heightWeight (p:Tests) (t:ℝ):ℝ:=1+‖p.height 0‖+‖p.height 1‖+‖t‖

def volume {ι:Type u} [Fintype ι] (s:Data ι):ℝ:=s.X₁*s.X₂*∏i,s.P i

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

def Admissible {ι:Type u} [Fintype ι] (s:Data ι) (p:Tests)
    (Q:Ideal O) (Z B r:ℝ) (z:O):Prop:=
  (∀i,1≤s.P i) ∧ s.m≠0 ∧ s.A≠0 ∧ z≠0 ∧ goodLambda∣s.m ∧ (2:O)∣s.m ∧
  (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B ∧
  CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z ∧
  s.W₁=p.profile 0 ∧ s.W₂=p.profile 1 ∧
  Z^r≤s.X₁ ∧ Z^r≤s.X₂ ∧ Z^r≤s.Y₁ ∧ Z^r≤s.Y₂

lemma norm_le_of_squared (x:ℂ) (H V d M:ℝ) (hH:0≤H) (hV:0≤V) (hd:0<d) (hM:0<M)
    (hb:‖x‖^2≤H^2*V/(d^2*M^2)):
    ‖x‖≤H*Real.sqrt V/(d*M):=by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  convert hb using 1
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hV]

lemma reduction_cap_identity {ι κ:Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Data ι) (v:Data κ) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))) (Z r:ℝ) (hZ:1<Z):
    1/(formalReductionFactor D a s.P*formalReductionFactor D b v.P*
      Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))=
      exceptionalWeight s.toSource v.toSource D a b Z r:=by
  have hz:=zero_lt_one.trans hZ
  unfold exceptionalWeight
  rw [show -Real.logb Z (formalReductionFactor D a s.P)-Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0=
      -(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P)+
        max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) by ring,
    Real.rpow_neg hz.le,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' (s.reduction_pos D a),Real.rpow_logb hz hZ.ne' (v.reduction_pos D b)]
  exact one_div _

theorem actual_paired_amplitude (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B r z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,hJ⟩:=actual_allocated_amplitude ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Tests)
      (hs:Admissible s p Q Z B r z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*Z^ε*p.heightWeight s.t^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound α s Z hZ hP z hm hA hz hml hm2 hcond hex D a
        (p.reverse 0) (p.reverse 1) (p.index 0) (p.index 1) (p.index_le 0) (p.index_le 1)
        (p.sigma 0) (p.sigma_mem 0) (p.sigma 1) (p.sigma_mem 1)
        (p.height 0) (p.height 1) r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hl:=hpoint ι s p hs a
  have hr:=hpoint κ v q hv b
  have hcap:1≤Z^(max (r-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*Z^ε*q.heightWeight v.t^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end OAIOriginalModule2246

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalSourceShell
Source SHA256: ad25aeeb74a6297a25082bb6e668ac0349beb550198a4c08cbd3440c1db3b872
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2247


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalSourceShell
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):ℝ:=
  p.heightWeight s.t^J*q.heightWeight v.t^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

lemma profileMass_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):0≤profileMass s v p q J:=by
  unfold profileMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
    (slotControl_nonneg s)) (slotControl_nonneg v)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem actual_paired_source_shell (ε δ B:ℝ) (hε:0<ε) (hδ:0<δ) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests)(Z r:ℝ),1<Z →
      ∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T:ℝ,1≤T →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*(2*T)^(2*δ)*Z^(2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_amplitude ε B hε hB
  obtain ⟨Cs,hCs,hshell⟩:=uniform_subset_shell (ι:=ι) δ hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  intro I L s v p q Z r hZ rows hs hv Ds hD T hT hlo hhi
  have hz:0<Z:=zero_lt_one.trans hZ
  let A:=Ca*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (mul_nonneg hCa.le (Real.rpow_nonneg hz.le _)) (profileMass_nonneg s v p q J)
  have hp (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        (rows.card:ℝ)*A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
    calc
      _≤∑z∈rows,A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r hZ z (hs z hzrow) (hv z hzrow) D a b).trans_eq (by
          dsimp only [A,profileMass]
          ring)
      _=_:=by simp; ring
  have hsum:=hshell I L s.toSource v.toSource Ds hD T Z r hT hZ hlo hhi
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        (rows.card:ℝ)*A*exceptionalWeight s.toSource v.toSource D a b Z r:=
      Finset.sum_le_sum (fun D _=>Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hp D a b)))
    _=(rows.card:ℝ)*A*(∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        exceptionalWeight s.toSource v.toSource D a b Z r):=by simp only [Finset.mul_sum]
    _≤(rows.card:ℝ)*A*(Cs*(2*T)^(2*δ)*Z^(v.toSource.allowance Z-r)):=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) hA)
    _=_:=by
      rw [show 2*ε+v.toSource.allowance Z-r=2*ε+(v.toSource.allowance Z-r) by ring,Real.rpow_add hz]
      dsimp only [A]
      ring

end SevenEighths.CenteredMomentExceptionalSourceShell

end

end OAI
end OAIOriginalModule2247

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalCanonicalShell
Source SHA256: d41654fca0d4966c5077230dd119998c5515a594684ef9ebd03c8a1a9c08d47f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2248



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalCanonicalShell
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_canonical_source_shell (ε δ B:ℝ) (hε:0<ε) (hδ:0<δ) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃C:ℝ,0<C ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests)(Z r:ℝ),1<Z →
      ∀(η:Character)(χ:RayFourExpansion.RayCharacter)(C₀ D₀:Ideal O)(_hC₀:Supported C₀)
        (U:Finset (CommonIndex C₀ D₀)),IsCoprime Q C₀ → idealCoeff η C₀≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C₀ D₀*nonunitFrequencyGenerator C₀ D₀ U) z) →
      (∀z∈rows,Admissible s p Q Z B r z) → (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T:ℝ,1≤T →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*(2*T)^(2*δ)*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
            (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
            2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_source_shell (ι:=ι) ε δ B hε hδ hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ0
  refine ⟨C,hC,?_⟩
  intro I L s v p q Z r hZ η χ C₀ D₀ hC₀ U hcop hη m hm hml hm2 rows hn hex hs hv
    Cr M hCr hN Ds hD T hT hlo hhi
  have hc:=actual_canonical_exceptional_count η χ C₀ D₀ hC₀ U Q hQ0 hQ hQ72 hcop hη
    m hm hml hm2 rows hn hex Z Cr M hZ hCr hN
  apply (hbound I L s v p q Z r hZ rows hs hv Ds hD T hT hlo hhi).trans
  have hz:=zero_lt_one.trans hZ
  calc
    _≤C*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6))*
        (2*T)^(2*δ)*Z^(2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
      apply mul_le_mul_of_nonneg_right _ (profileMass_nonneg s v p q J)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
      exact mul_le_mul_of_nonneg_left hc hC.le
    _=_:=by
      rw [show (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          2*ε+v.toSource.allowance Z-r=
          (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          (2*ε+v.toSource.allowance Z-r) by ring,Real.rpow_add hz]
      ring

end SevenEighths.CenteredMomentExceptionalCanonicalShell

end

end OAI
end OAIOriginalModule2248

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeSource
Source SHA256: 293cfef7f9b8786691a164d981e52a9842753b3abda4ca18a593518cc6466b9a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2249



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalWholeSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentWholeDivisorShell
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalSourceShell
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma weight_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Source α)(v:Source κ)(D:Ideal O)
    (a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (Z r:ℝ)(hZ:0≤Z):0≤exceptionalWeight s v D a b Z r:=Real.rpow_nonneg hZ _

 theorem whole_weight_bound (lo hi:ι→ℝ)(B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Source I)(v:Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ∀r:ℝ,(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r):=by
  obtain ⟨Cs,hCs,hshell⟩:=exceptional_shell_subpower lo hi B (δ/2) hB (by linarith)
  obtain ⟨Cn,hCn,hcard⟩:=selected_card_subpower B (δ/2) hB (by linarith)
  refine ⟨Cn*Cs,mul_pos hCn hCs,?_⟩
  filter_upwards [hcard] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v hlo hhi Ds hDs r
  rw [sum_norm_moebius_shells]
  have hz:=zero_lt_one.trans hZ.1
  have hs (n:ℤ)(hn:n∈selectedShells Ds):
      (∑D∈shell Ds n,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤Cs*Z^(δ/2-r):=by
    have ht:=selected_scale_bounds Ds (Z^B) hDs n hn
    apply (Finset.sum_le_sum (fun D hD=>mul_le_of_le_one_left
      (Finset.sum_nonneg (fun a _=>Finset.sum_nonneg (fun b _=>weight_nonneg s v D a b Z r hz.le)))
      (moebius_norm_le_one D))).trans
    exact hshell I L s v hlo hhi (shell Ds n)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.1) (dyadicScale n) Z r ht.1 hZ.1 ht.2
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.1)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.2)
  calc
    _≤∑n∈selectedShells Ds,Cs*Z^(δ/2-r):=Finset.sum_le_sum hs
    _=((selectedShells Ds).card:ℝ)*(Cs*Z^(δ/2-r)):=by simp
    _≤(Cn*Z^(δ/2))*(Cs*Z^(δ/2-r)):=
      mul_le_mul_of_nonneg_right (hZ.2 Ds hDs) (mul_nonneg hCs.le (Real.rpow_nonneg hz.le _))
    _=(Cn*Cs)*Z^(δ-r):=by
      rw [show δ-r=δ/2+(δ/2-r) by ring,Real.rpow_add hz]
      ring

theorem actual_whole_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_amplitude ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z r:=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z r):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-r)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs r) hA
    _=_:=by
      rw [show 2*ε+δ-r=2*ε+(δ-r) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

end SevenEighths.CenteredMomentExceptionalWholeSource

end

end OAI
end OAIOriginalModule2249

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalMaskedSource
Source SHA256: 53b0f7e4dc3cc14bfbf1d6b9c148df2fe80f24f2367aa957fb0afa8ab126575c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2250



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalMaskedSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentEligibleEnergy
open CenteredMomentDivisorRowEnergy CenteredMomentActiveAllocation
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalWholeSource
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSourceRow CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
universe u
variable {ι κ:Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def maskedAmplitude (s:Data ι)(D:Ideal O)(z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

theorem maskedAmplitude_eq (s:Data ι)(D:Ideal O)(hD:Squarefree D)(z:O):
    maskedAmplitude s D z=∑a∈s.toSource.active D,amplitude s D a z:=by
  unfold maskedAmplitude
  rw [masked_eq_active_allocations s.η s.m s.A z s.t s.slots s.coefficient D hD
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos,Finset.mul_sum]
  rfl

theorem source_polynomial_eq (s:Data ι)(S₁ S₂:Finset (Ideal O))(R D B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R)(hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁)(hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁)(hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hc₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁)(hc₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂)(z:O):
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      rowPolynomial Finset.univ (sourceGenerator (finiteColumns (tuplePool s.slots S₁ S₂)))
        (fun I: supportedColumns (finiteColumns (tuplePool s.slots S₁ S₂))=>
          finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
            (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ D) I*
              heightCoeff s.η s.t I) z=maskedAmplitude s D z:=by
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    s.slots S₁ S₂ R D s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hc₁ hc₂]
  simp only [maskedAmplitude,hm,hA,hX₁,hX₂,hY₁,hY₂]
  rfl

theorem paired_masked_le (s:Data ι)(v:Data κ)(D:Ideal O)(hD:Squarefree D)(rows:Finset O):
    (∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  calc
    _≤∑z∈rows,(∑a∈s.toSource.active D,‖amplitude s D a z‖)*
        (∑b∈v.toSource.active D,‖amplitude v D b z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      rw [maskedAmplitude_eq s D hD,maskedAmplitude_eq v D hD]
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
        (Finset.sum_nonneg (fun a _=>norm_nonneg _))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=s.toSource.active D)]
      exact Finset.sum_comm

theorem whole_masked_le (s:Data ι)(v:Data κ)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑D∈Ds,‖(moebius D:ℂ)‖*∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  apply Finset.sum_le_sum
  intro D hD
  by_cases hμ:(moebius D:ℂ)=0
  · simp [hμ]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply paired_masked_le s v D
    exact CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero D hμ

theorem actual_masked_whole_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_whole_source lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rows hs hv Ds hDs)

end SevenEighths.CenteredMomentExceptionalMaskedSource

end

end OAI
end OAIOriginalModule2250

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
Source SHA256: 0c9e65f319dad87a5fc9afc3aab699774e834aae8f810dca371fbbd3292a63ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2251



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedDomain
open CenteredMomentAmplificationLiveMask CenteredMomentExceptionalMaskedSource
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def sourceColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then β (C*I) else 0)*heightCoeff s.η s.t I) z

def liveColumn (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):ℂ:=
  let S:=liveBox s.pools B.val (alloc_ne s C B)
  rowPolynomial Finset.univ (sourceGenerator (finiteColumns S))
    (fun I:supportedColumns (finiteColumns S)=>finiteColumnCoefficient S
      (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
        heightCoeff s.η s.t I) z

omit [DecidableEq ι] in
theorem source_column_allocation (s:Input ι)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(hseed:seed∣C)(z:O):
    sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P*
        liveColumn s C R L B z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let b:=fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P
  let d:=fun (B:actualAllocations s.pools C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
      (liveProfile B.val C R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
      ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff s.η s.t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
        finiteColumnCoefficient (Fintype.piFinset s.pools)
          (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
          else 0)*heightCoeff s.η s.t I=∑B,b B*d B I:=by
    have hc:=original_source_punctured_column s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
      C R seed I hC.1 (Finset.mem_filter.mp I.property).2.1 hseed
      s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  change rowPolynomial Finset.univ (sourceGenerator Q) _ z=_
  rw [funext he,rowPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_rowPolynomial s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
    B.val (alloc_ne s C B) C R hC (Finset.mem_filter.mp B.property).1
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I) z
  change rowPolynomial Finset.univ (sourceGenerator Q) (d B) z=_ at hh
  rw [hh]
  unfold liveColumn
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem live_column_rectangle (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):
    liveColumn s C R L B z=
      CenteredMomentDivisorRowEnergy.maskedRectangle
        (commonData s C R B).η (commonData s C R B).m (commonData s C R B).A z
        (commonData s C R B).t (commonData s C R B).slots (commonData s C R B).coefficient L
        (commonData s C R B).W₁ (commonData s C R B).W₂
        (commonData s C R B).X₁ (commonData s C R B).X₂
        (commonData s C R B).Y₁ (commonData s C R B).Y₂:=by
  unfold liveColumn
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hc₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hc₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hc₁ hc₂
  have he:=CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    (commonData s C R B).slots
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (commonData s C R B).ν (commonData s C R B).W (commonData s C R B).P
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) hc₁ hc₂
  rw [height_source_row]
  convert he using 1 <;> simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  all_goals rfl

end SevenEighths.CenteredMomentCommonLinearSource

end

end OAI
end OAIOriginalModule2251

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates
Source SHA256: b87d2abdd3e763c615aadca9a14e46786682ce90bc5d75155b085247aad04a57
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2252



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalGates
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFixedRowMask CenteredExceptionalProfile CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coordinate_dvd (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    B.val j∣C:=by
  exact (Finset.dvd_prod_of_mem B.val (Finset.mem_univ j)).trans
    (dvd_of_eq (Finset.mem_filter.mp B.property).2)

omit [DecidableEq ι] in
theorem coordinate_norm_le (s:Input ι)(C:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    (Ideal.absNorm (B.val j):ℝ)≤Ideal.absNorm C:=by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm (coordinate_dvd s C B j))

omit [DecidableEq ι] in
theorem extracted_lower (s:Input ι)(C:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C)
    (j:ι⊕Fin 2)(Z r X:ℝ)(hZ:1<Z)(hX:Z^r≤X):
    Z^(r-Real.logb Z (Ideal.absNorm C:ℝ))≤X/Ideal.absNorm (B.val j):=by
  have hz:=zero_lt_one.trans hZ
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hN]
  exact div_le_div₀ ((Real.rpow_nonneg hz.le r).trans hX) hX (alloc_norm_pos s C B j)
    (coordinate_norm_le s C hC B j)

omit [DecidableEq ι] in
theorem common_mask_inducing (s:Input ι)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(z:O)(hz:z≠0):
    FixedInducingRow (commonData s C R B).η Q (commonData s C R B).m
      (commonData s C R B).A z ↔ FixedInducingRow s.η Q fixedBadMask 1 z:=by
  exact fixedInducingRow_mul_mask_iff s.η Q fixedBadMask (idealGenerator (R*C)) 1 z
    fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC)) one_ne_zero hz
    (dvd_mul_right _ _) (dvd_mul_left _ _)

omit [DecidableEq ι] in
theorem common_conductor (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)(z:O):
    HeckeRowClosure.rowConductorBound (commonData s C R B).η (commonData s C R B).m 1
      ((commonData s C R B).A*z)=
      s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:=by
  simp only [commonData,HeckeRowClosure.rowConductorBound,one_mul,
    ←Ideal.span_singleton_mul_span_singleton,span_idealGenerator,map_mul,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow]
  ring

omit [DecidableEq ι] in
theorem common_admissible (s:Input ι)(p:Tests)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    Admissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂

end SevenEighths.CenteredMomentCommonExceptionalGates

end

end OAI
end OAIOriginalModule2252

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonLinearNormalization
Source SHA256: a5c6a0a75ce25269f36738583fba75278958e3153c3bdff3dbc1bf3cab805bda
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2253



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearNormalization
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P

omit [DecidableEq ι] in
theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring

theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring

omit [DecidableEq ι] in
theorem commonScalar_sq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P:=
  CenteredMomentDivisorRawEnergy.normalized_norm_sq _
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) _

omit [DecidableEq ι] in
theorem commonScalar_sq_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2≤
      ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ):=by
  rw [commonScalar_sq]
  exact frozen_normalized_cost B.val (alloc_ne s C B) C R hC
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound s.W_bound
    s.M_ge_one s.lower s.upper s.lower_pos s.slot_support

end SevenEighths.CenteredMomentCommonLinearNormalization

end

end OAI
end OAIOriginalModule2253

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
Source SHA256: e54bc6bc5b7da6b0cbbca43ca58a43f7e7ddb5df76d9c2e3bf135b6cfd844e55
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2254


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonPairedSource
open HeckeFamily UniqueFactorizationMonoid CanonicalQuadraticSieve
open CenteredMomentCommonLinearSource CenteredMomentCommonLinearNormalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def normalizedColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z

theorem norm_column (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    ‖normalizedColumn s C hC R seed L z‖≤
      ∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖:=by
  unfold normalizedColumn
  rw [source_normalized s C hC R seed L hseed]
  simpa only [norm_mul] using norm_sum_le
    (Finset.univ:Finset (actualAllocations s.pools C))
    (fun B=>commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)

theorem paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed L:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(rows:Finset O):
    (∑z∈rows,‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑z∈rows,(∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖)*
      (∑E:actualAllocations v.pools D,‖commonScalar v D R E‖*
        ‖maskedAmplitude (commonData v D R E) L z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (norm_column s C hC R seed L hsC z)
        (norm_column v D hD R seed L hsD z) (norm_nonneg _)
        (Finset.sum_nonneg (fun B _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=Finset.univ)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro z hz
      ring

theorem whole_paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
            ‖maskedAmplitude (commonData s C R B) L z‖*
              ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑L∈Ds,‖(moebius L:ℂ)‖*
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=
      Finset.sum_le_sum (fun L hL=>mul_le_mul_of_nonneg_left
        (paired_columns s v C D hC hD R seed L hsC hsD rows) (norm_nonneg _))
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro L hL
      apply Finset.sum_congr rfl
      intro z hz
      ring

end SevenEighths.CenteredMomentCommonPairedSource

end

end OAI
end OAIOriginalModule2254

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCost
Source SHA256: b90e4890e8d9eb6c6f2ab0f5260faee9d0d2d9a9eac453e602563eec64a646e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2255


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalCost
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentCommonRawCost CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentAllocationCost CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def frozenProfile (s:Input ι):ℝ:=(∏i,s.M i)*(max 1 s.upper)^Fintype.card ι

omit [DecidableEq ι] in
lemma frozenProfile_nonneg (s:Input ι):0≤frozenProfile s:=by
  unfold frozenProfile
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

omit [DecidableEq ι] in
theorem scalar_volume_exact (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖*Real.sqrt (volume s.toData)/rawReduction B.val s.P:=by
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  rw [commonScalar,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),hs]
  have hsq:=Real.sq_sqrt hr.le
  have hn:Real.sqrt (rawReduction B.val s.P)≠0:=(Real.sqrt_pos.mpr hr).ne'
  field_simp
  rw [hsq]
  ring

omit [DecidableEq ι] in
theorem scalar_volume_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))≤
      frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ):=by
  rw [scalar_volume_exact]
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
  · rw [hz,norm_zero,zero_mul,zero_div]
    exact div_nonneg (mul_nonneg (frozenProfile_nonneg s) (Real.sqrt_nonneg _)) hN.le
  · have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R
      (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.P_pos s.lower s.upper
      s.lower_pos s.slot_support hz).2
    have hc:=frozenCoefficient_norm B.val C R s.ν s.W s.P s.M s.ν_bound s.W_bound s.M_ge_one
    have hi:(1:ℝ)/rawReduction B.val s.P≤(max 1 s.upper)^Fintype.card ι/(Ideal.absNorm C:ℝ):=
      (div_le_div_iff₀ hr hN).mpr (by simpa using hn)
    calc
      _≤((∏i,s.M i)*Real.sqrt (volume s.toData))/rawReduction B.val s.P:=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) hr.le
      _=((∏i,s.M i)*Real.sqrt (volume s.toData))*(1/rawReduction B.val s.P):=by ring
      _≤((∏i,s.M i)*Real.sqrt (volume s.toData))*
          ((max 1 s.upper)^Fintype.card ι/(Ideal.absNorm C:ℝ)):=
        mul_le_mul_of_nonneg_left hi (mul_nonneg
          (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) (Real.sqrt_nonneg _))
      _=_:=by unfold frozenProfile;ring

omit [DecidableEq ι] in
theorem common_slotControl (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    slotControl (commonData s C R B)≤slotControl s.toData:=by
  unfold slotControl
  change (∏i:liveIndices B.val,s.M i.val)*
    (∏i:liveIndices B.val,max 1 (128*max 0 (s.hi i.val)*s.M i.val))≤_
  rw [Finset.prod_coe_sort (liveIndices B.val) s.M,
    Finset.prod_coe_sort (liveIndices B.val) (fun i:ι=>max 1 (128*max 0 (s.hi i)*s.M i))]
  apply mul_le_mul
  · exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  · exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _ _=>le_max_left _ _)
  · exact Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _))
  · exact Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))

end SevenEighths.CenteredMomentCommonExceptionalCost

end

end OAI
end OAIOriginalModule2255

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalMass
Source SHA256: c3033064945b9fba1394d955b95162dbc6d98c2e96a2002069eacace56c3e656
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2256


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalMass
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonExceptionalCost CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentAllocatedDetectorAmplitude
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma scalar_profile_volume (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*slotControl (commonData s C R B)*Real.sqrt (volume (commonData s C R B))≤
      slotControl s.toData*frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ):=by
  calc
    _=slotControl (commonData s C R B)*
        (‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))):=by ring
    _≤slotControl s.toData*(frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ)):=
      mul_le_mul (common_slotControl s C R B) (scalar_volume_bound s C R hC B)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (slotControl_nonneg s.toData)
    _=_:=by ring

lemma common_pair_profile_bound (s v:Input ι)(C D R:Ideal O)(hC:C≠0)(hD:D≠0)
    (B:actualAllocations s.pools C)(E:actualAllocations v.pools D)(p q:Tests)(J:ℕ):
    (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
      profileMass (commonData s C R B) (commonData v D R E) p q J≤
        profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm D):=by
  have hs:=scalar_profile_volume s C R hC B
  have hv:=scalar_profile_volume v D R hD E
  have hprod:=mul_le_mul hs hv
    (mul_nonneg (mul_nonneg (norm_nonneg _) (slotControl_nonneg _)) (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg (slotControl_nonneg _) (frozenProfile_nonneg _))
      (Real.sqrt_nonneg _)) (Nat.cast_nonneg _))
  have hh:=mul_le_mul_of_nonneg_left hprod
    (show 0≤p.heightWeight s.t^J*q.heightWeight v.t^J by dsimp [Tests.heightWeight];positivity)
  convert hh using 1 <;> dsimp only [profileMass,commonData] <;> ring

theorem common_profile_mass (δ:ℝ)(hδ:0<δ):
    ∃K:ℝ,0<K ∧ ∀(s v:Input ι)(C D R:Ideal O),C≠0 → D≠0 → ∀(p q:Tests)(J:ℕ),
      (∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          profileMass (commonData s C R B) (commonData v D R E) p q J)≤
        K*((Ideal.absNorm C:ℝ)*Ideal.absNorm D)^δ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((Ideal.absNorm C:ℝ)*Ideal.absNorm D)):=by
  obtain ⟨K,hK,hcard⟩:=actualAllocations_small_power (ι:=ι⊕Fin 2) δ hδ
  refine ⟨K^2,sq_pos_of_pos hK,?_⟩
  intro s v C D R hC hD p q J
  let A:=profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
    ((Ideal.absNorm C:ℝ)*Ideal.absNorm D)
  have hA:0≤A:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg _ _ _ _ _)
    (frozenProfile_nonneg _)) (frozenProfile_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _≤∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,A:=
      Finset.sum_le_sum (fun B _=>Finset.sum_le_sum (fun E _=>common_pair_profile_bound s v C D R hC hD B E p q J))
    _=((actualAllocations s.pools C).card:ℝ)*((actualAllocations v.pools D).card:ℝ)*A:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
    _≤((K*(Ideal.absNorm C:ℝ)^δ)*(K*(Ideal.absNorm D:ℝ)^δ))*A:=
      mul_le_mul_of_nonneg_right (mul_le_mul (hcard s.pools C hC) (hcard v.pools D hD)
        (Nat.cast_nonneg _) (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))) hA
    _=_:=by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      dsimp only [A]
      ring

end SevenEighths.CenteredMomentCommonExceptionalMass

end

end OAI
end OAIOriginalModule2256

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonSectorColumn
Source SHA256: 228345d816415ee9aa49b3575692229a03b1d63acc6b47e0806b60184e010a61
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2257




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorColumn
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentSecondMaskedWindow
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open RayFourExpansion ActualEisensteinCubic CenteredMomentSourceRow CompletedGauss
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_sector_column (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ) z=
      sourceColumn (withHeight s τ t) C hC R seed L z:=by
  dsimp only
  rw [funext (masked_divisor_coefficient η τ χ A C hC hτ _ _ L t)]
  apply (sector_rowPolynomial (finiteColumns (Fintype.piFinset s.pools))
    (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
      else 0)*heightCoeff τ t I) C hC z).trans
  unfold sourceColumn
  dsimp only [withHeight,Input.pools]
  apply congrArg (fun c=>rowPolynomial Finset.univ
    (sourceGenerator (residualPool C hC.1 (finiteColumns (Fintype.piFinset (Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)))))) c z)
  funext I
  change (if IsCoprime C (I:Ideal O) then (if L∣(I:Ideal O) then _ else 0)*heightCoeff τ t I else 0)=
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then _ else 0)*heightCoeff τ t I
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentCommonSectorColumn

end

end OAI
end OAIOriginalModule2257

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
Source SHA256: 30a8f655a64f330e71c5838c8c7d077cfe9f499fbaf4263987b348a8d73d65df
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2258




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentCommonWindowColumn
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def columns (s:Input ι)(C:Ideal O)(hC:Supported C):Finset (Ideal O):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))

def coefficient (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (I:supportedColumns (columns s C hC)):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)

def windowColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

omit [DecidableEq ι] in
theorem coefficient_polynomial (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl

theorem sourceGenerator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

omit [DecidableEq ι] in
theorem whole_window_pair (s v:Input ι)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(Ds:Finset (Ideal O))(μ:Ideal O→ℂ)(rows:Finset O)
    (η τ:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u w:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖normalizedColumn (withHeight s η (t₁+2*Real.pi*(u-θ₁))) C hC R seed L z‖*
      ‖normalizedColumn (withHeight v τ (t₂+2*Real.pi*(w-θ₂))) D hD R seed L z‖)≤
        E*(1+‖u‖)^J₁*(1+‖w‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖windowColumn s C hC R seed L η t₁ θ₁ X V₁ z‖*
      ‖windowColumn v D hD R seed L τ t₂ θ₂ Y V₂ z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫w:ℝ,(1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖):=by
  have hh:=whole_plain_window_pair Ds μ rows Finset.univ Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator (columns v D hD))
    (sourceGenerator_supported _) (sourceGenerator_supported _)
    (coefficient s C hC R seed) (coefficient v D hD R seed) η τ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [sourceGenerator_span,windowColumn] using hh
  · intro u w
    simpa only [sourceGenerator_span,coefficient_polynomial] using hpair u w

end SevenEighths.CenteredMomentCommonWindowColumn

end

end OAI
end OAIOriginalModule2258

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
Source SHA256: 0e8a2a4a392e4cb5ea04583944921ab76559460ca4bb875deb8c608a37d22965
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2259


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentExceptionalAsymmetricSource
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalWholeSource
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_paired_asymmetric (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r rRight:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,hJ⟩:=actual_allocated_amplitude ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Tests)(r0:ℝ)
      (hs:Admissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*Z^ε*p.heightWeight s.t^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound α s Z hZ hP z hm hA hz hml hm2 hcond hex D a
        (p.reverse 0) (p.reverse 1) (p.index 0) (p.index 1) (p.index_le 0) (p.index_le 1)
        (p.sigma 0) (p.sigma_mem 0) (p.sigma 1) (p.sigma_mem 1)
        (p.height 0) (p.height 1) r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hl:=hpoint ι s p r hs a
  have hr:=hpoint κ v q rRight hv b
  have hcap:1≤Z^(max (rRight-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*Z^ε*q.heightWeight v.t^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

lemma reduction_ge_one {α:Type u} [Fintype α] [DecidableEq α]
    (s:Data α)(hP:∀i,1≤s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):1≤formalReductionFactor D a s.P:=by
  have hn (j:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hn 0) (hn 1))
    (Finset.one_le_prod₀ (fun i _=>hP i))

lemma raw_cap_weight {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(hP:∀i,1≤s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))(Z r:ℝ)(hZ:1<Z):
    exceptionalWeight s.toSource v.toSource D a b Z r=
      exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  have hd:0≤Real.logb Z (formalReductionFactor D a s.P):=
    Real.logb_nonneg hZ (reduction_ge_one s hP D a)
  unfold exceptionalWeight
  congr 2
  by_cases hr:0≤r
  · rw [max_eq_left hr]
  · have h0:r≤0:=le_of_not_ge hr
    rw [max_eq_right h0,max_eq_right (by linarith:r-Real.logb Z (formalReductionFactor D a s.P)≤0),
      max_eq_right (by linarith:0-Real.logb Z (formalReductionFactor D a s.P)≤0)]

theorem actual_paired_capped (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(α κ:Type u) [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ],
      ∀(s:Data α)(v:Data κ)(p q:Tests)(Z r rRight:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  obtain ⟨J,hJ⟩:=actual_paired_asymmetric ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro α κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  rw [←raw_cap_weight s v hs.1 D a b Z r hZ]
  exact hbound α κ s v p q Z r rRight hZ z hs hv D a b

theorem actual_whole_asymmetric (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_capped ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r rRight hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-max r 0)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs (max r 0)) hA
    _=_:=by
      rw [show 2*ε+δ-max r 0=2*ε+(δ-max r 0) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

theorem actual_masked_asymmetric (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_whole_asymmetric lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rRight rows hs hv Ds hDs)

end SevenEighths.CenteredMomentExceptionalAsymmetricSource

end

end OAI
end OAIOriginalModule2259

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource
Source SHA256: 95bbe1eaae8717c970c83b1b92c1d770776096c658f72b029e6c8307a934dee6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2260




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_exceptional (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)):=by
  obtain ⟨J,hJ⟩:=actual_masked_asymmetric lo hi ε δ B Lbound hε hδ hB hL
  obtain ⟨Km,hKm,hmass⟩:=common_profile_mass (ι:=ι) θ hθ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ka,hKa,hbound⟩:=hJ Q hQ
  refine ⟨Ka*Km,mul_pos hKa hKm,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let H:=Ka*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hH:0≤H:=by dsimp [H];positivity
  have hb (c:actualAllocations s.pools C)(d:actualAllocations v.pools D):
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude (commonData s C R c) L z‖*
          ‖maskedAmplitude (commonData v D R d) L z‖)≤
        H*profileMass (commonData s C R c) (commonData v D R d) p q J:=by
    apply hZ.2 _ _ (commonData s C R c) (commonData v D R d) p q
      (fun i=>hlo i.val) (fun i=>hhi i.val)
      (rLeft-Real.logb Z (C.absNorm:ℝ)) (rRight-Real.logb Z (D.absNorm:ℝ)) rows
    · intro z hz
      exact common_admissible s p C R Q hC.1 hR c Z B rLeft hZ.1 z (hn z hz) hsP
        (hsEx z hz) (hsCond z hz) hsW₁ hsW₂ hsX₁ hsX₂ hsY₁ hsY₂
    · intro z hz
      exact common_admissible v q D R Q hD.1 hR d Z B rRight hZ.1 z (hn z hz) hvP
        (hvEx z hz) (hvCond z hz) hvW₁ hvW₂ hvX₁ hvX₂ hvY₁ hvY₂
    · exact hDs
  apply (whole_paired_columns s v C D hC hD R seed hsC hsD Ds rows).trans
  calc
    _≤∑c:actualAllocations s.pools C,∑d:actualAllocations v.pools D,
      (‖commonScalar s C R c‖*‖commonScalar v D R d‖)*
        (H*profileMass (commonData s C R c) (commonData v D R d) p q J):=by
      apply Finset.sum_le_sum
      intro c hc
      exact Finset.sum_le_sum (fun d hd=>mul_le_mul_of_nonneg_left (hb c d)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=H*(∑c:actualAllocations s.pools C,∑d:actualAllocations v.pools D,
      (‖commonScalar s C R c‖*‖commonScalar v D R d‖)*
        profileMass (commonData s C R c) (commonData v D R d) p q J):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _≤H*(Km*((C.absNorm:ℝ)*D.absNorm)^θ*
      (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
        ((C.absNorm:ℝ)*D.absNorm))):=
      mul_le_mul_of_nonneg_left (hmass s v C D R hC.1 hD.1 p q J) hH
    _=_:=by dsimp only [H];ring

end SevenEighths.CenteredMomentCommonExceptionalSource

end

end OAI
end OAIOriginalModule2260

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
Source SHA256: d411388b03af3d2a0ba700f3ad6c35815c69dddc0f2f6bd4fa8722a9275384fa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2261


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSymmetry
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonExceptionalSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_better_side (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
            (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,hJ⟩:=actual_common_exceptional lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  have hl:=hZ.2 s v p q hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  have hr:=hZ.2 v s q p hslo hshi hvP hsP hvW₁ hvW₂ hsW₁ hsW₂ D C hD hC R seed hR hsD hsC
    rRight rLeft hvX₁ hvX₂ hvY₁ hvY₂ hsX₁ hsX₂ hsY₁ hsY₂ rows hn hvEx hsEx hvCond hsCond Ds hDs
  by_cases hc:max (rRight-Real.logb Z (D.absNorm:ℝ)) 0≤max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0
  · rw [max_eq_left hc]
    exact hl
  · rw [max_eq_right (le_of_not_ge hc)]
    have hswap:(∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)=
      ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn v D hD R seed L z‖*‖normalizedColumn s C hC R seed L z‖:=by
      apply Finset.sum_congr rfl
      intro L hL
      congr 1
      exact Finset.sum_congr rfl (fun z hz=>mul_comm _ _)
    rw [hswap]
    apply hr.trans_eq
    rw [mul_comm (D.absNorm:ℝ) (C.absNorm:ℝ)]
    unfold profileMass
    ring

lemma same_raw_better_cap (r c d:ℝ):
    max (max (r-c) 0) (max (r-d) 0)=max (r-min c d) 0:=by
  rcases le_total c d with h|h
  · rw [min_eq_left h,max_eq_left (max_le_max_right 0 (by linarith))]
  · rw [min_eq_right h,max_eq_right (max_le_max_right 0 (by linarith))]

end SevenEighths.CenteredMomentCommonExceptionalSymmetry

end

end OAI
end OAIOriginalModule2261

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricCanonical
Source SHA256: f559f85bb438d01899cbc262cf2af4b9089c23eab9a1e4152ce205803dd2b3c6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2262



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalAsymmetricCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAsymmetricSource CenteredMomentSecondExceptionalCount
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_asymmetric_canonical_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀(η:Character)(χ:RayFourExpansion.RayCharacter)(C₀ D₀:Ideal O)(_hC₀:Supported C₀)
        (U:Finset (CommonIndex C₀ D₀)),IsCoprime Q C₀ → idealCoeff η C₀≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C₀ D₀*nonunitFrequencyGenerator C₀ D₀ U) z) →
      (∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B rRight z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
            (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
            2*ε+δ-max r 0)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_masked_asymmetric lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight η χ C₀ D₀ hC₀ U hcop hη m hm hml hm2 rows hn hex hs hv
    Cr M hCr hN Ds hDs
  have hc:=actual_canonical_exceptional_count η χ C₀ D₀ hC₀ U Q hQ0 hQ hQ72 hcop hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  apply (hZ.2 I L s v p q hlo hhi r rRight rows hs hv Ds hDs).trans
  have hz:=zero_lt_one.trans hZ.1
  calc
    _≤C*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6))*
        Z^(2*ε+δ-max r 0)*profileMass s v p q J:=by
      apply mul_le_mul_of_nonneg_right _ (profileMass_nonneg s v p q J)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hC.le
    _=_:=by
      rw [show (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          2*ε+δ-max r 0=
          (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C₀ D₀=>P.val)
          (leftExponent C₀ D₀) (rightExponent C₀ D₀) (nonunitPartitionSet C₀ D₀ U)):ℝ))/6+
          (2*ε+δ-max r 0) by ring,Real.rpow_add hz]
      ring

end SevenEighths.CenteredMomentExceptionalAsymmetricCanonical

end

end OAI
end OAIOriginalModule2262

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCanonical
Source SHA256: b552e5c8c9ef458509b5b1c1daab36ed7ab9a5b0d04b42421efe1e991675e90a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2263



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalCanonical
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonExceptionalSource CenteredMomentCommonExceptionalSymmetry
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_canonical_bound (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
            (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,hJ⟩:=actual_common_better_side lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hc:=actual_canonical_exceptional_count η₀ χ C D hC U Q hQ hQtop hQ72 hcop hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  have hb:=hZ.2 s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let F:ℝ:=profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm)
  have hF:0≤F:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg _ _ _ _ _) (frozenProfile_nonneg _))
    (frozenProfile_nonneg _)) (by positivity)
  let e:ℝ:=2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
    (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)
  let f:ℝ:=(M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6
  have hz:=zero_lt_one.trans hZ.1
  apply hb.trans
  calc
    _≤K*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f)*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F:=by
      apply mul_le_mul_of_nonneg_right _ hF
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hK.le
    _=_:=by
      have hpow:Z^(f+e)=Z^f*Z^e:=Real.rpow_add hz _ _
      change K*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f)*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F=K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^(f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*((C.absNorm:ℝ)*D.absNorm)^θ*F
      rw [show f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)=f+e by dsimp [e];ring,hpow]
      ring

end SevenEighths.CenteredMomentCommonExceptionalCanonical

end

end OAI
end OAIOriginalModule2263

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalHeight
Source SHA256: 3a3f7a0f203ed69a525e5bb4ab9f9840164a3a10a8c0cdefb392da843091eb0a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2264




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentHeckeWindowEnergy HeckeFamily CenteredMomentAllocatedDetectorAmplitude
universe u

def cost (p:Tests)(t θ:ℝ):ℝ:=‖p.height 0‖+‖p.height 1‖+heightCost t θ

theorem cost_pos (p:Tests)(t θ:ℝ):0<cost p t θ:=by
  dsimp only [cost]
  linarith [norm_nonneg (p.height 0),norm_nonneg (p.height 1),heightCost_pos t θ]

theorem shifted_weight (p:Tests)(t θ u:ℝ):
    p.heightWeight (t+2*Real.pi*(u-θ))≤cost p t θ*(1+‖u‖):=by
  have h:=norm_height_shift t θ u
  dsimp only [Tests.heightWeight,cost]
  nlinarith [mul_nonneg (norm_nonneg (p.height 0)) (norm_nonneg u),
    mul_nonneg (norm_nonneg (p.height 1)) (norm_nonneg u)]

def mass {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  cost p t₁ θ₁^J*cost q t₂ θ₂^J*slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

theorem mass_nonneg {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):
    0≤mass s v p q t₁ t₂ θ₁ θ₂ J:=by
  unfold mass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (pow_nonneg (cost_pos p t₁ θ₁).le _) (pow_nonneg (cost_pos q t₂ θ₂).le _))
    (slotControl_nonneg _)) (slotControl_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem shifted_mass {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(η τ:Character)(p q:Tests)(t₁ t₂ θ₁ θ₂ u w:ℝ)(J:ℕ):
    profileMass (withHeight s η (t₁+2*Real.pi*(u-θ₁))).toData
      (withHeight v τ (t₂+2*Real.pi*(w-θ₂))).toData p q J≤
      mass s v p q t₁ t₂ θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J:=by
  have hp:=pow_le_pow_left₀ (by dsimp [Tests.heightWeight];positivity)
    (shifted_weight p t₁ θ₁ u) J
  have hq:=pow_le_pow_left₀ (by dsimp [Tests.heightWeight];positivity)
    (shifted_weight q t₂ θ₂ w) J
  have hh:=mul_le_mul hp hq (by dsimp [Tests.heightWeight];positivity)
    (pow_nonneg (mul_nonneg (cost_pos p t₁ θ₁).le (by positivity)) _)
  have hs:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
      (Real.sqrt_nonneg (volume v.toData))
  convert hs using 1
  · rfl
  · simp only [mass,mul_pow];ring

end SevenEighths.CenteredMomentExceptionalHeight

end

end OAI
end OAIOriginalModule2264

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCanonicalWindow
Source SHA256: b251fef9bce9fd5c5836923c50efbd4909034bd8558d104488230993537a458d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2265





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentCommonExceptionalCanonicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalSource CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentExceptionalHeight CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentCommonExceptionalCanonical CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_common_window (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀θ₁ θ₂ X Y:ℝ,0<X → 0<Y →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L s.η s.t θ₁ X logAnnulus z‖*
        ‖windowColumn v D hD R seed L v.η v.t θ₂ Y logAnnulus z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))*
          mass s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,hJ⟩:=actual_common_canonical_bound lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN θ₁ θ₂ X Y hX hY Ds hDs
  let F:=K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg v)) (by positivity))
  have hh:=whole_window_pair s v C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    s.η v.η s.t v.t θ₁ θ₂ X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (F*mass s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hm:=shifted_mass s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentCommonExceptionalCanonicalWindow

end

end OAI
end OAIOriginalModule2265

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonExceptionalWindow
Source SHA256: 62a8a8d029518f410d8502d86bd4053408e8206fc4bc193c9130fd38120f596a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2266




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentCommonExceptionalWindow
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalSource CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentExceptionalHeight CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_common_window (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀θ₁ θ₂ X Y:ℝ,0<X → 0<Y →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L s.η s.t θ₁ X logAnnulus z‖*
        ‖windowColumn v D hD R seed L v.η v.t θ₂ Y logAnnulus z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))*
          mass s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,hJ⟩:=actual_common_exceptional lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    θ₁ θ₂ X Y hX hY Ds hDs
  let F:=K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg v)) (by positivity))
  have hh:=whole_window_pair s v C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    s.η v.η s.t v.t θ₁ θ₂ X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (F*mass s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond Ds hDs
  have hm:=shifted_mass s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentCommonExceptionalWindow

end

end OAI
end OAIOriginalModule2266

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowHeight
Source SHA256: 3117dbe667d55a662f53d0f85d63bc7f4bc4896a1692157fa0a40aa3a68dc9a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2267


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalWindowHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData CenteredMomentExceptionalHeight
open CenteredMomentHeckeWindowEnergy CenteredMomentAllocatedDetectorAmplitude
universe u

theorem cost_phase (p:Tests)(t θ:ℝ):
    cost p t θ≤p.heightWeight t*(1+2*Real.pi)^2*(1+‖θ‖):=by
  have hc:0≤2*Real.pi:=by positivity
  have hp:1≤p.heightWeight t:=by
    dsimp only [Tests.heightWeight]
    linarith [norm_nonneg (p.height 0),norm_nonneg (p.height 1),norm_nonneg t]
  have h1:cost p t θ≤(p.heightWeight t+2*Real.pi*‖θ‖)*(1+2*Real.pi):=by
    dsimp only [cost,Tests.heightWeight,heightCost]
    nlinarith [mul_nonneg hc (norm_nonneg (p.height 0)),mul_nonneg hc (norm_nonneg (p.height 1))]
  have h2:p.heightWeight t+2*Real.pi*‖θ‖≤p.heightWeight t*(1+2*Real.pi)*(1+‖θ‖):=by
    nlinarith [mul_nonneg hc (norm_nonneg θ),mul_nonneg hc (show 0≤p.heightWeight t by linarith),
      mul_nonneg (show 0≤p.heightWeight t-1 by linarith) (mul_nonneg hc (norm_nonneg θ)),
      mul_nonneg (show 0≤p.heightWeight t by linarith) (norm_nonneg θ)]
  exact h1.trans ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans_eq (by ring))

theorem mass_phase {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(w:ℝ)(J:ℕ):
    mass s v p q s.t v.t w (-w) J≤
      (1+2*Real.pi)^(4*J)*profileMass s.toData v.toData p q J*(1+‖w‖)^(2*J):=by
  have hp:=pow_le_pow_left₀ (cost_pos p s.t w).le (cost_phase p s.t w) J
  have hq:=pow_le_pow_left₀ (cost_pos q v.t (-w)).le (cost_phase q v.t (-w)) J
  rw [norm_neg] at hq
  have hh:=mul_le_mul hp hq (pow_nonneg (cost_pos q v.t (-w)).le _) (by dsimp only [Tests.heightWeight]; positivity)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
        (Real.sqrt_nonneg (volume v.toData))
  apply he.trans_eq
  simp only [profileMass,mul_pow,←pow_mul]
  rw [show 4*J=2*J+2*J by omega,show 2*J=J+J by omega]
  simp only [pow_add]
  ring

end SevenEighths.CenteredMomentExceptionalWindowHeight

end

end OAI
end OAIOriginalModule2267

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalAmplitude
Source SHA256: b4044325b0dc4fc04c56d358464cfd5c0ed045a355aa7ab4a548b250f710e48e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2268



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedDetectorAmplitude ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
theorem allocated_amplitude_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),1<Z → (∀i,1≤s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r:ℝ,s.W₁=W₁ → s.W₂=W₂ →
      Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ s Z hZ hP z hm hA hz hml hm2 hcond hex D a r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap W₁ W₂ hs₁ hs₂ ι Z hZ s.η s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hR₁:=sourceControl_nonneg R W₁
  have hR₂:=sourceControl_nonneg R W₂
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule2268

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
Source SHA256: 956ff7daf1e9da732bfce2b6ada80f6b4edadf40b51858dd9ee3f011d11690d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2269



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u
structure Profiles (lo hi:ℝ) where
  profile : Fin 2→𝓢(ℝ,ℂ)
  support : ∀i,Function.support (profile i:ℝ→ℂ)⊆Set.Icc lo hi

def Profiles.control {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : ℝ :=
  sourceControl R (p.profile 0)*sourceControl R (p.profile 1)

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}
def ProfileAdmissible {ι:Type u} [Fintype ι] (s:Data ι) (p:Profiles lo hi)
    (Q:Ideal O) (Z B r:ℝ) (z:O):Prop:=
  (∀i,1≤s.P i) ∧ s.m≠0 ∧ s.A≠0 ∧ z≠0 ∧ goodLambda∣s.m ∧ (2:O)∣s.m ∧
  (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B ∧
  CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z ∧
  s.W₁=p.profile 0 ∧ s.W₂=p.profile 1 ∧
  Z^r≤s.X₁ ∧ Z^r≤s.X₂ ∧ Z^r≤s.Y₁ ∧ Z^r≤s.Y₂

theorem paired_amplitude_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Profiles lo hi)(Z r:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B r z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control R*q.control R*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_amplitude_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Profiles lo hi)
      (hs:ProfileAdmissible s p Q Z B r z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*p.control R*Z^ε*(1+‖s.t‖)^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    have hpc := Profiles.control_nonneg p R
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
        α s Z hZ hP z hm hA hz hml hm2 hcond hex D a r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂

  have hpc := Profiles.control_nonneg p R
  have hqc := Profiles.control_nonneg q R
  have hl:=hpoint ι s p hs a
  have hr:=hpoint κ v q hv b
  have hcap:1≤Z^(max (r-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*q.control R*Z^ε*(1+‖v.t‖)^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule2269

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonAsymmetric
Source SHA256: 630c4acce9a5415598e0eca3faf8417b8d5efa3abf1977223e961bc5cdb63cf5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2270



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalWholeSource
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentExceptionalAsymmetricSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):ℝ:=
  p.control R*q.control R*(1+‖s.t‖)^J*(1+‖v.t‖)^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

lemma profileMass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Profiles lo hi)(J:ℕ):0≤profileMass R s v p q J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s
  have hv:=slotControl_nonneg v
  unfold profileMass
  positivity

theorem actual_paired_asymmetric (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Profiles lo hi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control R*q.control R*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,R,hR,hJ⟩:=allocated_amplitude_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Profiles lo hi)(r0:ℝ)
      (hs:ProfileAdmissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*p.control R*Z^ε*(1+‖s.t‖)^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    have hpc := Profiles.control_nonneg p R
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
        α s Z hZ hP z hm hA hz hml hm2 hcond hex D a r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂

  have hpc := Profiles.control_nonneg p R
  have hqc := Profiles.control_nonneg q R
  have hl:=hpoint ι s p r hs a
  have hr:=hpoint κ v q rRight hv b
  have hcap:1≤Z^(max (rRight-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*q.control R*Z^ε*(1+‖v.t‖)^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

theorem actual_paired_capped (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(α κ:Type u) [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ],
      ∀(s:Data α)(v:Data κ)(p q:Profiles wlo whi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control Sprofile*q.control Sprofile*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_paired_asymmetric wlo whi ε B hwlo hwhi hε hB
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro α κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  rw [←raw_cap_weight s v hs.1 D a b Z r hZ]
  exact hbound α κ s v p q Z r rRight hZ z hs hv D a b

theorem actual_whole_asymmetric (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Profiles wlo whi),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,ProfileAdmissible s p Q Z B r z) →
      (∀z∈rows,ProfileAdmissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass Sprofile s v p q J:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_paired_capped wlo whi hwlo hwhi ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass Sprofile s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg Sprofile s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass Sprofile s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r rRight hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-max r 0)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs (max r 0)) hA
    _=_:=by
      rw [show 2*ε+δ-max r 0=2*ε+(δ-max r 0) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

theorem actual_masked_asymmetric (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Profiles wlo whi),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,ProfileAdmissible s p Q Z B r z) →
      (∀z∈rows,ProfileAdmissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass Sprofile s v p q J:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_whole_asymmetric wlo whi hwlo hwhi lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rRight rows hs hv Ds hDs)

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2270

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonGates
Source SHA256: e0847bdf344625fe25147cd0d28e25b885cbff37f66e9f579f2c38e925c5dc94
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2271





namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFixedRowMask CenteredExceptionalProfile CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentCommonExceptionalGates CenteredMomentFiniteProfileExceptional
variable {wlo whi:ℝ}
omit [DecidableEq ι] in
theorem common_admissible (s:Input ι)(p:Profiles wlo whi)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    ProfileAdmissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2271

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonMass
Source SHA256: 063bdf4cad4500f9e030da13e26ef78f8a0360b852ecc8be95f813803c250e81
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2272



namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonExceptionalCost CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalAmplitudePair CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentCommonExceptionalMass CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι] {wlo whi:ℝ}
lemma common_pair_profile_bound (Sprofile:Finset (ℕ×ℕ)) (s v:Input ι)(C D R:Ideal O)(hC:C≠0)(hD:D≠0)
    (B:actualAllocations s.pools C)(E:actualAllocations v.pools D)(p q:Profiles wlo whi)(J:ℕ):
    (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
      profileMass Sprofile (commonData s C R B) (commonData v D R E) p q J≤
        profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm D):=by
  have hs:=scalar_profile_volume s C R hC B
  have hv:=scalar_profile_volume v D R hD E
  have hprod:=mul_le_mul hs hv
    (mul_nonneg (mul_nonneg (norm_nonneg _) (slotControl_nonneg _)) (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg (slotControl_nonneg _) (frozenProfile_nonneg _))
      (Real.sqrt_nonneg _)) (Nat.cast_nonneg _))
  have hh:=mul_le_mul_of_nonneg_left hprod
    (show 0≤p.control Sprofile*q.control Sprofile*(1+‖s.t‖)^J*(1+‖v.t‖)^J from
      mul_nonneg (mul_nonneg (mul_nonneg (Profiles.control_nonneg p Sprofile)
        (Profiles.control_nonneg q Sprofile)) (by positivity)) (by positivity))
  convert hh using 1 <;> dsimp only [profileMass,commonData] <;> ring

theorem common_profile_mass (δ:ℝ)(hδ:0<δ):
    ∃K:ℝ,0<K ∧ ∀(Sprofile:Finset (ℕ×ℕ))(s v:Input ι)(C D R:Ideal O),C≠0 → D≠0 → ∀(p q:Profiles wlo whi)(J:ℕ),
      (∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          profileMass Sprofile (commonData s C R B) (commonData v D R E) p q J)≤
        K*((Ideal.absNorm C:ℝ)*Ideal.absNorm D)^δ*
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((Ideal.absNorm C:ℝ)*Ideal.absNorm D)):=by
  obtain ⟨K,hK,hcard⟩:=actualAllocations_small_power (ι:=ι⊕Fin 2) δ hδ
  refine ⟨K^2,sq_pos_of_pos hK,?_⟩
  intro Sprofile s v C D R hC hD p q J
  let A:=profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
    ((Ideal.absNorm C:ℝ)*Ideal.absNorm D)
  have hA:0≤A:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg Sprofile _ _ _ _ _)
    (frozenProfile_nonneg _)) (frozenProfile_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _≤∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,A:=
      Finset.sum_le_sum (fun B _=>Finset.sum_le_sum (fun E _=>common_pair_profile_bound Sprofile s v C D R hC hD B E p q J))
    _=((actualAllocations s.pools C).card:ℝ)*((actualAllocations v.pools D).card:ℝ)*A:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
    _≤((K*(Ideal.absNorm C:ℝ)^δ)*(K*(Ideal.absNorm D:ℝ)^δ))*A:=
      mul_le_mul_of_nonneg_right (mul_le_mul (hcard s.pools C hC) (hcard v.pools D hD)
        (Nat.cast_nonneg _) (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))) hA
    _=_:=by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      dsimp only [A]
      ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2272

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSource
Source SHA256: b051cf214b630f42e2b593db7e82c6e7f5c062639407699a83f28a858fb02ced
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2273





namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_exceptional (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Profiles wlo whi),(∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_masked_asymmetric wlo whi hwlo hwhi lo hi ε δ B Lbound hε hδ hB hL
  obtain ⟨Km,hKm,hmass⟩:=common_profile_mass (ι:=ι) θ hθ
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨Ka,hKa,hbound⟩:=hJ Q hQ
  refine ⟨Ka*Km,mul_pos hKa hKm,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let H:=Ka*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hH:0≤H:=by dsimp [H];positivity
  have hb (c:actualAllocations s.pools C)(d:actualAllocations v.pools D):
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude (commonData s C R c) L z‖*
          ‖maskedAmplitude (commonData v D R d) L z‖)≤
        H*profileMass Sprofile (commonData s C R c) (commonData v D R d) p q J:=by
    apply hZ.2 _ _ (commonData s C R c) (commonData v D R d) p q
      (fun i=>hlo i.val) (fun i=>hhi i.val)
      (rLeft-Real.logb Z (C.absNorm:ℝ)) (rRight-Real.logb Z (D.absNorm:ℝ)) rows
    · intro z hz
      exact common_admissible s p C R Q hC.1 hR c Z B rLeft hZ.1 z (hn z hz) hsP
        (hsEx z hz) (hsCond z hz) hsW₁ hsW₂ hsX₁ hsX₂ hsY₁ hsY₂
    · intro z hz
      exact common_admissible v q D R Q hD.1 hR d Z B rRight hZ.1 z (hn z hz) hvP
        (hvEx z hz) (hvCond z hz) hvW₁ hvW₂ hvX₁ hvX₂ hvY₁ hvY₂
    · exact hDs
  apply (whole_paired_columns s v C D hC hD R seed hsC hsD Ds rows).trans
  calc
    _≤∑c:actualAllocations s.pools C,∑d:actualAllocations v.pools D,
      (‖commonScalar s C R c‖*‖commonScalar v D R d‖)*
        (H*profileMass Sprofile (commonData s C R c) (commonData v D R d) p q J):=by
      apply Finset.sum_le_sum
      intro c hc
      exact Finset.sum_le_sum (fun d hd=>mul_le_mul_of_nonneg_left (hb c d)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=H*(∑c:actualAllocations s.pools C,∑d:actualAllocations v.pools D,
      (‖commonScalar s C R c‖*‖commonScalar v D R d‖)*
        profileMass Sprofile (commonData s C R c) (commonData v D R d) p q J):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _≤H*(Km*((C.absNorm:ℝ)*D.absNorm)^θ*
      (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
        ((C.absNorm:ℝ)*D.absNorm))):=
      mul_le_mul_of_nonneg_left (hmass Sprofile s v C D R hC.1 hD.1 p q J) hH
    _=_:=by dsimp only [H];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2273

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonHeight
Source SHA256: e2cbb743782abd6e50b0aa299ace3c760ac65d1f5dc8d816035052caaddff75c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2274




namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentExceptionalAmplitudePair CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentHeckeWindowEnergy
open HeckeFamily CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
universe u

def mass {lo hi:ℝ} (R:Finset (ℕ×ℕ)) {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  p.control R*q.control R*heightCost t₁ θ₁^J*heightCost t₂ θ₂^J*
    slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

theorem mass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ)) {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):
    0≤mass R s v p q t₁ t₂ θ₁ θ₂ J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s.toData
  have hv:=slotControl_nonneg v.toData
  have ht₁:=(heightCost_pos t₁ θ₁).le
  have ht₂:=(heightCost_pos t₂ θ₂).le
  unfold mass
  positivity

theorem shifted_mass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(η τ:Character)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂ u w:ℝ)(J:ℕ):
    profileMass R (withHeight s η (t₁+2*Real.pi*(u-θ₁))).toData
      (withHeight v τ (t₂+2*Real.pi*(w-θ₂))).toData p q J≤
      mass R s v p q t₁ t₂ θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J:=by
  have hp:=pow_le_pow_left₀ (by positivity) (norm_height_shift t₁ θ₁ u) J
  have hq:=pow_le_pow_left₀ (by positivity) (norm_height_shift t₂ θ₂ w) J
  have hh:=mul_le_mul hp hq (by positivity)
    (pow_nonneg (mul_nonneg (heightCost_pos t₁ θ₁).le (by positivity)) _)
  have hcontrol:=mul_nonneg (Profiles.control_nonneg p R) (Profiles.control_nonneg q R)
  have hs:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hcontrol)
        (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
      (Real.sqrt_nonneg (volume v.toData))
  convert hs using 1
  · dsimp only [profileMass,withHeight,slotControl,volume]
    ring
  · simp only [mass,mul_pow]
    ring
end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2274

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSymmetry
Source SHA256: 49a5b359d4439b3de7964cca12af39d805e6c2a40a3bae70dde53435ba695f27
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2275


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_better_side (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
            (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_exceptional wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  have hl:=hZ.2 s v p q hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  have hr:=hZ.2 v s q p hslo hshi hvP hsP hvW₁ hvW₂ hsW₁ hsW₂ D C hD hC R seed hR hsD hsC
    rRight rLeft hvX₁ hvX₂ hvY₁ hvY₂ hsX₁ hsX₂ hsY₁ hsY₂ rows hn hvEx hsEx hvCond hsCond Ds hDs
  by_cases hc:max (rRight-Real.logb Z (D.absNorm:ℝ)) 0≤max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0
  · rw [max_eq_left hc]
    exact hl
  · rw [max_eq_right (le_of_not_ge hc)]
    have hswap:(∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)=
      ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn v D hD R seed L z‖*‖normalizedColumn s C hC R seed L z‖:=by
      apply Finset.sum_congr rfl
      intro L hL
      congr 1
      exact Finset.sum_congr rfl (fun z hz=>mul_comm _ _)
    rw [hswap]
    apply hr.trans_eq
    rw [mul_comm (D.absNorm:ℝ) (C.absNorm:ℝ)]
    unfold profileMass
    ring
