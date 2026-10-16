import core.OAI07
-- import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
-- import Mathlib.MeasureTheory.Constructions.Polish.Basic
-- import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Pinned OAI dependency closure, consolidated without changing public namespaces.
Original module boundaries and hashes are preserved below. -/

/-! Original module: OAI.NumberTheory.DirichletL.Energy.State
Source SHA256: d3b480d46e850bb45422841816c644c9417b8d0f6cc651dabf3da89f1e0f5923
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2442



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

structure NaturalState (Z Bmask bΦ:ℝ) where
  character : Character
  fixedModulus : Ideal O
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  base_ge_one : 1≤Z
  row_nonneg : 0≤rowWidth
  character_nonneg : 0≤characterWidth
  scale_eq : radial.scale=Z^rowWidth
  modulus_bound : (character.modulus.absNorm:ℝ)≤Z^characterWidth
  puncture_ne_zero : puncture≠0
  puncture_bound : (puncture.absNorm:ℝ)≤Z^Bmask
  radial_support : Function.support (radial.profile:ℝ→ℂ)⊆Set.Iic bΦ
  row_ne_zero : ∀z,radial.keep z→z≠0
  nonexceptional : ∀z,radial.keep z→
    ¬FixedInducingRow character fixedModulus
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture) 1 z

namespace NaturalState
variable {Z Bmask bΦ:ℝ}
def width (s:NaturalState Z Bmask bΦ):ℝ := s.rowWidth+s.characterWidth
lemma width_nonneg (s:NaturalState Z Bmask bΦ):0≤s.width :=
  add_nonneg s.row_nonneg s.character_nonneg

def mask (s:NaturalState Z Bmask bΦ):O :=
  fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture

def plainEnergy (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):ℝ :=
  energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
    X₁ X₂ s.radial.keep s.radial.profile s.radial.scale

lemma plainEnergy_eq_zero (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):
    s.plainEnergy p t X₁ X₂=CenteredMomentCoreFloor.zeroEnergy s.character s.mask 1 t
      (p.profile 0) (p.profile 1) X₁ X₂ s.radial :=
  (CenteredMomentCoreFloor.zero_energy_eq _ _ _ _ _ _ _ _ _).symm

lemma radical_bound (s:NaturalState Z Bmask bΦ):
    (s.puncture.radical.absNorm:ℝ)≤Z^Bmask :=by
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=s.puncture))))
end NaturalState

def ZeroBound (Q:Ideal O) (a b bΦ Bmask M ε:ℝ)(degree:ℕ)(S:Finset (ℕ×ℕ))(C Z₀:ℝ):Prop :=
  ∀Z:ℝ,Z₀≤Z→∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→
    s.plainEnergy p t X₁ X₂≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree*
        Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyState

end

end OAI
end OAIOriginalModule2442

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ChildState
Source SHA256: 62e84ccaf59e12bc795d884d473cdeb450a83f5f9588144bb4a420ae7af44c65
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2443





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ):=by
  intro x hx
  by_cases h:0≤x
  · exact (CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

lemma canonical_mask_nonexceptional (τ:Character)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬CenteredExceptionalProfile.FixedInducingRow τ Q
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)

def canonicalState (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)):NaturalState Z Bmask 2 where
  character:=τ
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=>hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

lemma canonicalState_width (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring

lemma common_puncture_bound (Z Bmask Bsource:ℝ)(hZ:0<Z)(R C:Ideal O)
    (hR:(R.absNorm:ℝ)≤Z^Bmask)(hC:(C.absNorm:ℝ)≤Z^Bsource):
    ((R*C).absNorm:ℝ)≤Z^(Bmask+Bsource):=by
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hR hC (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

section Actual
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)

include hne in

lemma actual_dyad_ge_one : 1≤dyadicScale (n 1):=by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U
    radius rows W K n hne
  exact (normValue_ge_one z hz0).trans (dyadicRows_norm rows n z hz).2.le

def actualState (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):NaturalState Z Bmask 2:=
  canonicalState Z Bmask hZ (τ χ) Q R hR hRN n
    (actual_dyad_ge_one t S β radius rows W K n hne)

include h hK in

theorem actualState_width (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):
    (actualState (τ:=τ) t S β radius rows W K n hne Z Bmask hZ χ Q R hR hRN).width≤
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)):=by
  exact dyadic_log_budget h t S β radius rows W K hK n hne Z hZ χ

end Actual
end SevenEighths.CenteredMomentEnergyChildState

end

end OAI
end OAIOriginalModule2443

/-! Original module: OAI.NumberTheory.DirichletL.Energy.Floor
Source SHA256: ca646aeb42c50b87f24485bf6aede2b8044d51a0f3970a72d5677e7b0625f7d0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2444


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

theorem exists_zero_floor (a b bΦ Bmask ε:ℝ)(ha:0<a)(hb:0≤b)
    (hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀Q:Ideal HeckeFamily.O,ZeroBound Q a b bΦ Bmask (ε/16) ε degree S C 1:=by
  let e:ℝ:=ε/(4*(Bmask+1))
  have he:0<e:=div_pos hε (by positivity)
  have hbudget:e*Bmask+4*(ε/16)≤ε:=by
    have hcost:e*Bmask≤ε/4:=by
      have hinc:Bmask≤Bmask+1:=by linarith
      have hh:=mul_le_mul_of_nonneg_left hinc he.le
      have hid:e*(Bmask+1)=ε/4:=by dsimp [e];field_simp
      rw [hid] at hh
      exact hh
    linarith
  obtain ⟨degree,S,C,hC,hfloor⟩:=natural_masked_floor a b e ha hb he
  refine ⟨degree,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro Q Z hZ₀ s hQ hs p t X₁ X₂ hX₁ hX₂
  have hZ:=s.base_ge_one
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hrad: (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e):=by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hp:Z^(Bmask*e)*Z^(s.width+4*(ε/16))≤Z^(s.width+ε):=by
    rw [←Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hh:=hfloor (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
    s.character s.fixedModulus s.puncture s.radial bΦ s.puncture_ne_zero hbΦ.le
    s.radial_support s.row_ne_zero s.nonexceptional Z s.rowWidth s.characterWidth
    (ε/16) t X₁ X₂ hZ s.row_nonneg s.character_nonneg s.scale_eq hs hX₁ hX₂ s.modulus_bound
  rw [s.plainEnergy_eq_zero]
  change CenteredMomentCoreFloor.zeroEnergy _ _ _ _ _ _ _ _ _≤_
  apply hh.trans
  have hd:=diagonalControl_nonneg s.radial.profile
  have hc:=p.control_nonneg S
  change C*(s.puncture.radical.absNorm:ℝ)^e*bΦ^4*diagonalControl s.radial.profile*
    (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16))≤_
  calc
    _≤C*Z^(Bmask*e)*bΦ^4*diagonalControl s.radial.profile*
      (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16)):=by gcongr
    _=(C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree)*
      (Z^(Bmask*e)*Z^(s.width+4*(ε/16))):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentEnergyState

end

end OAI
end OAIOriginalModule2444

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalSource
Source SHA256: b6f22f83c25e667d0c93ff0c927dc17eb78363a5eae7950da501f0a711e26f5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2445





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentHeckeHeight
open CenteredMomentDivisorRowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRectangleEnergy
open CenteredMomentPositiveSummability CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance energyOriginalSourceDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def completeInput (s : Data ι) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hν : ∀i I,‖s.ν i I‖≤1) (hW : ∀i x,‖s.W i x‖≤s.M i)
    (lo hi : ℝ) (hlo : 0<lo) (hl : ∀i,lo≤s.lo i) (hh : ∀i,s.hi i≤hi) : Input ι where
  toData := s
  plain₁ := plainSupportPool s.b₁ s.X₁ s.Y₁
  plain₂ := plainSupportPool s.b₂ s.X₂ s.Y₂
  plain₁_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  plain₂_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  coverage₁ := plainSupportPool_coverage s.W₁ s.b₁ s.X₁ s.Y₁ hz₁ s.support₁ s.X₁_pos s.Y₁_pos
  coverage₂ := plainSupportPool_coverage s.W₂ s.b₂ s.X₂ s.Y₂ hz₂ s.support₂ s.X₂_pos s.Y₂_pos
  ν_bound := hν
  W_bound := hW
  lower := lo
  upper := hi
  lower_pos := hlo
  lower_le := hl
  upper_ge := hh

omit [DecidableEq ι] in
lemma input_tuplePool (s : Input ι) :
    Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
  ext v
  simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]

lemma input_polynomial_difference (s : Input ι) (R : Ideal O) (z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I)=
    (rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.X₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.X₂-
     rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.Y₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.Y₂)*
        ∏i,rowSlot s.η (fixedBadMask*idealGenerator R) 1 z (s.slots i)
          (s.toData.coefficient i) s.t := by
  unfold coefficient
  rw [input_tuplePool]
  rw [source_polynomial_eq_maskedRectangle s.η fixedBadMask 1 z s.t
    (dvd_mul_right _ _) (dvd_mul_left _ _) s.slots s.plain₁ s.plain₂ R 1
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 s.coverage₁ s.coverage₂]
  simp only [map_one,Nat.cast_one,div_one,maskedRectangle,one_dvd,ite_true,one_mul]
  exact actual_slot_rectangle_sum s.η (fixedBadMask*idealGenerator R) 1 z s.slots
    s.toData.coefficient s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos

lemma normalized_input_difference (s : Input ι) (R : Ideal O) (z : O) :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.X₁ s.X₂-
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (CenteredMomentAmplificationChildInput.volume s):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I := by
  rw [input_polynomial_difference]
  unfold positiveSlotRow CenteredMomentAmplificationChildInput.volume
  rw [s.same_product]
  ring

omit [DecidableEq ι] in
lemma input_energy_hasSum (s : Input ι) (R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O=>
      ‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R 1) Φ K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset s.pools))) (sourceGenerator_supported _)
    (fun I=>coefficient s R 1 I*rowWeight s.η fixedBadMask 1 1 s.t I) Φ K hK).hasSum
  change HasSum _ (rowEnergy _ _ _ Φ K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  simpa only [finiteHeckeEnergy_eq s.η fixedBadMask 1 s.t (dvd_mul_right _ _) (dvd_mul_left _ _),
    finite_hecke_sum_eq_rowPolynomial s.η fixedBadMask 1 _ s.t (dvd_mul_right _ _) (dvd_mul_left _ _)] using hs

theorem kept_difference_energy (s : Input ι) (R : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑'z : O,if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂-
        positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      CenteredMomentRestrictedSource.sourceRestrictedEnergy keep
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1)
        (CenteredMomentHeckeColumnWindow.heightCoeff s.η s.t) Φ K /
          CenteredMomentAmplificationChildInput.volume s := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
    CenteredMomentRestrictedEnergy.restrictedEnergy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [ite_eq_left hk,ite_eq_left hk,normalized_input_difference,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _
        (CenteredMomentAmplificationChildInput.volume_pos s)]
    ring
  · simp only [ite_eq_right hk,zero_div]

omit [DecidableEq ι] in
lemma input_positive_summable (s : Input ι) (R : Ideal O) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K X₁ X₂ : ℝ) (hK : 0<K) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    Summable (fun z : O=>if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t X₁ X₂‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := product_bounded s.η (fixedBadMask*idealGenerator R) 1 s.t
    (Real.sqrt (X₁*X₂*∏i,s.P i):ℂ)⁻¹ s.W₁ s.W₂ s.b₁ s.b₂ X₁ X₂
    s.support₁ s.support₂ hX₁ hX₂ s.slots s.toData.coefficient
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem positive_energy_comparison (s : Input ι) (R : Ideal O)
    (r : CenteredMomentRadialEligibleEnergy.Radial) :
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R 1) r.profile r.scale‖ / CenteredMomentAmplificationChildInput.volume s+
    2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale := by
  let V := CenteredMomentAmplificationChildInput.volume s
  have hV : 0<V := CenteredMomentAmplificationChildInput.volume_pos s
  let f : O→ℝ := fun z=>
    (‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re)/V
  let g : O→ℝ := fun z=>if r.keep z then
    ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0
  have hf := (input_energy_hasSum s R r.profile r.scale r.scale_pos).div_const V
  have hg := input_positive_summable s R r.keep r.profile r.scale s.Y₁ s.Y₂
    r.scale_pos s.Y₁_pos s.Y₂_pos
  have hfn (z : O) : 0≤f z := div_nonneg (mul_nonneg (sq_nonneg _) (r.nonneg z)) hV.le
  have hgn (z : O) : 0≤g z := by
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl
  unfold CenteredMomentInductionEnergy.energy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl)
  intro rows
  have hp (z : O) :
      (if r.keep z then
        ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂‖^2*
          (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0) ≤ 2*f z+2*g z := by
    by_cases hk : r.keep z
    · let x := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.X₁ s.X₂
      let y := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.Y₁ s.Y₂
      have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
      have hsq : ‖x‖^2≤2*‖x-y‖^2+2*‖y‖^2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg x) hn 2
        nlinarith [sq_nonneg (‖x-y‖-‖y‖)]
      dsimp only [x,y] at hsq
      rw [normalized_input_difference,CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hV] at hsq
      have hh := mul_le_mul_of_nonneg_right hsq (r.nonneg z)
      dsimp only [f,g]
      rw [ite_eq_left hk,ite_eq_left hk]
      convert hh using 1 ; ring
    · rw [ite_eq_right hk]
      exact add_nonneg (mul_nonneg (by norm_num) (hfn z)) (mul_nonneg (by norm_num) (hgn z))
  have hb := Finset.sum_le_sum (fun z (_:z∈rows)=>hp z)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hb
  have hs := sum_le_hasSum rows (fun z _=>hfn z) hf
  have ht := sum_le_hasSum rows (fun z _=>hgn z) hg.hasSum
  have he := div_le_div_of_nonneg_right
    (Complex.re_le_norm (finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale)) hV.le
  change ∑z∈rows,f z≤_ at hs
  change ∑z∈rows,g z≤∑'z,g z at ht
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/V+2*∑'z,g z
  rw [mul_div_assoc]
  linarith

section Natural
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0<a)
variable (S : ι→Finset (Ideal O)) (hp : ∀i,∀I∈S i,Prime I)
variable (ν : ι→Character) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
variable (hP : ∀i,0<P i) (hM : ∀i,1≤M i)
variable (aslot bslot : ℝ) (haslot : 0<aslot)
variable (hsSlot : ∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
variable (hWslot : ∀i x,‖Wslot i x‖≤M i)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hsame : Y₁*Y₂=X₁*X₂)

def naturalData : Data ι where
  η := state.character
  m := state.mask
  A := 1
  t := t
  slots := S
  prime := hp
  ν := fun i=>idealCoeff (ν i)
  W := Wslot
  lo := fun _=>aslot
  hi := fun _=>bslot
  P := P
  lo_pos := fun _=>haslot
  P_pos := hP
  support := hsSlot
  W₁ := p.profile 0
  W₂ := p.profile 1
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  M := M
  M_ge_one := hM
  coefficient_bound := fun i I _=>by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one (ν i) I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hWslot i ((Ideal.absNorm I:ℝ)/P i))
  b₁ := b
  b₂ := b
  support₁ := fun x hx=>(p.support 0 hx).2
  support₂ := fun x hx=>(p.support 1 hx).2
  X₁_pos := hX₁
  X₂_pos := hX₂
  Y₁_pos := hY₁
  Y₂_pos := hY₂
  same_product := hsame
  rows := ∅
  weight := fun _=>0
  weight_nonneg := fun _ _=>le_refl _

def naturalInput : Input ι :=
  completeInput (naturalData state p S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame)
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 0) a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 1) a b ha (p.support 1))
    (fun i I=>idealCoeff_norm_le_one (ν i) I) hWslot aslot bslot haslot
    (fun _=>le_refl _) (fun _=>le_refl _)

theorem natural_energy_comparison :
    let inp := naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale ≤
    2*‖finiteHeckeEnergy state.character fixedBadMask 1 t
      (finiteColumns (Fintype.piFinset inp.pools)) (coefficient inp state.puncture 1)
      state.radial.profile state.radial.scale‖/(X₁*X₂*∏i,P i)+
    2*CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale :=
  positive_energy_comparison
    (naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) state.puncture state.radial

end Natural
end SevenEighths.CenteredMomentEnergyOriginalSource

end

end OAI
end OAIOriginalModule2445

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FixedRadialSource
Source SHA256: cdee7d41ffb34fa441de7f6eb1e8eb655b9073f1b9c43da283c3a66a540a29be
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2446


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyFixedRadialSource
open HeckeFamily CenteredMomentSourceRow CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

lemma norm_le_diagonalControl (Φ:𝓢(ℝ,ℂ))(x:ℝ):‖Φ x‖≤diagonalControl Φ:=by
  have hs:SchwartzMap.seminorm ℝ 0 0 Φ≤
      (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    exact Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (by simp : (0,0)∈Finset.Iic (2,0))) Φ
  apply (SchwartzMap.norm_le_seminorm ℝ Φ x).trans
  apply hs.trans
  unfold diagonalControl
  exact le_mul_of_one_le_left (by positivity) (by nlinarith [Real.pi_nonneg])

theorem exists_fixed_bump (b:ℝ)(_hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ (∀x,(Ψ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) b,Ψ x=1):=by
  have hsub:Set.Icc (0:ℝ) b⊆Set.Ioo (-1) (b+1):=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) (b+1):=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  let Ψ:𝓢(ℝ,ℂ):=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).toSchwartzMap hv
  refine ⟨Ψ,hsupp,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem finite_energy_domination (b:ℝ)(Ψ:𝓢(ℝ,ℂ))
    (hΨ:∀x,0≤(Ψ x).re)(hone:∀x∈Set.Icc (0:ℝ) b,Ψ x=1)
    (Φ:𝓢(ℝ,ℂ))(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic b)
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (K:ℝ)(hK:0<K):
    ‖finiteHeckeEnergy η m A t S c Φ K‖≤
      diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  have hΦ:∀x:ℝ,0≤x→‖Φ x‖≤diagonalControl Φ*(Ψ x).re:=by
    intro x hx
    by_cases h:Φ x=0
    · rw [h,norm_zero]
      exact mul_nonneg (diagonalControl_nonneg Φ) (hΨ x)
    · rw [hone x ⟨hx,hs h⟩,Complex.one_re,mul_one]
      exact norm_le_diagonalControl Φ x
  have hsumΦ:=finite_hecke_energy_summable η m A t S c Φ K hK
  have hsumΨ:=finite_hecke_energy_summable η m A t S c Ψ K hK
  have hre:HasSum (fun z:O=>‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy η m A t S c Ψ K).re:=by
    have hh:=Complex.hasSum_re hsumΨ.hasSum
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      finiteHeckeEnergy] using hh
  calc
    _≤∑'z:O,‖((‖∑I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)‖:=norm_tsum_le_tsum_norm hsumΦ.norm
    _≤∑'z:O,diagonalControl Φ*(‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re):=by
      apply hsumΦ.norm.tsum_le_tsum _ (hre.summable.mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hΦ _ (by positivity)) (sq_nonneg _)).trans_eq (by ring)
    _=diagonalControl Φ*(finiteHeckeEnergy η m A t S c Ψ K).re:=by
      rw [tsum_mul_left,hre.tsum_eq]
    _≤_:=mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ)

theorem fixed_source (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic b→
      ∀(η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)(K:ℝ),0<K→
      ‖finiteHeckeEnergy η m A t S c Φ K‖≤
        diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  obtain ⟨Ψ,hs,hn,_,hone⟩:=exists_fixed_bump b hb
  exact ⟨Ψ,hs,hn,fun Φ hΦ η m A t S c K hK=>finite_energy_domination b Ψ hn hone Φ hΦ η m A t S c K hK⟩

end SevenEighths.CenteredMomentEnergyFixedRadialSource

end

end OAI
end OAIOriginalModule2446

/-! Original module: OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
Source SHA256: 0bc1762ba476de8e39a30e19ed0f84ceb1f7cecef7bc64f98d6b600d488dd5e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2447


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalEntry
open HeckeFamily CenteredMomentEnergyOriginalSource CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentExceptionalAmplitudePair
open CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance physicalEntryDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem positive_first_physical_entry (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:CenteredMomentRadialEligibleEnergy.Radial),
      volume s.toData≤Z^B→(r.scale)⁻¹≤Z^B→
      energy s.η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*physicalMass s R 1 fixedBadMask 1 r.profile r.scale Z ξ/volume s.toData+
      2*Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*r.scale*Z^ε+
      2*Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*r.scale*Z^(-saving)+
      2*energy s.η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,h⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R r hV hK
  have hh:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 r.profile r.scale r.scale_pos hV hK
  have hc:=positive_energy_comparison s R r
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/
      volume s.toData+_ at hc
  rw [mul_div_assoc] at hc ⊢
  linarith

lemma natural_inverse_scale {Z Bmask bΦ:ℝ} (state:NaturalState Z Bmask bΦ)
    (B:ℝ)(hB:0≤B):state.radial.scale⁻¹≤Z^B:=by
  have hscale:1≤state.radial.scale:=by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  exact (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow state.base_ge_one hB)

theorem natural_first_physical_entry (a b bslot B ε ξ saving Bmask bΦ:ℝ)
    (ha:0<a)(hb:0≤b)(hbslot:0≤bslot)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(state:NaturalState Z Bmask bΦ)(p:Profiles a b),
    ∀(slots:ι→Finset (Ideal O))(hp:∀i,∀I∈slots i,Prime I)
      (ν:ι→Character)(Wslot:ι→ℝ→ℂ)(P M:ι→ℝ)
      (hP:∀i,0<P i)(hM:∀i,1≤M i)(aslot:ℝ)(haslot:0<aslot)
      (hsSlot:∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
      (hWslot:∀i x,‖Wslot i x‖≤M i)
      (t X₁ X₂ Y₁ Y₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)
      (hsame:Y₁*Y₂=X₁*X₂),X₁*X₂*(∏i,P i)≤Z^B→
    let inp:=naturalInput state p ha slots hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1) slots
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale≤
    2*physicalMass inp state.puncture 1 fixedBadMask 1 state.radial.profile state.radial.scale Z ξ/
      (X₁*X₂*∏i,P i)+
    2*Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
      Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) state.radial.profile*state.radial.scale*Z^ε+
    2*Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
      Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) state.radial.profile*state.radial.scale*Z^(-saving)+
    2*energy state.character state.mask 1 t (p.profile 0) (p.profile 1) slots
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,h⟩:=positive_first_physical_entry (ι:=ι)
    (fun _=>bslot) a b B ε ξ saving (fun _=>hbslot) ha hb hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro state p slots hp ν Wslot P M hP hM aslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame hV
  exact hZ.2 (naturalInput state p ha slots hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) (p.profile 0) (p.profile 1) rfl rfl
    (p.support 0) (p.support 1) (fun _=>le_refl _) state.puncture state.radial hV
    (natural_inverse_scale state B hB)

end SevenEighths.CenteredMomentEnergyPhysicalEntry

end

end OAI
end OAIOriginalModule2447

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceState
Source SHA256: 7822d5282ad029c61edf88653e157d2c03f85c37bd7a9967cf680e3e3500a2bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2448




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

def effectiveRadial (r:Radial):Radial:=
  {r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}

lemma radialEnergy_effective (r:Radial)(f:O→ℂ):
    radialEnergy f (effectiveRadial r).keep r.profile r.scale=
      radialEnergy f r.keep r.profile r.scale:=by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hz:r.profile (‖eisEmbedding z‖^2/r.scale)=0 <;>
    simp [effectiveRadial,hk,hz]

def effectiveState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z Bmask bΦ:=
  {s with radial:=effectiveRadial s.radial
          row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
          nonexceptional:=fun z hz=>s.nonexceptional z hz.1}

lemma effective_row_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth:=by
  rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
  exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hz.2)

lemma effective_character_nonprincipal {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    (naturalCharacter s.character z).residue≠1:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  exact (naturalRow s.character z hn).nonprincipal hn s.fixedModulus s.puncture
    s.puncture_ne_zero (s.nonexceptional z hz.1)

lemma effective_character_cap {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hbΦ:0≤bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*bΦ*Z^s.width:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  have h:=(naturalRow s.character z hn).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans_le s.base_ge_one) hbΦ s.modulus_bound (effective_row_norm s z hz)
  simpa only [NaturalState.width,add_comm s.characterWidth s.rowWidth] using h

def comparisonFirst (Z M:ℝ):ℝ:=Z^(M/4)
def comparisonSecond (Z M X₁ X₂:ℝ):ℝ:=X₁*X₂/comparisonFirst Z M

lemma comparison_positive (Z M X₁ X₂:ℝ)(hZ:0<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    0<comparisonFirst Z M ∧ 0<comparisonSecond Z M X₁ X₂:=
  ⟨Real.rpow_pos_of_pos hZ _,div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos hZ _)⟩

lemma comparison_same_product (Z M X₁ X₂:ℝ)(hZ:0<Z):
    comparisonFirst Z M*comparisonSecond Z M X₁ X₂=X₁*X₂:=by
  unfold comparisonSecond
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hZ (M/4)).ne'

lemma comparison_second_power (Z M X₁ X₂:ℝ)(hZ:1<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    comparisonSecond Z M X₁ X₂=Z^(Real.logb Z (X₁*X₂)-M/4):=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos hX₁ hX₂)]
  rfl

theorem balanced_reference_geometry (Z M X₁ X₂ ell κ:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M):
    ell≤M/21 ∧
    1≤comparisonFirst Z M ∧
    comparisonFirst Z M≤comparisonSecond Z M X₁ X₂ ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4 ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)≤M:=by
  have hkell:7/2*ell≤(6*κ-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  have he:ell≤M/21:=by linarith
  have hlen:M/2≤Real.logb Z (X₁*X₂):=by linarith
  have hupper:Real.logb Z (X₁*X₂)-M/4≤M:=by linarith
  have hlog:Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4:=by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,Real.logb_rpow]
    · exact zero_lt_one.trans hZ
    · exact hZ.ne'
  refine ⟨he,Real.one_le_rpow hZ.le (by linarith),?_,hlog,by rw [hlog];exact hupper⟩
  rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem balanced_reflection_margins (Z M X₁ X₂ ell κ ξ reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+ξ):
    reflected+M/4+ell≤23*M/30+ξ ∧
    reflected+M/4+ell+(6*κ-1)*ell≤14*M/15+ξ:=by
  have hlog:=(balanced_reference_geometry Z M X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hlarge hcap).2.2.2.1
  rw [hlog] at href
  have hc:=CenteredMomentReflectionRetainedLength.positive_slot_width_drop M
    (Real.logb Z (X₁*X₂)+ell) ell ξ κ hM hell hκ hlarge hcap
  constructor <;> linarith [hc.1,hc.2]

end SevenEighths.CenteredMomentEnergyReferenceState

end

end OAI
end OAIOriginalModule2448

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceReflection
Source SHA256: 1f7f4353e86d2eb6f62439f0e30d7a0e303c1cb756afb3ad08ce225eb857de28
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2449



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=>HeckeFamily.O

lemma conductorFactor_pos : 0<(fixedConductorFactor:ℝ):=by
  unfold fixedConductorFactor
  norm_cast
  apply Nat.mul_pos
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero))
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))

theorem natural_reference_reflection (a b bΦ epsilon xi saving L:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B J:ℕ)(hB:2≤B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→Finset (Ideal O))
        (β:α→Ideal O→ℂ)(P:α→ℝ)(t along bshort E:ℝ),
      s.width≤L+along → 0≤E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,S,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P t along bshort E hlength hE hchildren
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=by dsimp [Src];positivity
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=by
    apply (hprofile Wlong hsLong t).trans
    dsimp [Src]
    gcongr
    linarith
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=>G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=>t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=>hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=>hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceReflection

end

end OAI
end OAIOriginalModule2449

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors
Source SHA256: 2dc5c493fd69cacb1014012b3602c8753c260c3e748cf8b35efd68a3066f5042
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2450


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceDivisors
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1<Z)(hY:0<Y)(hN:0<N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(L Y:ℝ)(hwidth:s.width≤L)(hY:1≤Y)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

theorem balanced_divisor_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(L X₁ X₂ ell κ:ℝ)(hwidth:s.width≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hlarge:5*s.width/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ)
    let long:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    -Bmask≤short ∧ -Bmask≤long ∧ s.width≤(L+Bmask)+long ∧
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^long=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hfirst:Real.logb Z (comparisonFirst Z s.width)=s.width/4:=by
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hs:=divisor_reflection_range s hZ L (comparisonFirst Z s.width) hwidth hg.2.1 D₁ hD₁
  have hl:=divisor_reflection_range s hZ L (comparisonSecond Z s.width X₁ X₂) hwidth
    (hg.2.1.trans hg.2.2.1) D₂ hD₂
  dsimp only at hs hl ⊢
  rw [hfirst] at hs
  rw [hg.2.2.2.1] at hl
  exact ⟨hs.1,hl.1,hl.2.1,hs.2.2,hl.2.2⟩

end SevenEighths.CenteredMomentEnergyReferenceDivisors

end

end OAI
end OAIOriginalModule2450

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous
Source SHA256: 175bf9bcb04aa126b04727bde84cbffa78f8ef5af86b697118c16bab5969764d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2451


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceHomogeneous
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceReflection CenteredMomentFiniteProfileExceptional

theorem natural_reference_reflection_homogeneous (a b bΦ epsilon xi saving L:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B J:ℕ)(hB:2≤B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→Finset (Ideal O))
        (β:α→Ideal O→ℂ)(P:α→ℝ)(t along bshort E:ℝ),
      s.width≤L+along → 0≤E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P t along bshort E hlength hE hchildren
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,summand,radialEnergy]
  have hpos:0<sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=>G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=>t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=>hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=>hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceHomogeneous

end

end OAI
end OAIOriginalModule2451

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneousError
Source SHA256: 27d71aae811f0a177bde0bc0d60795ef6bfda51f1bebba0087b85638a1071458
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2452



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceHomogeneousError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalReflectionErrorMass CenteredMomentNaturalFixedRaySource
open CenteredMomentOriginalRadialComparison CenteredMomentUniformReflectionProfile
open CenteredMomentCounting CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem natural_remaining_homogeneous_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort 1 b M*Bshort^2*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (hM j (hT hj)) (hP j hj) (hβ j hj) (hs j hj)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc₀ : (128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hT (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    unfold errorConstant
    simp only [mul_one]
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M*Bshort^2 := by
    calc
      _=((128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*Bshort^2:=by ring
      _≤_:=mul_le_mul_of_nonneg_right hc₀ (sq_nonneg Bshort)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ (errorConstant F bshort 1 b M*Bshort^2)*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
    _ = _ := by ring

theorem natural_reference_error_homogeneous {α:Type*}(F:Finset α)(bshort:ℝ)(b M:α→ℝ)
    (hM:∀i∈F,0≤M i):
    ∃C:ℝ,0<C ∧ ∀(T:Finset α),T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→Character)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) →
      (∀i∈T,∀I∈pool i,Prime I) →
      (∀i∈T,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈T,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  refine ⟨errorConstant F bshort 1 b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT W hsW χ pool β P t X K Φ keep hX hK hP hp hβ hs hΦ
  let A:=(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W
  have hA:0≤A:=apply_nonneg _ _
  have hWA:∀x,‖W x‖≤A:=SchwartzMap.norm_le_seminorm ℝ W
  let R:=fun z:O=>polynomial (χ z) false W X 0 t *
    ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)
  let V:=errorConstant F bshort 1 b M*A^2*X*∏i∈T,P i
  have hV:0≤V:=by
    dsimp only [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg (errorConstant_pos F bshort 1 b M).le
      (sq_nonneg A)) hX.le) (Finset.prod_nonneg (fun i hi=>(hP i hi).le))
  have hr(z:O):‖R z‖^2≤V:=by
    have hh:=natural_remaining_homogeneous_bound F T hT W bshort A b M hA hM hWA hsW
      (χ z) pool (fun i=>heightCoefficient (β i) t) P X t hX hP
      (fun i hi I hI=>by rw [heightCoefficient_norm _ _ _ (hp i hi I hI).ne_zero];exact hβ i hi I hI)
      (fun i hi I hI hn=>hs i hi I hI (left_ne_zero_of_mul hn))
    exact hh
  have hsum:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
  apply (radialEnergy_le_absolute_mass R keep Φ K hΦ hsum).trans
  calc
    _≤∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*V:=hsum.tsum_le_tsum
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
    _=(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=tsum_mul_right
    _≤(diagonalControl Φ*max 1 K)*V:=mul_le_mul_of_nonneg_right
      (radial_weight_lattice_bound_all Φ K hK) hV
    _=_:=by dsimp [V,A];ring

end SevenEighths.CenteredMomentEnergyReferenceHomogeneousError

end

end OAI
end OAIOriginalModule2452

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceScalarBounds
Source SHA256: de02784a2f1354d7134882c01b9a2b1071def5af974e1bd0141fa19d62762d1e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2453


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarBounds
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource

lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(d:ℝ)(hd:0≤d):
    (s.puncture.radical.absNorm:ℝ)^d≤Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤Mcap)(hd:0≤d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤Mcap:=s.width_nonneg.trans hs
  have hz:1≤Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma radial_scale {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    max 1 s.radial.scale≤Z^s.width:=by
  rw [s.scale_eq]
  apply max_le (Real.one_le_rpow s.base_ge_one s.width_nonneg)
  apply Real.rpow_le_rpow_of_exponent_le s.base_ge_one
  exact le_add_of_nonneg_right s.character_nonneg

lemma physical_slot_product {α:Type*}[Fintype α](Z:ℝ)(hZ:1≤Z)(w:α→ℝ)(Mcap:ℝ)
    (hwidth:(∑i,w i)≤Mcap): (∏i,Z^(w i))≤Z^Mcap:=by
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ hwidth

lemma short_slot_mass {α:Type*}[Fintype α]{Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap:ℝ)(hs:s.width≤Mcap)(w:α→ℝ)(hwidth:(∑i,w i)≤Mcap):
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))≤Z^(s.width+5*Mcap/4):=by
  have hz:0<Z:=zero_lt_one.trans_le s.base_ge_one
  calc
    _≤Z^s.width*Z^(Mcap/4)*Z^Mcap:=by
      apply mul_le_mul (mul_le_mul (radial_scale s)
        (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (physical_slot_product Z s.base_ge_one w Mcap hwidth)
        (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg hz.le _)) (by positivity)
    _=Z^(s.width+5*Mcap/4):=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

lemma log_interval (Z L d:ℝ)(hZ:1≤Z)(hL:0≤L)(hd:0<d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

end SevenEighths.CenteredMomentEnergyReferenceScalarBounds

end

end OAI
end OAIOriginalModule2453

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
Source SHA256: 6030ffd0e471ca53c2278286c0b5a9d82bc4f10c4cfeae5da84d96d0b3b0be92
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2454


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d saving ε:ℝ)
    (hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+2)≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBpos:0<B:=by dsimp only [B];positivity
  refine ⟨1+A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs α inst w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:=short_slot_mass s Mcap hs w hw
  have hdirect:(s.puncture.radical.absNorm:ℝ)^d*Z^(s.width+d)≤Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*Z^(s.width+d):=mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hz.le _)
      _=Z^(s.width+d*(Bmask+1)):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+d))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+d)):=by
        gcongr
      _=A^d*B*Z^(s.width+d*(Bmask+Mcap+2)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+d)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herrorTerm:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
        max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _=(s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          (max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))):=by ring
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by
        gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤Z^(s.width+ε)+A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add (add_le_add hdirect hreflect) herrorTerm
    _=_:=by ring

theorem exists_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let d:=ε/(4*(Bmask+Mcap+2))
  let xi:=rho/100
  let saving:=2*Mcap+Bmask*d+2*Mcap*d+1
  let L:=Mcap+Bmask+xi+1
  have hd:0<d:=by dsimp only [d];positivity
  have hxi:0<xi:=by dsimp only [xi];positivity
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hL:0≤L:=by dsimp only [L];positivity
  have hmain:d*(Bmask+Mcap+2)≤ε:=by
    dsimp only [d]
    have hp:0<Bmask+Mcap+2:=by positivity
    field_simp
    nlinarith
  have herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hledger⟩:=ledger_bound Mcap Bmask bΦ L d saving ε hM hB hL hd hmain herror
  exact ⟨d,xi,saving,L,C,hd,hxi,hsave,hC,le_rfl,by dsimp only [L];linarith,hledger⟩

end SevenEighths.CenteredMomentEnergyReferenceScalarReserve

end

end OAI
end OAIOriginalModule2454

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceSource
Source SHA256: 2b3caf3abe72ad618ee8590d36efafa503d1f6e96df9854d31acd4a5aa8bed7b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2455


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceSource
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def signedCommonSource {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(z:O):ℂ:=
  let χ:=naturalCharacter s.character z
  let R:=CompletedGauss.primeSupport s.puncture
  ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈(Finset.univ:Finset α).powerset,
    signedCoefficient χ R D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
      (polynomial χ false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
       polynomial χ false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
       ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i))

lemma original_row_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(z:O)(hz:z≠0):
    positiveSlotRow s.character s.mask 1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=by
  have hh:=original_positive_deletion s.character z hz s.puncture s.puncture_ne_zero
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool hp β P hP t X₁ X₂ hX₁ hX₂
  dsimp only at hh
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t] at hh
  simpa only [NaturalState.mask,signedCommonSource,naturalCharacter_eq s.character z hz] using hh

theorem original_energy_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale=
    radialEnergy (signedCommonSource s W₁ W₂ pool β P t X₁ X₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  change _=radialEnergy _ (effectiveRadial s.radial).keep _ _
  rw [radialEnergy_effective]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:s.radial.keep z
  · simp only [ite_eq_left hz]
    rw [original_row_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂
      z (s.row_ne_zero z hz),norm_mul,norm_mul,
      positive_height_phase_norm X₁ t hX₁,positive_height_phase_norm X₂ t hX₂,one_mul,one_mul]
  · simp only [ite_eq_right hz]

end SevenEighths.CenteredMomentEnergyReferenceSource

end

end OAI
end OAIOriginalModule2455

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceWeightedEnergy
Source SHA256: fe4592de6b36fad4f06a6b254e152da63b9438da13bd652b0353c595bc6ca418
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2456


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceWeightedEnergy
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison
local notation "O"=>HeckeFamily.O

lemma finite_weighted_energy {ι κ:Type*}[Fintype ι][Fintype κ]
    (a f:ι→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤q j)
    (ha:∀i j,‖a i j‖≤ρ j)(E:ℝ)(hE:0≤E)
    (hf:∀j,∑i,‖f i j‖^2≤E*(q j)^2):
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j*q j)^2*E:=by
  have hb(j:κ):(∑i,‖a i j*f i j‖^2)≤(ρ j*q j*Real.sqrt E)^2:=by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2:=Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2):=(Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*(E*(q j)^2):=mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_:=by rw [mul_pow,Real.sq_sqrt hE];ring
  have hh:=CompletedGauss.finite_tsum_energy_bound (fun j i=>a i j*f i j)
    (fun j=>ρ j*q j*Real.sqrt E) (fun j=>mul_nonneg (mul_nonneg (hρ j) (hq j)) (Real.sqrt_nonneg E))
    (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

theorem radial_weighted_energy {κ:Type*}[Fintype κ]
    (a f:O→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤q j)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K E:ℝ)
    (hΦ:∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (ha:∀z,keep z→∀j,‖a z j‖≤ρ j)(hE:0≤E)
    (hs:∀j,Summable (fun z:O=>if keep z then ‖f z j‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0))
    (hf:∀j,radialEnergy (fun z=>f z j) keep Φ K≤E*(q j)^2):
    radialEnergy (fun z=>∑j,a z j*f z j) keep Φ K≤(∑j,ρ j*q j)^2*E:=by
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let w(z:S):ℂ:=(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=finite_weighted_energy (fun z:S=>a z) (fun z:S=>fun j=>f z j*w z) ρ q hρ hq
    (fun z=>ha z (Finset.mem_filter.mp z.property).2) E hE ?_
  · have hsum(z:S):(∑j,a z j*(f z j*w z))=(∑j,a z j*f z j)*w z:=by
      rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro j _;ring
    simp_rw [hsum] at hh
    dsimp only [w] at hh
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>∑j,a z j*f z j) Φ K hΦ] at hh
    exact hh
  · intro j
    dsimp only [w]
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>f z j) Φ K hΦ]
    exact ((hs j).sum_le_tsum rows (fun z _=>by
      split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans (hf j)

end SevenEighths.CenteredMomentEnergyReferenceWeightedEnergy

end

end OAI
end OAIOriginalModule2456

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
Source SHA256: 59099173356976dd46dbe2da258e91064989c602748d3b2660281a6d5d168dcd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2457



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceSource CenteredMomentEnergyReferenceWeightedEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem original_energy_weighted_deletion (bslot M:α→ℝ)(hM:∀i,0≤M i)
    (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ a b:ℝ)(s:NaturalState Z Bmask bΦ)
      (W₁ W₂:𝓢(ℝ,ℂ)),0<a → 0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X₁ X₂ E p:ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0<P i) →
      (∀i,∀I∈pool i,‖β i I‖≤M i) →
      (∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤bslot i*P i) →
      0<X₁ → 0<X₂ → 0≤E → p≤1 →
      (∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀J∈(Finset.univ:Finset α).powerset,
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
          polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
          ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i)
            (heightCoefficient (β i) t) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
            ≤E*((∏I∈D₂,I).absNorm:ℝ)^p) →
      energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤C*(s.puncture.radical.absNorm:ℝ)^ε*E:=by
  obtain ⟨C,hC,hmass⟩:=CenteredMomentEnergyReferenceDeletionBudget.weighted_uniform_mass_subpower
    (Finset.univ:Finset α) bslot M (fun i _=>hM i) (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z Bmask bΦ a b s W₁ W₂ ha hb hs₁ hs₂ pool β P t X₁ X₂ E p hp hP hβ hs hX₁ hX₂ hE hple hchildren
  let R:=CompletedGauss.primeSupport s.puncture
  have hR:∀I∈R,Prime I:=support_prime s.puncture
  let κ:={D:Finset (Ideal O)//D∈R.powerset}×
    {D:Finset (Ideal O)//D∈R.powerset}×{J:Finset α//J∈(Finset.univ:Finset α).powerset}
  let cf(z:O)(j:κ):=signedCoefficient (naturalCharacter s.character z) R j.1.val j.2.1.val j.2.2.val
    pool (fun i=>heightCoefficient (β i) t) P
  let f(z:O)(j:κ):=polynomial (naturalCharacter s.character z) false W₁
    (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) 0 t *
    polynomial (naturalCharacter s.character z) false W₂
    (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) 0 t *
    ∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
      (heightCoefficient (β i) t) (P i)
  let ρ(j:κ):=uniformMajorant R j.1.val j.2.1.val j.2.2.val bslot M
  let q(j:κ):=((∏I∈j.2.1.val,I).absNorm:ℝ)^(p/2)
  have hρ(j:κ):0≤ρ j:=uniformMajorant_nonneg _ _ _ _ _ _ (fun i _=>hM i)
  have hq(j:κ):0≤q j:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn(D:Finset (Ideal O))(hD:D∈R.powerset):0<((∏I∈D,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hi=>(hR I (Finset.mem_powerset.mp hD hi)).ne_zero)))
  have hcf(z:O)(j:κ):‖cf z j‖≤ρ j:=by
    apply signedCoefficient_uniform _ R hR _ _ (Finset.mem_powerset.mp j.1.property)
      (Finset.mem_powerset.mp j.2.1.property) _ pool (fun i=>heightCoefficient (β i) t) P bslot M
      (fun i _=>hp i) (fun i _=>hP i) (fun i _=>hM i)
    · intro i _ I hI
      rw [heightCoefficient_norm _ _ _ (hp i I hI).ne_zero]
      exact hβ i I hI
    · intro i _ I hI hnz
      exact hs i I hI (left_ne_zero_of_mul hnz)
  have hsum(j:κ):Summable (fun z:O=>if (effectiveState s).radial.keep z then
      ‖f z j‖^2*(s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)).re else 0):=by
    obtain ⟨B,hB,hbound⟩:=slots_bounded (Finset.univ\j.2.2.val) pool (fun i=>heightCoefficient (β i) t) P
    exact pair_radial_summable (naturalCharacter s.character)
      (fun z=>∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (β i) t) (P i)) (fun _=>t) (fun _=>t) W₁ W₂ a b a b
      (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) B hb hb
      (div_pos hX₁ (hn _ j.1.property)) (div_pos hX₂ (hn _ j.2.1.property)) hs₁ hs₂
      (fun z=>hbound _) (effectiveState s).radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
  have hchild(j:κ):radialEnergy (fun z=>f z j) (effectiveState s).radial.keep
      s.radial.profile s.radial.scale≤E*(q j)^2:=by
    have hh:=hchildren j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property
    have hpow:(q j)^2=((∏I∈j.2.1.val,I).absNorm:ℝ)^p:=by
      dsimp only [q]
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      norm_num
    rw [hpow]
    exact hh
  have he:=radial_weighted_energy cf f ρ q hρ hq (effectiveState s).radial.keep s.radial.profile
    s.radial.scale E s.radial.nonneg (fun z _=>hcf z) hE hsum hchild
  have hid(z:O):(∑j:κ,cf z j*f z j)=signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=
    triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>signedCoefficient (naturalCharacter s.character z) R D₁ D₂ J
        pool (fun i=>heightCoefficient (β i) t) P *
        (polynomial (naturalCharacter s.character z) false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
         polynomial (naturalCharacter s.character z) false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
         ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i) (heightCoefficient (β i) t) (P i)))
  simp_rw [hid] at he
  rw [←original_energy_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂] at he
  have hm:(∑j:κ,ρ j*q j)≤C*((∏I∈R,I).absNorm:ℝ)^(ε/2):=by
    exact (triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J bslot M*((∏I∈D₂,I).absNorm:ℝ)^(p/2))).trans_le
      (hmass R hR (p/2) (by linarith))
  have hr:(((∏I∈R,I).absNorm:ℝ)^(ε/2))^2=(s.puncture.radical.absNorm:ℝ)^ε:=by
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  exact he.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>mul_nonneg (hρ j) (hq j))) hm 2) hE).trans_eq
    (by rw [mul_pow,hr]))

end SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy

end

end OAI
end OAIOriginalModule2457

/-! Original module: OAI.NumberTheory.DirichletL.Energy.StageReserve
Source SHA256: e173967b9f82d94b8d40dcf2457a517952121d9e753e654650d3879993f6df73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2458


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserve
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarReserve

theorem exists_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hze:1≤Z^e:=Real.one_le_rpow hZ he
  have hp:Z^(s.width+e)≤Z^e*Z^(s.width+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  let A:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))
  let B:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hLp:0≤L:=by linarith
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hA:0≤A:=by dsimp [A];positivity
  have hB0:0≤B:=by dsimp [B];positivity
  have hb:B≤Z^e*B:=by nlinarith
  have hh:=add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hp hA)) hb
  have hrad:0≤(s.puncture.radical.absNorm:ℝ)^d:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh':=(mul_le_mul_of_nonneg_left hh hrad)
  have hend:=mul_le_mul_of_nonneg_left (hledger Z hZ s hwidth α w hw)
    (Real.rpow_nonneg hz.le e)
  calc
    _≤Z^e*((s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+d)+A*Z^(s.width+d)+B)):=by
      convert hh' using 1 ; dsimp [A,B] ; ring
    _≤Z^e*(C*Z^(s.width+ε)):=by
      exact hend
    _=C*Z^(s.width+e+ε):=by
      rw [mul_left_comm,←Real.rpow_add hz]
      congr 2
      ring

lemma inherited_loss_budget (incoming overhead final:ℝ)
    (hin:incoming≤final/2)(hover:overhead≤final/2):incoming+overhead≤final:=by
  linarith

end SevenEighths.CenteredMomentEnergyStageReserve

end

end OAI
end OAIOriginalModule2458

/-! Original module: OAI.NumberTheory.DirichletL.Energy.StageReserveBounded
Source SHA256: b5ad381c8e1db808fc48de34dab0eef968a3eca9426b0ace5fd407ebfa36be95
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2459


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyStageReserve

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,Mcap+Bmask+xi,C,hd,hxi,hs,hC,hxr,le_refl _,by linarith,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  apply le_trans _ (hledger e he Z hZ s hwidth α w hw)
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hLp:0≤Mcap+Bmask+xi:=by linarith
  gcongr

end SevenEighths.CenteredMomentEnergyStageReserveBounded

end

end OAI
end OAIOriginalModule2459

/-! Original module: OAI.NumberTheory.DirichletL.Energy.BackwardSourceRanges
Source SHA256: f0ce11cd963df6bfcea297294fcbb1bbe4857ee7055c7f438ad408af5e690c18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2460



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBackwardSourceRanges
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyProfiles
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentEnergyStageReserveBounded

def lengthAt (M B L:ℝ)(depth k:ℕ):ℝ:=range M B L (depth-k)
def lowerAt (a b:ℝ)(depth k:ℕ):ℝ:=lower a b (depth-k)

lemma previous_length (M B L:ℝ)(depth k:ℕ)(hk:k<depth):
    lengthAt M B L depth k=CenteredMomentEnergyWidthRanges.step M B
      (lengthAt M B L depth (k+1)):=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lengthAt,hn,range]

lemma previous_lower (a b:ℝ)(depth k:ℕ)(hk:k<depth):
    lowerAt a b depth k=lowerAt a b depth (k+1)/max 1 b:=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lowerAt,hn,lower]

lemma length_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    0≤lengthAt M B L depth k:=range_nonneg M B L hM hB _

lemma original_length (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    L≤lengthAt M B L depth k:=range_original M B L hM hB _

lemma lower_positive (a b:ℝ)(ha:0<a)(depth k:ℕ):0<lowerAt a b depth k:=
  lower_pos a b ha _

theorem profile_step_support (a b:ℝ)(ha:0<a)(depth k:ℕ)(hk:k<depth)
    (W:Test (lowerAt a b depth (k+1)) b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Function.support
      ((CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).profile:ℝ→ℂ)
      ⊆Set.Icc (lowerAt a b depth k) b:=by
  rw [previous_lower a b depth k hk]
  exact (CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).support

theorem previous_admits (M B L stageCap rho d e Lref:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)(hd:d≤1)(he:e≤1)
    (depth k:ℕ)(hk:k<depth)(hLref:Lref≤stageCap+B+rho/100):
    lengthAt M B L depth (k+1)≤lengthAt M B L depth k ∧
    Lref≤lengthAt M B L depth k ∧
    max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1≤lengthAt M B L depth k ∧
    2*lengthAt M B L depth (k+1)+e≤lengthAt M B L depth k ∧
    2*(max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1)+e≤lengthAt M B L depth k:=by
  have h:=step_admits M B (lengthAt M B L depth (k+1)) rho d e hM hB
    (length_nonneg M B L hM hB depth (k+1)) hrho hd he
  rw [previous_length M B L depth k hk]
  refine ⟨h.1,?_,?_,h.2.2.2.1,?_⟩
  · exact (show Lref≤M+B+rho/100+1 by linarith).trans h.2.1
  · have hm:max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)≤
        max (lengthAt M B L depth (k+1)) (M+B+2*d):=max_le_max_left _ (by linarith)
    linarith only [hm,h.2.2.1]
  · apply le_trans _ h.2.2.2.2
    gcongr

lemma paired_contours (M B L stageCap rho L₁ L₂:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)
    (depth k:ℕ)(hk:k<depth)
    (h₁:L₁≤stageCap+B+rho/100)(h₂:L₂≤stageCap+B+rho/100):
    max L₁ L₂≤lengthAt M B L depth k:=
  (previous_admits M B L stageCap rho 0 0 (max L₁ L₂) hM hB hstage hrho
    (by norm_num) (by norm_num) depth k hk (max_le h₁ h₂)).2.1

lemma source_cap_uniform (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    sourceCap M B L (depth-k)≤sourceCap M B L depth:=by
  have h:=range_mono M B L hM hB (Nat.sub_le depth k)
  unfold sourceCap
  linarith

lemma scheduled_source_cap (M B L ε:ℝ)(hM:0≤M)(hB:0≤B)(k:ℕ):
    sourceCap M B L (count M ε-k)≤finalSourceCap M B L ε:=
  source_cap_uniform M B L hM hB _ _

theorem actual_reference_reserve_previous
    (M B L stageCap rho ε bΦ:ℝ)(hM:0≤M)(hB:0≤B)(hstage0:0≤stageCap)
    (hstage:stageCap≤M)(hrho:0<rho)(hrho1:rho≤1)(hε:0<ε)
    (depth k:ℕ)(hk:k<depth):
    ∃d xi saving Lref C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ stageCap+B+xi≤Lref ∧ Lref≤stageCap+B+rho/100 ∧
      Lref≤lengthAt M B L depth k ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z B bΦ,s.width≤stageCap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤stageCap →
      (s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(Lref*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,hledger⟩:=
    exists_bounded_separated_reference_reserve rho ε stageCap B bΦ hrho hε hstage0 hB
  refine ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,?_,hledger⟩
  exact (previous_admits M B L stageCap rho 0 0 Lref hM hB hstage hrho1
    (by norm_num) (by norm_num) depth k hk hLu).2.1

end SevenEighths.CenteredMomentEnergyBackwardSourceRanges

end

end OAI
end OAIOriginalModule2460

/-! Original module: OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule
Source SHA256: 412602f7f94d069ed7a65edd720f252deabdafccea322e8cdc589ba22cc45d9c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2461



namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

def stageLoss (M B ε:ℝ)(k:ℕ):ℝ:=ε/1000+loss M B ε k

lemma stageLoss_pos (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<stageLoss M B ε k:=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  unfold stageLoss loss
  positivity

lemma stageLoss_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤count M ε):stageLoss M B ε k≤ε/500:=by
  have hh:=loss_le_final M B κ ε hM hB hκ hε k hk
  unfold stageLoss
  linarith

lemma successor_with_references (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other highReflection zeroReflection:ℝ)
    (her:er≤reserve M B ε)(hd:d≤reserve M B ε)(he:e≤reserve M B ε)
    (hd1:d1≤reserve M B ε)(hd2:d2≤reserve M B ε)(ht:theta≤reserve M B ε)
    (ho:other≤48*reserve M B ε)
    (hhigh:highReflection≤reserve M B ε)(hzero:zeroReflection≤reserve M B ε):
    stageLoss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+
      other+highReflection+zeroReflection≤stageLoss M B ε (k+1):=by
  have hh:=next_paid_loss M B κ ε hM hB hκ hε k er d e d1 d2 theta
    (other+highReflection+zeroReflection) her hd he hd1 hd2 ht (by linarith)
  unfold stageLoss
  linarith

lemma one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(sourceLoss extra:ℝ)(hsource:sourceLoss≤ε/1000)
    (hextra:extra≤50*reserve M B ε):
    sourceLoss+extra≤stageLoss M B ε (k+1):=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have hk:0≤(k:ℝ):=Nat.cast_nonneg _
  simp only [stageLoss,loss,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma actual_one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(df es d theta other A extra:ℝ)
    (hdf:df≤reserve M B ε)(hes:es≤reserve M B ε)(hd:d≤reserve M B ε)
    (ht:theta≤reserve M B ε)(ho:other≤reserve M B ε)(he0:0≤es)(hA:A≤M)
    (hextra:extra≤50*reserve M B ε):
    CenteredMomentSuccessorPaidParameters.exceptional (amplification ε) df es d B theta+extra≤
      stageLoss M B ε (k+1) ∧
    CenteredMomentSuccessorPaidParameters.diagonal (amplification ε) d other es A+extra≤
      stageLoss M B ε (k+1):=by
  have hh:=one_time_losses M B κ ε hM hB hκ hε df es d theta other A hdf hes hd ht ho he0 hA
  exact ⟨one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.1 hextra,
    one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.2 hextra⟩

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI
end OAIOriginalModule2461

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FirstStageLossBudget
Source SHA256: c042eb1b3bb2f4ddb73078995e815c0471173ebf3e01260ba61abb6a177cb8ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2462




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

def sourcePaid (Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh:ℝ):ℝ:=
  (Bcap+Bcap)*emask+ell+er+(delta+reserveAmp+thetaSource)/6+thetaClip/3+κ*mesh

theorem literal_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(ell epsSrc epsMask deltaSrc thetaSrc deltaAmp reserveAmp thetaSource thetaClip
      er primeLoss physicalLoss highReflection zeroReflection saving:ℝ)
    (hell:ell≤stageLoss M Bcap ε k)
    (he0:0≤epsSrc)(he:epsSrc≤reserve M Bcap ε)
    (hemask:(Bcap+Bcap)*epsMask≤reserve M Bcap ε)
    (hdsrc:deltaSrc≤reserve M Bcap ε)(htsrc:thetaSrc≤reserve M Bcap ε)
    (hda:0≤deltaAmp)(hra:0≤reserveAmp)(hts:0≤thetaSource)(htc:0≤thetaClip)
    (hsmall:deltaAmp+reserveAmp+thetaSource≤reserve M Bcap ε)
    (hclip:thetaClip≤reserve M Bcap ε)(her:er≤reserve M Bcap ε)
    (hcommon:epsSrc*Bcommon≤reserve M Bcap ε)
    (hprime:primeLoss≤reserve M Bcap ε)(hphysical:physicalLoss≤reserve M Bcap ε)
    (hhigh:highReflection≤reserve M Bcap ε)(hzero:zeroReflection≤reserve M Bcap ε)
    (hsaving:2*amplification ε+deltaAmp+reserveAmp≤saving):
    ∀j:Fin 4,
      losses epsSrc deltaSrc thetaSrc Bcap j+
        lossVector (amplification ε) deltaAmp reserveAmp
          (sourcePaid Bcap epsMask ell er deltaAmp reserveAmp thetaSource thetaClip κ (mesh M Bcap κ ε))
          epsSrc M saving j+
        epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      stageLoss M Bcap ε (k+1):=by
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<reserve M Bcap ε:=hb.2.2.2.1
  have hs:0≤amplification ε:=hb.1.le
  have hother:epsSrc*Bcommon+primeLoss+physicalLoss≤48*reserve M Bcap ε:=by linarith
  have hextra:epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      50*reserve M Bcap ε:=by linarith
  have hdf:deltaAmp+reserveAmp≤reserve M Bcap ε:=by linarith
  have hdelta:deltaAmp≤reserve M Bcap ε:=by linarith
  have hres:reserveAmp≤reserve M Bcap ε:=by linarith
  have hmain:=successor_with_references M Bcap κ ε hM hB hκ hε k
    er deltaSrc epsSrc (deltaAmp+reserveAmp+thetaSource) ((Bcap+Bcap)*epsMask) thetaClip
    (epsSrc*Bcommon+primeLoss+physicalLoss) highReflection zeroReflection
    her hdsrc he hsmall hemask hclip hother hhigh hzero
  have hone:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaSrc thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdsrc htsrc hres he0 le_rfl hextra
  have hdiag:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaAmp thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdelta htsrc hres he0 le_rfl hextra
  have htail:=one_time_with_new_cost M Bcap κ ε hM hB hκ hε k 0
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection) (by positivity) hextra
  intro j
  fin_cases j <;> simp only [losses,lossVector,Matrix.cons_val,Fin.reduceFinMk]
  · dsimp [sourcePaid,edge] at hmain ⊢
    linarith
  · dsimp [exceptional] at hone
    linarith [hone.1]
  · dsimp [diagonal] at hdiag
    linarith [hdiag.2]
  · linarith

theorem chosen_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε;
    let es:=r/(Bcommon+1);
    let em:=r/(Bcap+Bcap+1);
    0<es ∧ es≤1 ∧ 0<em ∧ 0<r/4 ∧ 0<2*amplification ε+1 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
      highReflection≤r→zeroReflection≤r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es M (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<reserve M Bcap ε:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:reserve M Bcap ε≤amplification ε/100:=min_le_left _ _
  have hr1:reserve M Bcap ε≤1:=by linarith [hb.2.1]
  have hes:0<reserve M Bcap ε/(Bcommon+1):=by positivity
  have hem:0<reserve M Bcap ε/(Bcap+Bcap+1):=by positivity
  have hesle:reserve M Bcap ε/(Bcommon+1)≤reserve M Bcap ε:=by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hemscale:(Bcap+Bcap)*(reserve M Bcap ε/(Bcap+Bcap+1))≤reserve M Bcap ε:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hescale:(reserve M Bcap ε/(Bcommon+1))*Bcommon≤reserve M Bcap ε:=by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,hesle.trans hr1,hem,by positivity,by positivity,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero
  apply literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    (reserve M Bcap ε/(Bcommon+1)) (reserve M Bcap ε/(Bcap+Bcap+1))
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    highReflection zeroReflection (2*amplification ε+1)
    hell hes.le hesle hemscale
  all_goals first | exact hescale | exact hhigh | exact hzero | positivity | linarith

end SevenEighths.CenteredMomentEnergyFirstStageLossBudget

end

end OAI
end OAIOriginalModule2462

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FirstDeclaredCapacityLossBudget
Source SHA256: ce5d19aaaeef4f8b92580be6f2f40f2741783fd1c30e6efab03624771168f95e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2463


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

lemma lossVector_cap (sigma delta reserveAmp paid es M A saving:ℝ)
    (he:0≤es)(hM:0≤M)(hA:0≤A)(j:Fin 4):
    lossVector sigma delta reserveAmp paid es A saving j≤
      lossVector sigma delta reserveAmp paid es M saving j+es*A:=by
  fin_cases j <;> simp only [lossVector,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg he hM,mul_nonneg he hA]

theorem chosen_declared_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ es*A≤r/4 ∧ es*Bcommon≤r/4 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
      highReflection≤r→zeroReflection≤r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es A (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<r:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:r≤amplification ε/100:=min_le_left _ _
  have hr1:r≤1:=by linarith [hb.2.1]
  have hden:0<4*(Bcommon+A+1):=by positivity
  have hes:0<es:=by dsimp [es];positivity
  have hesle:es≤r/4:=by
    dsimp [es]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc,mul_nonneg hr.le hA]
  have hescap:es*A≤r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc]
  have hescommon:es*Bcommon≤r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hA]
  have hemscale:(Bcap+Bcap)*(r/(Bcap+Bcap+1))≤r:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,by linarith,by positivity,hescap,hescommon,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hh:=literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    es (r/(Bcap+Bcap+1)) (r/4) (r/4) (r/4) (r/4) (r/4) (r/4)
    (r/4) (r/4) (r/4+es*A) highReflection zeroReflection (2*amplification ε+1)
    hell hes.le (by dsimp [r] at *;linarith) hemscale
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    hhigh hzero (by linarith)
  have hc:=lossVector_cap (amplification ε) (r/4) (r/4)
    (sourcePaid Bcap (r/(Bcap+Bcap+1)) ell (r/4) (r/4) (r/4) (r/4) (r/4)
      κ (mesh M Bcap κ ε)) es M A (2*amplification ε+1) hes.le hM hA j
  have hj:=hh j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_
  linarith only [hj,hc]

end SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget

end

end OAI
end OAIOriginalModule2463

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FirstActualFrequencyBudget
Source SHA256: 96bd0011304aa7fdf771255697d9a02a32da573040a85bd0ecff91a81e2c200e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2464



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSectorLocalization

theorem eventually_frequency_loss (r:ℝ)(hr:0<r):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤r/4:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by positivity:0<r/8))) 128,
    eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  have hlog:=Real.logb_le_logb_of_le hZ (by norm_num:(0:ℝ)<128) hpow
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hlog
  refine ⟨hZ,frequencyLoss_nonneg Z 32 (r/4) hZ (by norm_num) (by positivity),?_⟩
  unfold frequencyLoss
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith only [hlog]

lemma paid_frequency_mono
    (sigma delta delta' reserveAmp Bcap emask ell er thetaSource thetaClip κ mesh
      es A saving:ℝ)(hd:delta≤delta')(j:Fin 4):
    lossVector sigma delta reserveAmp
      (sourcePaid Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh)
      es A saving j≤
    lossVector sigma delta' reserveAmp
      (sourcePaid Bcap emask ell er delta' reserveAmp thetaSource thetaClip κ mesh)
      es A saving j:=by
  fin_cases j <;>
    simp only [lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    linarith only [hd]

theorem actual_frequency_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ 0<r/4 ∧ r/4≤amplification ε/4 ∧
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤r/4 ∧
      ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
        highReflection≤r→zeroReflection≤r→∀j:Fin 4,
        losses es (r/4) (r/4) Bcap j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            (sourcePaid Bcap em ell (r/4) (frequencyLoss Z 32 (r/4))
              (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
            es A (2*amplification ε+1) j+
          es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  let em:=r/(Bcap+Bcap+1)
  obtain ⟨hes,hes1,hem,_,_,hbudget⟩:=chosen_declared_four_budget M A Bcap Bcommon κ ε
    hM hA hB hBc hκ hε
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<r:=hb.2.2.2.1
  have hrs:r≤amplification ε/100:=min_le_left _ _
  refine ⟨hes,hes1,hem,by positivity,by linarith [hb.1],?_⟩
  filter_upwards [eventually_frequency_loss r hr] with Z hZ
  refine ⟨hZ.1,hZ.2.1,hZ.2.2,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hfixed:=hbudget k ell highReflection zeroReflection hell hhigh hzero j
  have hmono:=paid_frequency_mono (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
    (r/4) Bcap em ell (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε) es A
    (2*amplification ε+1) hZ.2.2 j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_ at hfixed ⊢
  linarith only [hfixed,hmono]

end SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget

end

end OAI
end OAIOriginalModule2464

/-! Original module: OAI.NumberTheory.DirichletL.Energy.StageMargins
Source SHA256: c1ea4cc1264ad298f734639488564ffbdf27791b6d7249d949b39db9f774527d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2465


namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

def physicalLoss (M B ε:ℝ)(k:ℕ):ℝ:=stageLoss M B ε (k+1)-2*reserve M B ε
def reflectedLoss (M B ε:ℝ)(k:ℕ):ℝ:=physicalLoss M B ε k+reserve M B ε

lemma physicalLoss_eq (M B ε:ℝ)(k:ℕ):
    physicalLoss M B ε k=stageLoss M B ε k+62*reserve M B ε:=by
  unfold physicalLoss stageLoss
  rw [loss_succ]
  ring
lemma reflected_then_zero (M B ε:ℝ)(k:ℕ):
    reflectedLoss M B ε k+reserve M B ε=stageLoss M B ε (k+1):=by
  unfold reflectedLoss physicalLoss
  ring
lemma margins (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<physicalLoss M B ε k ∧
    stageLoss M B ε k≤physicalLoss M B ε k ∧
    reserve M B ε/4≤physicalLoss M B ε k ∧
    physicalLoss M B ε k≤reflectedLoss M B ε k ∧
    reflectedLoss M B ε k≤stageLoss M B ε (k+1):=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have he:=stageLoss_pos M B κ ε hM hB hκ hε k
  have hp:=physicalLoss_eq M B ε k
  have hf:=reflected_then_zero M B ε k
  unfold reflectedLoss at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyStageMargins

end

end OAI
end OAIOriginalModule2465

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroComparison
Source SHA256: ec3c7562c4af189e67a674ee496677c8c1acd4518ec658f64995186e29e1a997
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2466



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

def smallScale (b:ℝ):ℝ:=1/(2*max 1 b)

lemma smallScale_pos (b:ℝ):0<smallScale b:=by unfold smallScale;positivity

lemma smallScale_le_one (b:ℝ):smallScale b≤1:=by
  unfold smallScale
  apply (div_le_iff₀ (by positivity:0<(2:ℝ)*max 1 b)).mpr
  linarith [le_max_left (1:ℝ) b]

lemma smallScale_strict (b:ℝ):smallScale b*b<1:=by
  have hm:0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  unfold smallScale
  have hb:=le_max_right (1:ℝ) b
  rw [div_mul_eq_mul_div,one_mul]
  exact (div_lt_iff₀ (mul_pos (by norm_num) hm)).mpr (by linarith)

def zeroData (s:Input ι):CenteredMomentEligibleEnergy.Data ι := { s.toData with
  Y₁ := smallScale s.b₁
  Y₂ := s.X₁*s.X₂/smallScale s.b₁
  Y₁_pos := smallScale_pos _
  Y₂_pos := div_pos (mul_pos s.X₁_pos s.X₂_pos) (smallScale_pos _)
  same_product := by field_simp [ne_of_gt (smallScale_pos s.b₁)] }

def zeroInput (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):Input ι :=
  completeInput (zeroData s) hz₁ hz₂ s.ν_bound s.W_bound s.lower s.upper
    s.lower_pos s.lower_le s.upper_ge

omit [DecidableEq ι] in
@[simp] lemma zeroInput_volume (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):
    volume (zeroInput s hz₁ hz₂)=volume s:=rfl

omit [DecidableEq ι] in
lemma comparison_row_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(z:O):
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂=0:=by
  unfold positiveSlotRow
  change _*(rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t (smallScale s.b₁)*_*_)=0
  rw [strict_subunit_rowTwistedSum_zero s.η (fixedBadMask*idealGenerator R) 1 z
    s.W₁ s.b₁ s.t (smallScale s.b₁) (smallScale_pos _) s.support₁ (smallScale_strict _)]
  simp only [zero_mul,mul_zero]

omit [DecidableEq ι] in
lemma comparison_energy_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
      r.keep r.profile r.scale=0:=by
  unfold CenteredMomentInductionEnergy.energy
  simp only [comparison_row_zero s hz₁ hz₂ R, norm_zero, zero_pow (by decide : (2:ℕ)≠0),
    zero_mul, ite_self, tsum_zero]

theorem actual_zero_comparison_entry (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
      (coefficient (zeroInput s hz₁ hz₂) R 1) r.profile r.scale‖/volume s:=by
  have hh:=positive_energy_comparison (zeroInput s hz₁ hz₂) R r
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
    s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_scale_caps (b L ε:ℝ)(hL:0≤L)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → s.X₁≤Z^L → s.X₂≤Z^L →
      (zeroInput s hz₁ hz₂).Y₁≤Z^(2*L+ε) ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(2*L+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hX₁ hX₂
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨(smallScale_le_one _).trans (Real.one_le_rpow hZ.le (by positivity)),?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hp:s.X₁*s.X₂≤Z^(2*L):=by
    have hh:=mul_le_mul hX₁ hX₂ s.X₂_pos.le (Real.rpow_pos_of_pos hZ0 L).le
    rw [←Real.rpow_add hZ0] at hh
    simpa only [two_mul] using hh
  have hconst:2*max 1 s.b₁≤Z^ε:=(mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    s.X₁*s.X₂*(2*max 1 s.b₁)≤Z^(2*L)*Z^ε:=
      mul_le_mul hp hconst (by positivity) (Real.rpow_pos_of_pos hZ0 _).le
    _=Z^(2*L+ε):=(Real.rpow_add hZ0 _ _).symm

end SevenEighths.CenteredMomentEnergyZeroComparison

end

end OAI
end OAIOriginalModule2466

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FixedRadialEntry
Source SHA256: 08ddc83b2e4305f83348fcd574baba45ad8b6402a62c2013c070bed981ae73cd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2467



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFixedRadialEntry
open ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSourceMass CenteredMomentSourceRectangleMask
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialSource CenteredMomentSourceRow
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentRadialEligibleEnergy
open CenteredMomentEnergyZeroComparison CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

theorem original_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀R:Ideal O,∀r:Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) Ψ r.scale‖/volume s+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=fixed_source b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s R r hr
  apply (positive_energy_comparison s R r).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (volume_pos s).le
  have h:=mul_le_mul_of_nonneg_left
    (hh r.profile hr s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.scale r.scale_pos)
    (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using h

theorem original_zero_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      ∀R:Ideal O,∀r:Radial,Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
          (coefficient (zeroInput s hz₁ hz₂) R 1) Ψ r.scale‖/volume s :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=original_comparison (ι:=ι) b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s hz₁ hz₂ R r hr
  have h:=hh (zeroInput s hz₁ hz₂) R r hr
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P
    (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂ r.keep r.profile r.scale at h
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at h
  exact h
end SevenEighths.CenteredMomentEnergyFixedRadialEntry

end

end OAI
end OAIOriginalModule2467

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
Source SHA256: aec168f5276f728078233b396e1a469e9618570ab8514488bea4aacc3e4f6d46
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2468



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFixedRadialReduction
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyFixedRadialEntry
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputFirstRemainder
open CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

theorem actual_original_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧ 0<Ctail ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:Radial),Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ→
      volume s≤Z^B→(r.scale)⁻¹≤Z^B→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass s R 1 fixedBadMask 1 Ψ r.scale Z ξ/volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving))+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Ψ,hs,hn,hentry⟩:=original_comparison (ι:=ι) bΦ hbΦ
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Ψ,hs,hn,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  have hsource:=hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 Ψ r.scale r.scale_pos hV hK
  have hpos:=hentry s R r hr
  have hdom:=mul_le_mul_of_nonneg_left hsource
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg r.profile))
  apply hpos.trans
  apply add_le_add _ le_rfl
  simpa only [mul_div_assoc, CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume] using hdom
end SevenEighths.CenteredMomentEnergyFixedRadialReduction

end

end OAI
end OAIOriginalModule2468

/-! Original module: OAI.NumberTheory.DirichletL.Energy.LowFixedRadialEntry
Source SHA256: 15fb5c8e9cd03a9a652c86ccfde99c1a39b5b1bbcba3445f49cacae56bafff1d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2469




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyLowFixedRadialEntry
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyOriginalSource
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentEnergyPhysicalEntry
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

omit [DecidableEq ι] in
lemma zero_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

theorem original_low_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(a b B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(ha:0<a)(hb:0≤b)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧0<Ctail ∧∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),∀he₁:s.W₁=W₁,∀he₂:s.W₂=W₂,
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      (∀i,s.hi i≤hi i) →∀(R:Ideal O)(r:Radial),
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume s≤Z^B → r.scale⁻¹≤Z^B →
      let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁;
      let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂;
      energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
        s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass (zeroInput s hz₁ hz₂) R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    bΦ hbΦ hi a b B ε ξ saving hhi ha hb hB hε hξ
  refine ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  dsimp only
  let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁
  let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂
  have hh:=hz.2 (zeroInput s hz₁ hz₂) W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  change energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
    s.P s.X₁ s.X₂ r.keep r.profile r.scale≤_+2*energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero,zeroInput_volume,zero_control] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_product_cap (b B ε:ℝ)(_hB:0≤B)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b →s.X₁*s.X₂≤Z^B →
      (zeroInput s hz₁ hz₂).Y₁≤1 ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(B+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hprod
  refine ⟨smallScale_le_one _,?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    _≤Z^B*Z^ε:=mul_le_mul hprod hconst (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le
    _=Z^(B+ε):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

omit [DecidableEq ι] in
theorem zero_comparison_first_log (b ε:ℝ)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → -ε≤Real.logb Z (zeroInput s hz₁ hz₂).Y₁ ∧
        Real.logb Z (zeroInput s hz₁ hz₂).Y₁≤0:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb
  change -ε≤Real.logb Z (smallScale s.b₁) ∧ Real.logb Z (smallScale s.b₁)≤0
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  have hlower:Z^(-ε)≤smallScale s.b₁:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
    simpa only [smallScale,one_div] using one_div_le_one_div_of_le (by positivity) hconst
  refine ⟨?_,?_⟩
  · have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hlower
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  · have hh:=Real.logb_le_logb_of_le hZ (smallScale_pos s.b₁) (smallScale_le_one s.b₁)
    simpa only [Real.logb_one] using hh

end SevenEighths.CenteredMomentEnergyLowFixedRadialEntry

end

end OAI
end OAIOriginalModule2469

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReserve
Source SHA256: 623319508bc0b2e78de20fdb9eb0b9cf3be5768c192f36f109f5382260ef20ff
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2470


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d loss defect xi saving ε:ℝ)
    (_hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+1)+loss+defect+xi≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+L≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBp:0<B:=by dsimp [B];positivity
  refine ⟨A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:max 1 s.radial.scale≤Z^s.width:=by
    apply max_le (Real.one_le_rpow hZ s.width_nonneg)
    rw [s.scale_eq]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    exact le_add_of_nonneg_right s.character_nonneg
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+loss+defect+xi)):=by gcongr
      _=A^d*B*Z^(s.width+(d*(Bmask+Mcap+1)+loss+defect+xi)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+loss+defect+xi)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herr:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
        Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+L)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add hreflect herr
    _=_:=by ring

theorem exists_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      Loriginal≤L ∧ Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=ε/(8*(Bmask+Mcap+4))
  let L:=max Loriginal (Mcap+Bmask+d+d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=by dsimp [d];positivity
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+d+d)]
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by
    have heq:d*(Bmask+Mcap+4)=ε/8:=by
      dsimp only [d]
      field_simp
    nlinarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=ledger_bound Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  exact ⟨d,L,saving,C,hd,hL,hsave,hC,by dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+d+d)],
    by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+d+d)],hbound⟩

end SevenEighths.CenteredMomentEnergyZeroGrowthReserve

end

end OAI
end OAIOriginalModule2470

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ZeroReferenceError
Source SHA256: bfc3e1501fafffc552a057bb687513b10cb52748b16f2e5495d38f36db50a147
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2471


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceError
open HeckeFamily ConcreteTraceCRT HeckeDyadic QuadraticInitialBound
open CenteredMomentCommonMaskEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceHomogeneousError
local notation "O"=>HeckeFamily.O

theorem short_energy_bound (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),Function.support (W:ℝ→ℂ)⊆Set.Iic b →
      ∀(χ:O→Character)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),0<X →0<K →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*diagonalControl Φ*max 1 K*X:=by
  obtain ⟨C,hC,h⟩:=natural_reference_error_homogeneous (∅:Finset (Fin 0)) b
    (fun _=>0) (fun _=>0) (by simp)
  refine ⟨C,hC,?_⟩
  intro W hs χ t X K Φ keep hX hK hΦ
  have hh:=h ∅ (Finset.Subset.refl _) W hs χ (fun _=>∅) (fun _ _=>0)
    (fun _=>1) t X K Φ keep hX hK (by simp) (by simp) (by simp) (by simp) hΦ
  simpa only [Finset.prod_empty,mul_one] using hh

end SevenEighths.CenteredMomentEnergyZeroReferenceError

end

end OAI
end OAIOriginalModule2471

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Moments
Source SHA256: 42f8abfdd47817cedba7a079f6338efe9da4cb68e9189d86d49ef6f78a40e9f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2472



namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open ProbePhysical

def momentData (η : Character) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

def momentElement (u : FreeRow) : NonzeroElement := ⟨u.val,u.property.1⟩

theorem momentData_coeff (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I=
      idealCoeff η I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    idealCoeff_eq_row η ((momentData η).character (momentElement u)) rowMaskElement 1 u.val
      ((momentData η).character_spec (momentElement u)) I

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val∉S) :
    idealCoeff ((momentData η).character (momentElement u)) P.val=
      idealCoeff η P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,ite_eq_left hc,one_mul]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) I := by
  have he : idealCoeff (rowCharacter S hS u)=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=_
    rw [excludedTarget_prime]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,fixedSourcePrincipal_prime,ite_eq_left hP,zero_mul]
    · rw [ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP,
        momentData_prime_outside S hS hbad _ u P hP,
        fixedSourcePrincipal_prime,ite_eq_right hP,one_mul]
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((targetRow η u).excludePrimes S hS) I=
      conj (idealCoeff ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) I) := by
  have he : idealCoeff ((targetRow η u).excludePrimes S hS)=
      idealCoeff (((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)).inverse) := by
    apply hom_eq_of_primes
    intro P
    rw [idealCoeff_inverse_conj]
    change idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=_
    rw [target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,excludedTarget_prime,ite_eq_left hP,zero_mul,map_zero]
    · rw [ite_eq_right hP,momentData_prime_outside S hS hbad _ u P hP,
        excludedTarget_prime,ite_eq_right hP,idealCoeff_inverse_conj,map_mul]
      simp only [starRingEnd_self_apply]
  simpa only [idealCoeff_inverse_conj] using congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem numerator_moment_polynomial (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    HeckeDyadic.polynomial (rowCharacter S hS u) inv W D σ freq=
      HeckeDyadic.polynomial ((momentData (fixedSourcePrincipal S hS)).character
        (momentElement u)) inv W D σ freq :=
  HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
    (numerator_moment_coeff S hS hbad u) inv W D σ freq

theorem denominator_moment_norm (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖HeckeDyadic.polynomial ((targetRow η u).excludePrimes S hS) inv W D σ freq‖=
      ‖HeckeDyadic.polynomial ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) inv (fun x=>conj (W x)) D σ (-freq)‖ :=
  HeckeDetectorCoefficientTransfer.norm_of_oriented_coefficients _ _ true
    (denominator_moment_coeff S hS hbad η u) inv W D σ freq hD

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2472

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ReciprocalGrowth
Source SHA256: b49f57cf18afd6bf64e4e5a92cb7232bd0578c18441ba56f22397e0960fb6a64
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2473




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem targetRow_reciprocal_growth (e δ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤2) (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (x : ℂ),
      HeckeZeroSupremum.beta+8*e≤x.re →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*(3+|x.im|)^2 := by
  obtain ⟨D,hD,hmain⟩ := HeckeReciprocalGrowth.reciprocal_subpower e (δ/2) he he' (by linarith)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨D*(2:ℝ)^(δ/2)*(1+A^δ),by positivity,?_⟩
  intro η u x hx
  let q : ℝ := η.modulus.absNorm
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hq : 0≤q := by dsimp [q];positivity
  have hN : 0≤N := by dsimp [N];positivity
  have hQ : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤A*q*N := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [A,q,N]
    exact_mod_cast (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
  have hc := HeckeDyadic.presentationComplexity_le_of_modulus_le
    ((targetRow η u).excludePrimes S hS) (A*q*N) x.im hQ
  have ht : 0≤3+|x.im| := by positivity
  have hpow : (2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2)=
      (2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),
      ←Real.rpow_natCast_mul (mul_nonneg (mul_nonneg hA hq) hN),
      ←Real.rpow_natCast_mul ht]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(δ/2)=δ by ring,
      Real.mul_rpow (mul_nonneg hA hq) hN,Real.mul_rpow hA hq]
    ring
  have hbase := hmain ((targetRow η u).excludePrimes S hS) x hx
  calc
    _ ≤ D*(2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2) := by
      apply hbase.trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.rpow_le_rpow (by unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity;positivity) hc (by linarith)
    _ = D*(2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by rw [hpow];ring
    _ ≤ D*(2:ℝ)^(δ/2)*(1+A^δ)*q^δ*N^δ*(3+|x.im|)^2 := by
      have hh : (3+|x.im|)^δ≤(3+|x.im|)^2 := by
        simpa only [Real.rpow_ofNat] using
          (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x.im] : (1:ℝ)≤3+|x.im|) hδ')
      apply mul_le_mul _ hh (Real.rpow_nonneg ht δ) (by positivity)
      gcongr
      linarith

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2473

/-! Original module: OAI.NumberTheory.DirichletL.PrincipalMellinGrowth
Source SHA256: 3953720f4145fd60bdd494f1cf39c5fccac80cbad908db851806a08a3ee152de
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2474




namespace OAI

noncomputable section
open scoped Classical Topology
open Complex Set
namespace SevenEighths.PrincipalMellinGrowth
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

def principalConstant (M : Ideal HeckeFamily.O) : ℝ :=
  (1+HeckeLogarithmicInput.uniformConstant)*(M.absNorm : ℝ)^(3/5 : ℝ)*
    HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport M).card

theorem principalConstant_pos (M : Ideal HeckeFamily.O) [NeZero M] :
    0<principalConstant M := by
  have hQ : 0<(M.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  exact mul_pos (mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg])
    (Real.rpow_pos_of_pos hQ _)) (pow_pos (HeckeDeletionBounds.localBound_pos (by norm_num)) _)

lemma poleRemoved_eq_mul_regular (χ : Character) (hχ : χ.residue=1)
    {s : ℂ} (hs : s+1≠0) :
    HeckeOrigin.poleRemoved χ s=(s+1)*HeckeLogarithmicInput.regular χ s := by
  simp only [HeckeLogarithmicInput.regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized]
  field_simp

theorem principal_poleRemoved_growth (χ : Character) (hχ : χ.residue=1)
    {s : ℂ} (hs : (19/20 : ℝ)≤s.re) :
    ‖HeckeOrigin.poleRemoved χ s‖≤principalConstant χ.modulus*‖s+1‖*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue=1 := (HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mp hχ
  have hs0 : 0<s.re := by linarith
  have h0 : s≠0 := by intro hh; norm_num [hh] at hs
  have hplus : s+1≠0 := by
    intro hh
    have hr := congrArg Complex.re hh
    simp only [add_re,one_re,zero_re] at hr
    linarith
  have heq : HeckeOrigin.poleRemoved χ s=
      ((s+1)*HeckeLogarithmicInput.regular ψ s)*HeckeFiniteDeletion.factors χ.modulus ψ s := by
    rw [← poleRemoved_eq_mul_regular ψ hψ hplus]
    by_cases h1 : s=1
    · subst s
      rw [HeckeOrigin.poleRemoved_one,HeckeOrigin.poleRemoved_one]
      exact HeckeFiniteDeletion.regularizedL_eq_of_mask χ ψ hmask (by norm_num)
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeOrigin.poleRemoved_eq ψ h0 h1,
        HeckeFiniteDeletion.LFunction_eq_of_mask χ ψ hmask hs0 h1]
      ring
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ)≤s.re)
  have hd := (HeckeDeletionBounds.factors_bound_pow (19/20) (by norm_num)
    χ.modulus ψ hs).1
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hC := HeckeLogarithmicInput.uniformConstant_nonneg
  have hD := (HeckeDeletionBounds.localBound_pos (by norm_num : (0 : ℝ)<19/20)).le
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ (‖s+1‖*(HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport χ.modulus).card := by
      gcongr
    _ ≤ (‖s+1‖*((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport χ.modulus).card := by
      gcongr
      linarith
    _ = _ := by unfold principalConstant; ring

def wAmplitude (M : Ideal HeckeFamily.O) (cw : ℝ) : ℝ := 9*(cw+2)*principalConstant M

def zAmplitude (M : Ideal HeckeFamily.O) : ℝ := 216*principalConstant M

theorem wAmplitude_pos (M : Ideal HeckeFamily.O) [NeZero M] {cw : ℝ} (hcw : 1<cw) :
    0<wAmplitude M cw := by
  unfold wAmplitude
  exact mul_pos (mul_pos (by norm_num) (by linarith)) (principalConstant_pos M)

theorem zAmplitude_pos (M : Ideal HeckeFamily.O) [NeZero M] : 0<zAmplitude M := by
  unfold zAmplitude
  exact mul_pos (by norm_num) (principalConstant_pos M)

theorem fixed_principal_w_growth (M : Ideal HeckeFamily.O) [NeZero M]
    {cw : ℝ} (hcw : 1<cw) {x : ℝ} (hx : x∈Icc (19/20 : ℝ) cw) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤wAmplitude M cw*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(((x:ℂ)+t*I) : ℂ).re by simpa using hx.1)
  have hn : ‖((x:ℂ)+t*I)+1‖≤(cw+2)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    rw [abs_of_pos (by linarith [hx.1] : 0<x+1)]
    unfold height
    have hmul : 0≤(cw+1)*|t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith [hx.2]
  have hheight : (3+|t|)^2≤9*height t^2 := by
    have hh : 3+|t|≤3*height t := by unfold height; linarith [abs_nonneg t]
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+|t|) hh 2
    simpa only [mul_pow,show (3:ℝ)^2=9 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤
    principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|(((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  calc
    _ ≤ principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|t|)^2 := hb
    _ ≤ principalConstant M*((cw+2)*height t)*(9*height t^2) := by
      have hc2 : 0≤cw+2 := by linarith
      gcongr
    _ = _ := by unfold wAmplitude; ring

theorem fixed_principal_z_growth (M : Ideal HeckeFamily.O) [NeZero M]
    {e : ℝ} (he : 0<e) (he' : e≤2/3) {x : ℝ}
    (hx : x∈Icc (33/200 : ℝ) (1/6+e)) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤zAmplitude M*height t^3 := by
  have hre : (6*((x:ℂ)+t*I) : ℂ).re=6*x := by simp
  have him : (6*((x:ℂ)+t*I) : ℂ).im=6*t := by simp
  have habs : |(6*((x:ℂ)+t*I) : ℂ).im|=6*|t| := by rw [him,abs_mul]; norm_num
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((x:ℂ)+t*I) : ℂ).re by rw [hre]; linarith [hx.1])
  have hn : ‖(6*((x:ℂ)+t*I) : ℂ)+1‖≤6*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [add_re,add_im,one_re,one_im,add_zero,hre,him]
    rw [abs_of_pos (by linarith [hx.1] : 0<6*x+1),abs_mul]
    rw [abs_of_pos (by norm_num : (0:ℝ)<6)]
    unfold height
    linarith [hx.2]
  have hheight : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤
    principalConstant M*‖(6*((x:ℂ)+t*I) : ℂ)+1‖*(3+|(6*((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  rw [habs] at hb
  calc
    _ ≤ principalConstant M*‖(6*((x:ℂ)+t*I) : ℂ)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(6*height t)*(36*height t^2) := by gcongr
    _ = _ := by unfold zAmplitude; ring

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply ProbeMellinBoundary.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY eta s z hEta H B
    (AL:=wAmplitude M cw) hcw hAH (wAmplitude_pos M hcw).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_w_growth M hcw hx t

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH : ℝ}
    (he : 0<e) (he' : e≤2/3) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤AH*height t^JH) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ eta s hEta H B
    (AL:=zAmplitude M) he hAH (zAmplitude_pos M).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_z_growth M he he' hx t

end SevenEighths.PrincipalMellinGrowth

end

end OAI
end OAIOriginalModule2474

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
Source SHA256: 035108397f9752645adee4eae24c44091977d34f9b4179ef82d85942b0c2f2bc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2475




namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductBounds
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

def localMultiplier (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  (Q : ℂ)^(z-1) *
    (compensatedReplacement (coordV Q z) (coordW Q 1 w)
      (coordD Q (idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z)
      (star (idealCoeff η P.val)*(Q : ℂ)^x) ((Q : ℂ)^(-w)) /
      idealClosedCorrection η P x w z)

def selectedMultiplier (η : Character) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∏ P ∈ T, localMultiplier η P x w z

def slotMultiplier {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (x w z : ℂ) : ℂ :=
  ∏ j ∈ J, ∑ P ∈ T j, b j P * localMultiplier η P x w z

theorem correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma marked_differentiableAt_w (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : 7/8 ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

def localBound (Bx Bz : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  (Ideal.absNorm P.val : ℝ)^(Bz-1) * (400*(1+(Ideal.absNorm P.val : ℝ)^Bx))

lemma localBound_nonneg (Bx Bz : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

def selectedBound (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (Bx Bz : ℝ) : ℝ :=
  ∏ P ∈ T, localBound Bx Bz P

def slotBound {ι : Type*} (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (Bx Bz : ℝ) : ℝ :=
  ∏ j ∈ J, ∑ P ∈ T j, ‖b j P‖ * localBound Bx Bz P

lemma selectedBound_nonneg (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => localBound_nonneg Bx Bz P)

lemma slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg Bx Bz P))

theorem selected_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem selected_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem selected_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (globalClosedCorrection_analytic_w η S hS x z hx hz).mul (slot_analytic_w η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (globalClosedCorrection_analytic_z η S hS x w hx hw).mul (slot_analytic_z η S hS J T b hT x w hx hw)

theorem combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem selected_initial_identity (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  rw [spectralCompensatedHigh_continued S hS T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1<cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem source_z_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0<e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : 7/8 ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)<z.re at hz; linarith)
  have hH := (combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

theorem source_w_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1<cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · exact source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem source_residue_z_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0<e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · exact source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'

theorem local_eq_regionSlot (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s w z : ℂ) :
    localMultiplier η P s w z = (Ideal.absNorm P.val : ℂ)^(z-1) *
      PrincipalSlotEstimate.regionSlot (Ideal.absNorm P.val)
        (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s w z := by
  simp only [localMultiplier,PrincipalSlotEstimate.regionSlot,PrincipalSlotEstimate.regionReplacement,
    PrincipalSlotEstimate.regionMarked,idealMarkedClosed,idealClosedCorrection,Complex.ofReal_natCast]

def windowMultiplier {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (W : ι → ℝ → ℂ) (scale : ι → ℝ) (s w z : ℂ) : ℂ :=
  slotMultiplier η J T (fun j P => W j ((Ideal.absNorm P.val : ℝ)/scale j)) s w z

theorem window_at_residue {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (W : ι → ℝ → ℝ) (scale : ι → ℝ) (s : ℂ) :
    windowMultiplier η J T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      ∏ j ∈ J, ∑ P ∈ T j,
        ((W j ((Ideal.absNorm P.val : ℝ)/scale j) *
          (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ)) : ℝ) : ℂ) *
        PrincipalSlotEstimate.principalSlot (Ideal.absNorm P.val)
          (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s := by
  unfold windowMultiplier slotMultiplier
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro P hp
  rw [local_eq_regionSlot,PrincipalSlotEstimate.region_slot_at_residue]
  have hQ : 0 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hQ.le]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num
  ring_nf

theorem slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using PrincipalSlotEstimate.weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)

@[simp] theorem slotMultiplier_empty {ι : Type*} (η : Character) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (s w z : ℂ) : slotMultiplier η ∅ T b s w z = 1 := by
  simp [slotMultiplier]

theorem selected_as_slots (η : Character) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s w z : ℂ) :
    selectedMultiplier η T s w z = slotMultiplier η T (fun P => {P}) (fun _ _ => 1) s w z := by
  simp [selectedMultiplier,slotMultiplier]

theorem fixed_source_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (η : Character) (s : ℂ) (hs : 7/8 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem fixed_source_ordered_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (η : Character) (s : ℂ) (hs : 7/8 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hh := fixed_source_boundaries S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert boundary_mul_const _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
  funext w
  ring

theorem uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (7/8) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩

end SevenEighths.ProbeFiniteProductBounds
end

end OAI
end OAIOriginalModule2475

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FiniteProductX
Source SHA256: 4ae6793522fbe8bd7fe4c14647461dc1f032e4e2a93d4697437ecfe4b372d7d7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2476



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_x (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 7/8 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
