namespace SevenEighths.HeckeMaskDescent
open HeckeFamily CenteredExceptionalProfile CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem exists_coprime_shift (a c r : O) (hac : IsCoprime a c) (hr : r ≠ 0) :
    ∃ t : O, IsCoprime (a+t*c) r := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (normalizedFactors r).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, IsCoprime.symm ?_⟩
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hr h)
  intro p hp hpr hpnew
  by_cases hpa : p ∣ a
  · have hpc : ¬p ∣ c := fun h => hp.not_isUnit (hac.isUnit_of_dvd' hpa h)
    have hps : ¬p ∣ s.prod := by
      intro h
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd h
      obtain ⟨hqr,hqa⟩ := Multiset.mem_filter.mp hq
      exact hqa ((hp.associated_of_dvd (prime_of_normalized_factor q hqr) hpq).dvd'.trans hpa)
    have ht : p ∣ s.prod*c := by convert dvd_sub hpnew hpa using 1 ; ring
    exact (hp.dvd_or_dvd ht).elim hps hpc
  · obtain ⟨q,hq,hpq⟩ := exists_mem_normalizedFactors_of_dvd hr hp.irreducible hpr
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,fun h => hpa (hpq.dvd.trans h)⟩
    have ht : p ∣ s.prod*c := dvd_mul_of_dvd_left (hpq.dvd.trans (Multiset.dvd_prod hqs)) c
    exact hpa (by convert dvd_sub hpnew ht using 1 ; ring)

theorem exists_primitive_above (χ : Character) (Q : Ideal O)
    (hdesc : FiniteConductor.FactorsThroughIdeal χ.residue
      (Q.map (Ideal.Quotient.mk χ.modulus))) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨K,φ,hMK,hQK,hK,hprim,hnorm,hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation_above_quotient
      χ.modulus χ.residue (Q.map (Ideal.Quotient.mk χ.modulus)) hdesc
  have hu : IdealCharacter.UnitInvariant K φ := by
    intro u
    have h := hmask (u : O)
    simpa only [χ.unit_trivial u,u.isUnit.map (Ideal.Quotient.mk χ.modulus),ite_true] using h.symm
  refine ⟨Character.ofResidue K hK φ hu,hprim,?_,?_⟩
  · exact (Ideal.le_comap_map).trans hQK
  · exact IdealCharacter.ofResidue_source_mask χ.modulus K χ.residue φ χ.unit_trivial hu hmask

theorem descent_of_mask (χ χ' ψ : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ' ψ) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (ψ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a = (u : O ⧸ χ.modulus) := by
    dsimp [a];rw [map_add,map_one,hqu];ring
  have hψa : Ideal.Quotient.mk ψ.modulus a = 1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  let c := idealGenerator (χ.modulus*ψ.modulus)
  have hc : IsCoprime a c := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [show Ideal.span {c}=χ.modulus*ψ.modulus from span_idealGenerator _]
    apply IsCoprime.mul_right
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hψa ▸ isUnit_one)
  obtain ⟨t,htall⟩ := exists_coprime_shift a c (r*goodLambda) hc
    (mul_ne_zero hr goodLambda_prime.ne_zero)
  have ht := htall.of_mul_right_left
  let n := a+t*c
  have hmem : c ∈ χ.modulus*ψ.modulus := by
    rw [← span_idealGenerator (χ.modulus*ψ.modulus)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnχ : Ideal.Quotient.mk χ.modulus n = (u : O ⧸ χ.modulus) := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left hmem),mul_zero,add_zero,ha]
  have hnψ : Ideal.Quotient.mk ψ.modulus n = 1 := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hmem),mul_zero,add_zero,hψa]
  have hnχ' : elementCoeff χ' n ≠ 0 := by
    rw [he n,ite_eq_left ht]
    exact MulChar.apply_ne_zero_iff.mpr (hnχ ▸ u.isUnit)
  have hn0 : n ≠ 0 := by
    intro hz
    have hunit : IsUnit goodLambda := (htall.of_mul_right_right).isUnit_of_dvd'
      (by change goodLambda ∣ n; rw [hz]; exact dvd_zero _) (dvd_refl _)
    exact goodLambda_prime.not_isUnit hunit
  have hcop : IsCoprime (Ideal.span {n}) χ'.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hnχ')
  have heq := elementCoeff_eq_of_inducedBy χ' ψ hind n hn0 hcop
  rw [he n,ite_eq_left ht] at heq
  change χ.residue (Ideal.Quotient.mk χ.modulus n) = ψ.residue (Ideal.Quotient.mk ψ.modulus n) at heq
  simpa only [hnχ,hnψ,map_one] using heq

theorem inducedBy_mask (χ χ' ψ : Character) (r : O)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  intro I
  by_cases hI : I = 0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn' := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    let n := idealGenerator I
    have hn0 : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hval' : elementCoeff χ' n = idealCoeff χ' I := by
      rw [← idealCoeff_span χ' hn0,hspan]
    have hval : elementCoeff χ n = idealCoeff χ I := by
      rw [← idealCoeff_span χ hn0,hspan]
    have hm := he n
    have hcr : IsCoprime n r := by
      by_contra hr
      rw [ite_eq_right hr,hval'] at hm
      exact hn' hm
    rw [ite_eq_left hcr,hval',hval] at hm
    have hn := hm ▸ hn'
    have hcχ := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hm,hind I,ite_eq_left hcχ]
  · have hz : idealCoeff χ' I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixed_inducing_mask_iff (χ χ' : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0) (Q : Ideal O) :
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ' ψ) ↔
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ) := by
  constructor
  · rintro ⟨ψ,hprim,hQ,hind⟩
    obtain ⟨ρ,hρ,hmod,hindρ⟩ := exists_primitive_above χ ψ.modulus
      (descent_of_mask χ χ' ψ r hr he hind)
    exact ⟨ρ,hρ,hQ.trans hmod,hindρ⟩
  · rintro ⟨ψ,hprim,hQ,hind⟩
    exact ⟨ψ,hprim,hQ,inducedBy_mask χ χ' ψ r he hind⟩
end SevenEighths.HeckeMaskDescent

end

end OAI
end OAIOriginalModule1324

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FixedRowMask
Source SHA256: 9a440781108bafcc585539e3335109767636da222a130c3c14bbbfabae379a3e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1325


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRowMask
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem row_mask_mul (η : Character) (m r A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom η) (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist (elementHom η) m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs,
      rowTwist_extract_sixth_mask _ _ _ _ _ hs]
    change elementHom η n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask,hm,hr,show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) hs,
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs]
    split_ifs <;> rfl

theorem fixedInducingRow_mul_mask_iff (η : Character) (Q : Ideal O)
    (m r A z : O) (hm : m ≠ 0) (hr : r ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχ⟩ := exists_row_character η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  obtain ⟨χ',hχ'⟩ := exists_row_character η (m*r) 1 (A*z) (mul_ne_zero hm hr)
    one_ne_zero (mul_ne_zero hA hz) (hmLam.trans (dvd_mul_right _ _))
      (hm2.trans (dvd_mul_right _ _))
  have hmask (n : O) : elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : Character) (mask : O)
      (hρ : ∀ n,elementCoeff ρ n=rowTwist (elementHom η) mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q ≤ ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hprim,hQ,CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (fun n => (hρ n).trans (hρ₀ n).symm) hind⟩
    · rintro ⟨ψ,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ',transport χ m hχ]
  exact HeckeMaskDescent.fixed_inducing_mask_iff χ χ' r hr hmask Q
end SevenEighths.CenteredMomentFixedRowMask

end

end OAI
end OAIOriginalModule1325

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
Source SHA256: 7c10dd322c78666e825c349f0e820ac1a14bb2d64caf7ce9c4a1615cbda9f0c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1326



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRayInducingTransport
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile
open CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentExceptionalPair CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O

theorem modulus_generator_ne_zero (ν : Character) :
    idealGenerator ν.modulus ≠ 0 :=
  idealGenerator_ne_zero ν.modulus ν.modulus_ne_bot

theorem modulus_unit_iff (ν : Character) (n : O) :
    IsUnit (Ideal.Quotient.mk ν.modulus n) ↔
      IsCoprime n (idealGenerator ν.modulus) := by
  rw [IdealCharacter.isUnit_mk_iff_isCoprime]
  conv_lhs => rw [←span_idealGenerator ν.modulus]
  rw [Ideal.isCoprime_span_singleton_iff]

theorem elementCoeff_product_inverse_mask (η ν : Character) (n : O) :
    elementCoeff ((η.product ν).product ν.inverse) n =
      if IsCoprime n (idealGenerator ν.modulus) then elementCoeff η n else 0 := by
  rw [elementCoeff_product,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsCoprime n (idealGenerator ν.modulus)
  · have hv : elementCoeff ν n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr ((modulus_unit_iff ν n).mpr hn)
    simp only [hn,ite_true,mul_assoc,mul_inv_cancel₀ hv,mul_one]
  · have hv : elementCoeff ν n = 0 :=
      MulChar.map_nonunit ν.residue (fun hu=>hn ((modulus_unit_iff ν n).mp hu))
    simp only [hn,ite_false,hv,mul_zero,zero_mul]

theorem rowTwist_product (η ν : Character) (m f z n : O) :
    rowTwist (elementHom (η.product ν)) m f z n =
      rowTwist (elementHom η) m f z n * elementCoeff ν n := by
  change elementCoeff (η.product ν) n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) * elementCoeff ν n
  rw [elementCoeff_product]
  ring

theorem rowTwist_product_inverse_mask (η ν : Character) (m A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom ((η.product ν).product ν.inverse)) m 1 (A*z) n =
      rowTwist (elementHom η) (m*idealGenerator ν.modulus) 1 (A*z) n := by
  rw [row_mask_mul η m (idealGenerator ν.modulus) A z n hmLam hm2]
  change elementCoeff ((η.product ν).product ν.inverse) n *
    idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n}) = _
  rw [elementCoeff_product_inverse_mask]
  split_ifs
  · rfl
  · exact zero_mul _

theorem fixedInducingRow_product_of (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (h : FixedInducingRow η Q m A z) :
    FixedInducingRow (η.product ν) Q m A z :=
  fixedInducingRow_of_product η (η.product ν) ν Q m A z z hν
    (fun n=>rowTwist_product η ν m 1 (A*z) n) h

theorem fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν) Q m A z ↔ FixedInducingRow η Q m A z := by
  constructor
  · intro h
    have hi := fixedInducingRow_product_of (η.product ν) ν.inverse Q m A z hν h
    obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hi
    apply (fixedInducingRow_mul_mask_iff η Q m (idealGenerator ν.modulus) A z
      hm (modulus_generator_ne_zero ν) hA hz hmLam hm2).mp
    exact ⟨χ,ψ,hprim,hind,hQ,fun n=>(hrow n).trans
      (rowTwist_product_inverse_mask η ν m A z n hmLam hm2)⟩
  · exact fixedInducingRow_product_of η ν Q m A z hν

theorem not_fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_iff η ν Q m A z hν hm hA hz hmLam hm2)

theorem fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν.inverse) Q m A z ↔ FixedInducingRow η Q m A z :=
  fixedInducingRow_product_iff η ν.inverse Q m A z hν hm hA hz hmLam hm2

theorem not_fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν.inverse) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_inverse_iff η ν Q m A z hν hm hA hz hmLam hm2)

end SevenEighths.CenteredMomentFixedRayInducingTransport

end

end OAI
end OAIOriginalModule1326

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeCancellation
Source SHA256: 3148739bbbcb292de174fc5ce3dcbed2187e23a9a7475653d967a330f802c440
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1327



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

def densityControl (Q : Ideal O) (χ : Character) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)/‖eisEmbedding (fixedPeriod Q)‖^2

lemma volumeControl_nonneg (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : 0 ≤ volumeControl Q χ W :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pvControl_nonneg W)

lemma densityControl_nonneg (Q : Ideal O) (χ : Character) : 0 ≤ densityControl Q χ := by
  unfold densityControl
  positivity

theorem actual_rectangle_saving (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁*X₂=T) (hprodY : Y₁*Y₂=T) :
    let E := volumeControl Q χ W₁+volumeControl Q χ W₂
    let C := densityControl Q χ*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
    ‖idealSum χ W₁ X₁*idealSum χ W₂ X₂-idealSum χ W₁ Y₁*idealSum χ W₂ Y₂‖ ≤
      4*E*C*(T/L) := by
  let E := volumeControl Q χ W₁+volumeControl Q χ W₂
  let D := densityControl Q χ
  let C := D*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₂ 0
  have hE₁ := volumeControl_nonneg Q χ W₁
  have hE₂ := volumeControl_nonneg Q χ W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hD : 0 ≤ D := densityControl_nonneg Q χ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hL0 : 0 < L := by linarith
  have hden : ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus‖ ≤ D :=
    density_norm_le _ _ ψ χ.modulus χ.modulus_ne_bot
  have hvol₁ : ‖v₁‖ ≤ D*‖paperRadialFourier W₁ 0‖ := by
    dsimp only [v₁]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have hvol₂ : ‖v₂‖ ≤ D*‖paperRadialFourier W₂ 0‖ := by
    dsimp only [v₂]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₁ X-(X:ℂ)*v₁‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ b₁ X
      (lt_of_lt_of_le hL0 hX) hs₁).trans (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X-(X:ℂ)*v₂‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ b₂ X
      (lt_of_lt_of_le hL0 hX) hs₂).trans (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X:ℂ)*v₁‖ ≤ C*X := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by
      dsimp only [C]
      nlinarith [mul_nonneg hD (norm_nonneg (paperRadialFourier W₂ 0))]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X‖ ≤ C*X := by
    have hb := norm_le_norm_sub_add (idealSum χ W₂ X) ((X:ℂ)*v₂)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E*X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    have hv := mul_le_mul_of_nonneg_left hvol₂ (le_trans hL0.le hX)
    dsimp only [C]
    nlinarith [mul_nonneg (mul_nonneg hD (norm_nonneg (paperRadialFourier W₁ 0))) (le_trans hL0.le hX)]
  have hmain : ((X₁:ℂ)*v₁)*((X₂:ℂ)*v₂)=((Y₁:ℂ)*v₁)*((Y₂:ℂ)*v₂) := by
    have hp : (X₁:ℂ)*X₂=(Y₁:ℂ)*Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁:ℂ)*X₂)*(v₁*v₂) := by ring
      _ = ((Y₁:ℂ)*Y₂)*(v₁*v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI
end OAIOriginalModule1327

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeTwist
Source SHA256: a495e58ad0f408343b2e7808881086f01681a194b570d6d54e21d5c1d2c292fa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1328



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeTwist
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentLattice CenteredMomentCounting CenteredMomentTwist
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem idealSum_absolute (χ : Character) (W : ℝ → ℂ) (b M X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖idealSum χ W X‖ ≤ (128*b*M)*X := by
  have h := norm_tsum_ideal_ball (fun I => idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) M (mul_nonneg hb hX.le) hM (by change idealCoeff χ (0:Ideal O)*_ = 0; rw [map_zero,zero_mul])
    (by intro I; rw [norm_mul]; exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by intro I hI; apply (div_le_iff₀ hX).mp; apply hs; intro hz; exact hI (by rw [hz,mul_zero]))
  change ‖idealSum χ W X‖ ≤ _ at h
  convert h using 1 ; ring

theorem twistedIdealSum_scale (χ : Character) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedIdealSum χ W t X = (X : ℂ) ^ (Complex.I * t) *
      idealSum χ (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedIdealSum idealSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

theorem twistedIdealSum_volume (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twistedIdealSum_absolute (χ : Character) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact idealSum_absolute χ _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twisted_actual_volumeCoefficient_norm_le (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2)
  exact norm_linear_coefficient_le (fun X => idealSum χ V X)
    _ (128 * b * M) (volumeControl Q χ V) (volumeControl_nonneg Q χ V)
    (fun X hX => actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow V b X hX hV)
    (fun X hX => idealSum_absolute χ V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem actual_twisted_rectangle_saving
    (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
      twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := volumeControl Q χ V₁ + volumeControl Q χ V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := volumeControl_nonneg Q χ V₁
  have hE₂ := volumeControl_nonneg Q χ V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_actual_volumeCoefficient_norm_le η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X‖ ≤ C * X :=
    (twistedIdealSum_absolute χ W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeTwist

end

end OAI
end OAIOriginalModule1328

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeHeight
Source SHA256: 9070c8b58f75529fdd0a1563d9c4c8201eb0d4eaf2e8038d5ad195dc9f096176
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1329


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem volumeControl_polynomial_height (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ χ hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem normalized_actual_rectangle_estimate
    (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η χ ψ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      (Q ≤ ψ.modulus) → CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A₀ z : O, (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
          twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := volumeControl_polynomial_height Q a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := volumeControl_polynomial_height Q a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η χ ψ hnorm hQψ hind m A₀ z hmLam hm2 hrow t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

def rowTwistedSum (η : Character) (m A₀ z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A₀*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

theorem exceptional_rectangle_estimate (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩ := normalized_actual_rectangle_estimate Q hQ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI
end OAIOriginalModule1329

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeSlots
Source SHA256: 6ffc5659cfaa00feeebb1e7e9ca65b44de7071b460346cbeb28381f9b17d9c8d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1330


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentCounting CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def rowSlot (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑ P ∈ S, β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
    (Ideal.absNorm P:ℂ)^(Complex.I*t)

theorem row_twisted_coefficient_norm (η : Character) (m A z : O) (t : ℝ)
    (P : Ideal O) (hP : P ≠ 0) :
    ‖(idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t)‖ ≤ 1 := by
  have hn : 0 < (Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  rw [norm_mul, norm_mul, show (Ideal.absNorm P:ℂ)=((Ideal.absNorm P:ℝ):ℂ) by simp,
    norm_real_imaginary_power _ t hn, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η P)).trans
    (CanonicalRowCompletion.idealRowHom_norm _ _)

theorem rowSlot_bound (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hβ : ∀ P ∈ S, ‖β P‖ ≤ M)
    (hN : ∀ P ∈ S, β P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H) :
    ‖rowSlot η m A z S β t‖ ≤ 128*M*H := by
  let f : Ideal O → ℂ := fun P => if P ∈ S then
    β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t) else 0
  have hf0 : f 0=0 := by simp only [f, map_zero, zero_mul, mul_zero, ite_self]
  have hf : ∀ P, ‖f P‖ ≤ M := by
    intro P
    by_cases hP : P ∈ S
    · by_cases hP0 : P=0
      · rw [hP0,hf0,norm_zero]; exact hM
      · dsimp only [f]; rw [ite_eq_left hP, mul_assoc, norm_mul]
        exact (mul_le_mul (hβ P hP) (row_twisted_coefficient_norm η m A z t P hP0)
          (norm_nonneg _) hM).trans_eq (mul_one M)
    · simp only [f,ite_eq_right hP,norm_zero]; exact hM
  have hsup : ∀ P, f P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H := by
    intro P hP
    have hm : P ∈ S := by by_contra hn; exact hP (by simp only [f,ite_eq_right hn])
    exact hN P hm (by intro hz; exact hP (by simp only [f,ite_eq_left hm,hz,zero_mul]))
  have he : (∑' P, f P)=rowSlot η m A z S β t := by
    rw [tsum_eq_sum (s := S) (fun P hP => by simp only [f,ite_eq_right hP])]
    unfold rowSlot
    exact Finset.sum_congr rfl (fun P hP => by simp only [f,ite_eq_left hP])
  rw [← he]
  exact norm_tsum_ideal_ball f H M hH hM hf0 hf hsup

variable {ι : Type*} [Fintype ι]

theorem whole_product_normalization (R : ℂ) (q : ι → ℂ) (k p : ι → ℝ)
    (D T L : ℝ) (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L)
    (_hk : ∀ i, 0 ≤ k i) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, ‖q i‖ ≤ k i*p i)
    (hR : ‖(Real.sqrt T:ℂ)⁻¹*R‖ ≤ D*(Real.sqrt T/L)) :
    ‖(Real.sqrt (T*∏ i,p i):ℂ)⁻¹*(R*∏ i,q i)‖ ≤
      D*(∏ i,k i)*(Real.sqrt (T*∏ i,p i)/L) := by
  have hP : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => hp i)
  have hTP : 0 < T*∏ i,p i := mul_pos hT hP
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsTP : 0 < Real.sqrt (T*∏ i,p i) := Real.sqrt_pos.2 hTP
  have hQ : ‖∏ i,q i‖ ≤ (∏ i,k i)*(∏ i,p i) := by
    rw [norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hq i)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsT.le] at hR
  have hR' : ‖R‖ ≤ D*T/L := by
    have h := mul_le_mul_of_nonneg_left hR hsT.le
    rw [← mul_assoc,mul_inv_cancel₀ hsT.ne',one_mul] at h
    have hs := Real.sq_sqrt hT.le
    convert h using 1
    calc
      D*T/L = D*(Real.sqrt T)^2/L := by rw [hs]
      _ = _ := by ring
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsTP.le,norm_mul]
  calc
    _ ≤ (Real.sqrt (T*∏ i,p i))⁻¹*((D*T/L)*((∏ i,k i)*(∏ i,p i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hR' hQ (norm_nonneg _) (by positivity)) (inv_nonneg.mpr hsTP.le)
    _ = _ := by
      have hs := Real.sq_sqrt hTP.le
      field_simp
      rw [hs]

def centeredSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (p : ι → ℝ) (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt (T*∏ i,p i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
      rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

theorem exceptional_slots_estimate (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A z : O),
      m ≠ 0 → A ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀ (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (p b M : ι → ℝ),
      (∀ i, 0 < p i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ P ∈ S i, ‖β i P‖ ≤ M i) →
      (∀ i, ∀ P ∈ S i, β i P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ b i*p i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β p t X₁ X₂ Y₁ Y₂ T‖ ≤
        C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*M i)*(Real.sqrt (T*∏ i,p i)/L) := by
  obtain ⟨J,hJ⟩ := exceptional_rectangle_estimate Q hQ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β p b M hp hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖ ≤ (128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i => rowSlot η m A z (S i) (β i) t)
    (fun i => 128*b i*M i) p (C*Z^ε*(1+‖t‖)^J) T L
    (by positivity) hT hL (fun i => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hmLam hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentHeckeSlots

end

end OAI
end OAIOriginalModule1330

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
Source SHA256: ec6c0372863b81a30c6868959da1062567506f318d9b90d3b1b2aefcbc00f264
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1331



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

def rowWeight (η : Character) (m A z : O) (t : ℝ) : Ideal O →*₀ ℂ where
  toFun I := (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)
  map_one' := by simp only [map_one,Nat.cast_one,Complex.one_cpow,one_mul]
  map_zero' := by simp only [map_zero,zero_mul,mul_zero]
  map_mul' I J := by
    have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t) =
        (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I) : (0:ℝ) ≤ Ideal.absNorm I)
        (Nat.cast_nonneg (Ideal.absNorm J) : (0:ℝ) ≤ Ideal.absNorm J) (Complex.I*t)
    simp only [map_mul,Nat.cast_mul,hpow]
    ring

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem common_extracted_slot_rectangle (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal O, ∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
end OAIOriginalModule1331

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorAllocation
Source SHA256: d5197083ebb0e8133eeb36b7516732f029355ff02692059d904b0e2f7bb9de0e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1332



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def nonemptySelections (s : Finset ι) : Finset (Finset ι) := s.powerset.erase ∅

omit [DecidableEq ι] in
theorem prime_complement (P : Ideal O) (hP : Prime P) (s : Finset ι) (v : ι → Ideal O) :
    (∏ i ∈ s, (1-(if P ∣ v i then (1:ℂ) else 0))) =
      if P ∣ ∏ i ∈ s,v i then 0 else 1 := by
  by_cases h : P ∣ ∏ i ∈ s,v i
  · rw [ite_eq_left h]
    obtain ⟨i,hi,hd⟩ := (hP.dvd_finsetProd_iff v).mp h
    exact Finset.prod_eq_zero hi (by simp only [ite_eq_left hd,sub_self])
  · rw [ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    have hd : ¬P∣v i := fun hh => h ((hP.dvd_finsetProd_iff v).mpr ⟨i,hi,hh⟩)
    simp only [ite_eq_right hd,sub_zero]

theorem prime_factor_allocation (P : Ideal O) (hP : Prime P)
    (s : Finset ι) (v : ι → Ideal O) :
    (if P ∣ ∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
        ∏ i ∈ J, if P ∣ v i then (1:ℂ) else 0 := by
  let f := fun J : Finset ι => (-1:ℂ)^J.card*∏ i ∈ J,if P∣v i then (1:ℂ) else 0
  have he : (∑ J ∈ nonemptySelections s,f J)+1 =
      if P ∣ ∏ i ∈ s,v i then (0:ℂ) else 1 := by
    have hr := Finset.sum_erase_add s.powerset f (Finset.mem_powerset.mpr (Finset.empty_subset s))
    have hh := Finset.prod_sub (fun _i : ι => (1:ℂ))
      (fun i => if P∣v i then (1:ℂ) else 0) s
    simp only [Finset.prod_const_one,mul_one] at hh
    rw [prime_complement P hP s v] at hh
    simpa only [nonemptySelections,f,Finset.card_empty,pow_zero,Finset.prod_empty,one_mul] using hr.trans hh.symm
  have hn : (∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
      ∏ i ∈ J,if P∣v i then (1:ℂ) else 0) = -(∑ J ∈ nonemptySelections s,f J) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f]
    rw [pow_succ]
    ring
  rw [hn]
  by_cases h : P∣∏ i ∈ s,v i <;> simp only [h,ite_true,ite_false] at he ⊢ <;>
    linear_combination he

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

abbrev Allocation (D : Ideal O) (s : Finset ι) :=
  (P : primeSupport D) → nonemptySelections s

def allocationTerm (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)*
    ∏ i ∈ (a P).val, if (P:Ideal O)∣v i then (1:ℂ) else 0

theorem squarefree_mask_allocation (D : Ideal O) (hD : Squarefree D)
    (s : Finset ι) (v : ι → Ideal O) :
    (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ a : Allocation D s, allocationTerm D s v a := by
  have hprod : (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∏ P : primeSupport D, if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0 := by
    by_cases hd : D∣∏ i ∈ s,v i
    · rw [ite_eq_left hd]
      symm
      apply Finset.prod_eq_one
      intro P hP
      rw [ite_eq_left ((squarefree_dvd_iff _ _ hD).mp hd P P.property)]
    · rw [ite_eq_right hd]
      obtain ⟨P,hP,hnd⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff _ _ hD).mpr h))
        |> fun h => by simpa only [not_forall,not_imp] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨P,hP⟩ : primeSupport D)) (by simp only [ite_eq_right hnd])
  rw [hprod]
  have hl (P : primeSupport D) :
      (if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J : nonemptySelections s, (-1:ℂ)^(J.val.card+1)*
        ∏ i ∈ J.val, if (P:Ideal O)∣v i then (1:ℂ) else 0 := by
    rw [prime_factor_allocation P (support_prime P.property) s v]
    exact (Finset.sum_coe_sort (nonemptySelections s) (fun J =>
      (-1:ℂ)^(J.card+1)*∏ i ∈ J,if (P:Ideal O)∣v i then (1:ℂ) else 0)).symm
  simp_rw [hl]
  exact Fintype.prod_sum _

theorem allocationTerm_norm_le_one (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ‖allocationTerm D s v a‖ ≤ 1 := by
  unfold allocationTerm
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i hi
  split_ifs <;> norm_num

theorem allocation_card_bound (D : Ideal O) (s : Finset ι) :
    Fintype.card (Allocation D s) ≤ (2^(primeSupport D).card)^s.card := by
  have hc : (nonemptySelections s).card ≤ 2^s.card := by
    simpa only [nonemptySelections,Finset.card_powerset] using
      (Finset.card_erase_le (s := s.powerset) (a := (∅:Finset ι)))
  change Fintype.card (primeSupport D → nonemptySelections s) ≤ _
  simp only [Fintype.card_fun,Fintype.card_coe]
  calc
    _ ≤ (2^s.card)^(primeSupport D).card := Nat.pow_le_pow_left hc _
    _ = _ := by simp only [← pow_mul,Nat.mul_comm]

theorem allocation_mass_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      ∀ v : ι → Ideal O, (∑ a : Allocation D s, ‖allocationTerm D s v a‖) ≤
        C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs v
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ _a : Allocation D s,(1:ℝ) := Finset.sum_le_sum (fun a _ => allocationTerm_norm_le_one D s v a)
    _ = (Fintype.card (Allocation D s):ℝ) := by simp
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI
end OAIOriginalModule1332

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorExtraction
Source SHA256: d4facecfb46c7e1aa1e52f3a515db0564aee71b0147fedea97c164010e05b01e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1333


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [ite_eq_right h])

theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

theorem exists_factor_quotients (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) :
    ∃ q : ι → Ideal O, ∀ i, v i=selectedDivisor D s a i*q i := by
  choose q hq using (fun i => selectedDivisor_dvd D s v a hn i)
  exact ⟨q,hq⟩

theorem selected_prime_slot (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) (hv : Prime (v i)) :
    v i=(P:Ideal O) :=
  ((prime_dvd_prime_iff_eq (support_prime P.property) hv).mp
    (selected_divides_factor D s v a hn P i hi)).symm

theorem double_selected_prime_slot_zero (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (P Q : primeSupport D) (hPQ : P ≠ Q)
    (i : ι) (hPi : i ∈ (a P).val) (hQi : i ∈ (a Q).val) (hv : Prime (v i)) :
    allocationTerm D s v a=0 := by
  by_contra hn
  apply hPQ
  apply Subtype.ext
  exact (selected_prime_slot D s v a hn P i hPi hv).symm.trans
    (selected_prime_slot D s v a hn Q i hQi hv)

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI
end OAIOriginalModule1333

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorEnergy
Source SHA256: 1650b8b5d4a9ddf458137c7e0904dca8683b4ddd51986d6019cb9893d6c0bad4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1334


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorEnergy
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι α ρ : Type*} [DecidableEq ι]

def allocatedPolynomial (D : Ideal O) (s : Finset ι) (T : Finset α)
    (v : α → ι → Ideal O) (F : ρ → α → ℂ) (a : Allocation D s) (h : ρ) : ℂ :=
  ∑ j ∈ T, allocationTerm D s (v j) a*F h j

theorem finite_mask_regroup (D : Ideal O) (hD : Squarefree D) (s : Finset ι)
    (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (h : ρ) :
    (∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocatedPolynomial D s T v F a h := by
  have ht (j : α) : (if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocationTerm D s (v j) a*F h j := by
    have he := congrArg (fun w : ℂ => w*F h j) (squarefree_mask_allocation D hD s (v j))
    simpa only [ite_mul,one_mul,zero_mul,Finset.sum_mul] using he
  simp_rw [ht]
  rw [Finset.sum_comm]
  rfl

theorem allocation_card_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      (Fintype.card (Allocation D s):ℝ) ≤ C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

theorem allocated_energy_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), Squarefree D → ∀ s : Finset ι, s.card ≤ N →
      ∀ (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (rows : Finset ρ),
      (∑ h ∈ rows, ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι) N hN ε hε
  refine ⟨C,hC,?_⟩
  intro D hD s hs T v F rows
  have hrow (h : ρ) : ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2 ≤
      (Fintype.card (Allocation D s):ℝ)*∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 := by
    rw [finite_mask_regroup D hD s T v F h]
    calc
      _ ≤ (∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _a : Allocation D s => (1:ℝ))
          (fun a => ‖allocatedPolynomial D s T v F a h‖))
  calc
    _ ≤ ∑ h ∈ rows, (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero s hs)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end SevenEighths.CenteredMomentDivisorEnergy

end

end OAI
end OAIOriginalModule1334

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorTensor
Source SHA256: 8506a85d4c97df57dfa5583436db68405985e10b233aa231c4e6b490b80d49c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1335


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [ite_eq_left (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [ite_eq_right hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh,Finset.prod_eq_one (fun i hi => by rw [ite_eq_left (hh i hi)]),mul_one]
  · rw [ite_eq_right hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [ite_eq_right hnd]),mul_zero]

theorem selected_plain_sum (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (hD : D ≠ 0) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : Ideal O, if D∣I then rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) else 0) =
      rowWeight η m A z t D*rowTwistedSum η m A z W t (X/Ideal.absNorm D) := by
  rw [tsum_ideal_divisible D hD, rowTwistedSum_eq_weight,← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [map_mul]
  have he : (Ideal.absNorm (D*I):ℝ)/X = (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm D:ℝ)) := by
    simp only [map_mul,Nat.cast_mul,div_div_eq_mul_div]
    ring
  rw [he]
  ring

theorem selected_plain_scales (D₁ D₂ : Ideal O) (X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm D₁)*(X₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) ∧
    (Y₁/Ideal.absNorm D₁)*(Y₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) :=
  CenteredMomentExtraction.extracted_product_scale X₁ X₂ Y₁ Y₂ T D₁ D₂ hX hY

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI
end OAIOriginalModule1335

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorSlots
Source SHA256: 5852401d74e917107563e1488fa6603cd3d4a9dfcfb7b1790eb867cd1a6562d0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1336


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_slot_exact (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [ite_eq_right hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

theorem allocated_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ M)
    (hN : ∀ I ∈ S, β I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ H) :
    ‖rowSlot η m A z S (fun I => if selectedDivisor D s a i∣I then β I else 0) t‖ ≤
      if (selectedPrimes D s a i).Nonempty then M else 128*M*H := by
  by_cases hn : (selectedPrimes D s a i).Nonempty
  · rw [ite_eq_left hn]
    obtain ⟨P,hP⟩ := hn
    exact selected_slot_bound η m A z t (selectedDivisor D s a i) P (support_prime P.property)
      (Finset.dvd_prod_of_mem _ hP) S hS β M hM hβ
  · rw [ite_eq_right hn]
    have he := selectedDivisor_empty D s a i (Finset.not_nonempty_iff_eq_empty.mp hn)
    simp only [he,one_dvd,ite_true]
    exact rowSlot_bound η m A z S β t H M hH hM hβ hN

end SevenEighths.CenteredMomentDivisorSlots

end

end OAI
end OAIOriginalModule1336

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorBoundary
Source SHA256: 0553b106a29103eb034ffb9a9252a981f4f4a84aa1189d14ed259bbb34945294
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1337


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorBoundary
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def frozenSlots (D : Ideal O) (s slots : Finset ι) (a : Allocation D s) : Finset ι :=
  slots.filter (fun i => (selectedPrimes D s a i).Nonempty)

def extractedProduct (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) : Ideal O :=
  (∏ i ∈ plain,selectedDivisor D s a i)*(∏ i ∈ frozenSlots D s slots a,v i)

theorem divisor_dvd_extractedProduct (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0) :
    D∣extractedProduct D s plain slots a v := by
  apply (squarefree_dvd_iff _ _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  have hne : (a PP).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp (a PP).property).1
  obtain ⟨i,hi⟩ := hne
  have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a PP).property)) hi
  have hip : PP ∈ selectedPrimes D s a i := Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  rcases Finset.mem_union.mp (hs his) with hp | hslot
  · apply dvd_mul_of_dvd_left
    exact (Finset.dvd_prod_of_mem (fun Q : primeSupport D => (Q:Ideal O)) hip).trans
      (Finset.dvd_prod_of_mem (fun i => selectedDivisor D s a i) hp)
  · apply dvd_mul_of_dvd_right
    exact (selected_divides_factor D s v a hn PP i hi).trans
      (Finset.dvd_prod_of_mem v (Finset.mem_filter.mpr ⟨hslot,⟨PP,hip⟩⟩))

theorem extractedProduct_ne_zero (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0) :
    extractedProduct D s plain slots a v ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => selectedDivisor_ne_zero D s a i))
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hv i (Finset.mem_filter.mp hi).1))

theorem actual_divisor_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) :
    Ideal.absNorm D ≤ (∏ i ∈ plain,Ideal.absNorm (selectedDivisor D s a i))*
      (∏ i ∈ frozenSlots D s slots a,Ideal.absNorm (v i)) := by
  have hd := divisor_dvd_extractedProduct D hD s plain slots hs a v hn
  have hnorm := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (extractedProduct_ne_zero D s plain slots a v hv))) (map_dvd Ideal.absNorm hd)
  simpa only [extractedProduct,map_mul,map_prod] using hnorm

theorem actual_divisor_log_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  have hnorm : (Ideal.absNorm D:ℝ) ≤
      (∏ i ∈ plain,(Ideal.absNorm (selectedDivisor D s a i):ℝ))*
      (∏ i ∈ frozenSlots D s slots a,(Ideal.absNorm (v i):ℝ)) := by
    exact_mod_cast actual_divisor_norm_boundary D hD s plain slots hs a v hn hv
  have hp (i : ι) : (Ideal.absNorm (selectedDivisor D s a i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D s a i))
  have hq (i : ι) (hi : i ∈ frozenSlots D s slots a) : (Ideal.absNorm (v i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i (Finset.mem_filter.mp hi).1))
  have hh := Real.logb_le_logb_of_le hZ (show (0:ℝ)<Ideal.absNorm D by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)) hnorm
  rw [Real.logb_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr hq), Real.logb_prod _ _ (fun i _ => hp i),
    Real.logb_prod _ _ hq] at hh
  exact hh

def formalReduction (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (P : ι → ℝ) (Z : ℝ) : ℝ :=
  (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
    ∑ i ∈ frozenSlots D s slots a,Real.logb Z (P i)

def frozenRatio (D : Ideal O) (s slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) (P : ι → ℝ) (Z : ℝ) : ℝ :=
  ∑ i ∈ frozenSlots D s slots a,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)

theorem formal_reduction_add_ratio (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0)
    (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i) (Z : ℝ) :
    formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z =
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  unfold formalReduction frozenRatio
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have his := (Finset.mem_filter.mp hi).1
  rw [Real.logb_div (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i his))) (hP i his).ne']
  ring

theorem actual_formal_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z := by
  rw [formal_reduction_add_ratio D s plain slots a v hv P hP Z]
  exact actual_divisor_log_boundary D hD s plain slots hs a v hn hv Z hZ

theorem divisor_dyad_card (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1 ≤ T)
    (hD : ∀ D ∈ Ds,D ≠ 0) (hN : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T) :
    (Ds.card:ℝ) ≤ 256*T := by
  have h := DescentFiberCost.finite_ideal_count_real Ds (2*T) (by linarith) hD
    (fun D hD => (hN D hD).le)
  linarith

theorem paired_raw_divisor_bound (Ds : Finset (Ideal O)) (T Z θ : ℝ)
    (hT : 1 ≤ T) (hZ : 1 < Z) (r₁ r₂ w₁ w₂ : Ideal O → ℝ)
    (hD : ∀ D ∈ Ds,D ≠ 0)
    (hlo : ∀ D ∈ Ds,T ≤ (Ideal.absNorm D:ℝ))
    (hhi : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T)
    (hleft : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₁ D+w₁ D)
    (hright : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₂ D+w₂ D)
    (hw : ∀ D ∈ Ds,w₁ D+w₂ D ≤ 2*θ) :
    (∑ D ∈ Ds,Z^(-(r₁ D+r₂ D)/2)) ≤ 256*Z^θ := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have he (D : Ideal O) (hmem : D ∈ Ds) : Z^(-(r₁ D+r₂ D)/2) ≤ Z^θ/T := by
    have hn := Real.logb_le_logb_of_le hZ hT0 (hlo D hmem)
    have h₁ := hleft D hmem
    have h₂ := hright D hmem
    have hω := hw D hmem
    have hh : -(r₁ D+r₂ D)/2 ≤ θ-Real.logb Z T := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hh
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hT0] at hpow
    exact hpow
  calc
    _ ≤ ∑ _D ∈ Ds,Z^θ/T := Finset.sum_le_sum (fun D hD => he D hD)
    _ = (Ds.card:ℝ)*(Z^θ/T) := by simp
    _ ≤ (256*T)*(Z^θ/T) := mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT hD hhi) (by positivity)
    _ = _ := by field_simp

end SevenEighths.CenteredMomentDivisorBoundary

end

end OAI
end OAIOriginalModule1337

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorRectangle
Source SHA256: 1feb949fd3e521247dd0c1c61d814a5da8eadc6b376c84f211213dcb0189a5a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1338


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentHeckeExpansion CenteredMomentMask CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def factorTuple (v : ι → Ideal O) (I J : Ideal O) : (ι ⊕ Fin 2) → Ideal O :=
  Sum.elim v (fun j => if j=0 then I else J)

def selectedPlain (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) : Ideal O := selectedDivisor D Finset.univ a (Sum.inr j)

def selectedSlot (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) : Ideal O := selectedDivisor D Finset.univ a (Sum.inl i)

theorem allocationTerm_rectangle (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O) :
    allocationTerm D Finset.univ (factorTuple v I J) a =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i ∣ v i then (1:ℂ) else 0)*
        (if selectedPlain D a 0 ∣ I then 1 else 0)*
        (if selectedPlain D a 1 ∣ J then 1 else 0) := by
  rw [allocationTerm_eq_product,Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,
    selectedPlain,selectedSlot]
  simp only [mul_assoc]
  rfl

theorem double_selected_reindex (D₁ D₂ : Ideal O) (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0)
    (F : Ideal O → Ideal O → ℂ) :
    (∑' I : Ideal O,∑' J : Ideal O,
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J) =
      ∑' I : Ideal O,∑' J : Ideal O,F (D₁*I) (D₂*J) := by
  have he (I J : Ideal O) :
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J =
        if D₁∣I then (if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  have hi (I : Ideal O) :
      (∑' J : Ideal O,if D₁∣I then (if D₂∣J then F I J else 0) else 0) =
        if D₁∣I then (∑' J : Ideal O,if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hi]
  rw [tsum_ideal_divisible D₁ h₁]
  exact tsum_congr (fun I => tsum_ideal_divisible D₂ h₂ (F (D₁*I)))

theorem allocated_rectangle_reindex (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ∑ v : (i : ι) → S i,
          (∏ i,if selectedSlot D a i ∣ (v i:Ideal O) then β i (v i) else 0)*
          ∑' I : Ideal O,∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
            idealRectangle W₁ W₂
              (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
              (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1)) I J := by
  let F (v : (i : ι) → S i) (I J : Ideal O) :=
    rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        ((if selectedPlain D a 0∣I then (1:ℂ) else 0)*
          (if selectedPlain D a 1∣J then 1 else 0)*F v I J) := by
    rw [allocationTerm_rectangle]
    dsimp only [F]
    ring
  have hint (v : (i : ι) → S i) :
      (∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        (∑' I : Ideal O,∑' J : Ideal O,F v (selectedPlain D a 0*I) (selectedPlain D a 1*J)) := by
    simp_rw [he]
    have ht := double_selected_reindex (selectedPlain D a 0) (selectedPlain D a 1)
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)) (F v)
    rw [← ht,← tsum_mul_left]
    apply tsum_congr
    intro I
    exact tsum_mul_left
  simp_rw [hint]
  have hβ (v : (i : ι) → S i) :
      (∏ i,β i (v i))*(allocationSign D Finset.univ a*
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0)) =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then β i (v i) else 0) := by
    rw [mul_left_comm,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [← mul_assoc]
  simp only [← mul_assoc] at hβ
  simp_rw [hβ]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  dsimp only [F]
  rw [common_extracted_slot_rectangle η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t
    W₁ W₂ X₁ X₂ Y₁ Y₂ (selectedPlain D a 0) (selectedPlain D a 1)]
  simp only [mul_assoc]

end SevenEighths.CenteredMomentDivisorRectangle

end

end OAI
end OAIOriginalModule1338

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorRows
Source SHA256: 18d3d631ca666307faf2d4374adefd25f97163f998f12c4ea91737b09d24d519
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1339


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem allocatedRectangle_eq_rows (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ((rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
          rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1)))*
          ∏ i,rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t) := by
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedRectangle
  rw [allocated_rectangle_reindex]
  rw [actual_slot_rectangle_sum η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t W₁ W₂ b₁ b₂
    _ _ _ _ hW₁ hW₂ (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1))
    (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))]

theorem allocatedRectangle_norm_le (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      ‖rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
        rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))‖ *
        ∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖ := by
  rw [allocatedRectangle_eq_rows η m A z t S β D a W₁ W₂ b₁ b₂ _ _ _ _
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,norm_mul,norm_mul,allocationSign_norm,one_mul,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact row_twisted_coefficient_norm η m A z t _ (mul_ne_zero
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))

end SevenEighths.CenteredMomentDivisorRows

end

end OAI
end OAIOriginalModule1339

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorFullMask
Source SHA256: 977bf1ecf0010e105e7fe032d956358ced5f0b34ef6165681464daf3477d40ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1340


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorFullMask
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O

 theorem annular_hasFiniteSupport (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (fun I : Ideal O => W ((Ideal.absNorm I:ℝ)/X)).HasFiniteSupport := by
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b*X))).subset
  intro I hI
  have hn := (div_le_iff₀ hX).mp (hs hI)
  exact_mod_cast hn.trans (Nat.le_ceil (b*X))

theorem rectangle_hasFiniteSupport (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (fun v : Ideal O × Ideal O => idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2).HasFiniteSupport := by
  have h₁ := (annular_hasFiniteSupport W₁ b₁ X₁ hX₁ hW₁).union
    (annular_hasFiniteSupport W₁ b₁ Y₁ hY₁ hW₁)
  have h₂ := (annular_hasFiniteSupport W₂ b₂ X₂ hX₂ hW₂).union
    (annular_hasFiniteSupport W₂ b₂ Y₂ hY₂ hW₂)
  apply (h₁.prod h₂).subset
  intro v hv
  constructor
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,zero_mul,sub_self])
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,mul_zero,sub_self])

theorem rectangle_tsum_sum {α : Type*} [Fintype α]
    (f : α → Ideal O → Ideal O → ℂ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O,∑' J : Ideal O,
      ∑ a, f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a,∑' I : Ideal O,∑' J : Ideal O,f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by
  have hs (a : α) : Summable (fun v : Ideal O × Ideal O =>
      f a v.1 v.2*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2) :=
    summable_of_hasFiniteSupport ((rectangle_hasFiniteSupport W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
      hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).mul_right _)
  have hi (I : Ideal O) := Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod_factor I)
  simp_rw [hi]
  exact Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem factorTuple_product (v : ι → Ideal O) (I J : Ideal O) :
    (∏ i,factorTuple v I J i)=(∏ i,v i)*I*J := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false,mul_assoc]

theorem full_mask_eq_allocated_rectangles (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O) (hD : Squarefree D)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0) =
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a := by
    rw [← factorTuple_product]
    exact squarefree_mask_allocation D hD Finset.univ _
  simp_rw [he,Finset.sum_mul]
  simp_rw [rectangle_tsum_sum _ W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

end SevenEighths.CenteredMomentDivisorFullMask

end

end OAI
end OAIOriginalModule1340

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorRaw
Source SHA256: 3dc64fa0e72cae7c6d2434aacea90e5b08f8a0da996fe70315775b41bf1506bc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1341


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorSlots
open CenteredMomentDivisorRectangle CenteredMomentDivisorRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => (selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

def liveIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => ¬(selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

theorem split_slot_product {M : Type*} [CommMonoid M] (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (f : ι → M) :
    (∏ i∈frozenIndices D a,f i)*(∏ i∈liveIndices D a,f i)=∏ i,f i :=
  Finset.prod_filter_mul_prod_filter_not _ _ _

theorem selected_live_slot (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ liveIndices D a) (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal O))
    (hS : ∀ I∈S,Prime I) (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (IdealMobiusDivisorSum.support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    exact selected_frozen_slot_bound η m A z t D a i hi (S i) (hS i) (β i) (M i) (hM i) (hβ i)
  · apply le_of_eq
    apply Finset.prod_congr rfl
    intro i hi
    rw [selected_live_slot η m A z t D a i hi]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

def selectedNorm (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  (Ideal.absNorm (selectedPlain D a 0):ℝ)*(Ideal.absNorm (selectedPlain D a 1):ℝ)

theorem selectedNorm_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    0 < selectedNorm D a := by
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a _))

def rawRemaining (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) : ℝ := (T/selectedNorm D a)*∏ i∈liveIndices D a,P i

def formalReductionFactor (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) : ℝ := selectedNorm D a*∏ i∈frozenIndices D a,P i

theorem raw_scale_identity (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) :
    rawRemaining D a T P*formalReductionFactor D a P=T*∏ i,P i := by
  unfold rawRemaining formalReductionFactor
  rw [← split_slot_product D a P]
  field_simp [(selectedNorm_pos D a).ne']

end SevenEighths.CenteredMomentDivisorRaw

end

end OAI
end OAIOriginalModule1341

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy
Source SHA256: 452d7c6d0909811254ca595a4967386e0765072a82b70c14f4848b5fa7450f69
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1342


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_norm_sq (T : ℝ) (hT : 0 < T) (x : ℂ) :
    ‖(Real.sqrt T:ℂ)⁻¹*x‖^2=‖x‖^2/T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,
    Real.sq_sqrt hT.le]
  ring

def residualCenteredRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  centeredSlotRow η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
    (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1))
    (T/selectedNorm D a)

theorem allocated_raw_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 := by
  let R : ℂ :=
    rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
    rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))
  let L : ℂ := R*∏ i∈liveIndices D a,rowSlot η m A z (S i) (β i) t
  have hn : ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      (∏ i∈frozenIndices D a,M i)*‖L‖ := by
    apply (allocatedRectangle_norm_le η m A z t S β D a W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).trans
    have hh := mul_le_mul_of_nonneg_left
      (selected_slot_product_bound η m A z t D a S hS β M hM hβ) (norm_nonneg R)
    dsimp only [L]
    rw [norm_mul,norm_prod]
    convert hh using 1 ; ring
  have hraw : 0 < rawRemaining D a T P := mul_pos (div_pos hT (selectedNorm_pos D a))
    (Finset.prod_pos (fun i _ => hP i))
  have hformal : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hres : ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 =
      ‖L‖^2/rawRemaining D a T P := by
    unfold residualCenteredRow centeredSlotRow
    rw [Finset.prod_coe_sort (liveIndices D a) P,
      Finset.prod_coe_sort (liveIndices D a) (fun i => rowSlot η m A z (S i) (β i) t)]
    exact normalized_norm_sq _ hraw L
  rw [normalized_norm_sq _ htotal,hres]
  calc
    _ ≤ ((∏ i∈frozenIndices D a,M i)*‖L‖)^2/(T*∏ i,P i) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) htotal.le
    _ = _ := by
      rw [← raw_scale_identity D a T P,mul_pow]
      field_simp [hraw.ne',hformal.ne']

end SevenEighths.CenteredMomentDivisorRawEnergy

end

end OAI
end OAIOriginalModule1342

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorRowEnergy
Source SHA256: 9b06f4c2c421df0e354aab78e610cf4a1cd84c465525ae8c693512f141954c59
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1343



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRowEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRows CenteredMomentDivisorFullMask
open CenteredMomentDivisorEnergy CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem actual_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι ⊕ Fin 2) (N+2) (by omega) ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  have hc : (Finset.univ : Finset (ι ⊕ Fin 2)).card ≤ N+2 := by
    simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hslots 2
  have hrow (z : O) :
      ‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
        (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
    unfold maskedRectangle
    rw [full_mask_eq_allocated_rectangles η m A z t S β D hD W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
    calc
      _ ≤ (∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) => (1:ℝ))
          (fun a => ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖))
  calc
    _ ≤ ∑ z ∈ rows,ω z*((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrow z) (hω z hz))
    _ = (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
      simp_rw [mul_left_comm (ω _) _,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero Finset.univ hc)
      (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun z hz => mul_nonneg (hω z hz) (sq_nonneg _))))

end SevenEighths.CenteredMomentDivisorRowEnergy

end

end OAI
end OAIOriginalModule1343

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDegree
Source SHA256: 16adee87ae4c181d8190be87eda2b545082f06a5e08d45eb6e529f37edd54ff9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1344


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeTwist CenteredMomentLattice
open CenteredMomentMask CenteredMomentTwist CenteredMomentHeight CenteredMomentHeckeSlots
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem volumeControl_uniform_degree (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ Q : Ideal O, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro Q W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ χ hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q : Ideal O, Q≠0 → ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η χ ψ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      (Q ≤ ψ.modulus) → CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A₀ z : O, (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
          twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := volumeControl_uniform_degree a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := volumeControl_uniform_degree a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ Q W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ Q W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η χ ψ hnorm hQψ hind m A₀ z hmLam hm2 hrow t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

theorem row_rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q : Ideal O, Q≠0 → ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩ := rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

theorem slots_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q : Ideal O, Q≠0 → ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A z : O),
      m ≠ 0 → A ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀ (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (p b M : ι → ℝ),
      (∀ i, 0 < p i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ P ∈ S i, ‖β i P‖ ≤ M i) →
      (∀ i, ∀ P ∈ S i, β i P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ b i*p i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β p t X₁ X₂ Y₁ Y₂ T‖ ≤
        C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*M i)*(Real.sqrt (T*∏ i,p i)/L) := by
  obtain ⟨J,hJ⟩ := row_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β p b M hp hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖ ≤ (128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i => rowSlot η m A z (S i) (β i) t)
    (fun i => 128*b i*M i) p (C*Z^ε*(1+‖t‖)^J) T L
    (by positivity) hT hL (fun i => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hmLam hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule1344

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
Source SHA256: 98803ec478799b188928cc6d8d73ef4249d0ffdbef8e9d03424efe629f2d5c20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1345


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open FourierBridge JointLogSeparation CompletedHeight CenteredMomentLattice
open EisensteinSchwartzPoisson

theorem frequencyTwist_source_control (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (t : ℝ),
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤
          C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g * (1 + ‖t‖)^n := by
  let T := S.biUnion fun z => (Finset.range (z.2+1)).image fun i => (z.1,i)
  let c : ℕ × ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*(z.2+1)
  let C := 1 + ∑ z ∈ S, c z
  have hc (z) : 0 ≤ c z := by dsimp [c]; positivity
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z)
    dsimp [C]; linarith
  refine ⟨S.sup Prod.snd,T,C,hC,?_⟩
  intro g t
  have hder (z) (hz : z ∈ S) : derivativeSeminormSum g z.1 z.2 ≤
      (z.2+1:ℝ) * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
    calc
      _ ≤ ∑ i ∈ Finset.range (z.2+1), T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
        apply Finset.sum_le_sum
        intro i hi
        apply Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (i := (z.1,i))
        exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      _ = _ := by simp
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z ≤ C := by
    have := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]; linarith
  calc
    _ ≤ ((2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2) *
        (1+‖t‖)^z.2 := frequencyTwist_seminorm_polynomial g t z.1 z.2
    _ ≤ (c z * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^z.2 := by
      dsimp only [c]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hder z hz)
          (show 0 ≤ (2:ℝ)^z.2*(1+2*Real.pi)^z.2 by positivity))
        (show 0 ≤ (1+‖t‖)^z.2 by positivity)).trans_eq (by ring)
    _ ≤ (C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^(S.sup Prod.snd) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hzC (apply_nonneg _ _)
      · exact pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)
      · positivity
      · positivity

theorem normPowerProfile_source_control (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ, ℂ), ∀ hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b,
      ∀ t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := schwartzCLM_finite_seminorm_control (fixedLogReturnCLM a b ha) S
  obtain ⟨n,S₂,C₂,hC₂,h₂⟩ := frequencyTwist_source_control S₁
  obtain ⟨T,C₃,hC₃,h₃⟩ := schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM a b) S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W hs t
  have heq : CubicReflectionKernel.logSchwartz W a b ha hs (W.smooth ⊤) =
      CubicReflectionKernel.logPullbackCLM a b W := by
    ext u
    rw [CubicReflectionKernel.logSchwartz_apply,
      CubicReflectionKernel.logPullbackCLM_eq_actual a b ha W hs]
  have ht : (1+‖t/(2*Real.pi)‖)^n ≤ (1+‖t‖)^n := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  unfold normPowerProfile uniformTwistedSchwartz
  rw [heq]
  calc
    _ ≤ C₁ * S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (CubicReflectionKernel.logPullbackCLM a b W) (t/(2*Real.pi))) := h₁ _
    _ ≤ C₁ * (C₂ * (C₃ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (1+‖t‖)^n) := by
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      exact (h₂ _ _).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (h₃ W) hC₂.le) ht (by positivity) (by positivity))
    _ = _ := by ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1345

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalPrimitive
Source SHA256: 686c4713b5ea8bd81f76c30a43f1e362934f342e55d0d4a4ee262737b14c4bf2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1346



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentNaturalPrimitive
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def redundantSet (M C : Ideal O) : Finset (Ideal O) := primeSupport M\primeSupport C

def redundantIdeal (M C : Ideal O) : Ideal O := ∏P∈redundantSet M C,P

lemma redundantSet_prime (M C : Ideal O) : ∀P∈redundantSet M C,Prime P :=
  fun _ h=>support_prime (Finset.mem_sdiff.mp h).1

lemma redundantSet_subset (M C : Ideal O) : redundantSet M C⊆primeSupport M :=
  Finset.sdiff_subset

lemma prime_mem_support_iff (M P : Ideal O) (hM : M≠0) (hP : Prime P) :
    P∈primeSupport M ↔ P∣M := by
  simp only [primeSupport,Multiset.mem_toFinset,Ideal.mem_normalizedFactors_iff hM]
  exact ⟨fun h=>Ideal.dvd_iff_le.mpr h.2,fun h=>⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp h⟩⟩

lemma mem_redundantSet (M C P : Ideal O) (hC : C≠0) :
    P∈redundantSet M C ↔ P∈primeSupport M ∧ ¬P∣C := by
  constructor
  · intro h
    obtain ⟨hp,hc⟩ := Finset.mem_sdiff.mp h
    exact ⟨hp,fun hd=>hc ((prime_mem_support_iff C P hC (support_prime hp)).mpr hd)⟩
  · rintro ⟨hp,hc⟩
    exact Finset.mem_sdiff.mpr ⟨hp,fun h=>hc ((prime_mem_support_iff C P hC (support_prime hp)).mp h)⟩

lemma redundantIdeal_squarefree (M C : Ideal O) : Squarefree (redundantIdeal M C) :=
  squarefree_support_product (redundantSet_subset M C)

lemma redundantIdeal_ne_zero (M C : Ideal O) : redundantIdeal M C≠0 :=
  support_product_ne_zero (redundantSet_subset M C)

lemma redundantIdeal_support (M C : Ideal O) : primeSupport (redundantIdeal M C)=redundantSet M C := by
  unfold primeSupport redundantIdeal
  rw [factors_support_product (redundantSet_subset M C)]
  exact Finset.val_toFinset _

lemma redundantIdeal_coprime (M C : Ideal O) (hC : C≠0) : IsCoprime (redundantIdeal M C) C := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff (redundantIdeal_ne_zero M C) hC).mp
  rw [redundantIdeal_support]
  exact Finset.disjoint_left.mpr (fun P hp hc=>(Finset.mem_sdiff.mp hp).2 hc)

lemma primitive_redundant_dvd (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C*redundantIdeal M C∣M := by
  exact (redundantIdeal_coprime M C hC).symm.mul_dvd hCM
    (support_product_dvd hM (redundantSet_subset M C))

lemma primitive_redundant_norm (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C.absNorm*(redundantIdeal M C).absNorm≤M.absNorm := by
  have h := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (map_dvd Ideal.absNorm (primitive_redundant_dvd M C hM hC hCM))
  simpa only [map_mul] using h

lemma coprime_support_iff (I M : Ideal O) (hM : M≠0) :
    IsCoprime I M ↔ ∀P∈primeSupport M,IsCoprime I P := by
  have hprod (s : Multiset (Ideal O)) : IsCoprime I s.prod ↔ ∀P∈s,IsCoprime I P := by
    induction s using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_right : IsCoprime I (1 : Ideal O))
    | cons a s ih => simp only [Multiset.prod_cons,IsCoprime.mul_right_iff,Multiset.mem_cons,
        forall_eq_or_imp,ih]
  calc
    _ ↔ IsCoprime I (normalizedFactors M).prod := by rw [Ideal.prod_normalizedFactors_eq_self hM]
    _ ↔ _ := by simpa only [primeSupport,Multiset.mem_toFinset] using hprod (normalizedFactors M)

lemma coprime_original_iff (I M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    IsCoprime I M ↔ IsCoprime I C ∧ ∀P∈redundantSet M C,IsCoprime I P := by
  constructor
  · intro h
    refine ⟨h.of_isCoprime_of_dvd_right hCM,?_⟩
    intro P hP
    exact (coprime_support_iff I M hM).mp h P ((redundantSet_subset M C) hP)
  · rintro ⟨hIC,hIR⟩
    apply (coprime_support_iff I M hM).mpr
    intro P hP
    by_cases hPC : P∈primeSupport C
    · exact (coprime_support_iff I C hC).mp hIC P hPC
    · exact hIR P (Finset.mem_sdiff.mpr ⟨hP,hPC⟩)

theorem idealCoeff_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (I : Ideal O) :
    idealCoeff χ I=idealCoeff (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
      (redundantSet_prime χ.modulus ψ.modulus)) I := by
  rw [hmask I,idealCoeff_excludePrimes]
  have hm := coprime_original_iff I χ.modulus ψ.modulus χ.modulus_ne_bot ψ.modulus_ne_bot
    (Ideal.dvd_iff_le.mpr hmod)
  by_cases hC : IsCoprime I ψ.modulus
  · rw [hm]
    simp only [hC,true_and]
  · have hz : idealCoeff ψ I=0 := by simpa only [hC,ite_false] using idealCoeff_source_mask ψ I
    simp only [hz,ite_self]

theorem polynomial_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (inverse : Bool) (W : ℝ→ℂ) (D σ t : ℝ) :
    HeckeDyadic.polynomial χ inverse W D σ t=
      HeckeDyadic.polynomial (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
        (redundantSet_prime χ.modulus ψ.modulus)) inverse W D σ t := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [idealCoeff_natural_deletion χ ψ hmod hmask I.val]

theorem exists_natural_primitive (χ : Character) :
    ∃ψ : Character,χ.modulus≤ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (χ.residue≠1 → ψ.residue≠1) ∧
      Squarefree (redundantIdeal χ.modulus ψ.modulus) ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      ψ.modulus*redundantIdeal χ.modulus ψ.modulus∣χ.modulus ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀I : Ideal O,idealCoeff χ I=idealCoeff
        (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
          (redundantSet_prime χ.modulus ψ.modulus)) I := by
  obtain ⟨ψ,hmod,hprim,_,hmask⟩ := exists_primitive_character χ
  refine ⟨ψ,hmod,hprim,?_,redundantIdeal_squarefree _ _,redundantIdeal_coprime _ _ ψ.modulus_ne_bot,
    primitive_redundant_dvd _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    primitive_redundant_norm _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    idealCoeff_natural_deletion χ ψ hmod hmask⟩
  intro hχ hψ
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr hψ)

end SevenEighths.CenteredMomentNaturalPrimitive
end

end OAI
end OAIOriginalModule1346

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceMask
Source SHA256: 157f212ba5bab6088dc2c676c5a87e36b632b6768c32f8f5f37d74a8252af177
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1347



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma support_prime (R P : Ideal O) (hP : P∈primeSupport R) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma coprime_support_iff (I R : Ideal O) (hR : R≠0) :
    (∀P∈primeSupport R,IsCoprime I P) ↔ IsCoprime I R := by
  constructor
  · intro h
    have aux : ∀s : Multiset (Ideal O),(∀P∈s,IsCoprime I P)→IsCoprime I s.prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simpa using (isCoprime_one_right : IsCoprime I 1)
      | @cons a s ih =>
        intro hs
        rw [Multiset.prod_cons]
        exact (hs a (Multiset.mem_cons_self _ _)).mul_right
          (ih (fun P hP=>hs P (Multiset.mem_cons_of_mem hP)))
    rw [←Ideal.prod_normalizedFactors_eq_self hR]
    exact aux _ (fun P hP=>h P (Multiset.mem_toFinset.mpr hP))
  · intro h P hP
    exact h.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

def excluded (χ : Character) (R : Ideal O) : Character :=
  χ.excludePrimes (primeSupport R) (support_prime R)

lemma excluded_ideal (χ : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=if IsCoprime I R then idealCoeff χ I else 0 := by
  simp only [excluded,idealCoeff_excludePrimes,coprime_support_iff I R hR]

lemma excluded_element (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime (Ideal.span {n}) R then elementCoeff χ n else 0 := by
  by_cases hn : n=0
  · subst n
    have hh : elementCoeff (excluded χ R) 0=0 := by
      rw [excluded,Character.excludePrimes,elementCoeff_refineModulus,hχ0]
      split_ifs <;> rfl
    rw [hh,hχ0]
    split_ifs <;> rfl
  · rw [←idealCoeff_span _ hn,excluded_ideal χ R hR,idealCoeff_span χ hn]

lemma excluded_element_generator (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime n (idealGenerator R) then elementCoeff χ n else 0 := by
  rw [excluded_element χ hχ0 R hR]
  conv_lhs => rw [←span_idealGenerator R,Ideal.isCoprime_span_singleton_iff]

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end OAIOriginalModule1347

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Poisson
Source SHA256: 17363b43e0df1502cd7f761793765020810e798c2e81082c75646d4ee9a0e4c2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1348


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPoisson
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentFourier

theorem full_gauss_pair_poisson (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    letI := finite_quotient_span hu
    letI := finite_quotient_span hv
    letI : Fintype (Residue u) := Fintype.ofFinite _
    letI : Fintype (Residue v) := Fintype.ofFinite _
    (∑' z : O, residueGauss u hu χu (Ideal.Quotient.mk _ z) *
      star (residueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K : ℂ) * ∑' j : O, fullModulusCorrelation u v χu χv (-j) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) := by
  let := finite_quotient_span hu
  let := finite_quotient_span hv
  let := finite_quotient_span (mul_ne_zero hu hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  let : Fintype (Residue (u * v)) := Fintype.ofFinite _
  let P := fun h : Residue (u * v) =>
    residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
      star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h))
  have hcoeff (j : O) :
      (∑ r : Residue (u * v), P r * quotientTrace (u * v) (mul_ne_zero hu hv)
        (Ideal.Quotient.mk _ j * r)) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv (-j) := by
    have ht := actual_gauss_correlation u v hu hv χu χv (-j)
    have heq (r : Residue (u * v)) : -(r * Ideal.Quotient.mk _ (-j)) =
        Ideal.Quotient.mk _ j * r := by
      simp only [map_neg, mul_neg, neg_neg]
      exact mul_comm _ _
    simp_rw [heq] at ht
    exact ht
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (‖eisEmbedding (u * v)‖ ^ 2 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    norm_cast
  have hpoisson := actual_radial_paper_poisson_trace W K hK (u * v) (mul_ne_zero hu hv) P
  change (∑' z : O, P (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (u * v)‖ ^ 2 : ℝ) •
      ∑' j : O, (∑ r : Residue (u * v), P r * quotientTrace (u * v) (mul_ne_zero hu hv)
        (Ideal.Quotient.mk _ j * r)) *
          paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) at hpoisson
  simp only [P, frequencyReduction_mk] at hpoisson ⊢
  rw [hpoisson]
  change (K / ‖eisEmbedding (u * v)‖ ^ 2 : ℝ) •
    (∑' j : O, (∑ r : Residue (u * v), P r * quotientTrace (u * v) (mul_ne_zero hu hv)
      (Ideal.Quotient.mk _ j * r)) *
      paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2)) = _
  simp_rw [hcoeff, hcard, mul_assoc]
  rw [tsum_mul_left, Complex.real_smul, Complex.ofReal_div, ← mul_assoc]
  have hn : (‖eisEmbedding (u * v)‖ ^ 2 : ℂ) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (mul_ne_zero hu hv))))
  rw [Complex.ofReal_pow, div_mul_cancel₀ _ hn]

theorem normalized_gauss_pair_poisson (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    letI := finite_quotient_span hu
    letI := finite_quotient_span hv
    letI : Fintype (Residue u) := Fintype.ofFinite _
    letI : Fintype (Residue v) := Fintype.ofFinite _
    (∑' z : O, normalizedResidueGauss u hu χu (Ideal.Quotient.mk _ z) *
      star (normalizedResidueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : O, fullModulusCorrelation u v χu χv (-j) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) := by
  let := finite_quotient_span hu
  let := finite_quotient_span hv
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hterm (z : O) :
      normalizedResidueGauss u hu χu (Ideal.Quotient.mk _ z) *
        star (normalizedResidueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K) =
      (ru * rv)⁻¹ * (residueGauss u hu χu (Ideal.Quotient.mk _ z) *
        star (residueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖eisEmbedding z‖ ^ 2 / K)) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, full_gauss_pair_poisson u v hu hv χu χv W K hK]
  dsimp only [ru, rv]
  ring

theorem sextic_gauss_pair_poisson (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) z /
        (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ)) *
      star (ProbePhysical.sexticGauss v (supported_element_ne_zero v hv) z /
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ)) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : O, actualCorrelation u v hu hv (-j) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (u * v)‖ ^ 2) := by
  have h := normalized_gauss_pair_poisson u v
    (supported_element_ne_zero u hu) (supported_element_ne_zero v hv)
    (supportedModulusCharacter u hu) (supportedModulusCharacter v hv) W K hK
  simpa only [normalizedResidueGauss, residueGauss_supported_mk, actualCorrelation,
    supportedCorrelation] using h

end SevenEighths.CenteredMomentPoisson
end

end OAI
end OAIOriginalModule1348

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPoisson
Source SHA256: e720702873a48d46800061a9f308e8aadc933467746c11e4b3436dec66837888
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1349


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFirstPoisson
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

lemma principalCRT_scaled_left (a b : O) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  simp only [map_mul, hb, zero_mul]

lemma principalCRT_scaled_right (a b : O) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  simp only [map_mul, ha, zero_mul]

theorem coprime_character_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem residueGauss_inverse (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    residueGauss d hd χ⁻¹ h = star (residueGauss d hd χ (-h)) := by
  let := finite_quotient_span hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  have htrace (x : Residue d) : star (quotientTrace d hd x) = quotientTrace d hd (-x) := by
    rw [Complex.star_def, ← Complex.inv_eq_conj ((quotientTrace d hd).norm_apply x),
      AddChar.map_neg_eq_inv]
  simp only [residueGauss, tsum_fintype, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

theorem coprime_pair_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x)) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a)) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        star (residueGauss b hb χb (-(frequencyReduction b (a * b) (dvd_mul_left b a) h))) := by
  simp only [MulChar.star_apply']
  rw [coprime_character_fourier a b ha hb hcop χa χb⁻¹ h, residueGauss_inverse]

theorem coprime_pair_poisson (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, χa (Ideal.Quotient.mk _ z) * star (χb (Ideal.Quotient.mk _ z)) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) *
        (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
      ∑' j : O, residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) *
        paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P := fun x : Residue (a * b) =>
    χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
      star (χb (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hcoeff (j : O) :
      (∑ r : Residue (a * b), P r * quotientTrace (a * b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk _ j * r)) =
      (χa (Ideal.Quotient.mk _ b) * star (χb (Ideal.Quotient.mk _ a))) *
        (residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    have h := coprime_pair_fourier a b ha hb hcop χa χb (Ideal.Quotient.mk _ j)
    simpa only [P, frequencyReduction_mk, map_neg, mul_assoc] using h
  have hpoisson := actual_radial_paper_poisson_trace W K hK (a * b) (mul_ne_zero ha hb) P
  change (∑' z : O, P (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) •
      ∑' j : O, (∑ r : Residue (a * b), P r * quotientTrace (a * b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk _ j * r)) *
          paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) at hpoisson
  simp only [P, frequencyReduction_mk] at hpoisson
  rw [hpoisson]
  change (K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) •
    (∑' j : O, (∑ r : Residue (a * b), P r * quotientTrace (a * b) (mul_ne_zero ha hb)
      (Ideal.Quotient.mk _ j * r)) *
      paperRadialFourier W (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2)) = _
  simp_rw [hcoeff, mul_assoc]
  simp_rw [tsum_mul_left]
  rw [Complex.real_smul]

end SevenEighths.CenteredMomentFirstPoisson
end

end OAI
end OAIOriginalModule1349

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CalibrationCRT
Source SHA256: 8b959980cda702c19574fbffcabdec524da979475df31bf725dd9c2bf4f0a552
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1350




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem coprime_mixed_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        residueGauss a ha χa (frequencyReduction a (a*b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
          quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem calibration_mixed_fourier (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) =
      C.residueMonoid b * star (C.residueMonoid H) * (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        (∑' y : Residue b, F (Ideal.Quotient.mk _ C.generator*y) *
          quotientTrace b hb (Ideal.Quotient.mk _ H*y)) := by
  dsimp only
  let C := calibrationForSet S hS
  let := finite_quotient_span C.generator_ne_zero
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero C.generator_ne_zero hb)
  let : Fintype (Residue C.generator) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (C.generator*b)) := Fintype.ofFinite _
  rw [tsum_fintype, coprime_mixed_fourier _ _ C.generator_ne_zero hb hcop]
  change C.residueMonoid b * calibrationGauss C H * _ = _
  rw [calibrationForSet_gauss]
  rw [tsum_fintype]
  dsimp only [C]
  simp only [frequencyReduction_mk]
  ring

theorem calibration_mixed_fourier_zero (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) = 0 := by
  dsimp only
  rw [calibration_mixed_fourier S hS b hb hcop F H]
  have hz : (calibrationForSet S hS).residueMonoid H=0 := by
    change (calibrationForSet S hS).residue (Ideal.Quotient.mk _ H)=0
    apply MulChar.map_nonunit
    exact fun h => hH ((isUnit_quotient_span_iff _ _).mp h)
  rw [hz, star_zero]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1350

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FrequencySupport
Source SHA256: b01983419b2fd94f976c056324f24e0b1571b6b93360c3775bc833da5ede4996
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1351



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def elementFourier (c : O) (hc : c≠0) (f : O → ℂ) (H : O) : ℂ :=
  ∑' x : Residue c, f (representative c x) * quotientTrace c hc (Ideal.Quotient.mk _ H*x)

lemma elementFourier_congr (c d : O) (hc : c≠0) (hd : d≠0) (f : O → ℂ) (H : O)
    (he : c=d) : elementFourier c hc f H = elementFourier d hd f H := by
  subst d
  rfl

def movingQuotient (A s : O) (hs : s≠0) (x : Residue (A*s)) : ℂ :=
  idealRowHom (representative (A*s) x) (Ideal.span {A}) *
    sexticGauss s hs (-representative (A*s) x)

lemma movingQuotient_mk (A s : O) (hs : s≠0) (m : O) :
    movingQuotient A s hs (Ideal.Quotient.mk _ m) =
      idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m) := by
  have hd : A*s ∣ representative (A*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative (A*s) (Ideal.Quotient.mk _ m)-m ∈ (Ideal.span {A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right A s).trans hd)
  have hs' : -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) ∈ (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative (A*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s A).trans hd)
  unfold movingQuotient
  rw [idealRowHom_congr_mod _ _ _ hA, sexticGauss_frequency_congr s hs _ (-m) hs']

lemma physicalFourier_eq_element (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      elementFourier (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
        (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H := by
  change elementFourier ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
    (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H = _
  apply elementFourier_congr
  exact mul_assoc _ _ _

lemma physicalFourier_eq_mixed (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      ∑' x : Residue (C.generator*(A*s)),
        C.residue (frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x) *
          movingQuotient A s hs (frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x) *
          quotientTrace (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
            (Ideal.Quotient.mk _ H*x) := by
  rw [physicalFourier_eq_element]
  unfold elementFourier
  apply tsum_congr
  intro x
  have he : Ideal.Quotient.mk (Ideal.span {C.generator*(A*s)})
      (representative (C.generator*(A*s)) x) = x := representative_spec _ _
  have hrA : frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  have hrB : frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  rw [hrA, hrB, movingQuotient_mk]
  change _ = (C.residueMonoid _ * (_ * _)) * _

  ring

theorem actualPhysicalFourier_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualPhysicalFourier (calibrationForSet S hS) A s hA hs H=0 := by
  rw [physicalFourier_eq_mixed]
  exact calibration_mixed_fourier_zero S hS (A*s) (mul_ne_zero hA hs) hcop (movingQuotient A s hs) H hH

theorem actualCongruenceCoefficient_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA H=0 := by
  have he := actualPhysicalFourier_zero_off_calibration S hS A s hA hs hcop H hH
  rw [actualPhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  exact (mul_eq_zero.mp he).resolve_left hn

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1351

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
Source SHA256: 36cfd6b37ce7823c249e0f1e9535bd5ddc405e83a19d102f365b20757ef69fc8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1352



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_unit_scale (s : O) (hs : Supported (Ideal.span {s}))
    (b h : O) (hcop : IsCoprime b s) :
    sexticGauss s (supportedElement_ne_zero s hs) (b*h) =
      (idealRowHom b (Ideal.span {s}))⁻¹ * sexticGauss s (supportedElement_ne_zero s hs) h := by
  let := finite_quotient_span (supportedElement_ne_zero s hs)
  let : Fintype (Residue s) := Fintype.ofFinite _
  let χ := supportedModulusCharacter s hs
  let ψ := quotientTrace s (supportedElement_ne_zero s hs)
  let u := residueUnit s b hcop.symm
  have he := gaussSum_mulShift_eq χ (ψ.mulShift (Ideal.Quotient.mk _ h)) u
  simp only [gaussSum, AddChar.mulShift_apply, MulChar.inv_apply_eq_inv', u, residueUnit_coe,
    χ, supportedModulusCharacter_mk] at he
  rw [← residueGauss_supported_mk s hs (b*h), ← residueGauss_supported_mk s hs h]
  simp only [residueGauss, tsum_fintype, map_mul]
  simpa only [ψ, mul_assoc, mul_comm, mul_left_comm] using he

lemma movingQuotient_unit_scale (A s : O) (hs : Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b s) (x : Residue (A*s)) :
    movingQuotient A s (supportedElement_ne_zero s hs) (Ideal.Quotient.mk _ b*x) =
      idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹ *
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, movingQuotient_mk, movingQuotient_mk, idealRowHom_argument_mul]
  rw [show -(b*m)=b*(-m) by ring, sexticGauss_unit_scale s hs b (-m) hcop]
  ring

def barePhysicalFourier (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  elementFourier (A*s) (mul_ne_zero hA hs)
    (fun m => idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H

theorem actualPhysicalFourier_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualPhysicalFourier C A s hA (supportedElement_ne_zero s hs) H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  rw [physicalFourier_eq_mixed, calibration_mixed_fourier S hS (A*s)
    (mul_ne_zero hA (supportedElement_ne_zero s hs)) hcop]
  dsimp only [C] at hcs ⊢
  simp_rw [movingQuotient_unit_scale A s hs (calibrationForSet S hS).generator hcs]
  simp only [mul_assoc, tsum_mul_left]
  rfl

def bareCongruenceCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient A s hA (outerQuotient A) (outerQuotient s) H

lemma barePhysicalFourier_eq (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    barePhysicalFourier A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ)*bareCongruenceCoefficient A s hA H := by
  unfold bareCongruenceCoefficient
  rw [← fullFourier_eq_congruence A s hA hs]
  unfold barePhysicalFourier elementFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction A s m = Ideal.Quotient.mk (Ideal.span {A}) (representative (A*s) m) := by
    conv_lhs => rw [← representative_spec (A*s) m]
    rfl
  rw [he]
  unfold outerQuotient
  rw [sexticGauss_coefficient_mk]

theorem actualCongruenceCoefficient_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s hA H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      bareCongruenceCoefficient A s hA H := by
  dsimp only
  have he := actualPhysicalFourier_calibration_factor S hS A s hA hs hcop H
  dsimp only at he
  rw [actualPhysicalFourier_eq, barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1352

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CalibrationCancellation
Source SHA256: 2e6bedeaedd3c5c2f5869a6a3478b81984d4dfe12b396e79077c1a47729ec95e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1353



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma Xi_apply (C : CalibrationData) (a : O) :
    C.Xi a = C.residueMonoid a * idealRowHom C.generator (Ideal.span {a}) := rfl

theorem calibration_coefficient_cancel (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H *
      idealRowHom C.generator (Ideal.span {s}) /
        ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid H)) *
      (C.Xi A)⁻¹ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcA : IsCoprime C.generator A := hcop.of_mul_right_left
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  have hXA : C.Xi A≠0 := by
    intro h
    have hn := C.Xi_norm_one A hA hcA
    rw [h, norm_zero] at hn
    norm_num at hn
  have hXs : C.Xi s≠0 := by
    intro h
    have hn := C.Xi_norm_one s hs hcs
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [Xi_apply] at hXA hXs
  have hηA := left_ne_zero_of_mul hXA
  have hκA := right_ne_zero_of_mul hXA
  have hηs := left_ne_zero_of_mul hXs
  have hκs := right_ne_zero_of_mul hXs
  have hηH : C.residueMonoid H≠0 :=
    C.residue.apply_ne_zero_iff.mpr ((isUnit_quotient_span_iff C.generator H).mpr hH)
  have hηHstar : star (C.residueMonoid H)≠0 := star_ne_zero.mpr hηH
  have hτ : C.tau≠0 := calibrationForSet_tau_ne_zero S hS
  have hq : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hroot : (Real.sqrt (elementNorm C.generator):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have he := actualCongruenceCoefficient_calibration_factor S hS A s
    (supportedElement_ne_zero A hA) hs hcop H
  dsimp only at he
  rw [he, Xi_apply, map_mul]
  change _ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H
  dsimp only [C] at hηA hκA hηs hκs hηHstar hτ hroot
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1353

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LocalPhysical
Source SHA256: 853242bc20a864a714dad73e8cb7c3077fa893fe19f0d4e322db0a381b0991a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1354



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma outerQuotient_prime_power (p : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (k : ℕ) (hk : k≠0) (d : O ⧸ Ideal.span {p^k}) :
    outerQuotient (p^k) d =
      (actualSextic (Ideal.span {p}) hg ^ k)
        (Ideal.Quotient.mk _ (representative (p^k) d)) := by
  unfold outerQuotient
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg, MulChar.pow_apply' _ hk]

lemma sexticGauss_prime_power (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (n : ℕ) (H : O) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(n+1)) n H := by
  have he : sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      quotientFourier p (p^(n+1)) (pow_ne_zero _ hp.ne_zero)
        (actualSextic (Ideal.span {p}) hg^(n+1)) H := by
    unfold sexticGauss quotientFourier
    apply tsum_congr
    intro d
    have hc := outerQuotient_prime_power p hg (n+1) (by omega) d
    change idealRowHom (representative (p^(n+1)) d) (Ideal.span {p^(n+1)}) = _ at hc
    rw [hc]
    rw [(Ideal.Quotient.mk (Ideal.span {p^(n+1)})).map_mul, representative_spec]
  rw [he, primePowerGauss_eq_quotientFourier]
  apply quotientFourier_congr
  exact pow_succ' p n

theorem bareCongruenceCoefficient_prime_power_pos (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (n k j : ℕ) (hk : k≠0) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  unfold bareCongruenceCoefficient congruenceCoefficient
  rw [positiveScalar, ite_eq_right hk]
  apply tsum_congr
  intro d
  rw [outerQuotient_prime_power p hg k hk]
  split_ifs with hd
  · rw [rawFourier_outer, sexticGauss_prime_power p hp hg]
  · ring

lemma sexticGauss_one (H : O) : sexticGauss 1 one_ne_zero H=1 := by
  let : Subsingleton (O ⧸ Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  let : Unique (O ⧸ Ideal.span {(1:O)}) := uniqueOfSubsingleton 0
  let : Fintype (O ⧸ Ideal.span {(1:O)}) := Fintype.ofFinite _
  unfold sexticGauss
  have hrow (d : O ⧸ Ideal.span {(1:O)}) :
      idealRowHom (representative 1 d) (Ideal.span {(1:O)})=1 := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  simp only [hrow, one_mul]
  have ht (d : O ⧸ Ideal.span {(1:O)}) :
      quotientTrace 1 one_ne_zero (Ideal.Quotient.mk _ H*d)=1 := by
    rw [Subsingleton.elim (Ideal.Quotient.mk _ H*d) 0, AddChar.map_zero_eq_one]
  simp only [ht, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]

lemma barePhysicalFourier_outer_one (A : O) (hA : A≠0) (H : O) :
    barePhysicalFourier A 1 hA one_ne_zero H = sexticGauss A hA H := by
  unfold barePhysicalFourier
  rw [elementFourier_congr (A*1) A (mul_ne_zero hA one_ne_zero) hA _ H (mul_one A)]
  simp only [sexticGauss_one, mul_one]
  rfl

lemma bareCongruenceCoefficient_outer_one (A : O) (hA : A≠0) (H : O) :
    bareCongruenceCoefficient A 1 hA H=sexticGauss A hA H := by
  have he := barePhysicalFourier_eq A 1 hA one_ne_zero H
  rw [barePhysicalFourier_outer_one] at he
  simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, Nat.cast_one, one_mul] using he.symm

theorem bareCongruenceCoefficient_prime_power (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (n k j : ℕ) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  by_cases hk : k=0
  · subst k
    rw [pow_zero, bareCongruenceCoefficient_outer_one, sexticGauss_prime_power p hp hg,
      positiveScalar_kzero]
  · exact bareCongruenceCoefficient_prime_power_pos p hp hg n k j hk

theorem bareCongruenceCoefficient_inner_one (s : O) (hs : s≠0) (H : O) :
    bareCongruenceCoefficient 1 s one_ne_zero H = outerQuotient s (Ideal.Quotient.mk _ H) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  have htest (d : O ⧸ Ideal.span {s}) :
      s∣H-1*representative s d ↔ d=Ideal.Quotient.mk _ H := by
    rw [one_mul, ← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      representative_spec, eq_comm]
  have hraw (k : O) : rawFourier 1 one_ne_zero (outerQuotient 1) k=1 := by
    rw [rawFourier_outer, sexticGauss_one]
  unfold bareCongruenceCoefficient congruenceCoefficient
  simp_rw [hraw]
  simp only [tsum_fintype]
  rw [Finset.sum_eq_single (Ideal.Quotient.mk _ H)]
  · rw [dite_eq_left ((htest _).mpr rfl), mul_one]
  · intro d hd hne
    rw [dite_eq_right ((htest d).not.mpr hne), mul_zero]
  · simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1354

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
Source SHA256: d9b9c31ec2acfaddd4bca0fc2475151c9947851b39b27eb7f7721a77c98557a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1355


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalRowCompletion GaussianShiftedPartition
open CanonicalQuadraticSieve CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentFirstPoisson CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem coprime_function_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (Fa : Residue a → ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      Fa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      (∑ x : Residue a, Fa (Ideal.Quotient.mk _ b*x) *
        quotientTrace a ha (frequencyReduction a (a*b) (dvd_mul_right a b) h*x)) *
      (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
        quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [ he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem sexticGauss_coprime_product (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : IsCoprime a b) (H : O) :
    sexticGauss (a*b) (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)) H =
      idealRowHom b (Ideal.span {a}) * idealRowHom a (Ideal.span {b}) *
        sexticGauss a (supportedElement_ne_zero a ha) H *
        sexticGauss b (supportedElement_ne_zero b hb) H := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let := finite_quotient_span (supportedElement_ne_zero b hb)
  let := finite_quotient_span (mul_ne_zero (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a*b)) := Fintype.ofFinite _
  have he := coprime_character_fourier a b (supportedElement_ne_zero a ha) (supportedElement_ne_zero b hb)
    hcop (supportedModulusCharacter a ha) (supportedModulusCharacter b hb) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk,
    residueGauss_supported_mk] at he
  rw [← he]
  unfold sexticGauss
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sexticGauss_coefficient_mk]
  simp only [frequencyReduction_mk, supportedModulusCharacter_mk]
  congr 1
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma elementFourier_const_mul (c : O) (hc : c≠0) (F : O → ℂ) (H : O) (B : ℂ) :
    elementFourier c hc (fun m => B*F m) H = B*elementFourier c hc F H := by
  simp only [elementFourier, mul_assoc, tsum_mul_left]

lemma bareMoving_product (A B s r : O) (hs : Supported (Ideal.span {s}))
    (hr : Supported (Ideal.span {r})) (hcop : IsCoprime s r) (m : O) :
    idealRowHom m (Ideal.span {A*B}) *
      sexticGauss (s*r) (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) (-m) =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      ((idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) := by
  rw [sexticGauss_coprime_product s r hs hr hcop]
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  ring

theorem barePhysicalFourier_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    barePhysicalFourier (A*B) (s*r) (mul_ne_zero hA hB)
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero r hr)) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
  have hsc : IsCoprime s r := hcop.of_mul_left_right.of_mul_right_right
  have hc1 : IsCoprime (B*r) s := hcop.of_mul_left_right.symm
  have hc2 : IsCoprime (A*s) r := hcop.of_mul_right_right
  have hAs := mul_ne_zero hA (supportedElement_ne_zero s hs)
  have hBr := mul_ne_zero hB (supportedElement_ne_zero r hr)
  let := finite_quotient_span hAs
  let := finite_quotient_span hBr
  let := finite_quotient_span (mul_ne_zero hAs hBr)
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let : Fintype (Residue (B*r)) := Fintype.ofFinite _
  let : Fintype (Residue ((A*s)*(B*r))) := Fintype.ofFinite _
  have he := coprime_function_fourier (A*s) (B*r) hAs hBr hcop
    (movingQuotient A s (supportedElement_ne_zero s hs))
    (movingQuotient B r (supportedElement_ne_zero r hr)) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk] at he
  simp_rw [movingQuotient_unit_scale A s hs (B*r) hc1,
    movingQuotient_unit_scale B r hr (A*s) hc2, mul_assoc] at he
  simp only [← Finset.mul_sum] at he
  have hexpand : elementFourier ((A*s)*(B*r)) (mul_ne_zero hAs hBr)
      (fun m => (idealRowHom m (Ideal.span {A}) * sexticGauss s (supportedElement_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (supportedElement_ne_zero r hr) (-m))) H =
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H *
      barePhysicalFourier B r hB (supportedElement_ne_zero r hr) H := by
    unfold elementFourier
    rw [tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hmk := representative_spec ((A*s)*(B*r)) x
        have hred1 : frequencyReduction (A*s) ((A*s)*(B*r)) (dvd_mul_right _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        have hred2 : frequencyReduction (B*r) ((A*s)*(B*r)) (dvd_mul_left _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        rw [hred1, hred2, movingQuotient_mk, movingQuotient_mk]
        ring
      _ = _ := he
      _ = _ := by
        simp only [barePhysicalFourier, elementFourier, movingQuotient, tsum_fintype]
        ring
  simp only [barePhysicalFourier] at hexpand
  unfold barePhysicalFourier
  rw [elementFourier_congr ((A*B)*(s*r)) ((A*s)*(B*r)) _ (mul_ne_zero hAs hBr) _ H (by ring)]
  simp_rw [bareMoving_product A B s r hs hr hsc]
  rw [elementFourier_const_mul, hexpand]
  ring

theorem bareCongruenceCoefficient_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  have he := barePhysicalFourier_product A B s r hA hB hs hr hcop H
  simp only [barePhysicalFourier_eq] at he
  have hnorm : Ideal.absNorm (Ideal.span {s*r}) =
      Ideal.absNorm (Ideal.span {s}) * Ideal.absNorm (Ideal.span {r}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm, Nat.cast_mul] at he
  have hns : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  have hnr : (Ideal.absNorm (Ideal.span {r}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero r hr))
  apply mul_left_cancel₀ (mul_ne_zero hns hnr)
  rw [he]
  ring

lemma idealRowHom_ne_zero_of_coprime (s a : O)
    (hs : Supported (Ideal.span {s})) (hc : IsCoprime s a) :
    idealRowHom a (Ideal.span {s})≠0 := by
  rw [← supportedModulusCharacter_mk s hs a]
  exact (supportedModulusCharacter s hs).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff s a).mpr hc)

theorem bareCongruenceCoefficient_product_reduced (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  rw [bareCongruenceCoefficient_product A B s r hA hB hs hr hcop H]
  have hsr := idealRowHom_ne_zero_of_coprime s r hs
    hcop.of_mul_left_right.of_mul_right_right
  have hrs := idealRowHom_ne_zero_of_coprime r s hr
    hcop.of_mul_left_right.of_mul_right_right.symm
  have hsB := idealRowHom_ne_zero_of_coprime s B hs
    hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr
    hcop.of_mul_left_left.of_mul_right_right.symm
  simp only [idealRowHom_argument_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1355

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CubicGaussCRT
Source SHA256: b1624a922827f505a97694bc59e702ac994d1d28b06d24ff7d0efa8c416cf192
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1356




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CompletedGauss ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gaussTwo_eq_elementFourier (I : Ideal O) (hI : CubicSieve.Admissible I) :
    gaussTwo I hI.2 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 /
        (‖eisEmbedding (primaryGenerator I)‖:ℂ) := by
  let := finite_quotient_span hI.2
  let : Fintype (Residue (primaryGenerator I)) := Fintype.ofFinite _
  rw [CubicSieve.gaussTwo_eq_gaussSum I hI]
  unfold gaussSum elementFourier
  rw [tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]
  simp only [map_one, one_mul]
  rfl

lemma residueGauss_principalCubicCharacter (I : Ideal O) (hI : CubicSieve.Admissible I)
    [Fintype (Residue (primaryGenerator I))] :
    residueGauss (primaryGenerator I) hI.2 (CubicSieve.principalCubicCharacter I hI) 1 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 := by
  simp only [residueGauss, elementFourier, tsum_fintype, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]

theorem gaussTwo_coprime_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      (CubicSieve.cubicRow I (primaryGenerator J) * CubicSieve.cubicRow J (primaryGenerator I)) *
      gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  have hc : IsCoprime a b := by
    rw [← Ideal.isCoprime_span_singleton_iff]
    simpa only [a,b,(primaryGenerator_spec I hI.2).1,(primaryGenerator_spec J hJ.2).1] using hcop
  let := finite_quotient_span hI.2
  let := finite_quotient_span hJ.2
  let := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a*b)) := Fintype.ofFinite _
  have he := coprime_character_fourier a b hI.2 hJ.2 hc
    (CubicSieve.principalCubicCharacter I hI) (CubicSieve.principalCubicCharacter J hJ) 1
  simp only [map_one] at he
  have hfour : elementFourier (a*b) (mul_ne_zero hI.2 hJ.2)
      (CubicSieve.cubicRow (I*J)) 1 =
      (CubicSieve.cubicRow I b * CubicSieve.cubicRow J a) *
        elementFourier a hI.2 (CubicSieve.cubicRow I) 1 *
        elementFourier b hJ.2 (CubicSieve.cubicRow J) 1 := by
    unfold elementFourier
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [CubicSieve.cubicRow_mul]
        have hi : CubicSieve.cubicRow I (representative (a*b) (Ideal.Quotient.mk _ m)) =
            CubicSieve.cubicRow I m := by
          rw [← CubicSieve.principalCubicCharacter_mk I hI, ← CubicSieve.principalCubicCharacter_mk I hI]
          congr 1
          apply Ideal.Quotient.eq.mpr
          have hx := Ideal.Quotient.eq.mp (representative_spec (a*b) (Ideal.Quotient.mk _ m))
          exact Ideal.mem_span_singleton.mpr ((dvd_mul_right a b).trans (Ideal.mem_span_singleton.mp hx))
        have hj : CubicSieve.cubicRow J (representative (a*b) (Ideal.Quotient.mk _ m)) =
            CubicSieve.cubicRow J m := by
          rw [← CubicSieve.principalCubicCharacter_mk J hJ, ← CubicSieve.principalCubicCharacter_mk J hJ]
          congr 1
          apply Ideal.Quotient.eq.mpr
          have hx := Ideal.Quotient.eq.mp (representative_spec (a*b) (Ideal.Quotient.mk _ m))
          exact Ideal.mem_span_singleton.mpr ((dvd_mul_left b a).trans (Ideal.mem_span_singleton.mp hx))
        rw [hi,hj]
        simp only [frequencyReduction_mk, map_one, one_mul]
        rw [CubicSieve.principalCubicCharacter_mk I hI m, CubicSieve.principalCubicCharacter_mk J hJ m]
      _ = _ := he
      _ = _ := by
        rw [CubicSieve.principalCubicCharacter_mk I hI b,
          CubicSieve.principalCubicCharacter_mk J hJ a,
          residueGauss_principalCubicCharacter I hI, residueGauss_principalCubicCharacter J hJ]
        simp only [elementFourier, tsum_fintype]
        rfl
  rw [gaussTwo_eq_elementFourier (I*J) hIJ, gaussTwo_eq_elementFourier I hI,
    gaussTwo_eq_elementFourier J hJ]
  have hgen : primaryGenerator (I*J)=a*b := primaryGenerator_mul I J
  rw [elementFourier_congr _ (a*b) hIJ.2 (mul_ne_zero hI.2 hJ.2) _ 1 hgen, hfour]
  rw [hgen, map_mul, norm_mul, Complex.ofReal_mul]
  ring

theorem gaussTwo_coprime_product_sextic (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      ProbePhase.sexticPair (primaryGenerator I) (primaryGenerator J)^2 *
        gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  rw [gaussTwo_coprime_product I J hI hJ hIJ hcop]
  simp only [CubicSieve.cubicRow, ← idealRowHom_square, ProbePhase.sexticPair,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1, mul_pow]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1356

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalLocalEuler
Source SHA256: 59744e9d65c34d8209cc52288edac81e8b6fdd07bfe1b598ffc19943d8b9eca6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1357



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O

