    activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (Ideal.Quotient.mk _ z)=activeFunction I J hI (Ideal.Quotient.mk _ z):=by
  simp only [activeFunction]
  exact activeRow_extracted I J hI z

def mappedSubset (I J:Ideal O)(E:Finset (CommonIndex I J)):
    Finset (CommonIndex (commonPart I J) (commonPart J I)):=E.map (commonEquiv I J).toEmbedding

theorem mappedSubset_product (I J:Ideal O)(E:Finset (CommonIndex I J)):
    (∏P∈mappedSubset I J E,P.val)=∏P∈E,P.val:=by
  simp only [mappedSubset,Finset.prod_map,Equiv.toEmbedding_apply,commonEquiv_val]

theorem mappedSubset_generator (I J:Ideal O)(E:Finset (CommonIndex I J)):
    primeSubsetGenerator (fun P:CommonIndex (commonPart I J) (commonPart J I)=>P.val)
      (mappedSubset I J E)=primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E:=by
  unfold primeSubsetGenerator
  rw [mappedSubset_product]

theorem mappedSubset_inactive (I J:Ideal O)(E:Finset (CommonIndex I J)):
    mappedSubset I J E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I) ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J:=by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp:=h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp
  · intro h P hP
    obtain ⟨R,hR,rfl⟩:=Finset.mem_map.mp hP
    have hr:=h hR
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hr

theorem nominal_extracted (I J:Ideal O)(E:Finset (CommonIndex I J))(K X:ℝ):
    CenteredMomentFirstScale.firstNominalScale (commonPart I J) (commonPart J I)
      (∏P∈mappedSubset I J E,P.val) K X=
    CenteredMomentFirstScale.firstNominalScale I J (∏P∈E,P.val) K X:=by
  obtain ⟨hc,hd⟩:=fixed_common_parts (commonPart I J) (commonPart J I)
    (commonPart_ne_zero I J) (commonPart_ne_zero J I) (commonParts_equal_support I J)
  unfold CenteredMomentFirstScale.firstNominalScale
  rw [mappedSubset_product,activeConductor_extracted,hc,hd]

end SevenEighths.CenteredMomentFirstCommonTransport

end

end OAI
end OAIOriginalModule1677

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCommonFourierTransport
Source SHA256: 94a80550d74a1af395eb1dce1090664de7b3bf8caf90b2335f5fd4e358435e2f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1678


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonFourierTransport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentFirstCommonTransport
local notation "O"=>ActualEisensteinCubic.O

theorem quotient_function_heq (r r':O)(hr:r'=r)
    (G:Residue r→ℂ)(G':Residue r'→ℂ)
    (hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z)):
    HEq G' G:=by
  subst r'
  apply heq_of_eq
  funext x
  obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
  exact hG z

def retainedFourierTerm (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let k:=K/normValue e
  (UniqueFactorizationMonoid.moebius E:ℂ)*tripleRow a b r χa χb G e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑'h:O,
      (retainedWeight R (normValue h):ℂ)*tripleFourier a b r ha hb hr χa χb G h*
        EisensteinSchwartzPoisson.paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem retainedFourierTerm_transport (a b r r':O)(ha:a≠0)(hb:b≠0)(hr:r≠0)(hr':r'≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)(G':Residue r'→ℂ)
    (he:r'=r)(hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z))
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r' ha hb hr' χa χb G' e E W K R=
      retainedFourierTerm a b r ha hb hr χa χb G e E W K R:=by
  subst r'
  have hg:G'=G:=eq_of_heq (quotient_function_heq r r rfl G G' hG)
  subst G'
  rfl

def fixedRetainedTerm (C D:Ideal O)(hC:Supported C)(a b:O)
    (ha:Supported (Ideal.span {a}))(hb:Supported (Ideal.span {b}))
    (E:Finset (CommonIndex C D))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  retainedFourierTerm a b (activeConductor C D)
    (supported_element_ne_zero _ ha) (supported_element_ne_zero _ hb) (finitePrimeModulus_ne_zero _)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem canonicalRetainedTerm_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (E:Finset (CommonIndex I J))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    canonicalRetainedTerm I J hI hJ E W K
      (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ=
    fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (residualGenerator I J) (residualGenerator J I)
      (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ)
      (mappedSubset I J E) W K X Z ξ:=by
  unfold fixedRetainedTerm
  rw [nominal_extracted,mappedSubset_generator,mappedSubset_product]
  have hh:=retainedFourierTerm_transport (residualGenerator I J) (residualGenerator J I)
    (activeConductor I J) (activeConductor (commonPart I J) (commonPart J I))
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (finitePrimeModulus_ne_zero _) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹
    (activeFunction I J hI) (activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI))
    (activeConductor_extracted I J) (activeFunction_mk_extracted I J hI)
    (primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ)
  exact hh.symm

def inactiveEquiv (I J:Ideal O):
    CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J ≃
      CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I):=
  (Equiv.finsetCongr (commonEquiv I J)).subtypeEquiv (fun E=>(mappedSubset_inactive I J E).symm)

@[simp] theorem inactiveEquiv_val (I J:Ideal O)
    (E:CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J):
    (inactiveEquiv I J E).val=mappedSubset I J E.val:=rfl

theorem canonicalRetainedPair_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
    ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I),
      fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
        (residualGenerator I J) (residualGenerator J I)
        (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ) E W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedPair
  apply Finset.sum_bij (fun E _=>mappedSubset I J E)
  · intro E hE
    exact (mappedSubset_inactive I J E).mpr hE
  · intro E hE F hF he
    exact (Equiv.finsetCongr (commonEquiv I J)).injective he
  · intro F hF
    obtain ⟨E,he⟩:=(Equiv.finsetCongr (commonEquiv I J)).surjective F
    change mappedSubset I J E=F at he
    exact ⟨E,(mappedSubset_inactive I J E).mp (he.symm ▸ hF),he⟩
  · intro E hE
    exact canonicalRetainedTerm_fixed I J hI hJ E W K X Z ξ

end SevenEighths.CenteredMomentFirstCommonFourierTransport

end

end OAI
end OAIOriginalModule1678

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
Source SHA256: bfb4758a6423b4cfe08b0e19f84f51515144a0450e4e2f3a7ed6861a20ee2f2a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1679



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI
end OAIOriginalModule1679

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailPair
Source SHA256: 57884e73c894ca46be63e8e3f5bbdd9c4747582c5267e1cd1af05ba58677ff6e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1680


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum CenteredMomentFirstDiscardedEnergy
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_tail_denominator_mono (Tlocal Tupper H Z ξ:ℝ)(A:ℕ)(B:ℝ)
    (hT:0<Tlocal)(hupper:Tlocal≤Tupper)(hB:0≤B)(hZ:0≤Z):
    B/((min 1 (kernelReference Tlocal H))^2*(1+Z^(ξ/4))^A)≤
      B/((min 1 (kernelReference Tupper H))^2*(1+Z^(ξ/4))^A):=by
  have hu:0<Tupper:=hT.trans_le hupper
  have hk:kernelReference Tupper H≤kernelReference Tlocal H:=by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT hupper
  have hm:0<min 1 (kernelReference Tupper H):=lt_min zero_lt_one (kernelReference_pos _ _ hu)
  have hp:0≤Z^(ξ/4):=Real.rpow_nonneg hZ _
  apply div_le_div_of_nonneg_left hB (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ hm.le (min_le_min_left 1 hk) 2

theorem local_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => by
        let Tlocal:=firstNominalScale I J (∏ P∈E,P.val) K X
        have hE0:(∏ P∈E,P.val)≠(0:Ideal O):=by
          have he:=primeSubsetGenerator_ne_zero (fun P:CommonIndex I J=>P.val) E
          have hh:=Ideal.span_singleton_eq_bot.not.mpr he
          simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
        have hTl:0<Tlocal:=firstNominalScale_pos I J _ hE0 K X hK hX
        have hTu:Tlocal≤Tsec:=(first_nominal_scale_le I J E K X hK).trans hsec
        have hh:=ht W I J hI hJ E K X HN Tlocal Z Csec ξ hK hX hZ hCs hi hj le_rfl hthreshold
        exact hh.trans (local_tail_denominator_mono Tlocal Tsec HN Z ξ A
          (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) hTl hTu (by positivity) (zero_lt_one.trans hZ).le))
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
end OAIOriginalModule1680

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailAggregate
Source SHA256: 756e1cd9c2d5a11441373d1e49182fce34100bfd407aa9dba3b5a7d5d750427c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1681



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

theorem local_discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t S c W K X Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := local_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ‖≤B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj hsec hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => CenteredMomentFirstSectorLocalization.discardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K X Z ξ)
    (fun I => rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
end OAIOriginalModule1681

/-! Original module: OAI.NumberTheory.DirichletL.Moments.UniformDivisorShell
Source SHA256: e1cca22cd758f6cec24f72cef3be7aea8d82aa97ddc8166b10a5e77421e4643b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1682


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def ShellBound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε:ℝ) : Prop := ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2)

theorem uniform_subset_shell {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,ShellBound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ ShellBound p.1 p.2 C ε:=
    paired_all_active_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD T Z hT hZ hlo hhi
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD T Z hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

theorem paired_entrance_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L)
      (lo hi:ι→ℝ), (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((∑i,logWindow (lo i) (hi i))/Real.log Z) := by
  obtain ⟨C,hC,hbound⟩:=uniform_subset_shell (ι:=ι) ε hε
  refine ⟨C,hC,?_⟩
  intro J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  apply (hbound J L s v Ds hD T Z hT hZ hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hs:=subset_allowance J s lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v lo hi hvlo hvhi Z hZ
  linarith

theorem numerical_allowance (Z H:ℝ) (hZ:1<Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

theorem paired_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤C*Z^δ := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:2*B*ε≤δ:=by
    have hh:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=paired_entrance_allowance (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD T Z hT hZ hTZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=hbound J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  rw [numerical_allowance Z _ hZ,Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le] at hh
  have hpow:T^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  apply hh.trans
  calc
    C*(2^(2*ε)*T^(2*ε))*E=(C*2^(2*ε)*E)*T^(2*ε):=by ring
    _≤(C*2^(2*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hpow (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformDivisorShell

end

end OAI
end OAIOriginalModule1682

/-! Original module: OAI.NumberTheory.DirichletL.Moments.EligibleEnergy
Source SHA256: a7d6b9ec985e26a4f8918d4a4fa48f3145540cacbc400350fc3b39dd8dacbb45
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1683


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

structure Data (ι:Type*) [Fintype ι] extends Source ι where
  M : ι→ℝ
  M_ge_one : ∀i,1≤M i
  coefficient_bound : ∀i,∀I∈slots i,‖ν i I*W i ((Ideal.absNorm I:ℝ)/P i)‖≤M i
  b₁ : ℝ
  b₂ : ℝ
  support₁ : Function.support W₁⊆Set.Iic b₁
  support₂ : Function.support W₂⊆Set.Iic b₂
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : Y₁*Y₂=X₁*X₂
  rows : Finset O
  weight : O→ℝ
  weight_nonneg : ∀z∈rows,0≤weight z

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Data.coefficient (s:Data ι) (i:ι) (I:Ideal O) : ℂ :=
  s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)

def Data.energy (s:Data ι) (D:Ideal O) : ℝ :=
  ∑z∈s.rows,s.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def Data.childEnergy (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑z∈s.rows,s.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

def Data.profileFactor (s:Data ι) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2

lemma Data.energy_nonneg (s:Data ι) (D:Ideal O) : 0≤s.energy D :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (sq_nonneg _))

lemma Data.child_nonneg (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤s.childEnergy D a :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0<formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      s.energy D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s D hD E hE hchild
  have hh:=hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D hD s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product s.rows s.weight s.weight_nonneg
  change s.energy D≤_ at hh
  apply hh.trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      apply mul_le_mul _ (hchild a ha) (s.child_nonneg D a) _
      · apply div_le_div_of_nonneg_right _ (s.reduction_pos D a).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
      · exact div_nonneg s.profile_nonneg (s.reduction_pos D a).le
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma sqrt_sum_le {α:Type*} (S:Finset α) (f:α→ℝ) (hf:∀a∈S,0≤f a) :
    Real.sqrt (∑a∈S,f a)≤∑a∈S,Real.sqrt (f a) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun a _=>Real.sqrt_nonneg _),?_⟩
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun a=>Real.sqrt (f a))
    (fun a _=>Real.sqrt_nonneg _)
  have he:(∑a∈S,Real.sqrt (f a)^2)=∑a∈S,f a:=Finset.sum_congr rfl (fun a ha=>Real.sq_sqrt (hf a ha))
  rwa [he] at hh

lemma sqrt_reciprocal (x:ℝ) (_hx:0<x) : Real.sqrt (1/x)=1/Real.sqrt x := by
  rw [Real.sqrt_div (by norm_num:0≤(1:ℝ)),Real.sqrt_one]

theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      Real.sqrt (s.energy D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI
end OAIOriginalModule1683

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalAllocationShell
Source SHA256: 9386a78205c9486092fbaf4b17eba9b3e9186da7a5fdbc891bc303870935041f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1684


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalAllocationShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
open CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O

lemma exact_max_cancellation (r r₁ : ℝ) :
    -r₁-max (r-r₁) 0 = -max r r₁ := by
  by_cases h : r ≤ r₁
  · rw [max_eq_right (by linarith : r-r₁≤0),max_eq_right h]
    ring
  · rw [max_eq_left (by linarith : 0≤r-r₁),max_eq_left (le_of_not_ge h)]
    ring

def exceptionalWeight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2))) (Z r : ℝ) : ℝ :=
  Z^(-Real.logb Z (formalReductionFactor D a s.P)-
    Real.logb Z (formalReductionFactor D b v.P)-
    max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)

theorem active_exceptional_weight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2)))
    (_ha : a∈s.active D) (hb : b∈v.active D) (Z r : ℝ) (hZ : 1<Z) :
    exceptionalWeight s v D a b Z r ≤ Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : (0:ℝ)<Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hv := v.active_boundary D hD b hb Z hZ
  have hm := exact_max_cancellation r (Real.logb Z (formalReductionFactor D a s.P))
  have he : -Real.logb Z (formalReductionFactor D a s.P)-
      Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0 ≤
      v.allowance Z-r-Real.logb Z (Ideal.absNorm D:ℝ) := by
    linarith [le_max_left r (Real.logb Z (formalReductionFactor D a s.P))]
  unfold exceptionalWeight
  apply (Real.rpow_le_rpow_of_exponent_le hZ.le he).trans_eq
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hn]

theorem actual_exceptional_shell {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (hι : Fintype.card ι≤N) (hκ : Fintype.card κ≤N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by
  obtain ⟨C₁,hC₁,hcard₁⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z r hT hZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc₁ (D : Ideal O) (hd : D∈Ds) : ((s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D : Ideal O) (hd : D∈Ds) : ((v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D : Ideal O) (hd : D∈Ds) :
      (∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤
        (C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := by
    have hn : (0:ℝ)<Ideal.absNorm D := ht.trans_le (hlo D hd)
    have he : (Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε) := by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow : (Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε) :=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _ ≤ ∑_a∈s.active D,∑_b∈v.active D,Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) :=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>
          active_exceptional_weight s v D (hD D hd) a b ha hb Z r hZ))
      _ = ((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by simp; ring
      _ ≤ (C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*
          (Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _ = (C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
        (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _ ≤ ∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := Finset.sum_le_sum hp
    _ = (Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) := by simp
    _ ≤ (256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) :=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _ = (256*C₁*C₂)*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by field_simp

def ShellBound (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε : ℝ) : Prop := ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r)

theorem uniform_subset_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (hε : 0<ε) : ∃C : ℝ,0<C ∧ ∀J L : Finset ι,ShellBound J L C ε := by
  have he (p : Finset ι×Finset ι) : ∃C : ℝ,0<C ∧ ShellBound p.1 p.2 C ε :=
    actual_exceptional_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B : ℝ := 1+∑p : Finset ι×Finset ι,C p
  have hs : 0≤∑p : Finset ι×Finset ι,C p := Finset.sum_nonneg (fun p _=>(hC p).le)
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro J L s v Ds hD T Z r hT hZ hlo hhi
  have hc : C (J,L)≤B := by
    have hp := Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]; linarith
  exact (hbound (J,L) s v Ds hD T Z r hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem exceptional_shell_subpower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι→ℝ) (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(J L : Finset ι) (s : Source J) (v : Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,
      1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r) := by
  let ε : ℝ := δ/(2*(B+1))
  have hε : 0<ε := div_pos hδ (by positivity)
  have he : 2*B*ε≤δ := by
    have hh : ε*(2*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := uniform_subset_shell (ι:=ι) ε hε
  let E : ℝ := Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E]; positivity,?_⟩
  intro J L s v hvlo hvhi Ds hD T Z r hT hZ hTZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hbound J L s v Ds hD T Z r hT hZ hlo hhi
  have hv : Z^(v.allowance Z-r)≤E*Z^(-r) := by
    calc
      _≤Z^((∑i,logWindow (lo i) (hi i))/Real.log Z-r) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le
          (sub_le_sub_right (subset_allowance L v lo hi hvlo hvhi Z hZ) r)
      _=E*Z^(-r) := by rw [sub_eq_add_neg,Real.rpow_add hz,numerical_allowance Z _ hZ]
  have hpow : T^(2*ε)≤Z^δ := by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith [he])
  apply hh.trans
  calc
    _≤C*(2*T)^(2*ε)*(E*Z^(-r)) := mul_le_mul_of_nonneg_left hv (by positivity)
    _=(C*2^(2*ε)*E)*T^(2*ε)*Z^(-r) := by
      rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) ht.le]; ring
    _≤(C*2^(2*ε)*E)*Z^δ*Z^(-r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [E]; positivity)) (by positivity)
    _=(C*2^(2*ε)*E)*Z^(δ-r) := by rw [mul_assoc,←Real.rpow_add hz]; rfl

end SevenEighths.CenteredMomentExceptionalAllocationShell

end

end OAI
end OAIOriginalModule1684

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PairedEligibleEnergy
Source SHA256: 75edeeada2bb71f4a97cdf51ac7560e34f15cf3e90f2cc91b3bad47e4e944056
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1685


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O

lemma reciprocal_sums {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) :
    (∑a∈s.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
      (∑b∈v.active D,1/Real.sqrt (formalReductionFactor D b v.P))=
    ∑a∈s.active D,∑b∈v.active D,
      1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hf:0≤formalReductionFactor D a s.P:=
    (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  rw [Real.sqrt_mul hf]
  ring

theorem actual_paired_source_shell {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  obtain ⟨C₁,hC₁,hl⟩:=actual_source_root_from_children (ι:=ι) N hι ε hε
  obtain ⟨C₂,hC₂,hr⟩:=actual_source_root_from_children (ι:=κ) N hκ ε hε
  obtain ⟨C₃,hC₃,hshell⟩:=paired_all_active_shell (ι:=ι) (κ:=κ) N hι hκ ε hε
  refine ⟨C₁*C₂*C₃,by positivity,?_⟩
  intro s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  let W:ℝ:=Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)
  let θ:ℝ:=(s.toSource.allowance Z+v.toSource.allowance Z)/2
  let F:Ideal O→ℝ:=fun D=>∑a∈s.toSource.active D,∑b∈v.toSource.active D,
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)
  have hW:0≤W:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hF (D:Ideal O):0≤F D:=Finset.sum_nonneg (fun a _=>Finset.sum_nonneg
    (fun b _=>div_nonneg zero_le_one (Real.sqrt_nonneg _)))
  have ht:0<T:=zero_lt_one.trans_le hT
  have hp (D:Ideal O) (hd:D∈Ds):Real.sqrt (s.energy D)*Real.sqrt (v.energy D)≤
      (C₁*C₂)*(2*T)^ε*W*F D:=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have hpow:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
    have hmul:=mul_le_mul (hl s D (hD D hd) E₁ hE₁ (hleft D hd))
      (hr v D (hD D hd) E₂ hE₂ (hright D hd)) (Real.sqrt_nonneg _) (by positivity)
    apply hmul.trans
    calc
      _=(C₁*C₂)*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)^2*W*
          ((∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
           (∑b∈v.toSource.active D,1/Real.sqrt (formalReductionFactor D b v.P))):=by dsimp [W];ring
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^ε*W*F D:=by
        rw [Real.sq_sqrt hpow,reciprocal_sums]
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn.le (hhi D hd).le hε.le) (by positivity)) hW) (hF D)
  calc
    _≤∑D∈Ds,(C₁*C₂)*(2*T)^ε*W*F D:=Finset.sum_le_sum hp
    _=((C₁*C₂)*(2*T)^ε*W)*(∑D∈Ds,F D):=(Finset.mul_sum ..).symm
    _≤((C₁*C₂)*(2*T)^ε*W)*(C₃*(2*T)^(2*ε)*Z^θ):=
      mul_le_mul_of_nonneg_left (hshell s.toSource v.toSource Ds hD T Z hT hZ hlo hhi) (by positivity)
    _=(C₁*C₂*C₃)*(2*T)^(3*ε)*Z^θ*W:=by
      have hpow:(2*T)^ε*(2*T)^(2*ε)=(2*T)^(3*ε):=by
        rw [←Real.rpow_add (by positivity:0<2*T)];congr 1;ring
      calc
        _=(C₁*C₂*C₃)*((2*T)^ε*(2*T)^(2*ε))*Z^θ*W:=by ring
        _=_:=by rw [hpow]

end SevenEighths.CenteredMomentPairedEligibleEnergy

end

end OAI
end OAIOriginalModule1685

/-! Original module: OAI.NumberTheory.DirichletL.Moments.UniformEligibleEnergy
Source SHA256: 4bfb83de41452b76739a16871a135e221ac874bddb2d993bf430fb75d52e22f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1686


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentPairedEligibleEnergy
open CenteredMomentUniformDivisorShell CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def Bound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂))

theorem uniform_subset_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,Bound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ Bound p.1 p.2 C ε:=
    actual_paired_source_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by linarith) _)) (by positivity))

theorem actual_source_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Data J) (v:Data L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀E₁ E₂ T Z:ℝ,
      0≤E₁ → 0≤E₂ → 1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*Z^δ*(Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  let ε:ℝ:=δ/(3*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:3*B*ε≤δ:=by
    have hh:ε*(3*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=uniform_subset_energy (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(3*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hTZ hlo hhi hleft hright
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hs:=subset_allowance J s.toSource lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v.toSource lo hi hvlo hvhi Z hZ
  have hnum:Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)≤E:=by
    dsimp [E]
    rw [←numerical_allowance Z _ hZ]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hh:=hbound J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans
  rw [Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le]
  have hp:T^(3*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  calc
    C*(2^(3*ε)*T^(3*ε))*E=(C*2^(3*ε)*E)*T^(3*ε):=by ring
    _≤(C*2^(3*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hp (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformEligibleEnergy

end

end OAI
end OAIOriginalModule1686

/-! Original module: OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
Source SHA256: d5f9fe3d51245334263ad7544c285338f37ddfebfadce3070f0938b4a577ab1e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1687



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentWholeDivisorShell
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma divisorPool_nonzero_norm {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (Y : ℝ) (hY : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Y)
    (D : Ideal O) (hD : D∈divisorPool T B) : D≠0 ∧ (D.absNorm:ℝ)≤Y := by
  obtain ⟨j,hj,hd⟩:=Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hB j hj)).mp hd
  have hn : 0<(B j).absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB j hj))
  have hle : (D.absNorm:ℝ)≤(B j).absNorm := by
    exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdiv)
  exact ⟨IdealDivisorBound.divisor_ne_zero (hB j hj) hd,hle.trans (hY j hj)⟩

lemma moebius_norm_le_one (D : Ideal O) : ‖(moebius D:ℂ)‖≤1 := by
  by_cases hD : Squarefree D
  · simp only [hD.moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,norm_pow,norm_neg,norm_one,one_pow,le_refl]
  · simp only [moebius_of_not_squarefree hD,Int.cast_zero,norm_zero,zero_le_one]

lemma squarefree_of_moebius_ne_zero (D : Ideal O) (hD : (moebius D:ℂ)≠0) : Squarefree D := by
  by_contra hn
  exact hD (by rw [moebius_of_not_squarefree hn,Int.cast_zero])

def live (Ds : Finset (Ideal O)) : Finset (Ideal O) := Ds.filter (fun D=>(moebius D:ℂ)≠0)

lemma mem_live (Ds : Finset (Ideal O)) (D : Ideal O) :
    D∈live Ds ↔ D∈Ds ∧ (moebius D:ℂ)≠0 := Finset.mem_filter

lemma live_squarefree (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : Squarefree D :=
  squarefree_of_moebius_ne_zero D ((mem_live Ds D).mp hD).2

lemma live_norm_one (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : 1≤(D.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (live_squarefree Ds D hD).ne_zero)

theorem sum_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=∑D∈live Ds,(moebius D:ℂ)*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,zero_mul]

theorem sum_norm_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=∑D∈live Ds,‖(moebius D:ℂ)‖*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,norm_zero,zero_mul]

def normKey (D : Ideal O) : ℤ := ⌊Real.logb 2 (D.absNorm:ℝ)⌋
def shell (Ds : Finset (Ideal O)) (n : ℤ) : Finset (Ideal O) := (live Ds).filter (fun D=>normKey D=n)
def selectedShells (Ds : Finset (Ideal O)) : Finset ℤ := (live Ds).image normKey

lemma normKey_eq_iff (D : Ideal O) (hD : D≠0) (n : ℤ) :
    normKey D=n ↔ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hn : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hl := Real.logb_le_logb (by norm_num : (1:ℝ)<2) (dyadicScale_pos n) hn
  have hu := Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) hn (dyadicScale_pos (n+1))
  simp only [logb_dyadicScale,Int.cast_add,Int.cast_one] at hl hu
  rw [normKey,Int.floor_eq_iff,←hl,←dyadicScale_add,←hu]

lemma mem_shell_iff (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O) :
    D∈shell Ds n ↔ D∈Ds ∧ (moebius D:ℂ)≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  rw [shell,Finset.mem_filter]
  constructor
  · rintro ⟨hd,hk⟩
    exact ⟨((mem_live Ds D).mp hd).1,((mem_live Ds D).mp hd).2,
      (normKey_eq_iff D (live_squarefree Ds D hd).ne_zero n).mp hk⟩
  · rintro ⟨hd,hm,hlo,hhi⟩
    exact ⟨(mem_live Ds D).mpr ⟨hd,hm⟩,
      (normKey_eq_iff D (squarefree_of_moebius_ne_zero D hm).ne_zero n).mpr ⟨hlo,hhi⟩⟩

lemma shell_disjoint (Ds : Finset (Ideal O)) (m n : ℤ) (hmn : m≠n) :
    Disjoint (shell Ds m) (shell Ds n) := by
  apply Finset.disjoint_left.mpr
  intro D hm hn
  exact hmn ((Finset.mem_filter.mp hm).2.symm.trans (Finset.mem_filter.mp hn).2)

lemma shell_nonempty_iff (Ds : Finset (Ideal O)) (n : ℤ) :
    (shell Ds n).Nonempty ↔ n∈selectedShells Ds := by
  constructor
  · rintro ⟨D,hD⟩
    exact Finset.mem_image.mpr ⟨D,(Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro hn
    obtain ⟨D,hD,hk⟩:=Finset.mem_image.mp hn
    exact ⟨D,Finset.mem_filter.mpr ⟨hD,hk⟩⟩

lemma biUnion_shell (Ds : Finset (Ideal O)) :
    (selectedShells Ds).biUnion (shell Ds)=live Ds := by
  ext D
  simp only [Finset.mem_biUnion,shell,Finset.mem_filter]
  constructor
  · rintro ⟨n,hn,hd,hk⟩;exact hd
  · intro hd
    exact ⟨normKey D,Finset.mem_image.mpr ⟨D,hd,rfl⟩,hd,rfl⟩

theorem sum_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,(moebius D:ℂ)*f D := by
  rw [sum_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

theorem sum_norm_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,‖(moebius D:ℂ)‖*f D := by
  rw [sum_norm_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

lemma selected_scale_bounds (Ds : Finset (Ideal O)) (Y : ℝ)
    (hY : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y)
    (n : ℤ) (hn : n∈selectedShells Ds) :
    1≤dyadicScale n ∧ dyadicScale n≤Y := by
  obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hn
  have hd:=live_squarefree Ds D hD
  have hnorm:=live_norm_one Ds D hD
  have hkey : 0≤normKey D := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hnorm)
  have hscale : 1≤dyadicScale (normKey D) := by
    simpa only [dyadicScale,zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hkey
  exact ⟨hscale,((normKey_eq_iff D hd.ne_zero _).mp rfl).1.trans
    (hY D ((mem_live Ds D).mp hD).1 ((mem_live Ds D).mp hD).2)⟩

lemma selected_subset_indices (Ds : Finset (Ideal O)) (Y : ℝ) (hY : 1≤Y)
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y) :
    selectedShells Ds⊆indices 1 Y := by
  intro n hn
  have hh:=selected_scale_bounds Ds Y hbound n hn
  exact (mem_indices_iff_scale 1 Y (by norm_num) (zero_lt_one.trans_le hY) n).mpr
    ⟨hh.1,hh.2.trans (by linarith)⟩

theorem selected_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z)
    (Ds : Finset (Ideal O))
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) :
    ((selectedShells Ds).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hc : ((selectedShells Ds).card:ℝ)≤(indices 1 (Z^B)).card := by
    exact_mod_cast Finset.card_le_card (selected_subset_indices Ds (Z^B) hY hbound)
  have hi:=indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY
    (by simp only [div_one,one_mul,le_refl])
  exact hc.trans (by simpa only [Real.logb_one,add_zero] using hi)

theorem selected_card_subpower (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ((selectedShells Ds).card:ℝ)≤C*Z^δ := by
  let C:=2*(3+B/Real.log 2)
  have hC : 0<C := by
    have hh:=div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [C];linarith
  have ht:=(isLittleO_log_rpow_rpow_atTop (1:ℝ) hδ).bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1)] with Z ht hZ
  have hz : 1<Z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hZ
  have hl : 1≤Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hZ
  have hp : Real.log Z≤Z^δ := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log Z),
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hz).le _),one_mul] using ht
  refine ⟨hz,?_⟩
  intro Ds hb
  apply (selected_card_log B Z hB hz.le Ds hb).trans
  have hk : 0≤3+B/Real.log 2 := by positivity
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hp hk]

theorem divisorPool_card_log {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (L Z : ℝ) (hL : 0≤L) (hZ : 1≤Z)
    (hN : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) :
    ((selectedShells (divisorPool T B)).card:ℝ)≤(3+L/Real.log 2)*(1+Real.log Z) :=
  selected_card_log L Z hL hZ _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

theorem divisorPool_card_subpower (L δ : ℝ) (hL : 0≤L) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α:Type*}(T:Finset α)(B:α→Ideal O),
      (∀j∈T,B j≠0) → (∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) →
      ((selectedShells (divisorPool T B)).card:ℝ)≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L δ hL hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α T B hB hN
  exact hz.2 _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

lemma shell_member_data (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell Ds n) :
    D∈Ds ∧ (moebius D:ℂ)≠0 ∧ Squarefree D ∧ D≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hh:=(mem_shell_iff Ds n D).mp hD
  have hs:=squarefree_of_moebius_ne_zero D hh.2.1
  exact ⟨hh.1,hh.2.1,hs,hs.ne_zero,hh.2.2⟩

theorem finite_pair_mobius_shells {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α→Ideal O) (B : β→Ideal O) (hB : ∀j∈T,B j≠0) (F : α→β→ℂ) :
    (∑i∈S,∑j∈T,if IsCoprime (A i) (B j) then F i j else 0)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        (moebius D:ℂ)*∑i∈S,∑j∈T,if D∣A i ∧ D∣B j then F i j else 0 := by
  rw [finite_pair_mobius S T A B hB F]
  exact sum_moebius_shells _ _

theorem divisorPool_weighted_shells {α : Type*} (T : Finset α) (B : α→Ideal O)
    (f : Ideal O→ℝ) :
    (∑D∈divisorPool T B,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        ‖(moebius D:ℂ)‖*f D := sum_norm_moebius_shells _ _

end SevenEighths.CenteredMomentWholeDivisorShell

end

end OAI
end OAIOriginalModule1687

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
Source SHA256: 8ef3fc41fe855600bb4edd7bc15f5dcaf57acac5dbeb487c708569800a78afff
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1688



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentDivisorAllocation CenteredMomentWholeDivisorShell
open CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
abbrev Label := (Ideal O × Ideal O) × Finset (Ideal O)

def Valid (s : Ideal O) (v : Label) : Prop :=
  v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ primeSupport v.1.1 = primeSupport v.1.2 ∧
  s ∣ v.1.1 ∧ s ∣ v.1.2 ∧ v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)

def weight (v : Label) : ℝ := 1 / Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm)

lemma commonRadical_norm_le (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    (Ideal.absNorm (commonRadical I J):ℝ) ≤ min (I.absNorm:ℝ) J.absNorm := by
  have hd : commonRadical I J ∣ I ∧ commonRadical I J ∣ J := by
    constructor <;> apply (squarefree_dvd_iff _ _ (commonRadical_squarefree I J)).mpr
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).1)
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).2)
  apply le_min
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm hd.1)
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
      (map_dvd Ideal.absNorm hd.2)

lemma min_le_sqrt_mul (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    min x y ≤ Real.sqrt (x*y) := by
  apply (Real.le_sqrt (le_min hx hy) (mul_nonneg hx hy)).mpr
  rcases le_total x y with h|h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

lemma shell_scalar (e Y x y : ℝ) (he : 0<e) (hx : 0<x) (hy : 0<y)
    (hY : min x y ≤ Y) :
    (2*min x y)^(1+e)/Real.sqrt (x*y) ≤ 2^(1+e)*Y^e := by
  have hm : 0<min x y := lt_min hx hy
  have hsqrt : 0<Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  have hs := min_le_sqrt_mul x y hx.le hy.le
  apply (div_le_iff₀ hsqrt).mpr
  calc
    _ ≤ 2^(1+e)*(Real.sqrt (x*y)*Y^e) := by gcongr
    _ = _ := by ring

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0<T₁ → 0<T₂ → min T₁ T₂≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0<Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hsq : 0<Real.sqrt (T₁*T₂) := Real.sqrt_pos.2 (mul_pos hT₁ hT₂)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/Real.sqrt (T₁*T₂) := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hshell v hv).1 (hshell v hv).2.2.1 hT₂.le (hT₁.le.trans (hshell v hv).1)
    _ = (S.card:ℝ)/Real.sqrt (T₁*T₂) := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/Real.sqrt (T₁*T₂) :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/Real.sqrt (T₁*T₂)) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T₁ T₂ he hT₁ hT₂ hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

def key (v : Label) : ℤ×ℤ := (normKey v.1.1,normKey v.1.2)
def keys (S : Finset Label) : Finset (ℤ×ℤ) := S.image key
def shell (S : Finset Label) (n : ℤ×ℤ) : Finset Label := S.filter (fun v=>key v=n)

lemma norm_scale_bounds (I : Ideal O) (hI : I≠0) (Y : ℝ) (hY : (I.absNorm:ℝ)≤Y) :
    1≤dyadicScale (normKey I) ∧ dyadicScale (normKey I)≤Y := by
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hk : 0≤normKey I := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hn)
  refine ⟨?_,((normKey_eq_iff I hI _).mp rfl).1.trans hY⟩
  simpa only [dyadicScale,zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hk

lemma shell_norm_bounds (S : Finset Label) (n : ℤ×ℤ) (v : Label)
    (hv : v∈shell S n) (hC : v.1.1≠0) (hD : v.1.2≠0) :
    dyadicScale n.1≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*dyadicScale n.1 ∧
    dyadicScale n.2≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*dyadicScale n.2 := by
  have he := (Finset.mem_filter.mp hv).2
  have h₁ := (normKey_eq_iff v.1.1 hC n.1).mp (congrArg Prod.fst he)
  have h₂ := (normKey_eq_iff v.1.2 hD n.2).mp (congrArg Prod.snd he)
  exact ⟨h₁.1,h₁.2,h₂⟩

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)^2*(1+Real.log Z)^2 := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ (indices 1 (Z^B))×ˢ(indices 1 (Z^B)) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (h0 v hv).1 (Z^B) (hN v hv).1
    have hd := norm_scale_bounds v.1.2 (h0 v hv).2 (Z^B) (hN v hv).2
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hc.1,hc.2.trans (by linarith)⟩
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hd.1,hd.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ)^2 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product] at hh
    exact_mod_cast (by simpa only [pow_two] using hh)
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  calc
    _ ≤ ((indices 1 (Z^B)).card:ℝ)^2 := hc
    _ ≤ ((3+B/Real.log 2)*(1+Real.log Z))^2 := by gcongr
    _ = _ := by ring

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,weight v)≤C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

lemma log_square_subpower (d : ℝ) (hd : 0<d) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → (1+Real.log Z)^2≤C*Z^d := by
  let a : ℝ := d/2
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨(1+1/a)^2,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^a := Real.one_le_rpow hZ ha.le
  have hl := Real.log_le_rpow_div hz.le ha
  have hh : 1+Real.log Z≤(1+1/a)*Z^a := by
    calc
      _ ≤ Z^a+Z^a/a := add_le_add hp hl
      _ = _ := by ring
  calc
    _ ≤ ((1+1/a)*Z^a)^2 := by
      apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hh
    _ = (1+1/a)^2*Z^d := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le]
      congr 2
      dsimp [a]; ring

theorem common_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end SevenEighths.CenteredMomentCommonHarmonicMass

end

end OAI
end OAIOriginalModule1688

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonRadicalHarmonicMass
Source SHA256: 34f0e1600ba09213c352a230beaec3d1dafa3f56467c12a7fe51a5d5e1440e90
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1689


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadicalHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentWholeDivisorShell CenteredMomentDyadicCount CenteredMomentSectorLocalization
open CenteredMomentCommonHarmonicMass (Label Valid commonRadical_norm_le norm_scale_bounds log_square_subpower)
local notation "O" => ActualEisensteinCubic.O

def weight (v : Label) : ℝ := 1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)
def key (v : Label) : ℤ := normKey (commonRadical v.1.1 v.1.2)
def keys (S : Finset Label) : Finset ℤ := S.image key
def shell (S : Finset Label) (n : ℤ) : Finset Label := S.filter (fun v=>key v=n)

lemma radical_ne_zero (v : Label) : commonRadical v.1.1 v.1.2≠0 :=
  Squarefree.ne_zero (commonRadical_squarefree _ _)

lemma shell_scalar (e Y T : ℝ) (he : 0<e) (hT : 0<T) (hTY : T≤Y) :
    (2*T)^(1+e)/T≤2^(1+e)*Y^e := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hT.le,
    Real.rpow_add hT,Real.rpow_one]
  calc
    _ = 2^(1+e)*T^e := by field_simp
    _ ≤ 2^(1+e)*Y^e := by gcongr

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) → ∀Y T : ℝ,0<T → T≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
        (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*T) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T hT hTY hN hshell
  have hY : 0<Y := hT.trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*T) hY hY (by positivity) hN
    (fun v hv=>(hshell v hv).2.le)
  calc
    _ ≤ ∑_v∈S,1/T := by
      apply Finset.sum_le_sum
      intro v hv
      exact one_div_le_one_div_of_le hT (hshell v hv).1
    _ = (S.card:ℝ)/T := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*T)^(1+e)/(s.absNorm:ℝ))/T :=
      div_le_div_of_nonneg_right hc hT.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*T)^(1+e)/T) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T he hT hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

lemma shell_norm_bounds (S : Finset Label) (n : ℤ) (v : Label) (hv : v∈shell S n) :
    dyadicScale n≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
    (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*dyadicScale n := by
  exact (normKey_eq_iff _ (radical_ne_zero v) n).mp (Finset.mem_filter.mp hv).2

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ indices 1 (Z^B) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (h0 v hv).1 (h0 v hv).2).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z^B) hr
    exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
      ⟨hc.1,hc.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  exact hc.trans hi

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,weight v)≤C*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z^B) hr
    have hm : dyadicScale n≤Z^B := by
      exact hkey ▸ hc.2
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K*(1+Real.log Z))*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K)*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

theorem common_radical_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ))≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hl : 1+Real.log Z≤D*Z^(δ/2) := by
    have hn := Real.log_nonneg hZ1
    exact (show 1+Real.log Z≤(1+Real.log Z)^2 by nlinarith).trans (hlog Z hZ1)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end SevenEighths.CenteredMomentCommonRadicalHarmonicMass

end

end OAI
end OAIOriginalModule1689

/-! Original module: OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass
Source SHA256: 29f71b4cc9d0e5534ce0fb23c91d5d514b12d0b03b11f5b83d617a26f3bd8f9f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1690



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentMobiusHarmonicMass
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentDivisorBoundary CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma shell_mass (Ds:Finset (Ideal O)) (n:ℤ) (hn:n∈selectedShells Ds) :
    (∑D∈shell Ds n,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤256 := by
  have ht:1≤dyadicScale n:=
    (selected_scale_bounds Ds (∑D∈Ds,(Ideal.absNorm D:ℝ))
      (fun D hD _=>Finset.single_le_sum (fun D _=>Nat.cast_nonneg _) hD) n hn).1
  have htp:0<dyadicScale n:=zero_lt_one.trans_le ht
  have hcard:=divisor_dyad_card (shell Ds n) (dyadicScale n) ht
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.1)
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.2)
  calc
    _≤∑D∈shell Ds n,1/dyadicScale n:=by
      apply Finset.sum_le_sum
      intro D hd
      have hh:=(shell_member_data Ds n D hd).2.2.2.2.1
      exact div_le_div₀ (by norm_num) (moebius_norm_le_one D) htp hh
    _=((shell Ds n).card:ℝ)/dyadicScale n:=by simp [div_eq_mul_inv]
    _≤256:=(div_le_iff₀ htp).mpr hcard

 theorem full_mass_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (Ideal.absNorm D:ℝ)≤Z^B) →
      (∑D∈Ds,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower B δ hB hδ
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Ds hn
  have he:=sum_norm_moebius_shells Ds (fun D=>1/(Ideal.absNorm D:ℝ))
  simp only [mul_one_div] at he
  rw [he]
  calc
    _≤∑n∈selectedShells Ds,(256:ℝ):=Finset.sum_le_sum (fun n hn=>shell_mass Ds n hn)
    _=((selectedShells Ds).card:ℝ)*256:=by simp
    _≤(C*Z^δ)*256:=mul_le_mul_of_nonneg_right (hZ.2 Ds hn) (by norm_num)
    _=_:=by ring

 theorem actual_divisorPool_mass (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤Z^B) →
      (∑D∈divisorPool T v,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn
  exact hZ.2 (divisorPool T v) (fun D hd _=>(divisorPool_nonzero_norm T v hv (Z^B) hn D hd).2)

end SevenEighths.CenteredMomentMobiusHarmonicMass

end

end OAI
end OAIOriginalModule1690

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ZeroMode
Source SHA256: 707cff1bebaaee8bbe026a054e2bfc02eaa7972d55a6fe0dea5474b1c4f12d80
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1691



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentZeroMode
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcreteTraceCRT CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount CenteredExceptionalProfile
local notation "O" => ActualEisensteinCubic.O

@[simp] theorem pairResidue_mul (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x y : Residue (a * b)) :
    pairResidue a b ha hb (x * y) =
      pairResidue a b ha hb x * pairResidue a b ha hb y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, pairResidue_mk, pairResidue_mk, pairResidue_mk,
    idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

@[simp] theorem pairFourier_zero (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    pairFourier a b ha hb 0 = ∑' x : Residue (a * b), pairResidue a b ha hb x := by
  simp [pairFourier, quotientTrace]

theorem pairResidue_unit_eq_one_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (u : (Residue (a * b))ˣ) :
    pairResidue a b ha hb u = 1 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype] at hm
  have he : pairResidue a b ha hb u * (∑ x : Residue (a * b), pairResidue a b ha hb x) =
      ∑ x : Residue (a * b), pairResidue a b ha hb x := by
    simpa only [Finset.mul_sum, pairResidue_mul] using
      u.mulLeft_bijective.sum_comp (pairResidue a b ha hb)
  exact (mul_right_cancel₀ hm (he.trans (one_mul _).symm))

theorem rows_agree_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (n : O)
    (hn : IsCoprime (Ideal.span {n}) (Ideal.span {a} * Ideal.span {b})) :
    idealRowHom n (Ideal.span {a}) = idealRowHom n (Ideal.span {b}) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {a * b}) n) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [Ideal.span_singleton_mul_span_singleton] using hn
  have he := pairResidue_unit_eq_one_of_mean_ne_zero a b ha hb hm hunit.unit
  rw [hunit.unit_spec, pairResidue_mk] at he
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) n) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hn.of_mul_right_right
  have hj : idealRowHom n (Ideal.span {b}) * star (idealRowHom n (Ideal.span {b})) = 1 := by
    change supportedModulusCharacter b hb (Ideal.Quotient.mk _ n) *
      star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ n)) = 1
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
    exact MulChar.one_apply hu
  exact mul_right_cancel₀ (by intro hz; simp [hz] at hj) (he.trans hj.symm)

theorem valuation_profile_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    valuation (Ideal.span {a}) P % 6 = valuation (Ideal.span {b}) P % 6 := by
  apply valuation_mod_six_of_unit_agreement 1
    (Ideal.span {a} * Ideal.span {b}) _ _ P (mul_ne_zero ha.1 hb.1) ha hb
    hg hodd isCoprime_one_left
  intro n _ hn
  exact rows_agree_of_mean_ne_zero a b ha hb hm n hn

theorem powerful_product_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) :
    CompletedGauss.PowerfulIdeal (Ideal.span {a} * Ideal.span {b}) := by
  have hs := (supported_mul_iff _ _).mpr ⟨ha, hb⟩
  refine ⟨hs.1, ?_⟩
  intro P hP
  obtain ⟨hmax, hg, hodd⟩ := supported_factors_good _ hs P hP
  let := hmax
  have he := valuation_profile_of_mean_ne_zero a b ha hb hm P hg hodd
  have hp := Multiset.count_pos.mpr hP
  rw [normalizedFactors_mul ha.1 hb.1, Multiset.count_add] at hp ⊢
  unfold valuation at he
  omega

theorem powerful_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O × Ideal O)) (Y : ℝ), 1 ≤ Y →
      (∀ p ∈ S, CompletedGauss.PowerfulIdeal (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hp⟩ := CompletedGauss.powerful_ideal_count (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro S Y hY hS
  let T := S.image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hT (I : Ideal O) (hI : I ∈ T) :
      CompletedGauss.PowerfulIdeal I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hS p hp
  have hcard : (S.card : ℝ) = ∑ I ∈ T,
      ((S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card : ℝ) := by
    calc
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ I ∈ T, ∑ _p ∈ S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp =>
          Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp) _).symm
      _ = _ := by simp
  rw [hcard]
  calc
    _ ≤ ∑ I ∈ T, D * Y ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) := by
          exact_mod_cast product_fiber_card S I (hT I hI).1.1
        _ ≤ D * (Ideal.absNorm I : ℝ) ^ (ε / 2) := hd I (hT I hI).1.1
        _ ≤ D * Y ^ (ε / 2) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT I hI).2 (by positivity)) hD.le
    _ = (T.card : ℝ) * (D * Y ^ (ε / 2)) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε / 2)) * (D * Y ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hp T Y hY hT) (by positivity)
    _ = (C * D) * (Y ^ (1 / 2 + ε / 2) * Y ^ (ε / 2)) := by ring
    _ = (C * D) * Y ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < Y)]
      congr 2
      ring

theorem pairFourier_zero_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    ‖pairFourier a b ha hb 0‖ ≤ (Ideal.absNorm (Ideal.span {a * b}) : ℝ) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a * b), ‖pairResidue a b ha hb x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a * b), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [pairResidue_mk, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans
        (idealRowHom_norm _ _)
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem scaled_zero_mean_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (K : ℝ) (hK : 0 ≤ K) :
    ‖((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) * pairFourier a b ha hb 0‖ ≤ K := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {a * b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
        (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    eisEmbedding_norm_sq_eq_absNorm_span, abs_of_nonneg (div_nonneg hK hn.le)]
  calc
    _ ≤ (K / (Ideal.absNorm (Ideal.span {a * b}) : ℝ)) *
        (Ideal.absNorm (Ideal.span {a * b}) : ℝ) :=
      mul_le_mul_of_nonneg_left (pairFourier_zero_norm_le a b ha hb) (div_nonneg hK hn.le)
    _ = K := div_mul_cancel₀ _ hn.ne'

theorem nonzero_mean_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (Y : ℝ), 1 ≤ Y →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      ((S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)).card : ℝ)
        ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := powerful_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb Y hY hinj hN
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  let f := fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})
  have hf : Set.InjOn f (T : Set (α × β)) := by
    intro p hp q hq he
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have ht : (T.image f).card = T.card := Finset.card_image_of_injOn hf
  have hbound := hc (T.image f) Y hY (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hp' := Finset.mem_filter.mp hp
    exact ⟨powerful_product_of_mean_ne_zero (a p.1) (b p.2) (ha p.1) (hb p.2) hp'.2,
      hN p hp'.1⟩)
  simpa only [ht] using hbound

theorem first_zero_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (d : α × β → ℂ)
      (Y K B : ℝ), 1 ≤ Y → 0 ≤ K → 0 ≤ B →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      (∀ p ∈ S, ‖d p‖ ≤ B) →
      ‖∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ ≤
        C * K * B * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := nonzero_mean_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb d Y K B hY hK hB hinj hN hd
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  have hsum : (∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)) =
      ∑ p ∈ T, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpt
    have hz : pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 = 0 := by
      simpa only [T, Finset.mem_filter, hp, true_and, not_not] using hpt
    rw [hz, mul_zero, mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ p ∈ T, ‖d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B * K := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hd p (Finset.mem_filter.mp hp).1)
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (norm_nonneg _) hB
    _ = (T.card : ℝ) * (B * K) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε)) * (B * K) :=
      mul_le_mul_of_nonneg_right (hc S a b ha hb Y hY hinj hN) (mul_nonneg hB hK)
    _ = C * K * B * Y ^ (1 / 2 + ε) := by ring

theorem productColumnCoefficient_sextic_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    (∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)) =
      ∑ K ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2),
        productColumnCoefficient S T β K * idealRowHom z K := by
  rw [← Finset.sum_product (f := fun p : Ideal O × Ideal O =>
    β p.1 p.2 * idealRowHom z (p.1 * p.2))]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p ∈ S ×ˢ T) => Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp)]
  apply Finset.sum_congr rfl
  intro K hK
  rw [productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem productColumnCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ),
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ 1) →
      ∀ (I : Ideal O) (X : ℝ), I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ X →
        ‖productColumnCoefficient S T β I‖ ≤ D * X ^ ε := by
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro S T β hβ I X hI hX
  exact (productColumnCoefficient_norm S T β hβ I hI).trans
    ((hd I hI).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le) hD.le))

def idealColumn (S : Finset (Ideal O)) (I : S) : O :=
  ConcretePrimeRowBridge.idealGenerator I.val

@[simp] theorem idealColumn_span (S : Finset (Ideal O)) (I : S) :
    Ideal.span {idealColumn S I} = I.val :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem idealColumn_supported (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {idealColumn S I}) := by
  rw [idealColumn_span]
  exact hS I.val I.property

def idealZeroEnergy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (K : ℝ) : ℂ :=
  ∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
    (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (idealColumn S I) (idealColumn S J)
        (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0)

theorem ideal_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
      (c : Ideal O → ℂ) (X K B : ℝ), 1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ S, ‖c I‖ ≤ B) →
      ‖idealZeroEnergy S hS c K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := first_zero_sum_bound (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S hS c X K B hX hK hB hN hd
  have hinj : Set.InjOn (fun p : S × S =>
      (Ideal.span {idealColumn S p.1}, Ideal.span {idealColumn S p.2}))
        (↑(Finset.univ : Finset (S × S)) : Set (S × S)) := by
    intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.fst he)
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.snd he)
  have hNpair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      (Ideal.absNorm (Ideal.span {idealColumn S p.1} * Ideal.span {idealColumn S p.2}) : ℝ) ≤ X ^ 2 := by
    rw [idealColumn_span, idealColumn_span, map_mul, Nat.cast_mul, pow_two]
    exact mul_le_mul (hN _ p.1.property) (hN _ p.2.property) (Nat.cast_nonneg _) (by linarith)
  have hdPair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      ‖c p.1.val * star (c p.2.val)‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hd _ p.1.property) (hd _ p.2.property) (norm_nonneg _) hB
  have hh := hc Finset.univ (idealColumn S) (idealColumn S)
    (idealColumn_supported S hS) (idealColumn_supported S hS)
    (fun p : S × S => c p.1.val * star (c p.2.val)) (X ^ 2) K (B ^ 2)
    (by nlinarith) hK (sq_nonneg _) hinj hNpair hdPair
  have hp : (X ^ 2) ^ (1 / 2 + ε / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]
    congr 1
    ring
  simpa only [idealZeroEnergy, Fintype.sum_prod_type, hp] using hh

theorem productColumnCoefficient_norm_le (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖productColumnCoefficient S T β I‖ ≤ B * (IdealMobiusDivisorSum.idealDivisors I).card := by
  unfold productColumnCoefficient
  calc
    _ ≤ ∑ p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), ‖β p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), B := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = B * ((S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast product_fiber_card (S ×ˢ T) I hI) hB

theorem productColumns_supported (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J) :
    ∀ I ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2), Supported I := by
  intro I hI
  obtain ⟨⟨J, K⟩, hp, rfl⟩ := Finset.mem_image.mp hI
  have hh := Finset.mem_product.mp hp
  exact (supported_mul_iff J K).mpr ⟨hS J hh.1, hT K hh.2⟩

def productZeroEnergy (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (K : ℝ) : ℂ :=
  idealZeroEnergy ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (productColumns_supported S T hS hT) (productColumnCoefficient S T β) K

theorem product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖productZeroEnergy S T hS hT β K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := ideal_zero_energy_bound (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 4) (by positivity)
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hs := productColumns_supported S T hS hT
  have hn (I : Ideal O) (hI : I ∈ P) : (Ideal.absNorm I : ℝ) ≤ X := by
    obtain ⟨⟨J, L⟩, hp, rfl⟩ := Finset.mem_image.mp hI
    have hh := Finset.mem_product.mp hp
    exact hN J hh.1 L hh.2
  have hb (I : Ideal O) (hI : I ∈ P) :
      ‖productColumnCoefficient S T β I‖ ≤ B * (D * X ^ (ε / 4)) := by
    apply (productColumnCoefficient_norm_le S T β B hB hβ I (hs I hI).1).trans
    apply mul_le_mul_of_nonneg_left _ hB
    exact (hd I (hs I hI).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hn I hI) (by positivity)) hD.le)
  have hh := hc P hs (productColumnCoefficient S T β) X K (B * (D * X ^ (ε / 4)))
    hX hK (by positivity) hn hb
  change ‖productZeroEnergy S T hS hT β K‖ ≤ _ at hh
  apply hh.trans_eq
  have hx0 : 0 < X := by linarith
  have hp : (X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    C * K * (B * (D * X ^ (ε / 4))) ^ 2 * X ^ (1 + ε / 2) =
        (C * D ^ 2) * K * B ^ 2 * ((X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2)) := by ring
    _ = _ := by rw [hp]

theorem normalized_product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) * productZeroEnergy S T hS hT β K‖ ≤
        C * K * B ^ 2 * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  have hx0 : 0 < X := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  calc
    _ ≤ X⁻¹ * (C * K * B ^ 2 * X ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left (hc S T hS hT β X K B hX hK hB hN hβ) (by positivity)
    _ = C * K * B ^ 2 * X ^ ε := by
      rw [Real.rpow_add hx0, Real.rpow_one]
      field_simp

theorem aggregated_rowPolynomial (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowPolynomial Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) z =
      ∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J) := by
  dsimp only
  rw [rowPolynomial]
  simp only [idealColumn_span]
  rw [Finset.sum_coe_sort ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (fun I : Ideal O => productColumnCoefficient S T β I * idealRowHom z I)]
  exact (productColumnCoefficient_sextic_row_sum S T β z).symm

theorem aggregated_rowEnergy (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowEnergy Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) W K =
      ∑' z : O, ((‖∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)‖ ^ 2 : ℝ) : ℂ) *
        W (‖eisEmbedding z‖ ^ 2 / K) := by
  simp only [CenteredMomentRowNorm.rowEnergy, aggregated_rowPolynomial]

theorem idealZeroEnergy_first_frequency (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ)
    (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
        (pairFourier (idealColumn S I) (idealColumn S J)
          (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0 *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (K * ‖eisEmbedding (0 : O)‖ ^ 2 /
              ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2)))) =
      idealZeroEnergy S hS c K * EisensteinSchwartzPoisson.paperRadialFourier W 0 := by
  simp [idealZeroEnergy, Finset.sum_mul, mul_assoc]

theorem normalized_product_zero_mode_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        (productZeroEnergy S T hS hT β K * EisensteinSchwartzPoisson.paperRadialFourier W 0)‖ ≤
        C * K * B ^ 2 * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := normalized_product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β W X K B hX hK hB hN hβ
  rw [← mul_assoc, norm_mul]
  calc
    _ ≤ (C * K * B ^ 2 * X ^ ε) * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ :=
      mul_le_mul_of_nonneg_right (hc S T hS hT β X K B hX hK hB hN hβ) (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.CenteredMomentZeroMode

end

end OAI
end OAIOriginalModule1691

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AddedZero
Source SHA256: cc30397fa25cffed29ea7d089d7bbfc16a58b925fd45a9f93d3fed9d780f2145
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1692





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle CenteredMomentExtraction
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

theorem pairFourier_one (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    pairFourier u 1 hu supported_one_element h =
      ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) h := by
  have hone (x : Residue (1 : O)) : supportedModulusCharacter 1 supported_one_element x = 1 := by
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [supportedModulusCharacter_mk]
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using (idealRowHom n).map_one
  have aux (v : O) (hd : u ∣ v) (hv : v ≠ 0) (he : v = u) :
      (∑' x : Residue v, supportedModulusCharacter u hu (frequencyReduction u v hd x) *
        CubicEisenstein.quotientTrace v hv (Ideal.Quotient.mk _ h * x)) =
      residueGauss u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
        (Ideal.Quotient.mk _ h) := by
    subst v
    apply tsum_congr
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [frequencyReduction_mk]
  rw [← residueGauss_supported_mk u hu h]
  simpa only [pairFourier, pairResidue, hone, star_one, mul_one] using
    aux (u * 1) (dvd_mul_right u 1)
      (mul_ne_zero (supported_element_ne_zero u hu) (supported_element_ne_zero 1 supported_one_element))
      (mul_one u)

theorem gaussRow_zero_sixthRemainder (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) : sixthRemainder (Ideal.span {u}) = 1 := by
  have hg : ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) 0 ≠ 0 := by
    intro hz
    apply hzero
    simp only [gaussRow, hz, zero_div]
  have hm : pairFourier u 1 hu supported_one_element 0 ≠ 0 := by
    rwa [pairFourier_one]
  apply sixthRemainder_eq_of_prime_profile one_ne_zero
  intro P hP
  by_cases hmem : P ∈ normalizedFactors (Ideal.span {u})
  · obtain ⟨hmax, hlam, hodd⟩ := supported_factors_good _ hu P hmem
    let := hmax
    have hv := valuation_profile_of_mean_ne_zero u 1 hu supported_one_element hm P hlam hodd
    simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, valuation,
      normalizedFactors_one, Multiset.count_zero, Nat.zero_mod] using hv
  · simp only [valuation, Multiset.count_eq_zero.mpr hmem, normalizedFactors_one,
      Multiset.count_zero, Nat.zero_mod]

theorem gaussRow_zero_ideal_sixth_power (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) :
    sixthQuotient (Ideal.span {u}) ^ 6 = Ideal.span {u} := by
  simpa only [gaussRow_zero_sixthRemainder u hu hzero, one_mul] using
    sixth_normal_form (Ideal.span {u}) hu.1

theorem gaussRow_norm_le (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    ‖gaussRow u hu h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  have hb := CenteredMomentTail.normalizedResidueGauss_norm_le u
    (supported_element_ne_zero u hu) (supportedModulusCharacter u hu) (Ideal.Quotient.mk _ h)
  simpa only [normalizedResidueGauss, residueGauss_supported_mk,
    gaussRow] using hb

theorem squarefree_divisor_sixth_of_gauss_zero (u : O)
    (hu : Supported (Ideal.span {u})) (hzero : gaussRow u hu 0 ≠ 0)
    (s : Ideal O) (hs : Squarefree s) (hd : s ∣ Ideal.span {u}) :
    s ^ 6 ∣ Ideal.span {u} := by
  have he := gaussRow_zero_ideal_sixth_power u hu hzero
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

def idealGaussRow (I : Ideal O) (hI : Supported I) (h : O) : ℂ :=
  gaussRow (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h

lemma idealGaussRow_norm_le (I : Ideal O) (hI : Supported I) (h : O) :
    ‖idealGaussRow I hI h‖ ≤ Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hb := gaussRow_norm_le (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

lemma idealGaussRow_zero_sixthRemainder (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) : sixthRemainder I = 1 := by
  have hb := gaussRow_zero_sixthRemainder (primaryGenerator I)
    ((supported_span_primaryGenerator_iff I).mpr hI) hz
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

def tupleProduct {r : ℕ} (v : Fin r → Ideal O) : Ideal O := ∏ i, v i

lemma tupleEntry_dvd {r : ℕ} (v : Fin r → Ideal O) (i : Fin r) : v i ∣ tupleProduct v :=
  Finset.dvd_prod_of_mem v (Finset.mem_univ i)

theorem tuple_product_fiber_card {r : ℕ} (S : Finset (Fin r → Ideal O))
    (I : Ideal O) (hI : I ≠ 0) :
    (S.filter (fun v => tupleProduct v = I)).card ≤ (idealDivisors I).card ^ r := by
  let T := S.filter (fun v => tupleProduct v = I)
  let f (v : T) : Fin r → idealDivisors I := fun i => ⟨v.val i, by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact tupleEntry_dvd v.val i⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, T] using
    Fintype.card_le_of_injective f hf

def idealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) : ℂ :=
  ∑ I : S, c I.val * idealGaussRow I.val (hS I.val I.property) 0

theorem idealAddedZero_norm_le (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖idealAddedZero S hS c‖ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) := by
  let F := S.filter (fun I => sixthRemainder I = 1)
  have hcount : (F.card : ℝ) ≤ 128 * Y ^ (1 / 6 : ℝ) := by
    simpa only [map_one, Nat.cast_one, div_one] using
      ideal_count_fixed_remainder F 1 one_ne_zero Y hY
        (fun I hI => (hS I (Finset.mem_filter.mp hI).1).1)
        (fun I hI => (Finset.mem_filter.mp hI).2)
        (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  have hb (I : S) : ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ ≤
      if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 := by
    by_cases hr : sixthRemainder I.val = 1
    · simp only [hr, ite_true, norm_mul]
      exact mul_le_mul (hc I.val I.property)
        ((idealGaussRow_norm_le _ _ _).trans (Real.sqrt_le_sqrt (hN I.val I.property)))
        (norm_nonneg _) hB
    · have hz : idealGaussRow I.val (hS I.val I.property) 0 = 0 := by
        by_contra hn
        exact hr (idealGaussRow_zero_sixthRemainder _ _ hn)
      simp only [hr, ite_false, hz, mul_zero, norm_zero, le_refl]
  calc
    ‖idealAddedZero S hS c‖ ≤ ∑ I : S,
        ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ := norm_sum_le _ _
    _ ≤ ∑ I : S, if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 :=
      Finset.sum_le_sum (fun I _ => hb I)
    _ = (F.card : ℝ) * (B * Real.sqrt Y) := by
      rw [Finset.sum_coe_sort S (fun I => if sixthRemainder I = 1 then B * Real.sqrt Y else 0)]
      rw [← Finset.sum_filter]
      simp only [F, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hB (Real.sqrt_nonneg _))

def normalizedIdealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (T : ℝ) : ℂ := (Real.sqrt T : ℂ)⁻¹ * idealAddedZero S hS c

theorem idealAddedZero_energy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y T : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖normalizedIdealAddedZero S hS c T‖ ^ 2 ≤ 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
  have hb := idealAddedZero_norm_le S hS c B Y hB hY hc hN
  have hp : (Y ^ (1 / 6 : ℝ)) ^ 2 * Y = Y ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY]
    norm_num only [Nat.cast_ofNat]
    conv_lhs => rhs; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add' hY (by norm_num : (1 / 3 : ℝ) + 1 ≠ 0)]
    norm_num
  have hs := sq_le_sq₀ (norm_nonneg (idealAddedZero S hS c)) (by positivity : 0 ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y))
  have hb2 := hs.mpr hb
  have hn : ‖normalizedIdealAddedZero S hS c T‖ ^ 2 = T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 := by
    simp only [normalizedIdealAddedZero, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T), mul_pow, inv_pow,
      Real.sq_sqrt hT.le]
  rw [hn]
  calc
    T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 ≤ T⁻¹ * ((128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y)) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hT.le)
    _ = 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hY]
      rw [← hp]
      ring

def tupleCoefficient {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v

def tupleColumns {r : ℕ} (S : Finset (Fin r → Ideal O)) : Finset (Ideal O) :=
  S.image tupleProduct

lemma tupleColumns_supported {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) :
    ∀ I ∈ tupleColumns S, Supported I := by
  intro I hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
  exact hS v hv

theorem tupleCoefficient_norm_le {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ v ∈ S, ‖β v‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖tupleCoefficient S β I‖ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
  calc
    ‖tupleCoefficient S β I‖ ≤ ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v ∈ S.filter (fun v => tupleProduct v = I), B :=
      Finset.sum_le_sum (fun v hv => hβ v (Finset.mem_filter.mp hv).1)
    _ = B * ((S.filter (fun v => tupleProduct v = I)).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast tuple_product_fiber_card S I hI

theorem tuple_added_zero_energy (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Fin r → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin r → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let δ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hr')
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨16384 * (D ^ r) ^ 2, by positivity, ?_⟩
  intro S hS β B Y T hB hY hT hβ hN
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hδr : δ * (r : ℝ) = ε / 2 := by dsimp [δ]; field_simp
  have hc (I : Ideal O) (hI : I ∈ tupleColumns S) :
      ‖tupleCoefficient S β I‖ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    have hI0 := (hS v hv).1
    have hn0 : (0 : ℝ) ≤ Ideal.absNorm (tupleProduct v) := Nat.cast_nonneg _
    calc
      ‖tupleCoefficient S β (tupleProduct v)‖ ≤
          B * ((idealDivisors (tupleProduct v)).card : ℝ) ^ r :=
        tupleCoefficient_norm_le S β B hB hβ _ hI0
      _ ≤ B * (D * (Ideal.absNorm (tupleProduct v) : ℝ) ^ δ) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hI0) _) hB
      _ = B * (D ^ r * (Ideal.absNorm (tupleProduct v) : ℝ) ^ (ε / 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hn0, hδr]
      _ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
        gcongr
        exact hN v hv
  have hn (I : Ideal O) (hI : I ∈ tupleColumns S) : (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    exact hN v hv
  have he := idealAddedZero_energy (tupleColumns S) (tupleColumns_supported S hS)
    (tupleCoefficient S β) (B * (D ^ r * Y ^ (ε / 2))) Y T (by positivity) hY0.le hT hc hn
  have hy : (Y ^ (ε / 2)) ^ 2 * Y ^ (4 / 3 : ℝ) = Y ^ (4 / 3 + ε : ℝ) := by
    rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 16384 * (B * (D ^ r * Y ^ (ε / 2))) ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := he
    _ = (16384 * (D ^ r) ^ 2) * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
      rw [← hy]
      ring

def originalCoefficient (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Fin (N + 2) → Ideal O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

lemma idealRectangle_norm_le (W₁ W₂ : ℝ → ℂ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) :
    ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖ ≤ 2 * B₁ * B₂ := by
  have hprod (x y : ℝ) : ‖W₁ x * W₂ y‖ ≤ B₁ * B₂ := by
    rw [norm_mul]
    exact mul_le_mul (hW₁ x) (hW₂ y) (norm_nonneg _) hB₁
  unfold idealRectangle
  exact (norm_sub_le _ _).trans ((add_le_add
    (hprod ((Ideal.absNorm I : ℝ) / X₁) ((Ideal.absNorm J : ℝ) / X₂))
    (hprod ((Ideal.absNorm I : ℝ) / Y₁) ((Ideal.absNorm J : ℝ) / Y₂))).trans_eq (by ring))

theorem originalCoefficient_norm_le (N : ℕ) (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ)
    (hBslot : ∀ j, 0 ≤ Bslot j) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Fin (N + 2) → Ideal O) (hv : tupleProduct v ≠ 0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  have hslots : ‖∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)‖ ≤ ∏ j, Bslot j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hWslot j _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hweight := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  have hrect := idealRectangle_norm_le W₁ W₂ B₁ B₂ hB₁ hB₂ hW₁ hW₂ X₁ X₂ Y₁ Y₂
    (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩)
  by_cases hs : s ∣ tupleProduct v
  · simp only [originalCoefficient, hs, ite_true, mul_one, norm_mul]
    have hsw := mul_le_mul hslots hweight (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
    simp only [mul_one] at hsw
    exact mul_le_mul hsw hrect (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
  · simp only [originalCoefficient, hs, ite_false, mul_zero, norm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)

lemma originalCoefficient_eq_zero_of_not_dvd (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Fin (N + 2) → Ideal O) (hs : ¬s ∣ tupleProduct v) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalCoefficient, hs, ite_false, mul_zero]

theorem original_added_zero_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O), c ≠ 0 →
      ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
      (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ),
      (∀ j, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j I, ‖ν j I‖ ≤ 1) → (∀ j x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Fin (N + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v)) (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
        (tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ b₁ b₂ s)) T‖ ^ 2 ≤
        C * ((∏ j, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := tuple_added_zero_energy (N + 2) (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  apply he S hS _ _ Y T (mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)) hY hT _ hN
  intro v hv
  exact originalCoefficient_norm_le N c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s
    Bslot B₁ B₂ hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ v (hS v hv).1

theorem idealAddedZero_eq_gaussPolynomial (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) :
    idealAddedZero S hS c =
      gaussPolynomial (Finset.univ : Finset S)
        (fun I => primaryGenerator I.val)
        (fun I => (supported_span_primaryGenerator_iff I.val).mpr (hS I.val I.property))
        (fun I => c I.val) 0 := rfl

lemma idealGaussRow_zero_divisor_sixth (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) (s : Ideal O) (hs : Squarefree s) (hd : s ∣ I) :
    s ^ 6 ∣ I := by
  have hrem := idealGaussRow_zero_sixthRemainder I hI hz
  have he : sixthQuotient I ^ 6 = I := by
    simpa only [hrem, one_mul] using sixth_normal_form I hI.1
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

theorem idealAddedZero_nonzero_mask_norm (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Y : ℝ)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y)
    (hz : idealAddedZero S hS c ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  obtain ⟨I, _, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hg : idealGaussRow I.val (hS I.val I.property) 0 ≠ 0 := by
    intro he
    exact hI (by rw [he, mul_zero])
  have hd : s ∣ I.val := by
    by_contra hn
    exact hI (by rw [hmask I.val I.property hn, zero_mul])
  have hpow := idealGaussRow_zero_divisor_sixth I.val (hS I.val I.property) hg s hs hd
  have hn := (norm_le_of_dvd (hS I.val I.property).1 hpow).trans (hN I.val I.property)
  simpa only [map_pow, Nat.cast_pow] using hn

theorem original_tupleCoefficient_mask (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (S : Finset (Fin (N + 2) → Ideal O)) (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ b₁ b₂ s) I = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply originalCoefficient_eq_zero_of_not_dvd
  rwa [(Finset.mem_filter.mp hv).2]

theorem added_zero_exponent (a s θ : ℝ) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6) :
    a / 3 + 4 * θ / 3 ≤ a - s + 2 * θ := by linarith

theorem added_zero_scale_identity (Z a θ : ℝ) (hZ : 0 < Z) :
    (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) = Z ^ (a / 3 + 4 * θ / 3) := by
  rw [← Real.rpow_neg hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]
  congr 1
  ring

theorem idealAddedZero_source_energy (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (B Z a s θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 ≤ Z) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s + 2 * θ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := idealAddedZero_energy S hS c B (Z ^ (a + θ)) (Z ^ a)
    hB (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hc hN
  calc
    _ ≤ 16384 * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) := he
    _ = 16384 * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3) := by
      rw [mul_assoc, added_zero_scale_identity Z a θ hZ0]
    _ ≤ 16384 * B ^ 2 * Z ^ (a - s + 2 * θ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (added_zero_exponent a s θ ha hs))
        (by positivity)

theorem idealAddedZero_nonzero_mask_dyad (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Z a s₀ θ : ℝ) (hZ : 1 < Z)
    (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ))
    (hz : idealAddedZero S hS c ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ
  obtain ⟨I, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hY : 1 ≤ Z ^ (a + θ) :=
    (norm_one_le (hS I.val I.property).1).trans (hN I.val I.property)
  have ha : 0 ≤ a + θ := (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hY)
  have hm := idealAddedZero_nonzero_mask_norm S hS c s hs hmask (Z ^ (a + θ)) hN hz
  have hp : Z ^ (s₀ * (6 : ℕ)) ≤ Z ^ (a + θ) := by
    rw [Real.rpow_mul_natCast hZ0.le]
    exact (pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hNs 6).trans hm
  have hsp := (Real.rpow_le_rpow_left_iff hZ).mp hp
  constructor <;> norm_num at hsp ⊢ <;> linarith

theorem idealAddedZero_source_energy_of_mask (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (B Z a s₀ θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s₀ + 2 * θ) := by
  by_cases hz : idealAddedZero S hS c = 0
  · simp only [normalizedIdealAddedZero, hz, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨ha, hss⟩ := idealAddedZero_nonzero_mask_dyad S hS c s hs hmask Z a s₀ θ hZ hNs hN hz
    exact idealAddedZero_source_energy S hS c B Z a s₀ θ hB hZ.le ha hss hc hN

theorem actual_tuple_gauss_eq_columns {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) (β : (Fin r → Ideal O) → ℂ) :
    gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 =
    idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) := by
  let g (I : Ideal O) : ℂ := if hI : Supported I then idealGaussRow I hI 0 else 0
  have hl : gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 = ∑ v ∈ S, β v * g (tupleProduct v) := by
    rw [← Finset.sum_coe_sort S (fun v => β v * g (tupleProduct v))]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [g, dite_eq_left (hS v.val v.property), idealGaussRow]
  have hr : idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I * g I := by
    rw [← Finset.sum_coe_sort (tupleColumns S) (fun I => tupleCoefficient S β I * g I)]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [g, dite_eq_left (tupleColumns_supported S hS I.val I.property)]
  rw [hl, hr]
  symm
  simp only [tupleCoefficient, Finset.sum_mul]
  calc
    (∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g I) =
        ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ v ∈ S, β v * g (tupleProduct v) :=
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩) _

end SevenEighths.CenteredMomentAddedZero

end

end OAI
end OAIOriginalModule1692

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform
Source SHA256: c0ac095d1be1c3456f4adfee35b5daba5d5ac60ed3a3b68552941470ae5fb62b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1693


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

theorem uniform_tuple_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N →
      ∀ (S : Finset (Fin (n + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin (n + 2) → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  let D (n : ℕ) := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose
  have hD (n : ℕ) : 0 < D n := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.1
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let C := 1 + (Finset.range (N + 1)).sup' hne D
  have hzero : D 0 ≤ (Finset.range (N + 1)).sup' hne D :=
    Finset.le_sup' D (by simp : 0 ∈ Finset.range (N + 1))
  refine ⟨C, by dsimp [C]; linarith [hD 0], ?_⟩
  intro n hn S hS β B Y T hB hY hT hβ hN
  have hDn : D n ≤ C := by
    have h := Finset.le_sup' D (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp only [C]
    linarith
  have he := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.2
    S hS β B Y T hB hY hT hβ hN
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hT.le)
  exact mul_le_mul_of_nonneg_right hDn (sq_nonneg _)

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

lemma reindex_supported {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) :
    ∀ w ∈ S.image (tupleEquiv e), Supported (tupleProduct w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  rw [tupleProduct_reindex]
  exact hS v hv

def finiteGaussZero {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) : ℂ :=
  gaussPolynomial (Finset.univ : Finset S)
    (fun v => primaryGenerator (finiteTupleProduct v.val))
    (fun v => (supported_span_primaryGenerator_iff (finiteTupleProduct v.val)).mpr (hS v.val v.property))
    (fun v => β v.val) 0

theorem finiteGaussZero_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) :
    finiteGaussZero S hS β =
      idealAddedZero (tupleColumns (S.image (tupleEquiv e)))
        (tupleColumns_supported _ (reindex_supported e S hS))
        (tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w))) := by
  rw [← actual_tuple_gauss_eq_columns (S.image (tupleEquiv e)) (reindex_supported e S hS)
    (fun w => β ((tupleEquiv e).symm w))]
  unfold finiteGaussZero gaussPolynomial
  apply Finset.sum_bij (fun v _ => (⟨tupleEquiv e v.val,
    Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩ : S.image (tupleEquiv e)))
  · intros; exact Finset.mem_univ _
  · intro v hv w hw he
    apply Subtype.ext
    exact (tupleEquiv e).injective (congrArg Subtype.val he)
  · intro w hw
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp w.property
    exact ⟨⟨v, hv⟩, Finset.mem_univ _, Subtype.ext he⟩
  · intro v hv
    simp only [Equiv.symm_apply_apply, tupleProduct_reindex]

theorem uniform_finite_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (B Y T : ℝ), 0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_tuple_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β B Y T hB hY hT hβ hN
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β]
  apply he (Fintype.card ι) hn _ (reindex_supported e S hS) _ B Y T hB hY hT
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [Equiv.symm_apply_apply] using hβ v hv
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [tupleProduct_reindex] using hN v hv

theorem originalFiniteCoefficient_norm_le {ι : Type*} [Fintype ι]
    (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : ι → ℝ) (B₁ B₂ : ℝ) (hBslot : ∀ j, 0 ≤ Bslot j)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Tuple ι) (hv : finiteTupleProduct v ≠ 0) :
    ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  let e := Fintype.equivFin ι
  rw [← originalCoefficient_reindex e]
  have he := originalCoefficient_norm_le (Fintype.card ι) c hc χ R t
    (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j => Bslot (e.symm j)) B₁ B₂
    (fun j => hBslot _) hB₁ hB₂ (fun j I => hν _ I) (fun j x => hWslot _ x) hW₁ hW₂
    (tupleEquiv e v) (by rwa [tupleProduct_reindex])
  simpa only [e.symm.prod_comp Bslot] using he

theorem original_subset_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ _ Y T
    (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hY hT _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

theorem empty_finiteTupleProduct {α : Type*} (v : Tuple (∅ : Finset α)) :
    finiteTupleProduct v = v (Sum.inr 0) * v (Sum.inr 1) := by
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  have he : (∏ j : (∅ : Finset α), v (Sum.inl j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim (Finset.notMem_empty j.val j.property)
  rw [he, one_mul]

lemma reindexCoefficient_mask {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (s : Ideal O)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hwS, hwI⟩ := Finset.mem_filter.mp hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
  simp only [Equiv.symm_apply_apply]
  apply hmask v hv
  rwa [← tupleProduct_reindex e v, hwI]

lemma reindexColumns_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (Y : ℝ)
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) :
    ∀ I ∈ tupleColumns (S.image (tupleEquiv e)), (Ideal.absNorm I : ℝ) ≤ Y := by
  intro I hI
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  simpa only [tupleProduct_reindex] using hN v hv

theorem finiteGaussZero_nonzero_mask_norm {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Y : ℝ) (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y)
    (hz : finiteGaussZero S hS β ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_norm _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Y (reindexColumns_norm e S Y hN) hz

theorem finiteGaussZero_nonzero_mask_dyad {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Z a s₀ θ : ℝ) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ))
    (hz : finiteGaussZero S hS β ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_dyad _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Z a s₀ θ hZ hNs
    (reindexColumns_norm e S (Z ^ (a + θ)) hN) hz

lemma originalFiniteCoefficient_mask {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Tuple ι) (hs : ¬s ∣ finiteTupleProduct v) :
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalFiniteCoefficient, hs, ite_false, mul_zero]

theorem uniform_finite_source_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (s : Ideal O), Squarefree s →
      (∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0) →
      ∀ (B Z a s₀ θ : ℝ), 0 ≤ B → 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β s hs hmask B Z a s₀ θ hB hZ hNs hβ hN
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  by_cases hz : finiteGaussZero S hS β = 0
  · rw [hz, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (Real.rpow_nonneg hZ0.le _)
  · obtain ⟨ha, hss⟩ := finiteGaussZero_nonzero_mask_dyad S hS β s hs hmask Z a s₀ θ hZ hNs hN hz
    have hY : 1 ≤ Z ^ (a + θ) := Real.one_le_rpow hZ.le (by linarith)
    have hb := he hn S hS β B (Z ^ (a + θ)) (Z ^ a) hB hY
      (Real.rpow_pos_of_pos hZ0 _) hβ hN
    have hp : (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) =
        Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by
      rw [← Real.rpow_neg hZ0.le, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
      congr 1
      ring
    calc
      _ ≤ C * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) := hb
      _ = C * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by rw [mul_assoc, hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by linarith [added_zero_exponent a s₀ θ ha hss]))
        (mul_nonneg hC.le (sq_nonneg _))

theorem original_subset_source_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_source_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s hs Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Z a s₀ θ hZ hNs hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ s hs
    (fun v _ => originalFiniteCoefficient_mask c χ R t
      (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
      W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v)
    _ Z a s₀ θ (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hZ hNs _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
end OAIOriginalModule1693

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RadicalFamily
Source SHA256: c7c29c3a59abf088b6209a73a4a046b0304c484634a4a973b9769e3ddfc0112e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1694



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstFamily CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem elementCoeff_power_pos (χ : Character) (e : ℕ) (he : 0<e) (n : O) :
    elementCoeff (χ.power e) n=(elementCoeff χ n)^e := by
  by_cases hn : IsUnit (Ideal.Quotient.mk χ.modulus n)
  · exact elementCoeff_power_of_unit χ e n hn
  · have hz : elementCoeff χ n=0 := MulChar.map_nonunit _ hn
    have hp : elementCoeff (χ.power e) n=0 := MulChar.map_nonunit _ hn
    rw [hp,hz,zero_pow (Nat.ne_zero_of_lt he)]

theorem exists_product_presentation {ι : Type*} (S : Finset ι) (base : Character)
    (χ : ι→Character) (e : ι→ℕ) (he : ∀i∈S,0<e i)
    (M : Ideal O) (hb : M≤base.modulus) (hχ : ∀i∈S,M≤(χ i).modulus) :
    ∃τ : Character,M≤τ.modulus ∧ ∀n:O,
      elementCoeff τ n=elementCoeff base n*∏i∈S,(elementCoeff (χ i) n)^(e i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨base,hb,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨τ,hτ,ht⟩ := ih (fun i hi=>he i (Finset.mem_insert_of_mem hi))
      (fun i hi=>hχ i (Finset.mem_insert_of_mem hi))
    refine ⟨τ.product ((χ a).power (e a)),le_inf hτ (hχ a (Finset.mem_insert_self _ _)),?_⟩
    intro n
    rw [elementCoeff_product,elementCoeff_power_pos _ _ (he a (Finset.mem_insert_self _ _)),
      ht,Finset.prod_insert ha]
    ring

theorem single_row_on_base (η : Character) (m p n : O)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (hn : rowTwist (elementHom η) m 1 1 n≠0) :
    rowTwist (elementHom (η.power 0)) m 1 p n=idealRowHom p (Ideal.span {n}) := by
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  have hη : elementCoeff η n≠0 := left_ne_zero_of_mul hn
  have hunit := MulChar.apply_ne_zero_iff.mp hη
  have hp : elementCoeff (η.power 0) n=1 := by
    rw [elementCoeff_power_of_unit η 0 n hunit,pow_zero]
  have hm : IsCoprime m n := by
    by_contra h
    apply hn
    rw [rowTwist_extract_sixth_mask _ m 1 1 n hs]
    simp [coprimalityMask,h]
  rw [rowTwist_extract_sixth_mask _ m 1 p n hs]
  change elementCoeff (η.power 0) n*coprimalityMask m n*idealRowHom (1^4*p) _=_
  rw [hp,one_pow,one_mul]
  simp [coprimalityMask,hm]

theorem row_product_formula {ι : Type*} (S : Finset ι)
    (η : Character) (m : O) (p : ι→O) (e : ι→ℕ)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m) (n : O) :
    rowTwist (elementHom η) m 1 1 n*
      (∏i∈S,(rowTwist (elementHom (η.power 0)) m 1 (p i) n)^(e i))=
      rowTwist (elementHom η) m 1 (∏i∈S,(p i)^(e i)) n := by
  conv_rhs => rw [rowTwist_row_factor]
  by_cases hn : rowTwist (elementHom η) m 1 1 n=0
  · rw [hn,zero_mul,zero_mul]
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  congr 1
  simp_rw [single_row_on_base η m _ n hmLam hm2 hn]
  induction S using Finset.induction_on with
  | empty => simpa using (idealRowHom_one_supported (Ideal.span {n}) hs).symm
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,idealRowHom_argument_mul,
      idealRowHom_argument_pow _ _ _ hs,ih]

theorem exists_radical_row_presentation {ι : Type*} [Fintype ι]
    (η : Character) (m : O) (hm : m≠0) (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (e : ι→ℕ) (he : ∀i,0<e i) :
    ∃τ : Character,
      η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤τ.modulus ∧
      τ.modulus.absNorm≤η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (∏i,(p i)^(e i)) n := by
  obtain ⟨base,hbase,hbasec⟩ := exists_supported_row_presentation η m 1 hm
    CenteredMomentAddedZero.supported_one_element hmLam hm2
  choose χ hχ hc using fun i=>exists_supported_row_presentation (η.power 0) m (p i) hm
    (hp i) hmLam hm2
  let B := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}
  let M := B*∏i,Ideal.span {p i}
  have hb : M≤base.modulus := by
    rw [hbase,Ideal.span_singleton_one,←Ideal.one_eq_top,mul_one]
    exact Ideal.mul_le_left
  have hch (i : ι) : M≤(χ i).modulus := by
    rw [hχ i]
    change B*(∏j,Ideal.span {p j})≤B*Ideal.span {p i}
    apply Ideal.dvd_iff_le.mp
    exact mul_dvd_mul_left B (Finset.dvd_prod_of_mem (fun j=>Ideal.span {p j}) (Finset.mem_univ i))
  obtain ⟨τ,hM,ht⟩ := exists_product_presentation Finset.univ base χ e (fun i _=>he i) M hb
    (fun i _=>hch i)
  have hMn : M≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>(hp i).1))
  refine ⟨τ,hM,?_,?_⟩
  · have hd : τ.modulus∣M := Ideal.dvd_iff_le.mpr hM
    have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hMn))
      (map_dvd Ideal.absNorm hd)
    simpa only [M,B,map_mul,map_prod] using hn
  · intro n
    rw [ht,hbasec]
    simp_rw [hc]
    exact row_product_formula Finset.univ η m p e hmLam hm2 n

end SevenEighths.CenteredMomentRadicalFamily

end

end OAI
end OAIOriginalModule1694

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceMass
Source SHA256: 0c2fe23aa378e45b59354e53ee11fe41da47d4d70a92e79d04567a68d8826ee9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1695



namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

def idealBall (H : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).toFinset.filter
    (fun I => I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H)

@[simp] theorem mem_idealBall (H : ℝ) (I : Ideal O) :
    I ∈ idealBall H ↔ I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,h⟩
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).mem_toFinset.mpr
    exact_mod_cast h.2.trans (Nat.le_ceil H)

lemma idealBall_card (H : ℝ) (hH : 0 ≤ H) :
    ((idealBall H).card : ℝ) ≤ 128*H := by
  by_cases hs : (idealBall H).Nonempty
  · obtain ⟨I,hI⟩ := hs
    have hI := (mem_idealBall H I).mp hI
    have hn : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    exact DescentFiberCost.finite_ideal_count_real _ H (hn.trans hI.2)
      (fun J hJ => ((mem_idealBall H J).mp hJ).1)
      (fun J hJ => ((mem_idealBall H J).mp hJ).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

def tupleBox {r : ℕ} (H : Fin r → ℝ) : Finset (Fin r → Ideal O) :=
  Fintype.piFinset (fun i => idealBall (H i))

@[simp] lemma mem_tupleBox {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O) :
    v ∈ tupleBox H ↔ ∀ i, v i ≠ 0 ∧ (Ideal.absNorm (v i):ℝ) ≤ H i := by
  simp [tupleBox]

lemma tupleBox_card {r : ℕ} (H : Fin r → ℝ) (hH : ∀ i, 0 ≤ H i) :
    ((tupleBox H).card:ℝ) ≤ 128^r * ∏ i, H i := by
  simp only [tupleBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    (∏ i, ((idealBall (H i)).card:ℝ)) ≤ ∏ i, 128*H i :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => idealBall_card _ (hH i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def profileProduct {r : ℕ} (W : Fin r → ℝ → ℂ) (q : Fin r → ℝ)
    (v : Fin r → Ideal O) : ℂ := ∏ i, W i ((Ideal.absNorm (v i):ℝ)/q i)

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0<q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma profileProduct_norm_le {r : ℕ} (W : Fin r → ℝ → ℂ) (q B : Fin r → ℝ)
    (hW : ∀ i x, ‖W i x‖ ≤ B i) (v : Fin r → Ideal O) :
    ‖profileProduct W q v‖ ≤ ∏ i, B i := by
  rw [profileProduct,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hW i _)

theorem profileProduct_mass {r : ℕ} (W : Fin r → ℝ → ℂ) (b q B : Fin r → ℝ)
    (hb : ∀ i, 0≤b i) (hq : ∀ i, 0<q i) (hB : ∀ i, 0≤B i)
    (hzero : ∀ i, W i 0=0) (hs : ∀ i x, W i x ≠ 0 → x≤b i)
    (hW : ∀ i x, ‖W i x‖≤B i) (S : Finset (Fin r → Ideal O)) :
    (∑ v ∈ S, ‖profileProduct W q v‖) ≤
      (∏ i, B i) * (128^r * ∏ i, b i*q i) := by
  let F := S.filter (fun v => profileProduct W q v ≠ 0)
  have hsum : (∑ v ∈ S, ‖profileProduct W q v‖) = ∑ v ∈ F, ‖profileProduct W q v‖ := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    exact norm_ne_zero_iff.mp hv
  have hsub : F ⊆ tupleBox (fun i => b i*q i) := by
    intro v hv
    exact profileProduct_mem_box W b q hq hzero hs v (Finset.mem_filter.mp hv).2
  have hcard : (F.card:ℝ) ≤ 128^r * ∏ i, b i*q i :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (tupleBox_card _ (fun i => mul_nonneg (hb i) (hq i).le))
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ F, ∏ i, B i := Finset.sum_le_sum (fun v _ => profileProduct_norm_le W q B hW v)
    _ = (F.card:ℝ)*(∏ i, B i) := by simp
    _ ≤ (128^r * ∏ i, b i*q i)*(∏ i, B i) :=
      mul_le_mul_of_nonneg_right hcard (Finset.prod_nonneg (fun i _ => hB i))
    _ = _ := by ring

def sourceProfiles {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) :
    Fin (N+2) → ℝ → ℂ := Fin.append Wslot ![W₁,W₂]

def sourceScales {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    Fin (N+2) → ℝ :=
  Fin.append P ![X₁/(Ideal.absNorm B₁:ℝ),X₂/(Ideal.absNorm B₂:ℝ)]

def sourceBounds {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) : Fin (N+2) → ℝ :=
  Fin.append b ![b₁,b₂]

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceBounds_nonneg {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) :
    ∀ i, 0≤sourceBounds b b₁ b₂ i := by
  simp only [Fin.forall_fin_add,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hb,hb₁,hb₂⟩

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0<sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

def sourcePool {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : Finset (Fin (N+2) → Ideal O) :=
  ((tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i)) ∪
    tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P Y₁ Y₂ B₁ B₂ i)).filter
      (fun v => ∀ j,ν j (v (j.castAdd 2)) ≠ 0)

lemma sourcePool_slot {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (j : Fin N) :
    ν j (v (j.castAdd 2)) ≠ 0 := (Finset.mem_filter.mp hv).2 j

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

def sourceRadius {N : ℕ} (b P : Fin N → ℝ) (b₁ b₂ T : ℝ) (B₁ B₂ : Ideal O) : ℝ :=
  (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_profile_norm_le (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : tupleProduct v≠0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
  have hn : ‖∏ j,ν j (v (j.castAdd 2))‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hν j _)
  have hw := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  rw [originalCoefficient_factor,norm_mul,norm_mul,norm_mul]
  have hm : ‖(if s∣tupleProduct v then 1 else 0 : ℂ)‖≤1 := by split_ifs <;> norm_num
  have hnw : ‖∏ j,ν j (v (j.castAdd 2))‖*‖idealWeight c χ R t (tupleProduct v)‖≤1 := by
    simpa only [one_mul] using mul_le_mul hn hw (norm_nonneg _) zero_le_one
  calc
    _ ≤ (1*‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v-
        profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnw (norm_nonneg _)) hm (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simpa only [one_mul,mul_one] using norm_sub_le
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v)
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v)

def sourceMassConstant {N : ℕ} (b D : Fin N → ℝ) (b₁ b₂ D₁ D₂ : ℝ) : ℝ :=
  2*128^(N+2)*(∏ j,D j)*D₁*D₂*(∏ j,b j)*b₁*b₂

theorem originalCoefficient_mass (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P b D : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j, 0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (hW : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤sourceBounds D D₁ D₂ i)
    (S : Finset (Fin (N+2) → Ideal O)) :
    (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
      sourceMassConstant b D b₁ b₂ D₁ D₂ *
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  have hpoint (v : Fin (N+2) → Ideal O) :
      ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
    by_cases hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=0
    · rw [hv,norm_zero]; positivity
    · have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
      exact originalCoefficient_profile_norm_le N c hc χ R t ν hν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s v (sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm)
  have hx := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P X₁ X₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  have hy := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P Y₁ Y₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  rw [source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX,sourceBounds_product] at hx
  rw [source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY,sourceBounds_product] at hy
  calc
    _ ≤ ∑ v ∈ S, (‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact (add_le_add hx hy).trans_eq (by unfold sourceRadius sourceMassConstant; ring)

theorem sourcePool_original_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    ∀ j, v (j.castAdd 2)∈pool j := by
  intro j
  by_contra h
  exact sourcePool_slot _ _ _ _ _ _ _ _ _ _ _ v hv j (hpool j _ h)

theorem tuple_weighted_regroup {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (F : Ideal O → ℂ) :
    (∑ v ∈ S, β v*F (tupleProduct v)) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I*F I := by
  symm
  simp only [tupleCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), β v*F (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem tupleCoefficient_mass {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) :
    (∑ I ∈ tupleColumns S, ‖tupleCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma tupleCoefficient_eq_zero_outside {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) (hI : I∉tupleColumns S) :
    tupleCoefficient S β I=0 := by
  apply Finset.sum_eq_zero
  intro v hv
  exact False.elim (hI (Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩))

theorem source_column_support {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (β : (Fin (N+2) → Ideal O) → ℂ) (I : Ideal O)
    (hI : tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) β I ≠ 0) :
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm : I∈tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) := by
    by_contra h; exact hI (tupleCoefficient_eq_zero_outside _ _ _ h)
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hv,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hv⟩

theorem original_source_eq_columns (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (F : Ideal O → ℂ) :
    (∑' v : Fin (N+2) → Ideal O,
      originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v * F (tupleProduct v)) =
    ∑ I ∈ tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂),
      tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I * F I := by
  rw [← tuple_weighted_regroup]
  apply tsum_eq_sum
  intro v hv
  have hz : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v = 0 := by
    by_contra hn
    exact hv (originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hn)
  rw [hz,zero_mul]

lemma smooth_annular_bound (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ D : ℝ, 0≤D ∧ (∀ x, ‖W x‖≤D) ∧ W 0=0 ∧ (∀ x, W x≠0 → x≤b) := by
  let D := SchwartzMap.seminorm ℝ 0 0 (CenteredMomentLattice.normPowerProfile W a b ha hs hW 0)
  refine ⟨D,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    rw [← CenteredMomentTwist.normPowerProfile_norm W a b ha hs hW 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  · by_contra hz
    have h := (hs hz).1
    linarith
  · intro x hx
    exact (hs hx).2

theorem smooth_source_mass_uniform (N : ℕ)
    (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (hb : ∀ j, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : Fin N → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Fin (N+2) → Ideal O),
      (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ∧
      (∑ I ∈ tupleColumns S, ‖tupleCoefficient S
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  choose D hD hDbound hDzero hDsupport using
    fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDbound₁,hzero₁,hsupport₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDbound₂,hzero₂,hsupport₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  have hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDzero (And.intro hzero₁ hzero₂)
  have hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDsupport (And.intro hsupport₁ hsupport₂)
  have hbound : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤sourceBounds D D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDbound (And.intro hDbound₁ hDbound₂)
  let C₀ := sourceMassConstant b D b₁ b₂ D₁ D₂
  have hprodD : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏ j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤C₀ := by
    dsimp only [C₀,sourceMassConstant]
    positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := originalCoefficient_mass N c hc χ R t ν hν Wslot P b D W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s hb hb₁ hb₂ hD hD₁ hD₂
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound S
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by positivity
  have hbigger : C₀*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ≤
      (1+C₀)*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (by linarith : C₀≤1+C₀) hraw
  have hmass := hm.trans hbigger
  exact ⟨hmass,(tupleCoefficient_mass S _).trans hmass⟩

theorem originalCoefficient_original_masks (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (tupleProduct v) R ∧ s∣tupleProduct v ∧ ∀ j, ν j (v (j.castAdd 2))≠0 := by
  refine ⟨?_,?_,?_⟩
  · by_contra h
    apply hv
    simp only [originalCoefficient,idealWeight,h,ite_false,zero_mul,mul_zero]
  · by_contra h
    apply hv
    simp only [originalCoefficient,h,ite_false,mul_zero]
  · rw [originalCoefficient_factor] at hv
    have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

theorem sourceProfiles_annular_support (N : ℕ) (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) :
    (∀ i, sourceProfiles Wslot W₁ W₂ i 0=0) ∧
    (∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i) := by
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra h
    have h' := (hs h).1
    linarith
  constructor
  · simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
        (And.intro (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂))
  · simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j x (hx : Wslot j x≠0) => (hsSlot j hx).2)
        (And.intro (fun x (hx : W₁ x≠0) => (hs₁ hx).2) (fun x (hx : W₂ x≠0) => (hs₂ hx).2))

theorem sourcePool_prime_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (hprime : ∀ j I, I∈pool j → Prime I)
    (hdisjoint : Pairwise (Function.onFun Disjoint pool))
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (∀ j : Fin N, Prime (v (j.castAdd 2))) ∧ Function.Injective (fun j : Fin N => v (j.castAdd 2)) := by
  have hm := sourcePool_original_slots ν pool hpool b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v hv
  refine ⟨fun j => hprime j _ (hm j),?_⟩
  intro i j he
  by_contra hij
  have hmj : v (i.castAdd 2)∈pool j := by
    rw [show v (i.castAdd 2)=v (j.castAdd 2) from he]
    exact hm j
  exact Finset.disjoint_left.mp (hdisjoint hij) (hm i) hmj

open CenteredMomentAddedZeroUniform

def finiteColumns {ι : Type*} [Fintype ι] (S : Finset (Tuple ι)) : Finset (Ideal O) :=
  S.image finiteTupleProduct

def finiteColumnCoefficient {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), β v

lemma finiteColumnCoefficient_mass {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) :
    (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ finiteColumns S, ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma finite_original_mass_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (S : Finset (Tuple ι)) :
    (∑ v ∈ S.image (tupleEquiv e), ‖originalCoefficient n c χ R t
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) =
    ∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ := by
  rw [Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [originalCoefficient_reindex]

theorem smooth_finite_source_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (hb : ∀ j, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  obtain ⟨C,hC,hbound⟩ := smooth_source_mass_uniform (Fintype.card ι)
    (fun j => Wslot (e.symm j)) W₁ W₂ (fun j => a (e.symm j)) (fun j => b (e.symm j))
    a₁ b₁ a₂ b₂ (fun j => ha _) (fun j => hb _) ha₁ hb₁ ha₂ hb₂
    (fun j => hsSlot _) hs₁ hs₂ (fun j => hWslot _) hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := (hbound c hc χ R t (fun j => ν (e.symm j)) (fun j I => hν _ I)
    (fun j => P (e.symm j)) X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP _)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (S.image (tupleEquiv e))).1
  rw [finite_original_mass_reindex] at hm
  simpa only [e.symm.prod_comp P] using hm

theorem smooth_subset_source_mass_uniform {α : Type*} (A : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈A, 0<a j) (hb : ∀ j∈A, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈A, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈A, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ J : Finset α, J⊆A →
      ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ), (∀ j∈J, ∀ I, ‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple J),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
        (fun j : J => Wslot j.val) (fun j : J => P j.val)
        W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ∧
      (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by
  have hfamily (J : Finset α) (hJ : J⊆A) := smooth_finite_source_mass_uniform
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂
  let D (J : Finset α) : ℝ := if hJ : J⊆A then (hfamily J hJ).choose else 1
  have hD (J : Finset α) : 0<D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact (hfamily J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈A.powerset,D J
  have hsum : 0≤∑ J∈A.powerset,D J := Finset.sum_nonneg (fun J _ => (hD J).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro J hJ c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hDC : D J≤C := by
    have hle := Finset.single_le_sum (fun K _ => (hD K).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hm := (hfamily J hJ).choose_spec.2 c hc χ R t (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have he : D J=(hfamily J hJ).choose := by simp only [D,dite_eq_left hJ]
  rw [← he,Finset.prod_coe_sort] at hm
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by positivity
  have hm' := hm.trans (show D J*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ≤
      C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) from
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDC hraw)
  exact ⟨hm',(finiteColumnCoefficient_mass S _).trans hm'⟩

theorem finiteColumns_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) :
    tupleColumns (S.image (tupleEquiv e))=finiteColumns S := by
  simp only [tupleColumns,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleProduct_reindex e v

theorem finiteColumnCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I =
      finiteColumnCoefficient S β I := by
  unfold tupleCoefficient finiteColumnCoefficient
  have hset : (S.image (tupleEquiv e)).filter (fun w => tupleProduct w=I) =
      (S.filter (fun v => finiteTupleProduct v=I)).image (tupleEquiv e) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨v,hv,rfl⟩,hprod⟩
      exact ⟨v,⟨hv,by simpa only [tupleProduct_reindex] using hprod⟩,rfl⟩
    · rintro ⟨v,⟨hv,hprod⟩,rfl⟩
      exact ⟨⟨v,hv,rfl⟩,by simpa only [tupleProduct_reindex] using hprod⟩
  rw [hset,Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  simp only [Equiv.symm_apply_apply]

end SevenEighths.CenteredMomentSourceMass

end

end OAI
end OAIOriginalModule1695

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseAssignedCount
Source SHA256: ff0fae6ecac5980ebd9fc640416a319d8778960b705e387642b6a3958b1f5e3d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1696


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.DetectorDictionaryInverseAssignedCount
local notation "O" => ActualEisensteinCubic.O

def assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) : Finset (ι → Ideal O) := Fintype.piFinset L

@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (q : ι → Ideal O) :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]

def assignedConstant (K : ℕ) (b : ℝ) : ℝ := (128*b)^K

theorem assignedConstant_pos (K : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity

theorem list_card_le (L : Finset (Ideal O)) {H : ℝ} (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  exact (CenteredMomentSourceMass.mem_idealBall H I).mpr (hL I hI)

theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)

def assignedCoefficient {ι : Type*} [Fintype ι]
    (a : ι → Ideal O → ℂ) (q : ι → Ideal O) : ℂ := ∏ i, a i (q i)

theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (a : ι → Ideal O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (q : ι → Ideal O) (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod₀ (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))

theorem restricted_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL

theorem restricted_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp

theorem restricted_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT

theorem slots_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : σ → Ideal O → ℂ) (ha : ∀ i ∈ J, ∀ I ∈ L i, ‖a i I‖ ≤ 1)
    (T : Finset (J → Ideal O)) (hT : T ⊆ assignedTuples (fun i : J => L i)) :
    (∑ q ∈ T, ‖assignedCoefficient (fun i : J => a i) q‖) * U^(-(∑ i ∈ J, ell i)) ≤
      assignedConstant K b := by
  simpa only [Finset.sum_coe_sort] using
    restricted_normalized_mass_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI) (fun i : J => a i)
      (fun i I hI => ha i i.property I hI) T hT

theorem assigned_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1) :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)

theorem slots_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples (fun i : J => L i)).card : ℝ) ≤
      assignedConstant K b * U^(∑ i ∈ J, ell i) := by
  simpa only [Finset.sum_coe_sort] using
    assigned_card_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI)

theorem assignedTuples_eq_empty {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (i : ι) (hi : L i = ∅) :
    assignedTuples L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := (mem_assignedTuples L q).mp hq i
