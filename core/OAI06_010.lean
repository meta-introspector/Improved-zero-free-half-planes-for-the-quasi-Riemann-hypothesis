end OAIOriginalModule1735

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstRetainedSector
Source SHA256: 0db25cbc275e2cdfe367a7ca3a371e4b2d1f9dcf50a82a92bb09f8b9ef73b94b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1736




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedSector
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectorLocalization CenteredMomentFirstCommonFourierTransport
open CenteredMomentHeckeExpansion CenteredMomentCommonSectors
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow
open CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedKernel I J W K X Z ξ=CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ := by
  simp only [retainedKernel,dite_eq_left hI,dite_eq_left hJ]

theorem retainedEnergy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
            retainedKernel q.1 q.2 W K X Z ξ := by
  let F := fun I J : Ideal O=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
    retainedKernel I J W K X Z ξ
  have he : CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
              retainedKernel (C*I) (D*J) W K X Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*rowWeight η m A 1 t I)*star (β (D*J)*rowWeight η m A 1 t J))*
      retainedKernel (C*I) (D*J) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem reconstructed_residualParts (C D I J:Ideal O)(hC:C≠0)(hD:D≠0)(hI:I≠0)(hJ:J≠0)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J):
    residualPart (C*I) (D*J)=I ∧ residualPart (D*J) (C*I)=J:=by
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC hD hI hJ hCD hCI hCJ hIJ
  constructor
  · have hh:=reconstruct (C*I) (D*J) (mul_ne_zero hC hI)
    rw [hc] at hh
    exact (mul_left_cancel₀ hC hh).symm
  · have hh:=reconstruct (D*J) (C*I) (mul_ne_zero hD hJ)
    rw [hd] at hh
    exact (mul_left_cancel₀ hD hh).symm

theorem canonicalRetainedPair_of_common (I J C D:Ideal O)(hI:Supported I)(hJ:Supported J)
    (hC:Supported C)(hc:commonPart I J=C)(hd:commonPart J I=D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (CenteredMomentCanonicalFirst.residualGenerator I J)
          (CenteredMomentCanonicalFirst.residualGenerator J I)
          (CenteredMomentCanonicalFirst.residualGenerator_supported I J hI)
          (CenteredMomentCanonicalFirst.residualGenerator_supported J I hJ) E W K X Z ξ:=by
  subst C
  subst D
  exact canonicalRetainedPair_fixed I J hI hJ W K X Z ξ

theorem retainedKernel_fixed (C D I J:Ideal O)(hC:Supported C)(hD:Supported D)
    (hI:Supported I)(hJ:Supported J)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    retainedKernel (C*I) (D*J) W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) E W K X Z ξ:=by
  have hCI':Supported (C*I):=(supported_mul_iff C I).mpr ⟨hC,hI⟩
  have hDJ':Supported (D*J):=(supported_mul_iff D J).mpr ⟨hD,hJ⟩
  rw [retainedKernel_eq _ _ hCI' hDJ']
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  obtain ⟨hi,hj⟩:=reconstructed_residualParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  have hh:=canonicalRetainedPair_of_common (C*I) (D*J) C D hCI' hDJ' hC hc hd W K X Z ξ
  simpa only [CenteredMomentCanonicalFirst.residualGenerator,hi,hj] using hh

end SevenEighths.CenteredMomentFirstRetainedSector

end

end OAI
end OAIOriginalModule1736

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondCanonical
Source SHA256: dcca9fd743b32b11644a9027579b3f502a553bf98985ab117b61084e9c3b945e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1737




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

def commonPrime (C D : Ideal O) (P : CommonIndex C D) : O := primaryGenerator P.val

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

theorem commonPrime_coprime (C D : Ideal O) (hC : Supported C) :
    Pairwise (Function.onFun IsCoprime (commonPrime C D)) := by
  intro P Q hPQ
  change IsCoprime (commonPrime C D P) (commonPrime C D Q)
  rw [←Ideal.isCoprime_span_singleton_iff,commonPrime_span C D hC P,commonPrime_span C D hC Q]
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

theorem commonPart_eq_left (C D : Ideal O) (hC : C≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) : commonPart C D=C := by
  have hs : commonSupport C D=commonSupport C C := by
    change CompletedGauss.primeSupport C∩CompletedGauss.primeSupport D=
      CompletedGauss.primeSupport C∩CompletedGauss.primeSupport C
    rw [hCD]
  calc
    commonPart C D=commonPart C C := by unfold commonPart;rw [hs]
    _=C := commonPart_self C hC

theorem left_ideal_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P)=C := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_left_product,commonPart_eq_left C D hC.1 hCD]

theorem right_ideal_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P)=D := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_right_product,commonPart_eq_left D C hD.1 hCD.symm]

theorem left_generator_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)=primaryGenerator C := by
  have he := congrArg primaryGeneratorHom (left_ideal_product C D hC hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

theorem right_generator_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)=primaryGenerator D := by
  have he := congrArg primaryGeneratorHom (right_ideal_product C D hC hD hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

def commonFrequencyGenerator (C D : Ideal O) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P)

theorem actual_ideal_secondSaving_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (w : O) (Z : ℝ) (hZ : 1<Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) w Z := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P]
    infer_instance
  have hg (P : CommonIndex C D) : goodLambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P]
    exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P]
    exact common_odd C D hC P
  have hn : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (commonFrequencyGenerator C D*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      idealCorrelation] using hne
  have hh := actual_secondSaving_lower (commonPrime C D) (commonPrime_supported C D hC) hg hc
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) w Z hZ hn
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD] at hh
  exact hh

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end OAIOriginalModule1737

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
Source SHA256: 7fb47453ca2723661dd200119af51b2d9d969c35043f116650b23a6b58598e29
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1738




namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentFirstCanonicalAllowance
open ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonAllowance
local notation "O" => ActualEisensteinCubic.O

theorem activeConductor_span_product (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)

theorem active_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
      (leftExponent I J) (rightExponent I J), Ideal.span {commonPrime I J P}) =
      Ideal.span {activeConductor I J} := by
  simp_rw [commonPrime_span I J hI]
  exact (activeConductor_span_product I J).symm

theorem common_ideal_product (I J : Ideal O) :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := by
  exact Finset.prod_coe_sort (s := commonSupport I J) (f := fun P : Ideal O => P)

theorem common_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P : CommonIndex I J, Ideal.span {commonPrime I J P}) = commonRadical I J := by
  simp_rw [commonPrime_span I J hI]
  exact common_ideal_product I J

theorem commonRadical_active_principal (I J : Ideal O) :
    commonRadical I J = Ideal.span {activeConductor I J} *
      ∏ P ∈ principalSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [← common_ideal_product, activeConductor_span_product]
  simpa only [CenteredMomentActive.activeSupport, CenteredMomentActive.principalSupport, not_not] using
    (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P : CommonIndex I J => netExponent (leftExponent I J P) (rightExponent I J P) ≠ 0)
    (fun P => P.val)).symm

theorem actual_canonical_common_support_allowance
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_common_support_allowance (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) Z hZ
  dsimp only at h ⊢
  rw [left_ideal_product C D hC hCD, right_ideal_product C D hC hD hCD,
    common_generator_ideal_product C D hC, active_generator_ideal_product C D hC] at h
  exact h

theorem activeConductor_span_filter (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)

theorem extracted_activeConductor_span (I J : Ideal O) :
    Ideal.span {activeConductor (commonPart I J) (commonPart J I)} =
      Ideal.span {activeConductor I J} := by
  have hs : commonSupport (commonPart I J) (commonPart J I) = commonSupport I J := by
    unfold commonSupport
    rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
    rfl
  rw [activeConductor_span_filter, activeConductor_span_filter, hs]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro P hP
    rw [commonPart_valuation, commonPart_valuation, commonSupport_comm J I,
      ite_eq_left hP, ite_eq_left hP]
  · intro P _
    rfl

theorem actual_extracted_common_support_allowance
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z ((commonPart I J).absNorm : ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm : ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_canonical_common_support_allowance
    (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
    (commonPart_supported J I hJ) (commonParts_equal_support I J) Z hZ
  dsimp only at h ⊢
  rw [extracted_commonRadical, extracted_activeConductor_span] at h
  exact h

end SevenEighths.CenteredMomentFirstCanonicalAllowance

end

end OAI
end OAIOriginalModule1738

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstExtractedLedger
Source SHA256: dd5d08f90a32062fc05f70e6409b0e3becbce3590518a6966dec669b3fb43749
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1739



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExtractedLedger
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

theorem actual_extracted_first_saving (I J:Ideal O) (hI:Supported I) (hJ:Supported J)
    (Z:ℝ) (hZ:1<Z):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let B:=c+d-2*p-R
    ∀D₀ w q wo g ell σ δ:ℝ,0≤w → 0≤q → 0≤wo → 0≤σ → 0≤δ →
      R≤q → d-δ≤D₀ → g≤max (D₀-c-2*w+wo) 0+2*σ → 0≤ell → w≤7*σ/3 →
      2*(c+w)/3-3*σ-5*δ/6≤firstSaving c D₀ w q wo B g ell:=by
  dsimp only
  intro D₀ w q wo g ell σ δ hw hq hwo hσ hδ hR hD hg hell hwσ
  have ha:=actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at ha
  have hn:(1:ℝ)≤((commonPart I J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (commonPart_supported I J hI).1)
  have hc:0≤Real.logb Z ((commonPart I J).absNorm:ℝ):=Real.logb_nonneg hZ hn
  have hsecond:0≤max (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  have hfirst:0≤max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6:=by positivity
  exact firstSaving_lower _ _ D₀ w q _ wo _ g ell σ δ hc hw hq hwo
    (by linarith) hσ hδ hR (by linarith) hD hg hell hwσ

end SevenEighths.CenteredMomentFirstExtractedLedger

end

end OAI
end OAIOriginalModule1739

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalLedger
Source SHA256: 2981fd0f3d52384bca643de0408059fbb662a4c36e3d134bbfe03bad08fecd35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1740




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstExtractedLedger CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

theorem nominal_log (I J E : Ideal O) (hE : E≠0)
    (Z H X : ℝ) (hH : 0<H) (hX : 0<X) :
    Real.logb Z (firstNominalScale I J E H X)=
      2*Real.logb Z X-Real.logb Z ((commonPart I J).absNorm:ℝ)-
        Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)+
        Real.logb Z (E.absNorm:ℝ)-Real.logb Z H := by
  have hc:=norm_pos _ (commonPart_ne_zero I J)
  have hd:=norm_pos _ (commonPart_ne_zero J I)
  have he:=norm_pos E hE
  have hr:=active_norm_pos I J
  unfold firstNominalScale
  rw [Real.logb_div (mul_pos (mul_pos he hr) (sq_pos_of_pos hX)).ne'
      (mul_pos (mul_pos hH hc) hd).ne',
    Real.logb_mul (mul_pos he hr).ne' (sq_pos_of_pos hX).ne',
    Real.logb_mul he.ne' hr.ne',Real.logb_pow,
    Real.logb_mul (mul_pos hH hc).ne' hd.ne',Real.logb_mul hH.ne' hc.ne']
  push_cast
  ring

theorem retained_nominal_frequency (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1<Z) (hH : 0<H) (hX : 0<X)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n)≤
      Real.logb Z (firstNominalScale I J E H X)+frequencyLoss Z Csec ξ := by
  apply retained_first_dyad_enclosure Tsec Z Csec _ ξ hZ hC _ n hn
  simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (firstNominalScale_pos I J E hE H X hH hX)] using hsec

theorem retained_deficit (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1<Z) (hH : 0<H) (hX : 0<X)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec ξ≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n) := by
  linarith [retained_nominal_frequency I J E hE Z H X Tsec Csec ξ hZ hH hX hC hsec n hn]

theorem frequency_loss_eventually (Csec ξ : ℝ) (hC : 0<Csec) (hξ : 0<ξ) :
    ∃Z₀ : ℝ,1<Z₀ ∧ ∀Z : ℝ,Z₀≤Z → 1<Z ∧ frequencyLoss Z Csec ξ<ξ := by
  have hg := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ξ/4 by linarith))) (4*Csec)
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (hg.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max Z₀ 2,by linarith [le_max_right Z₀ (2:ℝ)],?_⟩
  intro Z hZ
  obtain ⟨hb,hZ1⟩:=hZ₀ Z ((le_max_left Z₀ 2).trans hZ)
  have hl:=Real.logb_le_logb_of_le hZ1 (show 0<4*Csec by positivity) hb
  rw [Real.logb_rpow (zero_lt_one.trans hZ1) hZ1.ne'] at hl
  exact ⟨hZ1,by unfold frequencyLoss;linarith⟩

theorem actual_first_saving (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hE : E≠0) (Z H X Tsec Csec ξ q w wo ell σ branch : ℝ)
    (hZ : 1<Z) (hH : 0<H) (hX : 0<X) (hC : 1≤Csec)
    (hξ : 0≤ξ) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hq : 0≤q) (hw : 0≤w) (hwo : 0≤wo) (hell : 0≤ell) (hσ : 0≤σ)
    (hbranch : branch≤2) (hwσ : w≤7*σ/3) :
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let e:=Real.logb Z (E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n)
    2*(c+w)/3-3*σ-5*(frequencyLoss Z Csec ξ)/6≤
      firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
        (max (D₀-c-2*w+wo) 0+branch*σ) ell := by
  dsimp only
  have hRn : (1:ℝ)≤((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hEn : (1:ℝ)≤(E.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hR:=Real.logb_nonneg hZ hRn
  have he:=Real.logb_nonneg hZ hEn
  apply actual_extracted_first_saving I J hI hJ Z hZ _ _ _ _ _ _ _ _ hw
    (by linarith) hwo hσ (frequencyLoss_nonneg Z Csec ξ hZ hC hξ)
    (by linarith) (retained_deficit I J E hE Z H X Tsec Csec ξ hZ hH hX
      (by linarith) hsec n hn) _ hell hwσ
  nlinarith

end SevenEighths.CenteredMomentFirstPhysicalLedger

end

end OAI
end OAIOriginalModule1740

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
Source SHA256: a81636625871f05ccfc6a876f803e48b6615b16c00b09ef528bf9e156b323984
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1741


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem commonFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    commonFrequencyGenerator C D∣primaryGenerator C ∧
    commonFrequencyGenerator C D∣primaryGenerator D := by
  rw [←left_generator_product C D hC hCD,←right_generator_product C D hC hD hCD]
  constructor
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>pow_dvd_pow _ (min_le_left _ _))
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=>pow_dvd_pow _ (min_le_right _ _))

theorem idealCorrelation_zero_outside_common (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (j : O) (hj : ¬commonFrequencyGenerator C D∣j) : idealCorrelation C D hC hD j=0 := by
  have hd := commonFrequencyGenerator_dvd C D hC hD hCD
  let := finite_quotient_span (supported_primaryGenerator_ne_zero C hC)
  let := finite_quotient_span (supported_primaryGenerator_ne_zero D hD)
  let : Fintype (O⧸Ideal.span {primaryGenerator C}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {primaryGenerator D}) := Fintype.ofFinite _
  unfold idealCorrelation actualCorrelation
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ _ _ _ _ hd.1 hd.2 hj

theorem idealCorrelation_tsum_common (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (F : O→ℂ) :
    (∑' j : O,idealCorrelation C D hC hD j*F j)=
      ∑' w : O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*
        F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq (f := fun j => idealCorrelation C D hC hD j*F j) ?_
  intro j hj
  have hd : commonFrequencyGenerator C D∣j := by
    by_contra hn
    exact hj (by dsimp only;rw [idealCorrelation_zero_outside_common C D hC hD hCD j hn,zero_mul])
  obtain ⟨w,hw⟩ := hd
  exact ⟨w,hw.symm⟩

def canonicalPartition (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : Prop :=
  actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U

def canonicalPartitionScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : ℂ :=
  if canonicalPartition C D U w then
    (partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U:ℂ)⁻¹ else 0

theorem actual_ideal_partition_scalar (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O) :
    ‖canonicalPartitionScalar C D U w*
      idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)‖≤1 := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hg (P : CommonIndex C D) : goodLambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P];exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P];exact common_odd C D hC P
  have hp : canonicalPartition C D U w→∀ i∈U,
      leftExponent C D i=rightExponent C D i ∧ ¬6∣leftExponent C D i ∧
        ¬commonPrime C D i∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w i := by
    intro h i hi
    rw [canonicalPartition] at h
    rw [←h] at hi
    exact (Finset.mem_filter.mp hi).2
  have hh := normalized_partition_norm_le_one (commonPrime C D) (commonPrime_supported C D hC)
    hg hc (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) U (canonicalPartition C D U) w hp
  simp only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD] at hh
  by_cases hw : canonicalPartition C D U w
  · simpa only [canonicalPartitionScalar,ite_eq_left hw,div_eq_mul_inv,mul_comm,
      idealCorrelation,commonFrequencyGenerator] using hh
  · simp only [canonicalPartitionScalar,ite_eq_right hw,zero_mul,norm_zero,zero_le_one]

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
end OAIOriginalModule1741

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
Source SHA256: 6e7170af6b8657e253fee677778f0c8654d68bb0b1d6baecd81142d9702c3756
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1742


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def equalActiveSet (C D : Ideal O) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P)

def nonunitPartitionSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  equalActiveSet C D\U

def nonunitFrequencyGenerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P∈nonunitPartitionSet C D U,commonPrime C D P

theorem commonPrime_dividedFrequency_iff (C D : Ideal O) (hC : Supported C)
    (w : O) (P : CommonIndex C D) :
    commonPrime C D P∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w P ↔
      commonPrime C D P∣w := by
  have hc : IsCoprime (commonPrime C D P)
      (cofactor (fun Q=>commonPrime C D Q^min (leftExponent C D Q) (rightExponent C D Q)) P) := by
    unfold cofactor
    apply IsCoprime.prod_right
    intro Q hQ
    exact (commonPrime_coprime C D hC (Finset.mem_erase.mp hQ).1.symm).pow_right
  constructor
  · exact fun h=>hc.dvd_of_dvd_mul_left h
  · exact fun h=>h.trans (dvd_mul_left _ _)

theorem nonunitPartitionSet_eq_actual (C D : Ideal O) (U : Finset (CommonIndex C D))
    (w : O) (hpart : canonicalPartition C D U w) :
    nonunitPartitionSet C D U=actualNonunitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w := by
  unfold canonicalPartition at hpart
  rw [nonunitPartitionSet,←hpart]
  ext P
  simp only [equalActiveSet,actualUnitSet,actualNonunitSet,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_univ,true_and]
  tauto

theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem nonunitFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (w : O) (hpart : canonicalPartition C D U w) :
    nonunitFrequencyGenerator C D U∣w := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hPQ
    exact commonPrime_coprime C D hC hPQ
  · intro P hP
    rw [nonunitPartitionSet_eq_actual C D U w hpart] at hP
    exact (commonPrime_dividedFrequency_iff C D hC w P).mp (Finset.mem_filter.mp hP).2.2.2

theorem partition_tsum_nonunit (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : O→ℂ) :
    (∑' w : O,if canonicalPartition C D U w then
      idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*F w else 0)=
      ∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        idealCorrelation C D hC hD ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)*
          F (nonunitFrequencyGenerator C D U*h) else 0 := by
  let f : O→ℂ := fun w=>if canonicalPartition C D U w then
    idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*F w else 0
  have hs : Function.support f⊆Set.range (fun h=>nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by simp only [f,ite_eq_right hn])
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact ⟨h,hh.symm⟩
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm

end SevenEighths.CenteredMomentSecondCanonicalNonunit

end

end OAI
end OAIOriginalModule1742

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
Source SHA256: 0a8b3ee8c6ea5e5ad4308ef2363b7839a5d00036c332e6bc3dad3eb837421b8f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1743



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalLedger
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentForcing
local notation "O" => ActualEisensteinCubic.O

theorem span_finset_product {ι : Type*} (S : Finset ι) (p : ι→O) :
    Ideal.span {∏ i∈S,p i}=∏ i∈S,Ideal.span {p i} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,
      ←Ideal.span_singleton_mul_span_singleton,ih]

theorem commonFrequencyGenerator_span (C D : Ideal O) (_hC : Supported C) :
    Ideal.span {commonFrequencyGenerator C D}=
      commonIdeal (commonPrime C D) (leftExponent C D) (rightExponent C D) := by
  simp only [commonFrequencyGenerator,span_finset_product,←Ideal.span_singleton_pow,commonIdeal]

theorem nonunitFrequencyGenerator_span (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    Ideal.span {nonunitFrequencyGenerator C D U}=
      unitIdeal (commonPrime C D) (nonunitPartitionSet C D U) := by
  simp only [nonunitFrequencyGenerator,span_finset_product,unitIdeal]

theorem actual_partitionNormalizer (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U=
      (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        Ideal.absNorm (∏ P∈U,P.val) := by
  rw [partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D),←commonFrequencyGenerator_span C D hC]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem actual_second_ledger_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O) (hpart : canonicalPartition C D U w)
    (Z : ℝ) (hZ : 1<Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ)-
      5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
      Real.logb Z (Ideal.absNorm (∏ P : CommonIndex C D,P.val):ℝ)+
      Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
      Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
      Real.logb Z (Ideal.absNorm (forcingIdeal (fun P : CommonIndex C D=>P.val)
        (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ)/3 := by
  have hh := actual_ideal_secondSaving_lower C D hC hD hCD w Z hZ hne
  rw [secondSaving_eq_norm_ledger _ (commonPrime_supported C D hC)] at hh
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD,
    ←commonFrequencyGenerator_span C D hC] at hh
  change actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U at hpart
  rw [hpart,←nonunitPartitionSet_eq_actual C D U w hpart,
    ←nonunitFrequencyGenerator_span C D U] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,forcingIdeal] using hh

theorem actual_partition_count (ε : ℝ) (hε : 0<ε) :
    ∃ B : ℝ,0<B ∧ ∀ C D : Ideal O,C≠0 →
      (Fintype.card (Finset (CommonIndex C D)):ℝ)≤B*(Ideal.absNorm C:ℝ)^ε := by
  obtain ⟨B,hB,hcount⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨B,hB,?_⟩
  intro C D hC
  have hc : Fintype.card (CommonIndex C D)≤(CompletedGauss.primeSupport C).card := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card Finset.inter_subset_left
  have hh : (Fintype.card (Finset (CommonIndex C D)):ℝ)≤
      (2:ℝ)^(CompletedGauss.primeSupport C).card := by
    rw [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hc
  exact hh.trans (hcount C hC)

end SevenEighths.CenteredMomentSecondCanonicalLedger

end

end OAI
end OAIOriginalModule1743

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondCanonicalScalar
Source SHA256: c52f4a4ae80e97f80fe5f761ebaf2aae357daf373f245f5ac6cca7e3e4f6d2c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1744



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def normalizer (C D : Ideal O) (U : Finset (CommonIndex C D)) : ℝ :=
  partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U

theorem normalizer_pos (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    0<normalizer C D U := by
  rw [normalizer,partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D)]
  exact div_pos (commonIdeal_norm_pos _ (commonPrime_supported C D hC) _ _)
    (unitIdeal_norm_pos _ (commonPrime_supported C D hC) _)

def retainedScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) : ℂ :=
  canonicalPartitionScalar C D U (nonunitFrequencyGenerator C D U*h)*
    (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)

theorem actual_retained_scalar_norm (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) :
    ‖retainedScalar C D U R h*idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)‖≤1 := by
  have hs := actual_ideal_partition_scalar C D hC hD hCD U (nonunitFrequencyGenerator C D U*h)
  have hw := retainedWeight_bounds R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))
  rw [retainedScalar,mul_right_comm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
  exact (mul_le_of_le_one_left hw.1 (by simpa only [mul_assoc] using hs)).trans hw.2

theorem original_partition_scalar (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) (F : ℂ) :
    (if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)*F else 0)=
      (normalizer C D U:ℂ)*(retainedScalar C D U R h*F) := by
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  unfold retainedScalar canonicalPartitionScalar
  change _=(normalizer C D U:ℂ)*((if _ then (normalizer C D U:ℂ)⁻¹ else 0)*_*F)
  split_ifs <;> simp_all [mul_assoc]

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI
end OAIOriginalModule1744

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
Source SHA256: 48566258b8b5941f09abd42573aa8d30ebe4c167cd5a577cf8a7f438c2cd04c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1745




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentSupport UniqueFactorizationMonoid
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

lemma supported_coprime_72 (C:Ideal O) (hC:Supported C) :
    IsCoprime (Ideal.span {(72:O)}) C := by
  let n:=primaryGenerator C
  have hn:Supported (Ideal.span {n}):=by rw [primary_span_supported C hC]; exact hC
  have h2:IsCoprime n (2:O):=(fixedBadMask_coprime n hn).of_mul_left_right.symm
  have h9: IsCoprime n (9:O):=
    (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n ((supported_span_iff n).mp hn).1).symm
  have h72:IsCoprime n (72:O):=by
    convert (h2.pow_right : IsCoprime n ((2:O)^3)).mul_right h9 using 1 ; norm_num
  rw [←primary_span_supported C hC,Ideal.isCoprime_span_singleton_iff]
  exact h72.symm

lemma common_prime_dvd_left (C D:Ideal O) (P:CommonIndex C D) : P.val∣C :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma common_prime_prime (C D:Ideal O) (hC:Supported C) (P:CommonIndex C D) :
    Prime (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma outer_nonzero_left (η:Character) (t:ℝ) (C D:Ideal O)
    (hne:heightCoeff η t C*star (heightCoeff η t D)≠0) : idealCoeff η C≠0 :=
  left_ne_zero_of_mul (left_ne_zero_of_mul hne)

theorem actual_canonical_exceptional_count (η:Character) (χ:RayFourExpansion.RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (Q:Ideal O) (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)})
    (hQC:IsCoprime Q C) (hη:idealCoeff η C≠0)
    (m:O) (hm:m≠0) (hmLam:goodLambda∣m) (hm2:(2:O)∣m)
    (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (hex:∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M:ℝ) (hZ:1<Z) (hCr:0≤Cr)
    (hN:∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) :
    (rows.card:ℝ)≤768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
        (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6) := by
  have he:elementCoeff η (primaryGenerator C)≠0 := by
    rw [←idealCoeff_span η (supported_primaryGenerator_ne_zero C hC),primary_span_supported C hC]
    exact hη
  have hinj:Function.Injective (fun P:CommonIndex C D=>Ideal.span {commonPrime C D P}):=by
    simpa only [commonPrime_span C D hC] using (Subtype.val_injective:Function.Injective (fun P:CommonIndex C D=>P.val))
  have hb:=actual_forcing_exceptional_count (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P hP
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),hQC.of_isCoprime_of_dvd_right (common_prime_dvd_left C D P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb

end SevenEighths.CenteredMomentSecondExceptionalCount

end

end OAI
end OAIOriginalModule1745

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount
Source SHA256: d09cd0373b14a9c5ad040a03807a205f07c0c91b3a25950974c2384dd7825d25
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1746



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedQForcingCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentForcing CenteredMomentChildRows CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSupport
open CenteredMomentSourceRow
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goodSet (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  (forcingSet c d V).filter (fun i => IsCoprime Q (P i))

def excludedSet (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  (forcingSet c d V).filter (fun i => ¬IsCoprime Q (P i))

def goodIdeal (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ goodSet Q P c d V, P i

def excludedIdeal (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ excludedSet Q P c d V, P i

omit [Fintype ι] [DecidableEq ι] in
lemma prime_product_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) : Squarefree (∏ i ∈ S, P i) := by
  simpa [forcingIdeal, forcingSet] using
    forcingIdeal_squarefree P hp hinj (fun _ => 1) (fun _ => 1) S

omit [Fintype ι] [DecidableEq ι] in
lemma prime_product_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (S : Finset ι) (R : Ideal O) (hR : R ∈ normalizedFactors (∏ i ∈ S, P i)) :
    ∃ i ∈ S, R = P i := by
  simpa [forcingIdeal, forcingSet] using
    forcing_prime_mem P hp (fun _ => 1) (fun _ => 1) S R (by
      simpa [forcingIdeal, forcingSet] using hR)

omit [Fintype ι] [DecidableEq ι] in
lemma goodIdeal_squarefree (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (goodIdeal Q P c d V) :=
  prime_product_squarefree P hp hinj _

omit [Fintype ι] [DecidableEq ι] in
lemma goodIdeal_ne_zero (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : goodIdeal Q P c d V ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)

lemma good_valuation_two (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι)
    (hi : i ∈ goodSet Q P c d V) :
    CenteredExceptionalCount.valuation (movingIdeal P c d V) (P i) = 2 :=
  forcing_valuation_two P hp hinj c d V i (Finset.mem_filter.mp hi).1

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_split (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) :
    goodIdeal Q P c d V * excludedIdeal Q P c d V = forcingIdeal P c d V := by
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

lemma prime_dvd_of_not_coprime (Q P : Ideal O) (hP : Prime P) (h : ¬IsCoprime Q P) : P ∣ Q := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hs : Q ⊔ P ≠ ⊤ := by simpa only [Ideal.isCoprime_iff_sup_eq] using h
  have he : P = Q ⊔ P := Ideal.IsMaximal.eq_of_le inferInstance hs le_sup_right
  exact Ideal.dvd_iff_le.mpr (le_sup_left.trans_eq he.symm)

omit [Fintype ι] [DecidableEq ι] in
lemma excludedIdeal_dvd_radical (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) : excludedIdeal Q P c d V ∣ commonRadical Q Q := by
  apply (CenteredMomentDivisorAllocation.squarefree_dvd_iff _ _
    (prime_product_squarefree P hp hinj _)).mpr
  intro R hR
  obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp _ R (Multiset.mem_toFinset.mp hR)
  have hd := prime_dvd_of_not_coprime Q (P i) (hp i) (Finset.mem_filter.mp hi).2
  have hm : P i ∈ IdealMobiusDivisorSum.primeSupport Q := by
    simpa only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hQ,
      hp i, true_and] using hd
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hm,hm⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_dvd_good_mul_radical (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) :
    forcingIdeal P c d V ∣ goodIdeal Q P c d V * commonRadical Q Q := by
  rw [←forcing_split Q P c d V]
  exact mul_dvd_mul_left _ (excludedIdeal_dvd_radical Q hQ P hp hinj c d V)

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_norm_le (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) :
    (Ideal.absNorm (forcingIdeal P c d V) : ℝ) ≤
      (Ideal.absNorm (goodIdeal Q P c d V) : ℝ) * Ideal.absNorm (commonRadical Q Q) := by
  have hd := map_dvd Ideal.absNorm (forcing_dvd_good_mul_radical Q hQ P hp hinj c d V)
  have hn : (goodIdeal Q P c d V) * commonRadical Q Q ≠ 0 :=
    mul_ne_zero (goodIdeal_ne_zero Q P hp c d V) (commonRadical_ne_zero Q Q)
  have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) hd
  exact_mod_cast (show Ideal.absNorm (forcingIdeal P c d V) ≤
    Ideal.absNorm (goodIdeal Q P c d V) * Ideal.absNorm (commonRadical Q Q) by simpa using hh)

lemma fixed_radical_power_loss (Z M f g r : ℝ) (hZ : 1 < Z)
    (hf : 0 < f) (hg : 0 < g) (hr : 0 < r) (hfg : f ≤ g*r) :
    Z ^ ((M-4*Real.logb Z g)/6) ≤
      r^(2/3:ℝ) * Z^((M-4*Real.logb Z f)/6) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.logb_le_logb_of_le hZ hf hfg
  rw [Real.logb_mul hg.ne' hr.ne'] at hl
  calc
    _ ≤ Z^(Real.logb Z r*(2/3)+(M-4*Real.logb Z f)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = _ := by
      rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hr]

theorem actual_forcing_exceptional_count_fixedQ (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι)
    (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m e : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      goodLambda ∉ Ideal.span {p i} ∧ (2 : O) ∉ Ideal.span {p i} ∧
      Ideal.span {p i} ∣ Ideal.span {e})
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr * Z ^ M) :
    (rows.card : ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ) *
      (768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card * Cr^(1/6:ℝ) *
        Z^((M-4*Real.logb Z (Ideal.absNorm
          (forcingIdeal (fun i => Ideal.span {p i}) c d V):ℝ))/6)) := by
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let G := goodIdeal Q P c d V
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  have hG0 : G ≠ 0 := goodIdeal_ne_zero Q P hp c d V
  have hGn : (0:ℝ) < Ideal.absNorm G := CenteredExceptionalCount.norm_pos hG0
  have hb := separated_exceptional_count η χ Q hQ0 hQ hQ72
    m (movingElement p c d V) e hm hA hmLam hm2 he rows hrows hex G
    (goodIdeal_squarefree Q P hp hinj c d V) (by
      intro R hR
      obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp (goodSet Q P c d V) R hR
      obtain ⟨hif,hQi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hl,h2,hd⟩ := hgood i hif
      refine ⟨hl,h2,hQi,hd,?_⟩
      rw [movingElement_span,good_valuation_two Q P hp hinj c d V i hi])
    Z Cr M (2*Real.logb Z (Ideal.absNorm G:ℝ)) (zero_lt_one.trans hZ) hCr (by
      rw [show (2*Real.logb Z (Ideal.absNorm G:ℝ))/2=Real.logb Z (Ideal.absNorm G:ℝ) by ring,
        Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hGn]) hN
  have hb' : (rows.card:ℝ) ≤ 768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm G:ℝ))/6) := by
    have heq : (M-2*(2*Real.logb Z (Ideal.absNorm G:ℝ)))/6 =
        (M-4*Real.logb Z (Ideal.absNorm G:ℝ))/6 := by ring
    simpa only [heq] using hb
  have hf : (0:ℝ) < Ideal.absNorm (forcingIdeal P c d V) := by
    apply CenteredExceptionalCount.norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  have hr : (0:ℝ) < Ideal.absNorm (commonRadical Q Q) :=
    CenteredExceptionalCount.norm_pos (commonRadical_ne_zero Q Q)
  have hs := fixed_radical_power_loss Z M _ _ _ hZ hf hGn hr
    (forcing_norm_le Q hQ0 P hp hinj c d V)
  apply hb'.trans
  calc
    _ ≤ (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        ((Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal P c d V):ℝ))/6)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem actual_canonical_exceptional_count_fixedQ (η : Character) (χ : RayFourExpansion.RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hη : idealCoeff η C ≠ 0)
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card:ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D => P.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6)) := by
  have he : elementCoeff η (primaryGenerator C) ≠ 0 := by
    rw [←idealCoeff_span η (supported_primaryGenerator_ne_zero C hC),primary_span_supported C hC]
    exact hη
  have hinj : Function.Injective (fun P:CommonIndex C D => Ideal.span {commonPrime C D P}) := by
    simpa only [commonPrime_span C D hC] using
      (Subtype.val_injective : Function.Injective (fun P:CommonIndex C D => P.val))
  have hb := actual_forcing_exceptional_count_fixedQ (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P _
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb

end SevenEighths.CenteredMomentFixedQForcingCount

end

end OAI
end OAIOriginalModule1746

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalEnergy
Source SHA256: 60d582ab53c02bbf3c7aabbdc84f93b17c6bc98f447d1800e26982ae48f5f041
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1747


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentSecondExceptionalEnergy
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentHeckeSlots CenteredMomentSecondExceptionalCount UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem actual_exceptional_slots_energy {ι:Type*} [Fintype ι]
    (Q:Ideal O) (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B) :
    ∃J:ℕ,∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L:ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩:=exceptional_slots_estimate (ι:=ι) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hpoint⟩:=hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hA:A≠0:=mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hc:=actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη m hm hmLam hm2
    rows hrows hex Z Cr M hZ hCr hN
  have hp:∀z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
      C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L):=by
    intro z hz
    exact hpoint Z hZ.le (childCharacter η χ) m A z hm hA (hrows z hz) hmLam hm2
      (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  calc
    _≤∑z∈rows,(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 :=
      Finset.sum_le_sum (fun z hz=>pow_le_pow_left₀ (norm_nonneg _) (hp z hz) 2)
    _=(rows.card:ℝ)*(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 := by simp
    _≤_:=mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end SevenEighths.CenteredMomentSecondExceptionalEnergy

end

end OAI
end OAIOriginalModule1747

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalCappedAmplitude
Source SHA256: c2796331998f0d9384e5f4d071aa813ba94ed10d7dc0d9e8c4e37a756ab663ca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1748




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentExceptionalCappedAmplitude
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentCounting CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentHeight CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondExceptionalCount
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_absolute (η : Character) (m A z : O) (W : ℝ→ℂ)
    (b M t X : ℝ) (hb : 0≤b) (hM : 0≤M) (hX : 0<X)
    (hs : Function.support W⊆Set.Iic b) (hW : ∀x,‖W x‖≤M) :
    ‖rowTwistedSum η m A z W t X‖≤(128*b*M)*X := by
  have hh := norm_tsum_ideal_ball
    (fun I : Ideal O => (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)) (b*X) M
    (mul_nonneg hb hX.le) hM (by
      change (idealCoeff η (0:Ideal O)*_)*_*_=0
      rw [map_zero,zero_mul,zero_mul,zero_mul]) (by
      intro I
      by_cases hI : I=0
      · subst I; simpa only [map_zero,zero_mul,mul_zero,norm_zero] using hM
      · rw [norm_mul]
        exact (mul_le_mul (row_twisted_coefficient_norm η m A z t I hI) (hW _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul M)) (by
      intro I hI
      exact (div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hI)))
  exact hh.trans_eq (by ring)

theorem normalized_rectangle_absolute (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hW₁ : ∀x,‖W₁ x‖≤M₁) (hW₂ : ∀x,‖W₂ x‖≤M₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹ *
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
      (2*(128*b₁*M₁)*(128*b₂*M₂))*Real.sqrt T := by
  have hT : 0<T := hpX ▸ mul_pos hX₁ hX₂
  have hsq : 0<Real.sqrt T := Real.sqrt_pos.2 hT
  have hprod (U V : ℝ) (hU : 0<U) (hV : 0<V) :
      ‖rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V‖≤
        ((128*b₁*M₁)*(128*b₂*M₂))*(U*V) := by
    rw [norm_mul]
    apply (mul_le_mul (rowTwistedSum_absolute η m A z W₁ b₁ M₁ t U hb₁ hM₁ hU hs₁ hW₁)
      (rowTwistedSum_absolute η m A z W₂ b₂ M₂ t V hb₂ hM₂ hV hs₂ hW₂)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hraw := (norm_sub_le
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)
    (rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)).trans
      (add_le_add (hprod X₁ X₂ hX₁ hX₂) (hprod Y₁ Y₂ hY₁ hY₂))
  rw [hpX,hpY] at hraw
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsq.le]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsq.le)).trans_eq
  have he := Real.sq_sqrt hT.le
  field_simp
  rw [he]
  ring

theorem capped_rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∀W₁ W₂ : ℝ→ℂ,
      ∀_hs₁ : Function.support W₁⊆Set.Icc a₁ b₁,
      ∀_hs₂ : Function.support W₂⊆Set.Icc a₂ b₂,
      ∀_hW₁ : ContDiff ℝ ∞ W₁,∀_hW₂ : ContDiff ℝ ∞ W₂,
      ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀(η : Character)(m A z : O),
      m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
         rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,hJ⟩ := row_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0≤M₁ := apply_nonneg _ _
  have hM₂ : 0≤M₂ := apply_nonneg _ _
  have hbound₁ (x : ℝ) : ‖W₁ x‖≤M₁ := by
    rw [←normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (x : ℝ) : ‖W₂ x‖≤M₂ := by
    rw [←normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let D : ℝ := 2*(128*b₁*M₁)*(128*b₂*M₂)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : 0≤Z^ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    exact (hcancel Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L
      hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hpow) (by positivity))
          (div_nonneg (Real.sqrt_nonneg _) hL.le))
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have ha := normalized_rectangle_absolute η m A z W₁ W₂ b₁ b₂ M₁ M₂ hb₁ hb₂ hM₁ hM₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hbound₁ hbound₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    calc
      D≤C+D := le_add_of_nonneg_left hC.le
      _≤(C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
      _≤(C+D)*Z^ε*(1+‖t‖)^J := le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by linarith [norm_nonneg t]))

theorem actual_capped_slots
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∀W₁ W₂ : ℝ→ℂ,
      ∀_hs₁ : Function.support W₁⊆Set.Icc a₁ b₁,
      ∀_hs₂ : Function.support W₂⊆Set.Icc a₂ b₂,
      ∀_hW₁ : ContDiff ℝ ∞ W₁,∀_hW₂ : ContDiff ℝ ∞ W₂,
      ∃C : ℝ,0<C ∧ ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,hJ⟩ := capped_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

theorem actual_canonical_capped_energy
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B) :
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀(ι:Type*) [Fintype ι],∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L:ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 := by
  obtain ⟨J,hJ⟩:=actual_capped_slots a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hpoint⟩:=hJ Q hQ0 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro ι _ Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hA:A≠0:=mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hc:=actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη m hm hmLam hm2
    rows hrows hex Z Cr M hZ hCr hN
  have hp:∀z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
      C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L):=by
    intro z hz
    exact hpoint ι Z hZ.le (childCharacter η χ) m A z hm hA (hrows z hz) hmLam hm2
      (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  calc
    _≤∑z∈rows,(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 :=
      Finset.sum_le_sum (fun z hz=>pow_le_pow_left₀ (norm_nonneg _) (hp z hz) 2)
    _=(rows.card:ℝ)*(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 := by simp
    _≤_:=mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    max 1 (Z^r/Rred)=Z^(max (r-Real.logb Z Rred) 0) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he : Z^r/Rred=Z^(r-Real.logb Z Rred) := by
    rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hR]
  rw [he]
  by_cases h : 0≤r-Real.logb Z Rred
  · rw [max_eq_left h,max_eq_right (Real.one_le_rpow hZ.le h)]
  · rw [max_eq_right (le_of_not_ge h),Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_not_ge h))]

theorem reciprocal_max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    1/max 1 (Z^r/Rred)=Z^(-max (r-Real.logb Z Rred) 0) := by
  rw [max_raw_reduction Z Rred r hZ hR,Real.rpow_neg (zero_le_one.trans hZ.le),one_div]

theorem allocation_reciprocal_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : CenteredMomentActiveDivisorShell.Source ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (Z r : ℝ) (hZ : 1<Z) :
    1/max 1 (Z^r/formalReductionFactor D a s.P)=
      Z^(-max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) := by
  apply reciprocal_max_raw_reduction Z _ r hZ
  exact mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalCappedAmplitude

end

end OAI
end OAIOriginalModule1748

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocatedCenteredCapped
Source SHA256: c7b8685be7124aa99d89ef9642f008a21f2cbc1fa43479fd06e69000f28ee7b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1749



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAllocatedCenteredCapped
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentExceptionalCappedAmplitude
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma plain_norm_le_reduction (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (j:Fin 2):
    (Ideal.absNorm (selectedPlain L a j):ℝ)≤formalReductionFactor L a P:=by
  have hN (k:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain L a k):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr k)))
  have hh:(Ideal.absNorm (selectedPlain L a j):ℝ)≤selectedNorm L a:=by
    fin_cases j
    · exact le_mul_of_one_le_right (by positivity) (hN 1)
    · exact le_mul_of_one_le_left (by positivity) (hN 0)
  exact hh.trans (le_mul_of_one_le_right (selectedNorm_pos L a).le
    (Finset.one_le_prod₀ (fun i _=>hP i)))

lemma allocated_lower (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (Z r X:ℝ) (hZ:0<Z) (hX:Z^r≤X) (j:Fin 2):
    Z^r/formalReductionFactor L a P≤X/(Ideal.absNorm (selectedPlain L a j):ℝ):=by
  have hn:(0:ℝ)<Ideal.absNorm (selectedPlain L a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ.le _) hn
    (plain_norm_le_reduction L a P hP j)).trans (div_le_div_of_nonneg_right hX hn.le)

lemma remaining_volume (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,0<P i) (T:ℝ):
    (T/selectedNorm L a)*(∏i:liveIndices L a,P i)=
      (T*∏i,P i)/formalReductionFactor L a P:=by
  rw [Finset.prod_coe_sort]
  apply (eq_div_iff (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).ne').mpr
  exact raw_scale_identity L a T P

 theorem actual_allocated_capped_energy
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀t X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖residualCenteredRow (childCharacter η χ) m A z t S β P L a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i:liveIndices L a,128*b i*Ms i)*
          (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
            Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)))^2:=by
  obtain ⟨J,hJ⟩:=actual_canonical_capped_energy a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hbound⟩:=hJ Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro ι _ _ Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs L a t X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (liveIndices L a) Z hZ η χ C D hC U hQC hη m hm hmLam hm2 rows hrows hex hcond Cr M hCr hN
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>Ms i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hMs i) (fun i=>hβ i) (fun i=>hNs i)
    t (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
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

end SevenEighths.CenteredMomentAllocatedCenteredCapped

end

end OAI
end OAIOriginalModule1749

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalRow
Source SHA256: de1d3e122da1cc136d8bd2cd94976cc575530d2ffd8b9f7149e220535a1b979e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1750



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem row_rectangle_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hJ⟩ := rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1750

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCapped
Source SHA256: 5f64d16980c72f5ae9fb62e4b5c8da1cb8cf0c9fa6d236000fc2868bf4d85930
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1751


namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeTwist CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem capped_rectangle_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,S,hS,hJ⟩ := row_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ
  let D : ℝ := 2*(128*b)*(128*b)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let P₁ := sourceControl S W₁
  let P₂ := sourceControl S W₂
  have hP₁ : 0≤P₁ := sourceControl_nonneg S W₁
  have hP₂ : 0≤P₂ := sourceControl_nonneg S W₂
  have hw₁ (x:ℝ) : ‖W₁ x‖≤P₁ :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₁) (i := (0, 0)) hS)
  have hw₂ (x:ℝ) : ‖W₂ x‖≤P₂ :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
        (s := S) (x := W₂) (i := (0, 0)) hS)
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    apply (hcancel W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
    gcongr
    exact le_add_of_nonneg_right hD
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have habs := normalized_rectangle_absolute η m A z W₁ W₂ b b P₁ P₂ hb hb hP₁ hP₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hw₁ hw₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    have hc : D ≤ (C+D)*Z^ε*(1+‖t‖)^J := by
      calc
        _ ≤ C+D := le_add_of_nonneg_left hC.le
        _ ≤ (C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith [norm_nonneg t]))
    apply habs.trans
    calc
      _ = D*(P₁*P₂)*Real.sqrt T := by dsimp [D]; ring
      _ ≤ ((C+D)*Z^ε*(1+‖t‖)^J)*(P₁*P₂)*Real.sqrt T := by
        gcongr
      _ = _ := by dsimp [P₁,P₂]; ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1751

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalSlots
Source SHA256: ef07318e7392d531abae46181c92e78847d5cdbb6e3d796bcc3e3ceadc17a935
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1752


namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
theorem capped_slots_source_control
    (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ, ∃ R : Finset (ℕ×ℕ), (0,0)∈R ∧
      ∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,R,hR,hJ⟩ := capped_rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hR₁ := sourceControl_nonneg R W₁
  have hR₂ := sourceControl_nonneg R W₂
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound W₁ W₂ hs₁ hs₂ Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1752

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalAllocated
Source SHA256: c29d81c3503369b9f699bee1141d127c966276e455d7b01c9c8a0a3fb3845a1e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1753



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open ConcretePrimeRowBridge CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O
theorem allocated_source_control (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ), Function.support (W₁:ℝ→ℂ)⊆Set.Icc lo hi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc lo hi →
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        W₁ W₂ X₁ X₂ Y₁ Y₂ T‖≤
      C*(sourceControl R W₁*sourceControl R W₂)*Z^ε*(1+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,R,hR,hJ⟩:=capped_slots_source_control lo hi ε B hlo hhi hε hB
  refine ⟨J,R,hR,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound W₁ W₂ hs₁ hs₂ (liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    h
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

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1753

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondMovingSupport
Source SHA256: 249e832bcbb14b298ef644fdbe3b412b704f3526ead201411da96e4476e9987e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1754


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondMovingSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem actual_unequal_min_six (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (P : CommonIndex C D) (hneq : leftExponent C D P≠rightExponent C D P) :
    6∣min (leftExponent C D P) (rightExponent C D P) := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hglobal : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      ((∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P))*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      commonFrequencyGenerator,idealCorrelation] using hne
  have hl := local_nonzero_of_global (commonPrime C D) (commonPrime_supported C D hC)
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D) w hglobal P
  exact nonzero_unequal_min_six (commonPrime C D P) (commonPrime_supported C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_good C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_odd C D hC P)
    _ _ (leftExponent_pos C D P) (rightExponent_pos C D P) hneq _ hl

def fixedExponent (C D : Ideal O) (U : Finset (CommonIndex C D)) (P : CommonIndex C D) : ℕ :=
  min (leftExponent C D P) (rightExponent C D P)+if P∈nonunitPartitionSet C D U then 1 else 0

def fixedActiveSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>¬6∣fixedExponent C D U P)

theorem fixedActiveSet_subset (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    fixedActiveSet C D U⊆U∪nonunitPartitionSet C D U := by
  intro P hP
  have ha := (Finset.mem_filter.mp hP).2
  by_contra hn
  have hU : P∉U := fun h=>hn (Finset.mem_union_left _ h)
  have hV : P∉nonunitPartitionSet C D U := fun h=>hn (Finset.mem_union_right _ h)
  have heq : ¬(leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P) := by
    intro he
    exact hV (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hU⟩)
  rw [fixedExponent,ite_eq_right hV,add_zero] at ha
  by_cases hc : leftExponent C D P=rightExponent C D P
  · rw [hc,min_self] at ha
    exact heq ⟨hc,by simpa only [hc] using ha⟩
  · exact ha (actual_unequal_min_six C D hC hD hCD w hne P hc)

theorem fixed_active_log_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (Ideal.absNorm (∏P∈fixedActiveSet C D U,P.val):ℝ)≤
      Real.logb Z (Ideal.absNorm (∏P∈U,P.val):ℝ)+
        Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ) := by
  have hn (P : CommonIndex C D) : 0≤Real.logb Z (Ideal.absNorm P.val:ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1)))
  have hlog (T : Finset (CommonIndex C D)) :
      Real.logb Z (Ideal.absNorm (∏P∈T,P.val):ℝ)=∑P∈T,Real.logb Z (Ideal.absNorm P.val:ℝ) := by
    simp only [map_prod,Nat.cast_prod]
    exact Real.logb_prod _ _ (fun P _=>Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1))
  rw [CenteredMomentSecondCanonicalLedger.nonunitFrequencyGenerator_span,unitIdeal]
  simp only [commonPrime_span C D hC]
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hU hV
    exact (Finset.mem_sdiff.mp hV).2 hU
  rw [hlog,hlog,hlog,←Finset.sum_union hdis]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fixedActiveSet_subset C D hC hD hCD U w hne)
    (fun P _ _=>hn P)

end SevenEighths.CenteredMomentSecondMovingSupport

end

end OAI
end OAIOriginalModule1754

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren
Source SHA256: bec2dbe8b6a9a3211d4cba081ae9fb70925f15e67d78416e5b1ef3b2c5e59ce0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1755



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily CenteredMomentSupport
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_correlation_children (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (A₀ : O) (rows : Finset O) (q : O → ℂ) (K : O → Ideal O → Ideal O → ℂ) :
    let a := sectorElement C hC.1 S
    let b := sectorElement D hD.1 S
    let c := fun I : sectorPool C hC.1 S => β (C*I)*heightCoeff η t I
    let d := fun J : sectorPool D hD.1 S => β (D*J)*heightCoeff η t J
    (∑ z∈rows,q z*∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A₀*z)
        else 0)*(c I*star (d J))*K z I J)=
      ∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J:Ideal O)),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
              ∑ z∈rows,(q z*idealCorrelation C D hC hD (A₀*z))*
                ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
                  ((divisorCoefficient L a (movingCoefficient A₀ a c) χ I*idealRowHom z I)*
                    star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) J*idealRowHom (-z) J))*K z I J := by
  dsimp only
  have hb (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := actual_scaled_row_children rows Finset.univ Finset.univ
    (primaryGenerator C) (primaryGenerator D) A₀
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hb q
    (fun I => β (C*I)*heightCoeff η t I) (fun J => β (D*J)*heightCoeff η t J)
    (fun z I J => K z I J)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔ IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondSectorChildren

end

end OAI
end OAIOriginalModule1755

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
Source SHA256: 6719453e147e0169819e2be3d90d843cb30583589d40fdce3ef071f56603e3d6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1756



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy
open CenteredMomentLiveDomain CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,hτ I (sectorPool_supported C hC.1 S I) t]
  dsimp only [sectorElement]
  split_ifs <;> ring

theorem sector_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C : Ideal O) (hC : Supported C) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem sector_child_row (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) =>
          (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) z := by
  have he := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L t)
  rw [he,sector_rowPolynomial S (fun I => (if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  congr 1
  funext I
  split_ifs <;> simp_all

theorem sector_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) W K=
      sourceRestrictedEnergy keep (residualPool C hC.1 S)
        (fun I => if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) W K := by
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_child_row η τ χ A hτ S β C hC L t z]

end SevenEighths.CenteredMomentSecondSectorEnergy

end

end OAI
end OAIOriginalModule1756

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSectorFrequency
Source SHA256: e455943132dcc48f3ee0993ab5611038d5754c6d3048a432f14e492197cf5920
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1757



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorFrequency
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

def sectorFrequency (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) : ℂ :=
  ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
    (if IsCoprime (I:Ideal O) (J:Ideal O) then
      idealCorrelation (C*I) (D*J)
        ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
        ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) j
      else 0)*((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F j I J

theorem sectorFrequency_zero_of_common (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) (hj : idealCorrelation C D hC hD j=0) :
    sectorFrequency η t S β C D hC hD F j=0 := by
  have he := sector_correlation_children η t S β C D hC hD hCD 1 {j} (fun _=>1) F
  simpa only [Finset.sum_singleton,one_mul,hj,zero_mul,mul_zero,Finset.sum_const_zero,
    sectorFrequency] using he

theorem sectorFrequency_common_support (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O)
    (hj : sectorFrequency η t S β C D hC hD F j≠0) : commonFrequencyGenerator C D∣j := by
  by_contra hn
  exact hj (sectorFrequency_zero_of_common η t S β C D hC hD hCD F j
    (idealCorrelation_zero_outside_common C D hC hD hCD j hn))

theorem sectorFrequency_tsum_common (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) :
    (∑' j : O,sectorFrequency η t S β C D hC hD F j)=
      ∑' w : O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq
    (f := sectorFrequency η t S β C D hC hD F) ?_
  intro j hj
  obtain ⟨w,hw⟩ := sectorFrequency_common_support η t S β C D hC hD hCD F j hj
  exact ⟨w,hw.symm⟩

theorem sectorFrequency_tsum_partition (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ)
    (hs : Summable (fun w : O=>sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))) :
    (∑' w : O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))=
      ∑ U : Finset (CommonIndex C D),∑' w : O,if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
  have he (w : O) : sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w)=
      ∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
    simp [canonicalPartition,eq_comm]
  calc
    _ = ∑' w : O,∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun U _=>hs.indicator {w | canonicalPartition C D U w})

theorem sectorFrequency_partition_nonunit (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : O→Ideal O→Ideal O→ℂ) :
    (∑' w : O,if canonicalPartition C D U w then
      sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0)=
      ∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD F
          ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  let f : O→ℂ := fun w=>if canonicalPartition C D U w then
    sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0
  have hs : Function.support f⊆Set.range (fun h=>nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by simp only [f,ite_eq_right hn])
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact ⟨h,hh.symm⟩
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm

end SevenEighths.CenteredMomentSecondSectorFrequency

end

end OAI
end OAIOriginalModule1757

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSixthReduction
Source SHA256: 537bfc71b25e2222924fac9bc770fd1da57d2fcf61c8912dfbc174606faa6254
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1758



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthReduction
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondMovingSupport CenteredMomentFixedRowMask
open CenteredExceptionalProfile CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def reducedNumerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P%6)

def sixthFactor (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P/6)

theorem fixed_numerator_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,commonPrime C D P^fixedExponent C D U P := by
  have hv : nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,if P∈nonunitPartitionSet C D U then commonPrime C D P else 1 := by
    simp only [nonunitFrequencyGenerator,Finset.prod_ite_mem,Finset.univ_inter]
  rw [commonFrequencyGenerator,hv,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [fixedExponent,pow_add]
  split_ifs <;> simp

theorem fixed_sixth_factorization (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      reducedNumerator C D U*(sixthFactor C D U)^6 := by
  rw [fixed_numerator_product,reducedNumerator,sixthFactor,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [←pow_mul,←pow_add]
  congr 1
  omega

theorem reducedNumerator_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))

theorem sixthFactor_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    sixthFactor C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))

theorem fixed_sixth_row (η : Character) (m h n : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    rowTwist (elementHom η) m 1
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) n=
    rowTwist (elementHom η) (m*sixthFactor C D U) 1 (reducedNumerator C D U*h) n := by
  rw [fixed_sixth_factorization]
  have he : m ^ 6 * 1 ^ 4 * ((reducedNumerator C D U * sixthFactor C D U ^ 6) * h) =
      (m * sixthFactor C D U) ^ 6 * 1 ^ 4 * (reducedNumerator C D U * h) := by ring
  exact congrArg
    (fun x => elementHom η n * idealRowHom x (Ideal.span {n})) he

theorem fixed_sixth_inducing_iff (η : Character) (Q : Ideal O) (m h : O)
    (hm : m≠0) (hh : h≠0) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q m (reducedNumerator C D U) h := by
  have he : FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q (m*sixthFactor C D U) (reducedNumerator C D U) h := by
    unfold FixedInducingRow
    simp only [fixed_sixth_row]
  exact he.trans (fixedInducingRow_mul_mask_iff η Q m (sixthFactor C D U)
    (reducedNumerator C D U) h hm (sixthFactor_ne_zero C D hC U)
    (reducedNumerator_ne_zero C D hC U) hh hmLam hm2)

end SevenEighths.CenteredMomentSecondSixthReduction

end

end OAI
end OAIOriginalModule1758

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSixthSource
Source SHA256: a7d4be0ef4a6a5f38b7e6b821501c373910a301ae057e77148e91b081aed4bf1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1759


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hc := leftExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤leftExponent C D P := min_le_left _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem fixed_sixth_coefficient (C D : Ideal O) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I*
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I hI]

theorem residual_sixth_coefficient (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]

abbrev ActiveIndex (C D : Ideal O) (U : Finset (CommonIndex C D)) := ↥(fixedActiveSet C D U)

def activePrime (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : O := commonPrime C D P.val

def activeExponent (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : ℕ := fixedExponent C D U P.val%6

theorem activeExponent_pos (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : 0<activeExponent C D U P := by
  have hp : ¬6∣fixedExponent C D U P.val := (Finset.mem_filter.mp P.property).2
  exact Nat.pos_of_ne_zero (fun h=>hp (Nat.dvd_of_mod_eq_zero h))

theorem activeExponent_lt (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : activeExponent C D U P<6 := Nat.mod_lt _ (by norm_num)

theorem reducedNumerator_active_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D=>commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    simpa only [fixedActiveSet,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]

end SevenEighths.CenteredMomentSecondSixthSource

end

end OAI
end OAIOriginalModule1759

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondRadicalFamily
Source SHA256: 47ffceab874ea2b5dd09ac209cd11b5d749ea930cc0282e035b7ef8292dfee20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1760




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst (CommonIndex)
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentRadicalFamily CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem active_radical_product (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    (∏ P : ActiveIndex C D U,Ideal.span {activePrime C D U P})=
      ∏ P∈fixedActiveSet C D U,P.val := by
  simp only [activePrime,commonPrime_span C D hC]
  exact Finset.prod_coe_sort _ (fun P : CommonIndex C D=>P.val)

theorem exists_second_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      (∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
        fixedBadMask 1 (reducedNumerator C D U) n) ∧
      ∀I:Ideal O,Supported I → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hM,hN,hτ⟩ := exists_radical_row_presentation (childCharacter η χ) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (activePrime C D U) (fun P=>commonPrime_supported C D hC P.val)
    (activeExponent C D U) (activeExponent_pos C D U)
  have he (n:O) : elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n := by
    rw [reducedNumerator_active_product]
    exact hτ n
  refine ⟨τ,?_,he,?_⟩
  · rw [←map_prod,active_radical_product C D hC U] at hN
    exact hN
  · intro I hI t
    have ht := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1
      (reducedNumerator C D U) he I
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [ht,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
    simp only [one_pow,mul_one]
    rw [heightCoeff_eq_fixed_rowWeight η t I hI]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
    ring_nf

end SevenEighths.CenteredMomentSecondRadicalFamily

end

end OAI
end OAIOriginalModule1760

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
Source SHA256: 94dd796ed54ab752af4934ebeb61f4b3f5ac9d96bc8ecf63f4b3b7cadc6193f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1761


namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
namespace SevenEighths.CenteredMomentSecondRadicalBudget
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalFamily CenteredMomentSecondMovingSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentPartitionNorm
open CenteredMomentHeckeColumnWindow RayFourExpansion CenteredMomentCommonSupport CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def fixedFactor : ℕ := (Ideal.span {(12:O)}).absNorm*
  (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedFactor_pos : 0<fixedFactor := by
  unfold fixedFactor
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))

theorem child_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm≤η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  have hn : η.modulus*Ideal.span {(12:O)}≠0 := mul_ne_zero η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  have hd : (childCharacter η χ).modulus∣η.modulus*Ideal.span {(12:O)} := by
    apply Ideal.dvd_iff_le.mpr
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) (map_dvd Ideal.absNorm hd)

theorem active_radical_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val)∣
      (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U} := by
  have hd := Finset.prod_dvd_prod_of_subset (fixedActiveSet C D U)
    (U∪nonunitPartitionSet C D U) (fun P:CommonIndex C D=>P.val)
    (fixedActiveSet_subset C D hC hD hCD U w hne)
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hdis] at hd
  rw [nonunitFrequencyGenerator_span]
  simpa only [unitIdeal,commonPrime_span C D hC] using hd

theorem active_radical_norm_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val).absNorm≤
      (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero (hp U) hv)))
    (map_dvd Ideal.absNorm (active_radical_dvd C D hC hD hCD U w hne))

theorem exists_second_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*
        (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  obtain ⟨τ,hN,he,ht⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne
  have h1 := child_modulus_bound η χ
  have h2 := active_radical_norm_bound C D hC hD hCD U w hne
  apply hN.trans
  calc
    _≤(η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)) h2
    _=_ := by unfold fixedFactor;ring

theorem conductor_log_bound (η τ : Character) (A B : Ideal O) (hA : A≠0) (hB : B≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*A.absNorm*B.absNorm)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z (A.absNorm:ℝ)+Real.logb Z (B.absNorm:ℝ) := by
  have hτ : (0:ℝ)<τ.modulus.absNorm := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  have hη : (η.modulus.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hK : (fixedFactor:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt fixedFactor_pos)
  have ha : (A.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  have hb : (B.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hh := Real.logb_le_logb_of_le hZ hτ (show (τ.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*fixedFactor*A.absNorm*B.absNorm by exact_mod_cast hN)
  rwa [Real.logb_mul (mul_ne_zero (mul_ne_zero hη hK) ha) hb,
    Real.logb_mul (mul_ne_zero hη hK) ha,Real.logb_mul hη hK] at hh

theorem exists_second_log_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z:ℝ,1<Z → Real.logb Z (τ.modulus.absNorm:ℝ)≤
        Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ) := by
  obtain ⟨τ,he,ht,hN⟩ := exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne Z hZ
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  exact conductor_log_bound η τ _ _ (hp U) hv (hN hD hCD w hne) Z hZ

theorem fixed_log_cost_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in Filter.atTop,1<Z ∧ Real.logb Z (fixedFactor:ℝ)≤ε := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (fixedFactor:ℝ)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with Z hK hZ
  refine ⟨hZ,?_⟩
  have hp : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  have hh := Real.logb_le_logb_of_le hZ hp hK
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

end SevenEighths.CenteredMomentSecondRadicalBudget

end

end OAI
end OAIOriginalModule1761

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondActualWidth
Source SHA256: 464991e23f1358e0857966baf9e0af3268c0b03134cf65a7ccd15f565d53f2ec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1762



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentSupport CenteredMomentDescentLedger
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_common_log_ge_unit (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

theorem actual_width_bound (η τ : Character) (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z Tsec Csec L ξ : ℝ)
    (hZ : 1<Z) (hCsec : 0<Csec) (hT : Tsec≤Csec*Z^L)
    (hτ : Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ))
    (h : O) (hne : retainedWeight (frequencyRadius Tsec Z ξ)
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0) :
    max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
      frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      L+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ-
        (Real.logb Z (normValue (commonFrequencyGenerator C D))-
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  have hn:=actual_nonempty_width_of_weight Tsec Z Csec L ξ hZ hCsec hT _ h hne
  rw [max_eq_right hn]
  have hg := normValue_pos (commonFrequencyGenerator C D)
    (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C D hC)
  have hv := normValue_pos (nonunitFrequencyGenerator C D U)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  rw [normValue_mul,Real.logb_mul hg.ne' hv.ne']
  change _≤_
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z (normValue (nonunitFrequencyGenerator C D U)) at hτ
  linarith

theorem exists_actual_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),primeSupport C=primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z Tsec Csec L ξ M σ:ℝ,1<Z → 0<Csec → Tsec≤Csec*Z^L →
      L+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_log_budgeted_family η χ C D hC U
  refine ⟨τ,ht,?_⟩
  intro hD hCD w hw Z Tsec Csec L ξ M σ hZ hCs hT hnom h hh
  have hb:=actual_width_bound η τ C D hC U Z Tsec Csec L ξ hZ hCs hT
    (hN hD hCD w hw Z hZ) h hh
  have hg:=actual_common_log_ge_unit C D hC U Z hZ
  linarith

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI
end OAIOriginalModule1762

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
Source SHA256: db6a7682289f2f19215e9dbd0806c1db79d7fb51ae223defae129eaa695c37a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1763


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]

theorem exists_actual_masked_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      ∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,he,hτ⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,hN,?_⟩
  intro I hI hi t
  rw [hτ I hI t]
  rcases hi with hi|hi
  · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
  · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]

end SevenEighths.CenteredMomentSecondRadicalColumns

end

end OAI
end OAIOriginalModule1763

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate
Source SHA256: d18d0f084f723a34d24de0a39db7ffe667397f48653732581643f6d524c1a360
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1764




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondReducedPredicate
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem fixed_mask_change (η : Character) (Q : Ideal O) (m n A z : O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hnLam:ConcretePrimeRowBridge.goodLambda∣n) (hn2:(2:O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2

theorem actual_reduced_inducing_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm

theorem actual_nonexceptional_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp only [hz,ne_eq,not_true_eq_false,false_and]
  · rw [actual_reduced_inducing_iff η τ χ C D hC U hτ Q m z hm hz hmLam hm2]

end SevenEighths.CenteredMomentSecondReducedPredicate

end

end OAI
end OAIOriginalModule1764

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NonprincipalGate
Source SHA256: 3db2ba9b4a71294d9c0d61ec5241ff0c7c1c19d1ce892761bd27061b816f4c04
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1765


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNonprincipalGate
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentRestrictedEnergy CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O

def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))

theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue := by
  change FiniteFourier.IsPrimitiveOnIdeals (1:MulChar (O⧸(⊤:Ideal O)) ℂ)
  intro I hI
  exact (hI (Subsingleton.elim _ _)).elim

theorem unitCharacter_ideal (I:Ideal O) (hI:I≠0) : idealCoeff unitCharacter I=1 := by
  rw [←span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI)]
  change (1:MulChar (O⧸(⊤:Ideal O)) ℂ) (Ideal.Quotient.mk _ (idealGenerator I))=1
  rw [show Ideal.Quotient.mk (⊤:Ideal O) (idealGenerator I)=1 from Subsingleton.elim _ _]
  exact map_one _

theorem principal_inducedBy_unit (χ:Character) (hχ:χ.residue=1) : InducedBy χ unitCharacter := by
  intro I
  by_cases hI:I=0
  · subst I
    simp only [map_zero,ite_self]
  · have hn:=idealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_idealGenerator I,idealCoeff_span χ hn]
    change χ.residue (Ideal.Quotient.mk χ.modulus (idealGenerator I))=_
    rw [hχ]
    by_cases hc:IsCoprime (Ideal.span {idealGenerator I}) χ.modulus
    · rw [ite_eq_left hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [ite_eq_right hc]
      exact MulChar.map_nonunit _ (fun h=>hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))

theorem principal_row_fixed (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hχ:χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,unitCharacter_primitive,principal_inducedBy_unit χ hχ,le_top,hrow⟩

theorem actual_row_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hex:¬FixedInducingRow η Q m A z) : χ.residue≠1 :=
  fun h=>hex (principal_row_fixed η χ Q m A z hrow h)

theorem nonexceptional_row_nonprincipal (η χ:Character) (ξ:RayCharacter)
    (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom (childCharacter η ξ)) m 1 (A*z) n)
    (hex:nonexceptional η ξ Q m A z) : χ.residue≠1 :=
  actual_row_nonprincipal (childCharacter η ξ) χ Q m A z hrow hex.2

end SevenEighths.CenteredMomentNonprincipalGate

end

end OAI
end OAIOriginalModule1765

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
Source SHA256: 2820c4ff2b35a7765ed9797a582217401a71bb7e800443e6978b31f955cb58c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1766



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

structure NaturalRow (η : Character) (z : O) where
  character : Character
  modulus_bound : character.modulus.absNorm≤rowConductorBound η fixedBadMask 1 z
  element : ∀n,elementCoeff character n=rowTwist (elementHom η) fixedBadMask 1 z n

def naturalRow (η : Character) (z : O) (hz : z≠0) : NaturalRow η z := by
  let e:=exists_row_character_with_conductor η fixedBadMask 1 z
    fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨Classical.choose e,(Classical.choose_spec e).1,(Classical.choose_spec e).2⟩

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : Character} {z : O} (F : NaturalRow η z) :
    elementCoeff F.character 0=0 := by
  rw [F.element]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded F.character R) n=
      rowTwist (elementHom η) (fixedBadMask*idealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character F.element_zero R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (idealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded F.character R) I=
      idealCoeff η I*idealRowHom ((fixedBadMask*idealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*idealGenerator R) 1 z (F.masked_element R hR) I

lemma NaturalRow.masked_element_span {η : Character} {z : O} (F : NaturalRow η z)
    (r : O) (hr : r≠0) (n : O) :
    elementCoeff (excluded F.character (Ideal.span {r})) n=
      rowTwist (elementHom η) (fixedBadMask*r) 1 z n := by
  rw [excluded_element F.character F.element_zero (Ideal.span {r})
    (Ideal.span_singleton_eq_bot.not.mpr hr),Ideal.isCoprime_span_singleton_iff,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask r 1 z n (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

theorem NaturalRow.nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (hz : z≠0) (Q R : Ideal O) (hR : R≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    F.character.residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η F.character Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) hbase

def fixedConductorFactor : ℕ := (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

lemma NaturalRow.natural_modulus_bound {η : Character} {z : O} (F : NaturalRow η z) :
    F.character.modulus.absNorm≤η.modulus.absNorm*fixedConductorFactor*(Ideal.span {z}).absNorm := by
  have hh:=F.modulus_bound
  simpa [rowConductorBound,fixedConductorFactor,Ideal.span_singleton_one,mul_assoc] using hh

theorem NaturalRow.modulus_power_bound {η : Character} {z : O} (F : NaturalRow η z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (_hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m)
    (hz : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (F.character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by
  have hb : (F.character.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(fixedConductorFactor:ℝ)*((Ideal.span {z}).absNorm:ℝ) :=
    by exact_mod_cast F.natural_modulus_bound
  apply hb.trans
  calc
    _≤(Z^m*(fixedConductorFactor:ℝ))*(Cz*Z^q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)) hz
        (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _))
    _=(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by rw [Real.rpow_add hZ]; ring

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end OAIOriginalModule1766

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary
Source SHA256: fb915e959dd7d2659b800fa5ad8688015dd73a15aab105b0d9c7fcda28be5251
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1767



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.masked_plain {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := by
  exact rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η (fixedBadMask*idealGenerator R) 1 z S β t=
      ∑I∈S,β I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

theorem NaturalRow.masked_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

theorem NaturalRow.masked_retained {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    retainedPositiveRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) (dilated W₁ (clipDilation X₁)) t (clippedScale X₁)*
          twistedIdealSum (excluded F.character R) (dilated W₂ (clipDilation X₂)) t (clippedScale X₂))*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  exact F.masked_positive R hR _ _ S β P t _ _

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end OAIOriginalModule1767

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
Source SHA256: 57e91a58c3473cf5d6ddd93b39318d03c25cd3694ec76d615313ede86a765f42
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1768



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology

namespace SevenEighths.CenteredMomentSecondRetainedWidth
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalBudget CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentCanonicalFirst
open CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem retained_geometry (R : ℝ) (G V z : O)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    0<R ∧ G≠0 ∧ V≠0 ∧ z≠0 ∧ 1≤normValue z ∧
      normValue z≤4*R/(normValue G*normValue V) ∧
      1≤4*R/(normValue G*normValue V) := by
  obtain ⟨hGV,hz⟩:=retained_product_ne_zero R (G*V) z hne
  have hg:=left_ne_zero_of_mul hGV
  have hv:=right_ne_zero_of_mul hGV
  have hrow:=retained_norm_enclosure R (G*V) z hGV hne
  rw [normValue_mul] at hrow
  have hn:=normValue_ge_one z hz
  have hr:=retainedWeight_enclosure R _ hne
  refine ⟨by linarith,hg,hv,hz,hn,hrow,hn.trans hrow⟩

theorem retained_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (max 1 (4*R/(normValue G*normValue V)))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨hR,hG,hV,_,_,_,hmax⟩:=retained_geometry R G V z hne
  have hg:=normValue_pos G hG
  have hv:=normValue_pos V hV
  have hF : (fixedFactor:ℝ)≠0:=by exact_mod_cast fixedFactor_pos.ne'
  have hc:=conductor_log_bound η τ U (Ideal.span {V}) hU
    (Ideal.span_singleton_eq_bot.not.mpr hV) hN Z hZ
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z (U.absNorm:ℝ)+Real.logb Z (normValue V) at hc
  rw [max_eq_right hmax,Real.logb_div (mul_ne_zero (by norm_num) hR.ne')
    (mul_ne_zero hg.ne' hv.ne'),Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne',
    Real.logb_mul hg.ne' hv.ne',Real.logb_mul (by norm_num : (4:ℝ)≠0) hF]
  linarith

theorem retained_row_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨_,_,_,hz,_,hn,_⟩:=retained_geometry R G V z hne
  have hh:=Real.logb_le_logb_of_le hZ (normValue_pos z hz) (hn.trans (le_max_right 1 _))
  have hb:=retained_log_budget η τ G V z U hU hN R Z hZ hne
  linarith

theorem exists_retained_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,1<Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  have hb:=hN hD hCD w hw
  refine ⟨hb,?_⟩
  intro Z R hZ z hz
  have hU : (∏P∈U,P.val)≠0:=Finset.prod_ne_zero_iff.mpr
    (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  obtain ⟨hR,_,_,hne,h1,hrow,_⟩:=retained_geometry R _ _ z hz
  exact ⟨hR,hne,h1,hrow,retained_log_budget η τ _ _ z _ hU hb R Z hZ hz,
    retained_row_log_budget η τ _ _ z _ hU hb R Z hZ hz⟩

theorem fixed_width_cost_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in Filter.atTop,1<Z ∧ Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*(fixedFactor:ℝ))
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with Z hF hZ
  refine ⟨hZ,?_⟩
  have hp : (0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hh:=Real.logb_le_logb_of_le hZ (by positivity : 0<4*(fixedFactor:ℝ)) hF
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

theorem exists_uniform_retained_width_family (ε : ℝ) (hε : 0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(χ:RayCharacter)(C D:Ideal O)
      (hC:Supported C)(U:Finset (CommonIndex C D)),
    ∃τ:Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,Z₀≤Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε := by
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp (fixed_width_cost_eventually ε hε)
  refine ⟨Z₀,(hZ₀ Z₀ le_rfl).1,?_⟩
  intro η χ C D hC U
  obtain ⟨τ,he,ht,hb⟩:=exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  obtain ⟨hN,hrow⟩:=hb hD hCD w hw
  refine ⟨hN,?_⟩
  intro Z R hZ z hz
  obtain ⟨hZ1,hcost⟩:=hZ₀ Z hZ
  obtain ⟨hR,hn,h1,hup,hmax,hlog⟩:=hrow Z R hZ1 z hz
  exact ⟨hR,hn,h1,hup,by linarith,by linarith⟩

end SevenEighths.CenteredMomentSecondRetainedWidth

end

end OAI
end OAIOriginalModule1768

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourceMask
Source SHA256: 43bb4c2c8310dab139b58754cfe6796173e6f6639b8a857de9ba2673e7a4997c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1769



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSourceMask
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem divisor_dvd_common (C D a b s : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hsI : s∣C*a) (hsJ : s∣D*b) : s∣C ∧ s∣D := by
  have hDa := (coprime_of_same_support C D a hC hD ha hCD).mp hCa
  have hDb := (coprime_of_same_support C D b hC hD hb hCD).mp hCb
  have hsa : IsCoprime s a := ((hDa.symm.mul_right hab).of_isCoprime_of_dvd_right hsJ).symm
  have hsb : IsCoprime s b := ((hCb.symm.mul_right hab.symm).of_isCoprime_of_dvd_right hsI).symm
  exact ⟨hsa.dvd_mul_right_iff.mp hsI,hsb.dvd_mul_right_iff.mp hsJ⟩

variable {ι : Type*} [Fintype ι]

theorem column_nonzero_divisor (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (h : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) : s∣I := by
  rw [column_mask] at h
  by_contra hn
  exact h (by rw [ite_eq_right hn,mul_zero])

theorem source_pair_divisor_common (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hleft : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)≠0)
    (hright : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (D*b)≠0) : s∣C ∧ s∣D :=
  divisor_dvd_common C D a b s hC hD ha hb hCD hCa hCb hab
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hleft)
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hright)

end SevenEighths.CenteredMomentSecondSourceMask

end

end OAI
end OAIOriginalModule1769

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondLiveEnergy
Source SHA256: e2544280b28d244034cb79abf39e7dccadcccc1c8c5f7a654f9ef25b0ea7512a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1770



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R L : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I => (if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem actual_second_child_live_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*CanonicalRowCompletion.idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 Q)
      (divisorCoefficient L (sectorElement C hC.1 Q)
        (movingCoefficient A (sectorElement C hC.1 Q)
          (fun J : sectorPool C hC.1 Q => β (C*J)*heightCoeff η t J)) χ) W K≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K := by
  dsimp only
  rw [sector_child_energy η τ χ A hτ (finiteColumns (Fintype.piFinset S))
    (finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) C hC L t keep W K]
  have he := original_restricted_child_energy S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentSecondLiveEnergy

end

end OAI
end OAIOriginalModule1770

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourceCost
Source SHA256: 7180ffb8a5817dfdf16cecbbaec29e087b75a6c78f99b40a985ad5e7ed6f9d9c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1771



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceCost
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentSecondLiveEnergy CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem source_divisor_common_saving (τ : Character)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    sourceRestrictedEnergy keep (residualPool C hC.1 Q)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ t) W K/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K)/CenteredMomentCommonRawScale.remainingRaw B Traw P := by
  dsimp only
  have he := restricted_child_common_saving S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP M hν hWnorm hM a b ha hslot
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  congr 1
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentSecondSourceCost

end

end OAI
end OAIOriginalModule1771

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
Source SHA256: 4f02ffa976c52267036272a35acecdb9f00c0cec676291821dee741a5815d3a2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1772




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentScale CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def secondEffectiveScale (C D : Ideal O) (A : O) (K : ℝ) : ℝ :=
  K*‖eisEmbedding A‖^2/((Ideal.absNorm C:ℝ)*(Ideal.absNorm D:ℝ))

theorem secondEffectiveScale_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : 0<secondEffectiveScale C D A K := by
  apply div_pos (mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hA))))
  exact mul_pos (CenteredMomentFirstScale.norm_pos C hC) (CenteredMomentFirstScale.norm_pos D hD)

theorem primary_norm_sq (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (primaryGenerator I)‖^2=(Ideal.absNorm I:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,primary_span_supported I hI]

theorem second_kernel_argument (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (K : ℝ) :
    K*‖eisEmbedding (A*h)‖^2/
      ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2=
      secondEffectiveScale C D A K*‖eisEmbedding h‖^2/((Ideal.absNorm a:ℝ)*(Ideal.absNorm b:ℝ)) := by
  simp only [map_mul,norm_mul,mul_pow,primary_norm_sq (C*a) ((supported_mul_iff _ _).mpr ⟨hC,ha⟩),
    primary_norm_sq (D*b) ((supported_mul_iff _ _).mpr ⟨hD,hb⟩),map_mul,Nat.cast_mul,secondEffectiveScale]
  ring

theorem common_normalized_kernel (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (k H a b C D K K₀ H₀ A₀ B₀ : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b)
    (hC : 0<C) (hD : 0<D) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    (K:ℂ)/((Real.sqrt (C*a):ℂ)*(Real.sqrt (D*b):ℂ))*
      windows V k H a b K₀ H₀ A₀ B₀*paperRadialFourier W (k*H/(a*b))=
      (K:ℂ)/((Real.sqrt C:ℂ)*(Real.sqrt D:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (H/H₀)) (Real.log (a/A₀)) (Real.log (b/B₀)) := by
  rw [wholeKernel_actual W V k H a b K₀ H₀ A₀ B₀ hk hH ha hb hK₀ hH₀ hA₀ hB₀]
  rw [Real.sqrt_mul hC.le a,Real.sqrt_mul hD.le b]
  simp only [Complex.ofReal_mul,windows]
  have hc : (Real.sqrt C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
  have hd : (Real.sqrt D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  have haa : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hbb : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

theorem second_frequency_whole_kernel (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (hA : A≠0) (hh : h≠0) (K : ℝ) (hK : 0<K)
    (F : ℂ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let k := secondEffectiveScale C D A K
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*a):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*b):ℝ):ℂ)))*F*
      windows V k (‖eisEmbedding h‖^2) (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) K₀ H₀ A₀ B₀*
      paperRadialFourier W (K*‖eisEmbedding (A*h)‖^2/
        ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*F*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log ((Ideal.absNorm a:ℝ)/A₀)) (Real.log ((Ideal.absNorm b:ℝ)/B₀)) := by
  dsimp only
  rw [second_kernel_argument C D a b hC hD ha hb]
  simp only [map_mul,Nat.cast_mul]
  have he := common_normalized_kernel W V (secondEffectiveScale C D A K) (‖eisEmbedding h‖^2)
    (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) (Ideal.absNorm C:ℝ) (Ideal.absNorm D:ℝ)
    K K₀ H₀ A₀ B₀ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))
    (CenteredMomentFirstScale.norm_pos a ha.1) (CenteredMomentFirstScale.norm_pos b hb.1)
    (CenteredMomentFirstScale.norm_pos C hC.1) (CenteredMomentFirstScale.norm_pos D hD.1)
    hK₀ hH₀ hA₀ hB₀
  convert congrArg (fun z : ℂ => F*z) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI
end OAIOriginalModule1772

/-! Original module: OAI.NumberTheory.DirichletL.Moments.LogDyadic
Source SHA256: cd86b40a23c7f4a556bd0cf5d9741434b2e029cc509478ffe6ed15821e075bba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1773



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simpa only [Function.mem_support,logAnnulus,ne_eq,Complex.ofReal_eq_zero] using hx
  have hlo : 1/4<Real.exp x := lt_of_not_ge (fun h=>hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=>hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro (isCompact_Icc) (fun x hx=>by
    by_contra hn
    exact hx (logAnnulus_support hn))

theorem logAnnulus_norm (x : ℝ) : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
end OAIOriginalModule1773

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondTail
Source SHA256: d29a4f81e9fddb368d90dcd2a9eaa114165c68d2365dfb6b60b2993dbf79a3b6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1774



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

theorem actual_second_kernel_reference (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (K X H Tsec : ℝ) (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp H*X) (hj : (Ideal.absNorm J:ℝ)≤Real.exp H*X)
    (hsec : X^2/K≤Tsec) :
    kernelReference Tsec H≤K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hNi := CenteredMomentFirstScale.norm_pos I hI
  have hNj := CenteredMomentFirstScale.norm_pos J hJ
  have hprod : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*H)*X^2 := by
    apply (mul_le_mul hi hj hNj.le (by positivity)).trans_eq
    rw [show 2*H=H+H by ring,Real.exp_add]
    ring
  unfold kernelReference
  apply (le_div_iff₀ (mul_pos hNi hNj)).mpr
  calc
    _ ≤ (Real.exp (-2*H)/Tsec)*(Real.exp (2*H)*X^2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = X^2/Tsec := by
      rw [show -2*H=-(2*H) by ring,Real.exp_neg]
      field_simp
    _ ≤ K := (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hsec)

def secondDiscardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem second_discarded_pair_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
        (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp H*X → (Ideal.absNorm J:ℝ)≤Real.exp H*X →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedPair I J hI hJ W K Tsec Z ξ‖≤
        K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_second_tail Adec
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ K X H Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hb := ht W Tsec Z Csec H ξ (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))
    hT hZ hCs hthreshold (actual_second_kernel_reference I J hI.1 hJ.1 K X H Tsec hK hX hi hj hsec)
    (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  have hu : normValue (primaryGenerator I)=(Ideal.absNorm I:ℝ) := by rw [normValue,primary_span_supported I hI]
  have hv : normValue (primaryGenerator J)=(Ideal.absNorm J:ℝ) := by rw [normValue,primary_span_supported J hJ]
  rw [hu,hv] at hb
  have hNi : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hNj : (1:ℝ)≤Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hroot : 1≤Real.sqrt (Ideal.absNorm I:ℝ)*Real.sqrt (Ideal.absNorm J:ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hNi) (Real.one_le_sqrt.mpr hNj)
  have hnorm : ‖(K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))‖≤K := by
    rw [norm_div,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hK.le hroot
  unfold secondDiscardedPair
  simp_rw [he]
  rw [norm_mul]
  apply (mul_le_mul hnorm hb (norm_nonneg _) hK.le).trans
  have hprod := mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity : 0≤Real.exp H*X)
  have hfac : 0≤(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hfac) hK.le
  convert hb' using 1 <;> ring

end SevenEighths.CenteredMomentSecondTail

end

end OAI
end OAIOriginalModule1774

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondWidthDrop
Source SHA256: c54ec925d4b034f80203e0eb3a763177578d59d0fbb8f33cf107e9b44260d455
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1775


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondWidthDrop
open HeckeFamily CenteredMomentSecondActualWidth CenteredMomentSecondRadicalBudget
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => HeckeFamily.O

def amplificationIncrement (η:Character) (Z H K M σ:ℝ) : ℝ :=
  max (2*Real.logb Z H-Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-M) 0+σ

def nominalLength (Z H K g:ℝ) : ℝ := 2*Real.logb Z H-Real.logb Z K-g

lemma physical_frequency_scale (Z H K g:ℝ) (hZ:1<Z) (hH:0<H) (hK:0<K) :
    H^2/(K*Z^g)=Z^(nominalLength Z H K g) := by
  have hzg:0<Z^g:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hp:0<H^2/(K*Z^g):=div_pos (sq_pos_of_pos hH) (mul_pos hK hzg)
  have he:Real.logb Z (H^2/(K*Z^g))=nominalLength Z H K g := by
    rw [Real.logb_div (sq_pos_of_pos hH).ne' (mul_pos hK hzg).ne',Real.logb_pow,
      Real.logb_mul hK.ne' hzg.ne',Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]
    unfold nominalLength
    norm_num
    ring
  rw [←he,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hp]

lemma actual_nominal_drop (η:Character) (Z H K M σ:ℝ) :
    nominalLength Z H K (amplificationIncrement η Z H K M σ)+
      Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
  have hh:=le_max_left (2*Real.logb Z H-Real.logb Z K+
    Real.logb Z (η.modulus.absNorm:ℝ)-M) 0
  unfold nominalLength amplificationIncrement
  linarith

theorem exists_physical_width_family (η:Character) (χ:RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z H K Tsec Csec ξ M σ g:ℝ,1<Z → 0<H → 0<K → 0<Csec →
      amplificationIncrement η Z H K M σ≤g →
      Tsec≤Csec*(H^2/(K*Z^g)) →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (nominalLength Z H K g-
        Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,hτ,hw⟩:=exists_actual_width_family η χ C D hC U
  refine ⟨τ,hτ,?_⟩
  intro hD hCD w hn Z H K Tsec Csec ξ M σ g hZ hH hK hCs hg hscale h hret
  apply hw hD hCD w hn Z Tsec Csec (nominalLength Z H K g) ξ M σ hZ hCs
  · rwa [←physical_frequency_scale Z H K g hZ hH hK]
  · have hh:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hh ⊢
    linarith
  · exact hret

end SevenEighths.CenteredMomentSecondWidthDrop

end

end OAI
end OAIOriginalModule1775

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondWindowSource
Source SHA256: 1649b0b03fbb84531456d08abfa0baf3cc9213a48bf4771f9705e92bc3d01e94
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1776






namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O

theorem sector_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  have he (v : ℝ) := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L v)
  simp_rw [sector_divisor_coefficient η τ χ A hτ S β C hC L t]
  have hh := restricted_window_energy_from_height keep V hVc hVs J Finset.univ
    (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I : sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←sector_child_energy η τ χ A hτ S β C hC L v keep Φ H,he v] at hs
  simpa only [sectorElement_span] using hs

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

theorem sector_conjugate_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) Φ H≤
      (E*heightCost t (-θ)^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  simp only [star_logAnnulus_column]
  exact sector_window_from_source η τ χ A hτ S β C hC L keep t (-θ) X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE hsource

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI
end OAIOriginalModule1776

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondReducedEnergy
Source SHA256: a0f34dc0352edc3ac97dc6ae00c5308675a8af32a7900f5209d8daaa156c2ad8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1777



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondReducedEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentChildAssembly
open CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion CenteredMomentLogDyadic
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondWindowSource
local notation "O" => ActualEisensteinCubic.O

theorem masked_source_energy (η τ τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O)
    (keep : O→Prop) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τr t) Φ H := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs with hi
  · have hI : Supported (I:Ideal O) := (Finset.mem_filter.mp I.property).2
    rw [hτ I hI t,hτr I hI t,residual_sixth_coefficient C D hC hCD U I hI hi.1]
  · simp only [zero_mul]

theorem original_window_from_reduced_source (η τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (_hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τr v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
          (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 := by
    rw [fixed_sixth_factorization]
    exact mul_ne_zero (reducedNumerator_ne_zero C D hC U) (pow_ne_zero _ (sixthFactor_ne_zero C D hC U))
  obtain ⟨τ,hN,hτ⟩ := exists_second_family η χ _ hA
  apply sector_window_from_source η τ χ _ hτ S β C hC L keep t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE
  intro v
  rw [masked_source_energy η τ τr χ C D hC hCD U hτ hτr S β L keep v Φ H]
  exact hsource v

end SevenEighths.CenteredMomentSecondReducedEnergy

end

end OAI
end OAIOriginalModule1777

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow
Source SHA256: abe3cab8f5e28e8f3da9fea1258a0098f0186a783d6e9c1ecceaadd6be5c23fd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1778


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondMaskedWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
