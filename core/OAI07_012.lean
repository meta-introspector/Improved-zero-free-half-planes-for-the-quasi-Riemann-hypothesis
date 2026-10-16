


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0<rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2346

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQDyadic
Source SHA256: 434093965df52f69e4a60198f5495018c79b2bd087e592b3476693eeb1b9fd0f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2347






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=>dyadicRows_nonzero rows n z hz)
    (fun χ z hz=>hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hη m hm hml hm2 (fun z hz=>hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2347

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
Source SHA256: 063fa5df481282bcadd20ac10a7efc0c0e474e8be8b1293a8cae4ed82ba46c92
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2348



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondPhysicalLedger
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ):
    profileMass Sprofile s.toData s.toData p p J=
      p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold CenteredMomentFiniteProfileExceptionalCommon.profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor Sprofile s p J Q K:=by
  unfold profileFactor
  have hp:=Profiles.control_nonneg p Sprofile
  positivity

lemma sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

theorem central_sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact Sprofile s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2348

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalRows
Source SHA256: 43a8c87cf8276f01fa7a306679da08e09f22b6f23d39753bc824976ee9ea7971
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2349





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0<rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2349

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalDyadic
Source SHA256: efa2da05f1888c5c59c398dd771fcea1711350db598638b870be23ac7999bd21
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2350






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=>dyadicRows_nonzero rows n z hz)
    (fun χ z hz=>hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hcop hη m hm hml hm2 (fun z hz=>hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2350

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
Source SHA256: e9043102cb911a11838130508bd82adaee2b4b0f852217aa7003854aa868bcba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2351




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (s : Input ι) : ℝ := ∏ i,s.M i

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤mass s :=
  Finset.one_le_prod₀ (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤mass s := zero_le_one.trans (mass_one s)

omit [DecidableEq ι] in
lemma child_mass (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : mass (child s C R B τ t)≤mass s := by
  change (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma child_card (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (liveIndices B))

omit [DecidableEq ι] in
lemma slot_control_bound (s : Input ι) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) :
    slotControl s.toData≤(128*b)^Fintype.card ι*mass s^2 := by
  have hpoint (i : ι) : max 1 (128*max 0 (s.hi i)*s.M i)≤(128*b)*s.M i := by
    apply max_le
    · have hM:=s.M_ge_one i
      nlinarith
    · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (s.M_ge_one i))
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) ((s.upper_ge i).trans hu)) (by norm_num)
  have hp:=Finset.prod_le_prod₀ (fun i (_:i∈Finset.univ)=>by positivity)
    (fun i (_:i∈Finset.univ)=>hpoint i)
  calc
    slotControl s.toData=mass s*(∏i,max 1 (128*max 0 (s.hi i)*s.M i)):=rfl
    _≤mass s*(∏i,(128*b)*s.M i):=mul_le_mul_of_nonneg_left hp (mass_nonneg s)
    _=(128*b)^Fintype.card ι*mass s^2:=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      unfold mass
      ring

omit [DecidableEq ι] in
lemma profile_cost_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileCost s≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*A^2)*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have hm2:=pow_le_pow_left₀ (mass_nonneg s) hm 2
  have h:=mul_le_mul hm2 hp (by positivity) (sq_nonneg A)
  have h':=(mul_le_mul_of_nonneg_right h
    (show 0≤2*(max 1 s.b₁*max 1 s.b₂)*mass s^2 by positivity))
  convert h' using 1 <;> simp only [profileCost,Data.profileFactor,mass]; ring

omit [DecidableEq ι] in
lemma exceptional_slot_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    slotControl s.toData^2*frozenProfile s^2≤
      ((128*b)^N)^2*(b^N)^2*A^4*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have h128 : (1:ℝ)≤128*b := by linarith
  have hs : slotControl s.toData≤(128*b)^N*mass s^2 :=
    (slot_control_bound s b hb hu).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h128 hc) (sq_nonneg _))
  have hf : frozenProfile s≤mass s*b^N :=
    mul_le_mul_of_nonneg_left hp (mass_nonneg s)
  have h:=mul_le_mul (pow_le_pow_left₀ (slotControl_nonneg _) hs 2)
    (pow_le_pow_left₀ (frozenProfile_nonneg s) hf 2) (sq_nonneg _) (sq_nonneg _)
  calc
    _≤((128*b)^N*mass s^2)^2*(mass s*b^N)^2:=h
    _=((128*b)^N)^2*(b^N)^2*mass s^4*mass s^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg s) hm 4) (by positivity))
      (sq_nonneg _)

omit [DecidableEq ι] in
theorem twice_controls (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileCost d≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*mass s^2)*mass d^2 ∧
    slotControl d.toData^2*frozenProfile d^2≤
      ((128*b)^N)^2*(b^N)^2*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact ⟨profile_cost_bound d N b (mass s) hb hu hn hm,
    exceptional_slot_bound d N b (mass s) hb hu hn hm⟩

def exceptionalConstant (N : ℕ) (b : ℝ) (J : ℕ) (Q : Ideal O) (K : ℝ) : ℝ :=
  K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2*
    ((128*b)^N)^2*(b^N)^2

omit [DecidableEq ι] in
lemma exceptional_factor_bound {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K : ℝ)
    (hK : 0≤K) (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileFactor S s p J Q K≤exceptionalConstant N b J Q K*
      p.control S^2*(1+‖s.t‖)^(2*J)*A^4*mass s^2 := by
  have h:=exceptional_slot_bound s N b A hb hu hc hm
  let F:=K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*p.control S^2*(1+‖s.t‖)^(2*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hh:=mul_le_mul_of_nonneg_left h hF
  convert hh using 1 <;> simp only [profileFactor,exceptionalConstant,F] <;> ring

omit [DecidableEq ι] in
theorem twice_exceptional_factor {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Qfix : Ideal O) (K : ℝ)
    (hK : 0≤K) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileFactor S d p J Qfix K≤exceptionalConstant N b J Qfix K*
      p.control S^2*(1+‖v‖)^(2*J)*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact exceptional_factor_bound S p J Qfix K hK d N b (mass s) hb hu hn hm

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI
end OAIOriginalModule2351

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstDivisorSupport
Source SHA256: 114f5e2afeda8018df072f4af0e4564189ea015c1459b08336b34749195563b8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2352






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorSupport
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentSecondDivisorSupport CenteredMomentChildAssembly
open CenteredMomentHeckeColumnWindow
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

lemma right_coefficient_zero (s : OriginalData ι) (C D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (a : columns C D hD.1 s.columns→ℂ) (I : columns C D hD.1 s.columns) :
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun I=>coefficient η m 1 t s.beta D I*a I) χ I=0 := by
  unfold divisorCoefficient
  rw [element_span]
  split_ifs with hd
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (column_supported C D hD.1 s.columns I).1 s.beta H hβ hn hd)
    simp only [coefficient,hz,zero_mul]
  · rfl

theorem rightWindowChild_zero (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild s η m t C D hC hD E χ L θ X V z=0 := by
  unfold rightWindowChild gaussPolynomial
  dsimp only
  simp only [right_coefficient_zero s C D hD H hβ L hL η m t χ,
    zero_mul,Finset.sum_const_zero]

theorem signed_right_window_filter (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (Ds : Finset (Ideal O)) (rows : Finset O)
    (F : Ideal O→O→ℂ) :
    (∑L∈Ds,∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)))=
      ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hl : (L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl]
    simp only [rightWindowChild_zero s C D hC hD E H hβ L (lt_of_not_ge hl),star_zero,
      mul_zero,Finset.sum_const_zero]

theorem supported_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(Ds : Finset (Ideal O))(D : Ideal O)(H : ℝ),H/(D.absNorm:ℝ)≤Z^B →
      (∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds D H hcap
  exact hz.2 _ (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hcap)

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

theorem input_commonEnergy_zero (s : Input ι) (R seed D : Ideal O) (hD : Supported D)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy (original s R seed) D hD τ t L W K=0 :=
  commonEnergy_zero (original s R seed) D hD _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL τ t W K

theorem input_rightWindowChild_zero (s : Input ι) (R seed C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild (original s R seed) η m t C D hC hD E χ L θ X V z=0 :=
  rightWindowChild_zero (original s R seed) C D hC hD E _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL η m t χ θ X V z

end SevenEighths.CenteredMomentFirstDivisorSupport

end

end OAI
end OAIOriginalModule2352

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstDivisorCommonBound
Source SHA256: 7dc383f4560c277dddf55b775670364327057c8e90d800852f6945cbe65c1f16
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2353





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorCommonBound
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
local notation "O"=>ActualEisensteinCubic.O

def pairMajorant {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑i∈S,∑j∈S,b i*b j*‖∑'z:O,(gaussRow (a i) (ha i) z*star (gaussRow (a j) (ha j) z))*
    W (‖eisEmbedding z‖^2/K)‖

lemma pairMajorant_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (hb : ∀i∈S,0≤b i)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤pairMajorant S a ha b W K :=
  Finset.sum_nonneg (fun i hi=>Finset.sum_nonneg (fun j hj=>
    mul_nonneg (mul_nonneg (hb i hi) (hb j hj)) (norm_nonneg _)))

lemma gaussEnergy_pair_bound {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (b : α→ℝ)
    (hc : ∀i∈S,‖c i‖≤b i) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (gaussEnergy S a ha c W K).re≤pairMajorant S a ha b W K := by
  apply (Complex.re_le_norm _).trans
  rw [gaussEnergy_expand S a ha c W K hK]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hc i hi) (hc j hj) (norm_nonneg _) ((norm_nonneg _).trans (hc i hi)))
    (norm_nonneg _)

variable {ι : Type*} [Fintype ι]

def coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  pairMajorant Finset.univ (sourceGenerator (residualPool C hC.1 s.columns))
    (sourceGenerator_supported _) (fun I:supportedColumns (residualPool C hC.1 s.columns)=>
      ‖if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (C*I) else 0‖) W K

lemma coarse_nonneg (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤coarse s C hC L W K :=
  pairMajorant_nonneg _ _ _ _ (fun _ _=>norm_nonneg _) _ _

lemma commonEnergy_coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (τ : Character) (v : ℝ) :
    (commonEnergy s C hC τ v L W K).re≤coarse s C hC L W K := by
  apply gaussEnergy_pair_bound _ _ _ _ _ _ W K hK
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ v I
      (Finset.mem_filter.mp I.property).2.1)

universe u

theorem actual_supported_annular_block (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        (∑ L∈(divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b})).filter
            (fun L=>(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
            (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  let live (L : Ideal O) : Prop := (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let U := CenteredMomentFirstAnnularMajorant.profile
  let H := dyadicScale (n 1)
  let active (L : Ideal O) : Prop := live L ∧ (UniqueFactorizationMonoid.moebius L:ℂ)≠0
  let F₁ (L : Ideal O) := if active L then E₁/(L.absNorm:ℝ) else coarse s C hC L U H
  let F₂ (L : Ideal O) := if active L then E₂/(L.absNorm:ℝ) else if live L then coarse s D hD L U H else 0
  have hF₁ (L : Ideal O) : 0≤F₁ L := by
    dsimp only [F₁]; split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
  have hF₂ (L : Ideal O) : 0≤F₂ L := by
    dsimp only [F₂]; split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
    · exact le_rfl
  have hh:=hbound η s t C D hC hD hCD E rows K hK n F₁ F₂
    (fun L _=>hF₁ L) (fun L _=>hF₂ L)
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · apply (commonEnergy_coarse s C hC L U H (dyadicScale_pos _) _ v).trans
        rw [show F₁ L=coarse s C hC L U H from ite_eq_right hl]
        exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _)
          (one_le_pow₀ (by linarith [norm_nonneg v])))
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₂,ite_eq_left hl] using hright L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · by_cases hc:live L
        · apply (commonEnergy_coarse s D hD L U H (dyadicScale_pos _) _ v).trans
          simp only [F₂,ite_eq_right hl,ite_eq_left hc]
          exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _) (one_le_pow₀ (by linarith [norm_nonneg v]))
        · rw [commonEnergy_zero s D hD Hsource hβ L (lt_of_not_ge hc)]
          simp only [F₂,ite_eq_right hl,ite_eq_right hc,Complex.zero_re,zero_mul,le_refl])
  let Ds:=divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})
  have he : (∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L))) =
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
    · simp only [hμ,norm_zero,zero_mul,zero_div,ite_self]
    · by_cases hl:live L
      · have ha:active L:=⟨hl,hμ⟩
        simp only [F₁,F₂,ite_eq_left ha,live,ite_eq_left hl]
        rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
        ring
      · have ha:¬active L:=fun hh=>hl hh.1
        simp only [F₂,ite_eq_right ha,live,ite_eq_right hl,windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  exact hh.trans_eq (by rw [he]; ring)

theorem actual_supported_annular_harmonic (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ)
    (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ Cbound : ℝ, 0<Cbound ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    Hsource/(D.absNorm:ℝ)≤Z^B → ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*Z^δ*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_supported_annular_block W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=supported_harmonic_mass B δ hB hδ
  refine ⟨(Cb+1)*Cm,mul_pos (by linarith) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ hcap E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  have hm:=hZ.2 (divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})) D Hsource hcap
  have hW : 0≤windowBudget J₁ t E₁*windowBudget J₂ t E₂ :=
    mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)
  have hz : 0≤Z^δ := Real.rpow_nonneg ((zero_lt_one.trans hZ.1).le) _
  calc
    _ ≤ _ := hh
    _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*(Cm*Z^δ)*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
      gcongr
    _ ≤ _ := by
      have hc : Cb≤Cb+1 := by linarith
      calc
        _ = ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by ring
        _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*(Cb+1)*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by gcongr
        _ = _ := by ring

end SevenEighths.CenteredMomentFirstDivisorCommonBound

end

end OAI
end OAIOriginalModule2353

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstErrorAllocationPower
Source SHA256: b7e0359a14458f71eb4d0ca6983caa60b796f796927324fe881054aa17ff43a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2354



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstErrorAllocationPower
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildProfileControl
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma child_mass_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    mass (child s (Q^k) R B τ t)=mass s := by
  change (∏i:liveIndices B.val,s.M i.val)=∏i,s.M i
  rw [Finset.prod_coe_sort,prime_slots_live s Q hQ k hslot B]

lemma allocations_card (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) :
    Fintype.card (actualAllocations s.pools (Q^k))≤k+1 := by
  simpa only [Fintype.card_coe] using actual_amplification_allocations_card s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩)

theorem power_sum_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)=
    Fintype.card (actualAllocations s.pools (Q^k))*
      (volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  simp_rw [child_volume s Q hQ k hslot,child_mass_eq s Q hQ k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem power_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  rw [power_sum_eq s Q hQ.ne_zero k hslot R τ t α]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) α)
  exact_mod_cast allocations_card s Q hQ k hslot

theorem budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  simp_rw [child_volume s Q hQ.ne_zero k hslot,child_mass_eq s Q hQ.ne_zero k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs : 0≤∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j) :=
    Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _))
  have hc : (Fintype.card (actualAllocations s.pools (Q^k)):ℝ)≤k+1 := by
    exact_mod_cast allocations_card s Q hQ k hslot
  calc
    _≤((k:ℝ)+1)*((∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hs (sq_nonneg _))
    _=_ := by push_cast;ring

theorem error_budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    8*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  apply (budget_sum_le s Q hQ k hslot R τ t n a α ha).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _)))
  rcases hk with rfl|rfl|rfl <;> norm_num

end SevenEighths.CenteredMomentFirstErrorAllocationPower

end

end OAI
end OAIOriginalModule2354

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
Source SHA256: 18455527d4dc63cf31ee1c73ae66c7705d2281d84d187e5adb8a3db0bf19f1af
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2355





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAmplifiedPowerBudget
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

open CenteredMomentFirstAnnularInput CenteredMomentFirstErrorAllocationPower
theorem eventually_input_power_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec
    H0 hH0 houter hcap amain aerror α haerr hmain herr
  have he:=henergy s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec
    hK hX hsec H0 hH0 houter hcap
  apply he.trans
  have hpweight:0≤56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ):=by positivity
  have hmweight:0≤(Mmax+2*sigma)/(sigma/6):=by positivity
  have herror: ∀p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∀i:Fin 3,
      (∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          R seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
            (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1)))≤
      (errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
        (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
          CenteredMomentFirstChildProfileControl.mass s^2:=by
    intro p i
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
    have hcop:∀j,∀Q∈(activeInput s).slots j,IsCoprime (Ideal.span {p.val}) Q:=by
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
        hsupp (original s R seed).active_slot
        (fun j Q hQ=>s.prime j Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hq:Prime (Ideal.span {p.val}):=(hdata _ hd.2.1).1
    calc
      _≤∑χ:RayCharacter,((errorIndex i+1+1:ℕ):ℝ)*
          (∑j,aerror p i χ j*(volume (activeInput s)/
            ((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
              CenteredMomentFirstChildProfileControl.mass (activeInput s)^2:=by
        apply Finset.sum_le_sum
        intro χ hχ
        apply le_trans (Finset.sum_le_sum (fun B _=>herr p i χ B))
        exact budget_sum_le (activeInput s) (Ideal.span {p.val}) hq (errorIndex i+1) hcop R
          (fun _=>τ p i χ) (fun _=>s.t) 4 (aerror p i χ) α (haerr p i χ)
      _=_:=by
        simp only [CenteredMomentFirstChildProfileControl.mass,activeInput]
        push_cast
        rw [←Finset.sum_mul,←Finset.mul_sum]
        congr 2
        ring
  calc
    _≤(56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          ((∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)+
          ∑p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
            ((errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
              (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
                CenteredMomentFirstChildProfileControl.mass s^2)):=by
      apply mul_le_mul_of_nonneg_left _ hpweight
      apply add_le_add (mul_le_mul_of_nonneg_left hmain hmweight)
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herror p i)
        (mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i)))
    _=_:=by
      simp only [←mul_assoc,←Finset.sum_mul]
      ring

theorem eventually_original_subsets_power_amplification {Ω : Type*} [Fintype Ω]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  have hall:=Filter.eventually_all.mpr (fun A:Finset Ω=>
    eventually_input_power_amplification (ι:=A) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
      hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hall] with Z hz
  have hbase:=hz (∅:Finset Ω)
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,?_⟩
  intro η
  have hf (A:Finset Ω):=(hz A).2.2.2 η
  choose τ hN he using hf
  exact ⟨τ,hN,he⟩

end SevenEighths.CenteredMomentFirstAmplifiedPowerBudget

end

end OAI
end OAIOriginalModule2355

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstReferenceBlock
Source SHA256: 5d554551189b5bbc264562201da53ddc96adad2ecc5c5084d13ef98a16ef27a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2356



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedWindow CenteredMomentFirstWindowBudgets
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O

theorem actual_reference_block (W:𝓢(ℝ,ℂ)) (decay J₁ J₂:ℕ)
    (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃Cb:ℝ,0<Cb ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι],∀s:Input ι,∀R seed:Ideal O,
    ∀a₁ a₂:ℝ,0<a₁→0<a₂→
    (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀E:Finset (CommonIndex C D),∀ξ₁ ξ₂:RayCharacter,
    ∀F:FixedPair s.η C D hC E ξ₁ ξ₂,∀rows:Finset O,∀K:ℝ,0<K→∀n:Fin 4→ℤ,
    sourceRadius s/(D.absNorm:ℝ)≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
    let V:=volume s;
    let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z);
    let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z);
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) C hC (fixedPair s.η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) D hD (fixedPair s.η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))→
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay*
      ‖block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
        (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
        K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))‖/V≤
      Cb*Z^δ*(‖inactiveWeight C D E‖*(Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*
        fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
      (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j)):=by
  obtain ⟨Cb,hCb,hev⟩:=CenteredMomentFirstDivisorCommonBound.actual_supported_annular_harmonic
    W decay J₁ J₂ B δ hB hδ
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ C D hC hD hCD E ξ₁ ξ₂ F rows K hK n hcap EL ER hEL hER
    V refL refR hleft hright
  have hz:0≤Z:=zero_le_one.trans hZ.1.le
  have hcb:0≤Cb:=hCb.le
  have hf:0≤fixedPresentationCost:=fixedPresentationCost_pos.le
  have hprodlo:0≤∏i,s.lo i:=Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  have hV:0<V:=volume_pos s
  have hRL:0≤refL:=by dsimp [refL]; positivity
  have hRR:0≤refR:=by dsimp [refR]; positivity
  have hLE:∀i:Fin 4,0≤refL*EL i:=fun i=>mul_nonneg hRL (hEL i)
  have hRE:∀i:Fin 4,0≤refR*ER i:=fun i=>mul_nonneg hRR (hER i)
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  have hb:=hZ.2 s.η (original s R seed) s.t C D hC hD hCD E rows K hK n
    (sourceRadius s) (fun I hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)
    hcap (∑i,refL*EL i) (∑i,refR*ER i)
    (Finset.sum_nonneg (fun i _=>hLE i)) (Finset.sum_nonneg (fun i _=>hRE i)) hleft hright
  have hw:=windowBudget_pair_sum Finset.univ Finset.univ (fun i=>refL*EL i) (fun i=>refR*ER i)
    (fun i _=>hLE i) (fun i _=>hRE i) J₁ J₂ s.t
  have hb':=hb.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  by_cases hn:block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
      (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0
  · simp only [hn,norm_zero,mul_zero,zero_div]
    have he:0≤∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j):=
      Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>mul_nonneg
        (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    positivity
  · have href:=original_four_budget_reference s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns C D hC hD hCD E
      ξ₁ ξ₂ F rows W (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) (Real.log 4) Z EL ER J₁ J₂ s.t hK
      (dyadicScale_pos _) (dyadicScale_pos _) hZ.1 hEL hER
      (fun _ x hx=>by
        have hh:=logAnnulus_support hx
        exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩) hn
    have hh:=div_le_div_of_nonneg_right hb' hV.le
    have hscale:0≤Cb*Z^δ:=by positivity
    have hmul:=mul_le_mul_of_nonneg_left href hscale
    calc
      _ ≤ _ := hh
      _ = Cb*Z^δ*(‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖/V*
          (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (refL*EL i)*windowBudget J₂ s.t (refR*ER j))) := by ring
      _ ≤ _ := by convert hmul using 1 <;> (try dsimp [refL,refR,V,volume,CenteredMomentExceptionalAmplitudePair.volume]) ; ring

end SevenEighths.CenteredMomentFirstReferenceBlock

end

end OAI
end OAIOriginalModule2356

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCanonicalPair
Source SHA256: 833182bdfc0e27e8f5ba3b30224d50ed1207f78544be9638387b7adcebe1a80b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2357





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalCanonicalPair
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow CenteredMomentExceptionalWindowHeight
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentCommonExceptionalCanonicalWindow CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=actual_canonical_common_window lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentSecondExceptionalCanonicalPair

end

end OAI
end OAIOriginalModule2357

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalOriginalBlock
Source SHA256: feb7715090bec07d46ec49fbb4fde19e5bb5d6809597090eefcf344f00540ee5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2358




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalOriginalBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound CenteredMomentSecondExceptionalCanonicalPair
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤sourceBudget s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0<rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,hJ⟩:=actual_canonical_original_pair lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentSecondExceptionalOriginalBlock

end

end OAI
end OAIOriginalModule2358

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalBudget
Source SHA256: b56ec74ec8b790d05474dc558404180677833a27a976641fa40eadf567929b2b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2359



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalBudget
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondPhysicalLedger
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self (s:Input ι)(p:Tests)(J:ℕ):
    profileMass s.toData s.toData p p J=
      p.heightWeight s.t^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.heightWeight s.t^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor s p J Q K:=by
  unfold profileFactor
  have hp:0≤p.heightWeight s.t:=by unfold Tests.heightWeight; positivity
  positivity

lemma sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

theorem central_sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp

end SevenEighths.CenteredMomentSecondExceptionalBudget

end

end OAI
end OAIOriginalModule2359

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
Source SHA256: df2740b4da67cfb019ea97010711cdbc067b5706377637864d9ce22bf3ddc3a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2360



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondExceptionalBudget
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma column_power_saving (Z c d θ:ℝ) (hZ:1<Z) (hc:1≤c) (hd:1≤d) (hθ:θ≤1/3) :
    (c*d)^θ*Z^(-(Real.logb Z c+Real.logb Z d)/3)≤1 := by
  have hc0:0<c:=zero_lt_one.trans_le hc
  have hd0:0<d:=zero_lt_one.trans_le hd
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:-(Real.logb Z c+Real.logb Z d)/3=Real.logb Z (c*d)*(-1/3):=by
    rw [Real.logb_mul hc0.ne' hd0.ne'];ring
  rw [he,Real.rpow_mul hz.le,Real.rpow_logb hz (ne_of_gt hZ) (mul_pos hc0 hd0),
    ←Real.rpow_add (mul_pos hc0 hd0)]
  have hcd:1≤c*d:=by nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hcd (by linarith : θ+ -1/3≤0)).trans_eq
    (Real.rpow_zero _)

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

theorem original_budget_physical_saving_full
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

lemma column_cap_ledger (c d r:ℝ)(hc:0≤c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  have hmin:0≤min c d:=le_min hc hd
  have hc':min c d≤c:=min_le_left _ _
  have hd':min c d≤d:=min_le_right _ _
  by_cases hr:0≤r
  · rw [max_eq_left hr]
    by_cases hm:r≤min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤max (r-min c d) 0:=le_max_right _ _
    linarith

theorem original_budget_physical_saving
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)(hθ:θ≤1/3)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  have hcol:=column_power_saving Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ hZ hc hd hθ
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hA:0≤A:=mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _)
  have hv:=volume_pos s.toData
  have hE:0≤E:=by dsimp [E];positivity
  have hnum:A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n≤A*E:=by
    calc
      _≤A*((C.absNorm:ℝ)*D.absNorm)^θ*
          (E*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
        exact mul_le_mul_of_nonneg_left hcost (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
      _=A*E*(((C.absNorm:ℝ)*D.absNorm)^θ*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by ring
      _≤A*E*1:=mul_le_mul_of_nonneg_left hcol (mul_nonneg hA hE)
      _=A*E:=mul_one _
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right hnum (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving

end

end OAI
end OAIOriginalModule2360

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving
Source SHA256: 7fba2f930c8a8b840630371c399641be27bc8af6571a3604d7ea3a1dde995245
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2361




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalPhysicalSaving
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem original_budget_physical_saving_full
    {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg Sprofile s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact Sprofile s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2361

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQSaved
Source SHA256: e0d8fa66fe002cf53ecd8f2b3f6ebe22be70bf5598aff64d0ea72efc653c079d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2362








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤_:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 ; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2362

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved
Source SHA256: a61a2e04672e9b6987940b144508eaf6edf5c6204efe77e033ee80fe7c1f0481
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2363








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤_:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 ; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2363

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
Source SHA256: 676647a34089a39ddb4332099d710962599ca418bad84064fce840145c422f82
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2364


namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSecondExceptionalCommonSaving
open CenteredMomentSecondExceptionalPhysicalSaving
lemma common_weight_bound (Z c d θ B ε δ r:ℝ)(hZ:1<Z)(hc:1≤c)(hd:1≤d)
    (hθ:0≤θ)(hC:c≤Z^B)(hD:d≤Z^B):
    Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*(c*d)^θ*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)≤
        Z^(2*ε+δ+2*B*θ-2*max r 0/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hcd:0≤c*d:=mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hd)
  have hpow:(c*d)^θ≤Z^(2*B*θ):=by
    calc
      _≤(Z^B*Z^B)^θ:=Real.rpow_le_rpow hcd
        (mul_le_mul hC hD (zero_le_one.trans hd) (Real.rpow_nonneg hz.le _)) hθ
      _=Z^(2*B*θ):=by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1;ring
  have hl:=column_cap_ledger (Real.logb Z c) (Real.logb Z d) r
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  calc
    _≤Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*Z^(2*B*θ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3):=by gcongr
    _=Z^((2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)+2*B*θ-
      (Real.logb Z c+Real.logb Z d)/3):=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1;ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end SevenEighths.CenteredMomentSecondExceptionalCommonSaving

end

end OAI
end OAIOriginalModule2364

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQUniform
Source SHA256: 36d035c95fc7e41540301f92f8a9a33e1b750d04cc5f5eaf198bf099a9d85d29
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2365









namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2365

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalUniform
Source SHA256: 9190e8756e1cb6c236fac9b6cea135a956cbb0a2a2741ce9843c64a8bc6df438
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2366









namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2366

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
Source SHA256: 5249b188c9ee252ef66f5e3f4cbd7e48a51530c0ca86e3d4d4e7afaa677f5764
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2367


namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace SevenEighths.CenteredMomentSecondExceptionalSourceCaps
open HeckeFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalFamilyUniform
local notation "O" => HeckeFamily.O

theorem eventually_source_caps :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(η:Character)(R0:Ideal O)(H R B:ℝ),
      0≤B → 0≤H → 0≤R → (η.modulus.absNorm:ℝ)≤Z^B →
      (R0.absNorm:ℝ)≤Z^B → H≤Z^B → R≤Z^B →
      H≤Z^(5*B+1) ∧
      (expandedFactor η:ℝ)*R0.absNorm*H^2*(4*R)≤Z^(5*B+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (4*fixedExpandedCost)] with Z hZ hfixed
  refine ⟨hZ,?_⟩
  intro η R0 H R B hB hH hR hη hR0 hHN hRN
  have hz:0<Z:=zero_lt_one.trans hZ
  have hH2:H^2≤(Z^B)^2:=pow_le_pow_left₀ hH hHN 2
  have hbig:B≤5*B+1:=by linarith
  refine ⟨hHN.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hbig),?_⟩
  rw [expandedFactor_real]
  calc
    _=(4*fixedExpandedCost)*(η.modulus.absNorm:ℝ)*R0.absNorm*H^2*R:=by ring
    _≤Z*(Z^B)*(Z^B)*(Z^B)^2*(Z^B):=by gcongr
    _=Z^(5*B+1):=by
      rw [show (Z^B)^2=Z^B*Z^B by ring]
      calc
        _=Z^(1:ℝ)*Z^B*Z^B*(Z^B*Z^B)*Z^B:=by rw [Real.rpow_one]
        _=Z^(5*B+1):=by
          repeat rw [←Real.rpow_add hz]
          congr 1
          ring

end SevenEighths.CenteredMomentSecondExceptionalSourceCaps

end

end OAI
end OAIOriginalModule2367

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
Source SHA256: 42fcfc7503565b15bbce1b152a1d210f62eed2cc5a6cc932f7afe62710591dd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2368




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalSourceFamily
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalKernel
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredExceptionalProfile
local notation "O"=>HeckeFamily.O

lemma exceptional_part_nonzero (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):z≠0:=
  sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1

lemma exceptional_part_inducing (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)(z:O)
    (hz:z∈partRows true η χ₀ Q m C D U R):
    FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z:=
  (Finset.mem_filter.mp hz).2

lemma actual_family_both_rows (η:Character)(χ₀:RayCharacter)(Q:Ideal O)
    (hQ:Q≤Ideal.span {(72:O)})(m:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (τ:RayCharacter→Character)(hf:Family η C D hC hD U τ)(R:ℝ):
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)):=by
  have hz0:=exceptional_part_nonzero η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing η χ₀ Q m C D U R
  constructor
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ χ Q hQ m _ hml hm2 _ hex).1 z hz
    exact (hf.inducing_iff χ Q m z hm (hz0 z hz) hml hm2).mp hh
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ (χ⁻¹) Q hQ m _ hml hm2 _ hex).2 z hz
    simp only [inv_inv] at hh
    exact (hf.inducing_iff χ Q m (-z) hm (neg_ne_zero.mpr (hz0 z hz)) hml hm2).mp hh

lemma exceptional_part_live (η:Character)(χ₀:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    liveRows C D U R (partRows true η χ₀ Q m C D U R)=
      partRows true η χ₀ Q m C D U R:=by
  apply Finset.filter_eq_self.mpr
  intro z hz
  exact liveRows_weight C D U R _ z (Finset.mem_filter.mp hz).1

end SevenEighths.CenteredMomentSecondExceptionalSourceFamily

end

end OAI
end OAIOriginalModule2368

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQChosenBlock
Source SHA256: e094038ea6cef135844eb84328fcea20f851b30d25ae2aedc29705a50b898c6c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2369














namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

theorem chosen_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),
      R0≠0 → seed∣C → seed∣D → (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      sourceRadius s≤Z^Lbound → ∀(R Kphys:ℝ),0<Kphys →
      (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(4*R)≤Z^B →
      ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R0 seed) C D hC hD U R
        (partRows true s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hbound⟩:=
    CenteredMomentFiniteProfileExceptionalFixedQ.actual_uniform_exceptional_block
      wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 χ₀ hη m hm hml hm2 hsource R Kphys hKphys hcond n
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R0 seed
  let rows:=partRows true s.η χ₀ Q m C D U R
  have hn:∀z∈rows,z≠0:=exceptional_part_nonzero s.η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing s.η χ₀ Q m C D U R
  have hprofile0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hp:=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hprofile0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hprofile0 1
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2
  have hD1:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤Z^Lbound:=by
    by_cases hh:0≤sourceRadius s
    · exact (div_le_self hh hD1).trans hsource
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have ha:0<(∏i,s.lo i)*wlo*wlo:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
  have hlower (I:Ideal O)(hI:β I≠0):
      ((∏i,s.lo i)*wlo*wlo)*volume s.toData≤(I.absNorm:ℝ):=by
    have hh:=profile_column_lower R0 s.ν s.W s.P s.lo s.W₁ s.W₂ wlo wlo
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos (fun i=>(s.lo_pos i).le)
      hwlo.le hwlo.le s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      (fun i x hx=>(s.support i hx).1)
      (fun x hx=>(p.support 0 (by rwa [hW1] at hx)).1)
      (fun x hx=>(p.support 1 (by rwa [hW2] at hx)).1)
      (Fintype.piFinset s.pools) I hI
    simpa only [CenteredMomentExceptionalAmplitudePair.volume,map_one,Nat.cast_one,mul_one,div_one,mul_assoc] using hh
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have hZpos:0<Z:=zero_lt_one.trans hZ.1
    exact mul_nonneg hCk (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hp (Real.rpow_nonneg hZpos.le _)) (Real.rpow_nonneg hv.le _))
      (Real.rpow_nonneg hKphys.le _)) (Real.rpow_nonneg ha.le _)) (Nat.cast_nonneg _))
  obtain ⟨τ,hτ⟩:=exists_exceptional_family s.η C D hC hD hCD U
  have he:=actual_family_both_rows s.η χ₀ Q hQ72 m hm hml hm2 C D hC hD U τ hτ R
  have hc (χ ξ:RayCharacter)(z:O)(hz:z∈rows):
      (expandedConductor (τ χ) R0 C z:ℝ)≤Z^B ∧
      (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤Z^B:=by
    have hg:=expanded_conductor_bounds hτ hCD s.t S β R rows W Kphys hKphys n hzero χ ξ R0 z
    have hzlive:z∈liveRows C D U R rows:=by
      rw [show liveRows C D U R rows=rows from exceptional_part_live s.η χ₀ Q m C D U R]
      exact hz
    have hzN:=live_norm_le_four_radius C D U R rows z hzlive
    have hb:(expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤Z^B:=by
      apply le_trans _ hcond
      exact mul_le_mul_of_nonneg_left hzN (by positivity)
    constructor
    · exact (show (expandedConductor (τ χ) R0 C z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.1).trans hb
    · exact (show (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.2).trans hb
  exact hZ.2 s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 τ hτ.height_eq rows hn he.1 he.2
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).1)
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).2)
    χ₀ hη m hm hml hm2 hex (sourceRadius s) hβ hHD
    ((∏i,s.lo i)*wlo*wlo) ha hlower R Kphys hKphys n

end SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock

end

end OAI
end OAIOriginalModule2369

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQSource
Source SHA256: 49d2a891448583561e4f607a615bd86524c3a7ddbece00a20dcdfb6103a7c62c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2370
















namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hblock⟩:=chosen_exceptional_block wlo whi hwlo hwhi lo hi W
    ε δ θ B B hε hδ hθ hB hB
  obtain ⟨Cm,hCm,hmass⟩:=source_part_radical_bound B L Cr δ hB hL hCr hδ
  refine ⟨J,Sprofile,hSp,Ck*Cm,mul_nonneg hCk hCm.le,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hblock⟩:=hblock Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRcap hcond r hX1 hX2 hY1 hY2
  have hp0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hh':=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hp0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hp0 1
  let V:=volume s.toData
  let a:ℝ:=(∏i,s.lo i)*wlo*wlo
  let F:=Ck*profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ+2*B*θ-2*max r 0/3)*V^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
    have hzp:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F,V]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hcap)
    true s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) V F
    hKphys hRcap hcap (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:CenteredMomentSecondBlockAggregate.SourceBlocks q.val.1 q.val.2 U Kphys R (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U R
        (partRows true s.η χ₀ Q m q.val.1 q.val.2 U R) W Kphys (fun i=>(n i:ℤ))‖/V≤
          F*radicalWeight q.val.1 q.val.2:=by
    intro q hq U n
    have hg:=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource S β) _ _ q.property
    have hcnd:(expandedFactor s.η:ℝ)*R0.absNorm*q.val.1.absNorm*q.val.2.absNorm*(4*R)≤Z^B:=by
      apply le_trans _ hcond
      have hH:0≤sourceRadius s:=(Nat.cast_nonneg q.val.1.absNorm).trans hg.2.2.2.2.2.1
      calc
        _=(expandedFactor s.η:ℝ)*R0.absNorm*((q.val.1.absNorm:ℝ)*q.val.2.absNorm)*(4*R):=by ring
        _≤(expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s*sourceRadius s)*(4*R):=by
          gcongr
          · exact hg.2.2.2.2.2.1
          · exact hg.2.2.2.2.2.2
        _=_:=by ring
    have hh:=hZ.2 s p hlo hhi hP hW1 hW2 q.val.1 q.val.2 hs.1 hs.2 R0 seed hR0
      hg.2.2.2.1 hg.2.2.2.2.1 (hg.2.2.2.2.2.1.trans hcap) (hg.2.2.2.2.2.2.trans hcap)
      hg.2.2.1 U r hX1 hX2 hY1 hY2 χ₀ ((mem_liveLabels _ _ _ q).mp hq).1
      m hm hml hm2 hcap R Kphys hKphys hcnd (fun i=>(n i:ℤ))
    rw [←physicalBlock_active]
    exact hh.trans_eq (by dsimp only [F,V,a,radicalWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ=
      Z^(2*ε+2*δ+2*B*θ-2*max r 0/3):=by
    rw [←Real.rpow_add (zero_lt_one.trans hZ.1)]
    congr 1
    ring
  dsimp only [F,V,a]
  calc
    _=(Ck*Cm)*profileFactor Sprofile s p J Q K*
      (Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]

end SevenEighths.CenteredMomentSecondExceptionalFixedQSource

end

end OAI
end OAIOriginalModule2370

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalUniformSource
Source SHA256: 5e184d97161c24ce02b4df931decccc96a759a1fb8f483db8e6272dff58b5ca4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2371


















namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalUniformSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ) :=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hsource⟩:=
    CenteredMomentSecondExceptionalFixedQSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ (5*B+1) B 1 hε hδ hθ (by positivity) hB zero_lt_one
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hsource⟩:=hsource Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hsource,CenteredMomentSecondExceptionalSourceCaps.eventually_source_caps] with Z hZ hcaps
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRN r hX1 hX2 hY1 hY2
  obtain ⟨hHlarge,hcond⟩:=hcaps.2 s.η R0 (sourceRadius s) R B hB hH0 hR.le hη hR0N hH hRN
  exact hZ.2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hHlarge χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys hR (by simpa using hRN) hcond r hX1 hX2 hY1 hY2

end SevenEighths.CenteredMomentSecondExceptionalUniformSource

end

end OAI
end OAIOriginalModule2371

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
Source SHA256: 46c96d7a7f74fff3e80da18e475766c365b74f3f340aae23315dc3cfc4f3926e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2372




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma live_harmonic_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,pairWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2:=by
  rw [CenteredMomentSecondBlockHarmonicMass.active_blocks_sum_eq]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _=>Finset.sum_nonneg (fun U _=>mul_nonneg (Nat.cast_nonneg _) (pairWeight_nonneg _ _)))

theorem part_energy_harmonic_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        pairWeight q.1.1.val.1 q.1.1.val.2):=by
  apply (div_le_div_of_nonneg_right
    (partEnergy_norm_le exceptional η χ Q m t S β W K Tsec Z ξ H) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*pairWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          pairWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left (live_harmonic_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

theorem source_part_harmonic_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm exceptional η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (part_energy_harmonic_bound exceptional η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)

end SevenEighths.CenteredMomentSecondNonexceptionalAggregate

end

end OAI
end OAIOriginalModule2372

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
Source SHA256: c853e9e8e9c9575e4f9c0c58393636918e3ceb2c2a79e249e8ee51c69cd341d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2373




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSourceBlockWindows
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

lemma scalar_cancel (K G V U c d x y h q M:ℝ)
    (hc:0<c)(hd:0<d)(hx:0<x)(hy:0<y)(hU:0<U)(hq:0≤q) :
    (K/(Real.sqrt c*Real.sqrt d*Real.sqrt x*Real.sqrt y))*(G/U)/Real.sqrt (c*d)*
      (M*U*V*h)/(1+q)=M*((K*G*V/(c*d))*h/(x*y))/(1+q)*Real.sqrt (x*y) := by
  rw [Real.sqrt_mul hc.le,Real.sqrt_mul hx.le]
  have hc':Real.sqrt c≠0:=(Real.sqrt_pos.mpr hc).ne'
  have hd':Real.sqrt d≠0:=(Real.sqrt_pos.mpr hd).ne'
  have hx':Real.sqrt x≠0:=(Real.sqrt_pos.mpr hx).ne'
  have hy':Real.sqrt y≠0:=(Real.sqrt_pos.mpr hy).ne'
  have hq':1+q≠0:=by positivity
  field_simp
  ; ring_nf
  ; simp [Real.sq_sqrt,hc.le,hd.le,hx.le,hy.le]

theorem physical_effective_scale (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K<
      dyadicScale (n 0) := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    exact (dyadicWeight_support (n 0) h0).2
  · exact False.elim (hz rfl)

def childEnvelope (η:Character)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ :=
  (fixedFactor:ℝ)*η.modulus.absNorm*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

theorem family_child_envelope {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(hf:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    ((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤childEnvelope η C D U n := by
  have hh := (hf.physical_budget t S β R rows W K hK n hne χ).1
  have hh' : ((τ χ).modulus.absNorm:ℝ)≤
      (fixedFactor:ℝ)*η.modulus.absNorm*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
    have hhcast : ((τ χ).modulus.absNorm:ℝ)≤
        (η.modulus.absNorm:ℝ)*fixedFactor*(∏P∈U,P.val).absNorm*
          (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by exact_mod_cast hh
    simpa only [mul_comm (η.modulus.absNorm:ℝ) (fixedFactor:ℝ)] using hhcast
  exact mul_le_mul_of_nonneg_right hh' (dyadicScale_pos _).le

theorem actual_envelope_scalar (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(_hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    (fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  have hn (i:Fin 4):0<dyadicScale (n i):=dyadicScale_pos _
  let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr:0<r:=div_pos (mul_pos (hn 0) (hn 1)) (mul_pos (hn 2) (hn 3))
  have hscale := (physical_effective_scale η t S β C D hC hD U R rows W K n hne).le
  have he : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((C.absNorm:ℝ)*D.absNorm) := by
    rw [secondEffectiveScale,←normValue_eq_embedding,normValue_mul]
    dsimp only [normValue]
    ring
  have hrat : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))≤r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (dyadicScale_pos _).le) (mul_pos (hn 2) (hn 3)).le
  have hfrac : (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)≤1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  rw [outerScalar,normalizer,actual_partitionNormalizer C D hC]
  change _≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  rw [childEnvelope,scalar_cancel _ _ _ _ _ _ _ _ _ r _ hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) hu hr.le]
  rw [←he]
  calc
    _=((fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      ((secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
        dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)):=by ring
    _≤_:=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) by positivity)

theorem actual_residual_sqrt_cap (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))≤
      4*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  have hH:0≤Hsource:=(Nat.cast_nonneg ((C*(I:Ideal O)).absNorm)).trans (hsource _ hI)
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:dyadicScale (n 2)≤4*Hsource/(C.absNorm:ℝ):=
    (residual_window_bounds C I hC.1 0 Hsource (n 2) (Nat.cast_nonneg _) (hsource _ hI) hwi).2
  have hy:dyadicScale (n 3)≤4*Hsource/(D.absNorm:ℝ):=
    (residual_window_bounds D J hD.1 0 Hsource (n 3) (Nat.cast_nonneg _) (hsource _ hJ) hwj).2
  have hh:=Real.sqrt_le_sqrt (mul_le_mul hx hy (dyadicScale_pos _).le (by positivity))
  have he:(4*Hsource/(C.absNorm:ℝ))*(4*Hsource/(D.absNorm:ℝ))=
      (4*Hsource)^2/((C.absNorm:ℝ)*D.absNorm):=by ring
  rw [he,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity)] at hh
  exact hh

theorem actual_source_envelope_scalar (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  apply (actual_envelope_scalar η t S β C D hC hD U R rows W K hK n hne).trans
  have hh:=mul_le_mul_of_nonneg_left
    (actual_residual_sqrt_cap η t S β C D hC hD U R rows W K n Hsource hsource hne)
    (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm by positivity)
  convert hh using 1 ; ring

theorem actual_source_envelope_scalar_extra (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (Eextra:ℝ)(hEextra:0≤Eextra) :
    ((outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))*Eextra≤
    (4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*Eextra :=
  mul_le_mul_of_nonneg_right
    (actual_source_envelope_scalar η t S β C D hC hD U R rows W K hK n Hsource hsource hne) hEextra
end SevenEighths.CenteredMomentSecondNonexceptionalScalar

end

end OAI
end OAIOriginalModule2373

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondCapacitySourceShift
Source SHA256: c0aab3bd90f113c61e5cc2ae259ea7812e30175f1d1b4f9087b2270af206ed5d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2374




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondCapacitySourceShift
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondPhysicalLedger
open CenteredMomentSectorLocalization CenteredMomentSourceBlockWindows
open CenteredMomentSecondPhysicalCost CenteredMomentSecondRadicalBudget
open CenteredMomentSupport CenteredMomentSecondWholeKernel ConcretePrimeRowBridge CenteredMomentSourceRow
local notation "O"=>HeckeFamily.O

theorem effective_upper (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    dyadicScale (n 0)≤4*secondEffectiveScale C D
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K:=by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    have h0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1
    have hh:=(dyadicWeight_support (n 0) h0).1
    linarith
  · exact False.elim (hz rfl)

lemma adjusted_row_lower (k h x y:ℝ)(hk:0<k)(hh:0<h)(hx:0<x)(hy:0<y):
    x*y/k≤h*max 1 (1/(k*h/(x*y))):=by
  calc
    _=h*(1/(k*h/(x*y))):=by field_simp
    _≤_:=mul_le_mul_of_nonneg_left (le_max_right _ _) hh.le

lemma scalar_capacity_shift (Z F q U V H K a c d k h x y:ℝ)
    (hZ:1<Z)(hF:0<F)(hq:0<q)(hU:1≤U)(hV:0<V)(hH:0<H)(hK:0<K)(ha:0<a)
    (hc:0<c)(hd:0<d)(hk:0<k)(hh:0<h)(hx:0<x)(hy:0<y)
    (g:ℝ)(hg:0<g)(hgc:g≤c)
    (hscale:k≤4*(K*g*V/(c*d)))(hleft:a*H/c≤x)(hright:a*H/d≤y):
    Real.logb Z (H/c)-Real.logb Z (F*q*U*V*h*max 1 (1/(k*h/(x*y))))≤
      Real.logb Z K-Real.logb Z q-Real.logb Z H+Real.logb Z (4/(F*a^2)):=by
  have hu:0<U:=zero_lt_one.trans_le hU
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hs:=Real.logb_le_logb_of_le hZ hk hscale
  have hg':=Real.logb_le_logb_of_le hZ hg hgc
  have hu':0≤Real.logb Z U:=Real.logb_nonneg hZ hU
  have hrow:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos hx hy) hk)
    (adjusted_row_lower k h x y hk hh hx hy)
  have hm:0<max 1 (1/(k*h/(x*y))):=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow] at hl hr hs hrow ⊢
  linarith

def adjustedEnvelope (η:Character)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  childEnvelope η C D U n*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

def adjustedEnvelopeRef (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)*
    max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))

theorem actual_capacity_shift_reference (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0<qref)(hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣C:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).1
    simpa only [primary_span_supported C hC] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ C hC.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert hv' using 1 ; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert hv' using 1 ; ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  exact scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (C.absNorm:ℝ) (D.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hZ hf hq hu1 hv hH hK ha hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs hl hr

theorem actual_capacity_shift_reference_right (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z qref:ℝ)(n:Fin 4→ℤ)
    (hq:0<qref)(hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(D.absNorm:ℝ))-Real.logb Z (adjustedEnvelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=by
  have hc:=CenteredMomentFirstScale.norm_pos C hC.1
  have hd:=CenteredMomentFirstScale.norm_pos D hD.1
  have hg:=CenteredMomentFirstScale.norm_pos (Ideal.span {commonFrequencyGenerator C D})
    (Ideal.span_singleton_eq_bot.not.mpr (commonFrequencyGenerator_ne_zero C D hC))
  have hv:=CenteredMomentFirstScale.norm_pos (Ideal.span {nonunitFrequencyGenerator C D U})
    (Ideal.span_singleton_eq_bot.not.mpr (nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hu1:1≤((∏P∈U,P.val).absNorm:ℝ):=by exact_mod_cast (show 1≤(∏P∈U,P.val).absNorm from by exact_mod_cast hu)
  have hf:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hdiv:Ideal.span {commonFrequencyGenerator C D}∣D:=by
    have hh:=Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (commonFrequencyGenerator_dvd C D hC hD hCD).2
    simpa only [primary_span_supported D hD] using hh
  have hgc:=CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ D hD.1 hdiv
  have hh:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hv':=(le_div_iff₀ ha).mp hh.1
    convert hv' using 1 ; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hv':=(le_div_iff₀ ha).mp hh.2
    convert hv' using 1 ; ring
  have hs:=effective_upper η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hs
  have hs':dyadicScale (n 0)≤4*(K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((D.absNorm:ℝ)*C.absNorm)):=by
    simpa only [mul_comm (C.absNorm:ℝ) (D.absNorm:ℝ)] using hs
  have hh':=scalar_capacity_shift Z (fixedFactor:ℝ) qref
    ((∏P∈U,P.val).absNorm:ℝ) ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ)
    H K a (D.absNorm:ℝ) (C.absNorm:ℝ) (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 3)) (dyadicScale (n 2)) hZ hf hq hu1 hv hH hK ha hd hc
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    ((Ideal.span {commonFrequencyGenerator C D}).absNorm:ℝ) hg hgc hs' hr hl
  simpa only [adjustedEnvelopeRef,mul_comm (dyadicScale (n 3)) (dyadicScale (n 2))] using hh'

theorem actual_capacity_shift (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K H a Z:ℝ)(n:Fin 4→ℤ)
    (hK:0<K)(hH:0<H)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(I.absNorm:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (H/(C.absNorm:ℝ))-Real.logb Z (adjustedEnvelope η C D U n)≤
      Real.logb Z K-Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z H+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)):=
  actual_capacity_shift_reference η t S β C D hC hD hCD U R rows W K H a Z
    (η.modulus.absNorm:ℝ) n (CenteredMomentFirstScale.norm_pos η.modulus η.modulus_ne_bot)
    hK hH ha hZ hlower hne

end SevenEighths.CenteredMomentSecondCapacitySourceShift

end

end OAI
end OAIOriginalModule2374

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondRetainedRatioScalar
Source SHA256: 0a0907e9e530def29db3497b18f76bf639acfd3d4f8d21931211cc5441b93789
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2375


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRatioScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSourceBlockWindows
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

open CenteredMomentSecondNonexceptionalScalar

theorem ratio_penalty_le (r a:ℝ) (hr:0<r) (_ha:0≤a) (ha1:a≤1) :
    r/(1+r)*(max 1 (1/r))^a≤1 := by
  by_cases h:r≤1
  · have hi:1≤1/r:=(le_div_iff₀ hr).mpr (by linarith)
    rw [max_eq_right hi]
    have hp: (1/r)^a≤1/r:=Real.rpow_le_self_of_one_le hi ha1
    calc
      _≤r/(1+r)*(1/r):=mul_le_mul_of_nonneg_left hp (by positivity)
      _=1/(1+r):=by field_simp
      _≤1:=(div_le_one (by positivity)).mpr (by linarith)
  · have hi:1/r≤1:=(div_le_one hr).mpr (by linarith)
    rw [max_eq_left hi,Real.one_rpow,mul_one]
    exact (div_le_one (by positivity)).mpr (by linarith)

def retainedRatio (n:Fin 4→ℤ):ℝ :=
  dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))

theorem retainedRatio_pos (n:Fin 4→ℤ):0<retainedRatio n := by
  unfold retainedRatio
  exact div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))

theorem actual_envelope_scalar_ratio (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(_hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (a:ℝ)(ha:0≤a)(ha1:a≤1) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
      (max 1 (1/retainedRatio n))^a≤
    (fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  have hn (i:Fin 4):0<dyadicScale (n i):=dyadicScale_pos _
  let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr:0<r:=div_pos (mul_pos (hn 0) (hn 1)) (mul_pos (hn 2) (hn 3))
  have hscale := (physical_effective_scale η t S β C D hC hD U R rows W K n hne).le
  have he : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((C.absNorm:ℝ)*D.absNorm) := by
    rw [secondEffectiveScale,←normValue_eq_embedding,normValue_mul]
    dsimp only [normValue]
    ring
  have hrat : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))≤r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (dyadicScale_pos _).le) (mul_pos (hn 2) (hn 3)).le
  have hfrac : (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)*
        (max 1 (1/r))^a≤1 := by
    apply le_trans _ (ratio_penalty_le r a hr ha ha1)
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hrat (by positivity)) (Real.rpow_nonneg (by positivity) _)
  rw [outerScalar,normalizer,actual_partitionNormalizer C D hC]
  change _≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  rw [childEnvelope,scalar_cancel _ _ _ _ _ _ _ _ _ r _ hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) hu hr.le]
  rw [←he]
  calc
    _=((fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      ((secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
        dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)*(max 1 (1/r))^a):=by
      dsimp only [retainedRatio,r];ring
    _≤_:=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) by positivity)

theorem actual_source_envelope_scalar_ratio (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (a:ℝ)(ha:0≤a)(ha1:a≤1) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
      (max 1 (1/retainedRatio n))^a≤
    4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  apply (actual_envelope_scalar_ratio η t S β C D hC hD U R rows W K hK n hne a ha ha1).trans
  have hh:=mul_le_mul_of_nonneg_left
    (actual_residual_sqrt_cap η t S β C D hC hD U R rows W K n Hsource hsource hne)
    (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm by positivity)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentSecondRetainedRatioScalar

end

end OAI
end OAIOriginalModule2375

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
Source SHA256: f35d5c5f2d1755dd2f92ab3a1bfafbe294e8a87daed85c42f50591bbbd300c8a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2376





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSourceDiagonal
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceSecondZeroEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem actual_second_zero (N:ℕ)(ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[Fintype ι][DecidableEq ι],Fintype.card ι≤N →
      ∀(a b:ℝ),0<a → 0≤b → ∀(s:Input ι)(p:Profiles a b),
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → ∀(R seed:Ideal O),seed≠0 →
      ∀κ:ℂ,
      ‖κ*sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData≤
      C*‖κ‖*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*
        (∏i,s.M i))^2*(1+(∏i,max 0 (s.hi i))*b*b)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=profile_second_zero_energy N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p hw1 hw2 R seed hseed κ
  have hM (i:ι):0≤s.M i:=zero_le_one.trans (s.M_ge_one i)
  have hhi (i:ι):0≤max 0 (s.hi i):=le_max_left _ _
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt ha) (p.support i hn).1
  have hslotzero (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hW1:∀x,‖s.W₁ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 0):=by
    intro x;rw [hw1];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hW2:∀x,‖s.W₂ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 1):=by
    intro x;rw [hw2];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hh:=(hbound hcard s.η s.t R s.ν s.ν_bound s.W s.P s.M (fun i=>max 0 (s.hi i)) s.W₁ s.W₂
    (SchwartzMap.seminorm ℝ 0 0 (p.profile 0)) (SchwartzMap.seminorm ℝ 0 0 (p.profile 1)) b b
    hM (apply_nonneg _ _) (apply_nonneg _ _) hhi hb hb s.W_bound hW1 hW2
    hslotzero (by rw [hw1];exact hz 0) (by rw [hw2];exact hz 1)
    (fun i x hx=>((s.support i hx).2).trans (le_max_right _ _))
    (by intro x hx;rw [hw1] at hx;exact (p.support 0 hx).2)
    (by intro x hx;rw [hw2] at hx;exact (p.support 1 hx).2)
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero hseed rfl s.same_product (Fintype.piFinset s.pools)).2 κ
  have hV:=volume_pos s.toData
  simpa only [map_one,Nat.cast_one,mul_one,div_one,coefficient,volume,norm_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV,abs_of_pos s.X₁_pos,abs_of_pos s.X₂_pos,
    abs_of_pos (Finset.prod_pos (fun i _=>s.P_pos i)),mul_div_assoc,div_mul_eq_mul_div] using hh

end SevenEighths.CenteredMomentSecondSourceDiagonal

end

end OAI
end OAIOriginalModule2376

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
Source SHA256: 965b193db93606eea206de355658f652730efa88e846321608a4bb514a34be2e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2377



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSupportedChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound CenteredMomentSecondDivisorSupport CenteredMomentSourceRow
open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren
local notation "O" => ActualEisensteinCubic.O

theorem paired_rows_filter_right
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (η:Character) (t:ℝ) (A:O) (ξ:RayCharacter)
    (v:Ideal O→sectorPool D hD.1 S→ℂ) (argument:O→O)
    (Ds:Finset (Ideal O)) (rows:Finset O) (scalar:Ideal O→ℂ) (left:Ideal O→O→ℂ) :
    (∑L∈Ds,scalar L*∑z∈rows,left L z*star
      (rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v L I)
        (argument z)))=
    ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)),
      scalar L*∑z∈rows,left L z*star
      (rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v L I)
        (argument z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hn:(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn]
    have hz:=right_divisor_row_zero D hD S β Hsource hβ L (lt_of_not_ge hn) η t A ξ
    simp only [hz,star_zero,mul_zero,Finset.sum_const_zero]

theorem right_source_energy_zero
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (L:Ideal O) (hL:Hsource/(D.absNorm:ℝ)<L.absNorm)
    (keep:O→Prop) (f:Ideal O→ℂ) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) :
    sourceRestrictedEnergy keep (residualPool D hD.1 S)
      (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0) f Φ H=0 := by
  have hc (I:supportedColumns (residualPool D hD.1 S)) :
      (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then β (D*I) else 0)=0 := by
    split_ifs with hi
    · by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 β Hsource hβ hn hi.2)
    · rfl
  simp only [sourceRestrictedEnergy,restrictedEnergy,rowPolynomial,hc,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide:2≠0),ite_self,tsum_zero]

theorem actual_block_from_supported_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
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
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let live (L:Ideal O):Prop:=(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let Ds:=divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
  let coarse (L:Ideal O):ℝ:=QuadraticInitialBound.diagonalControl Φ*max 1 H*
    (∑I∈residualPool C hC.1 S,‖if IsCoprime C I ∧ L∣I then β (C*I) else 0‖)^2
  have hcoarse (L:Ideal O):0≤coarse L:=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=>if live L then E₁/(L.absNorm:ℝ) else coarse L
  let F₂:Ideal O→ℝ:=fun L=>if live L then E₂/(L.absNorm:ℝ) else 0
  have hF₁ (L:Ideal O):0≤F₁ L:=by
    dsimp only [F₁];split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact hcoarse L
  have hF₂ (L:Ideal O):0≤F₂ L:=by
    dsimp only [F₂];split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact le_rfl
  have hk:=hkernel r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl hsf χ v
      · have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (τ χ) v
          (nonexceptional η χ Q m A) Φ H hH
        exact hh.trans (by simpa only [F₁,ite_eq_right hl] using
          le_mul_of_one_le_right (hcoarse L) (one_le_pow₀ (by linarith [norm_nonneg v]) (n:=2*J₁))))
    (by
