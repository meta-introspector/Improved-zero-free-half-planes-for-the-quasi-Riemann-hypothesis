
end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2275

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonCanonical
Source SHA256: 23043ebeda6adac752a191b43cbd0933d8d4b16761560b46a7ad873e819afde6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2276



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
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

theorem actual_common_canonical_bound (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
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
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_better_side wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
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
  let F:ℝ:=profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm)
  have hF:0≤F:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg Sprofile _ _ _ _ _) (frozenProfile_nonneg _))
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

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2276

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonWindow
Source SHA256: 3a5a7d9ff13e94437860a52dd51124611857116ffdb92b552ee297619a974f9a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2277





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_common_window (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
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
          mass Sprofile s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_canonical_bound wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
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
    J J (F*mass Sprofile s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg Sprofile s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hm:=shifted_mass Sprofile s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass Sprofile (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass Sprofile s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end OAIOriginalModule2277

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQCanonical
Source SHA256: 896ed33d4a3be9c2bf603c99e7e66654d02622d2f09cb3eb453136f8302771f0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2278




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFixedQForcingCount CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_canonical_bound (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
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
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
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
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_better_side wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  let qcost:ℝ:=(Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)
  have hqcost:0<qcost:=by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero Q Q))
  refine ⟨K*qcost,mul_pos hK hqcost,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hc:=actual_canonical_exceptional_count_fixedQ η₀ χ C D hC U Q hQ hQtop hQ72 hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  have hb:=hZ.2 s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let F:ℝ:=profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm)
  have hF:0≤F:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg Sprofile _ _ _ _ _) (frozenProfile_nonneg _))
    (frozenProfile_nonneg _)) (by positivity)
  let e:ℝ:=2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
    (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)
  let f:ℝ:=(M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6
  have hz:=zero_lt_one.trans hZ.1
  apply hb.trans
  calc
    _≤K*(qcost*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f))*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F:=by
      apply mul_le_mul_of_nonneg_right _ hF
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hK.le
    _=_:=by
      have hpow:Z^(f+e)=Z^f*Z^e:=Real.rpow_add hz _ _
      change K*(qcost*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f))*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F=(K*qcost)*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^(f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*((C.absNorm:ℝ)*D.absNorm)^θ*F
      rw [show f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)=f+e by dsimp [e];ring,hpow]
      ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2278

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQWindow
Source SHA256: 3b4cce1b875174f295691640f1a691bc931f2a41769dd2c847241b7de2d9be4d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2279





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_common_window (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
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
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
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
          mass Sprofile s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_canonical_bound wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hη m hm hml hm2 hex Cr M hCr hN θ₁ θ₂ X Y hX hY Ds hDs
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
    J J (F*mass Sprofile s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg Sprofile s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond η₀ χ U hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hm:=shifted_mass Sprofile s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass Sprofile (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass Sprofile s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2279

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight
Source SHA256: 9c72a759b2f7037e4045ad618705dbaf6fb60babcb9024e3af5224a7719f50fa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2280


namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentHeckeWindowEnergy
open CenteredMomentExceptionalAmplitudePair CenteredMomentAllocatedDetectorAmplitude
universe u

theorem heightCost_phase (t θ:ℝ):
    heightCost t θ≤(1+‖t‖)*(1+2*Real.pi)^2*(1+‖θ‖):=by
  have hc:0≤2*Real.pi:=by positivity
  have ht:0≤‖t‖:=norm_nonneg t
  have hθ:0≤‖θ‖:=norm_nonneg θ
  have hh:1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖)*(1+2*Real.pi)*(1+‖θ‖):=by
    nlinarith [mul_nonneg hc ht,mul_nonneg ht hθ,mul_nonneg (mul_nonneg hc ht) hθ]
  exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq (by ring)

theorem mass_phase {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(w:ℝ)(J:ℕ):
    mass R s v p q s.t v.t w (-w) J≤
      (1+2*Real.pi)^(4*J)*profileMass R s.toData v.toData p q J*(1+‖w‖)^(2*J):=by
  have hp:=pow_le_pow_left₀ (heightCost_pos s.t w).le (heightCost_phase s.t w) J
  have hq:=pow_le_pow_left₀ (heightCost_pos v.t (-w)).le (heightCost_phase v.t (-w)) J
  rw [norm_neg] at hq
  have hh:=mul_le_mul hp hq (pow_nonneg (heightCost_pos v.t (-w)).le _) (by positivity)
  have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (mul_nonneg (Profiles.control_nonneg p R) (Profiles.control_nonneg q R)))
      (slotControl_nonneg s.toData)) (slotControl_nonneg v.toData))
      (Real.sqrt_nonneg (volume s.toData))) (Real.sqrt_nonneg (volume v.toData))
  have hmass:mass R s v p q s.t v.t w (-w) J =
      p.control R*q.control R*(heightCost s.t w^J*heightCost v.t (-w)^J)*
        slotControl s.toData*slotControl v.toData*Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData):=by
    unfold mass
    ring
  rw [hmass]
  apply he.trans_eq
  simp only [profileMass,mul_pow,←pow_mul]
  rw [show 4*J=2*J+2*J by omega,show 2*J=J+J by omega]
  simp only [pow_add]
  ring
end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2280

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalStability
Source SHA256: f5750202f0b4cc1ddd15abe8c863e2bf6c6c7f4a78cc41a5df9863d939f06c21
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2281





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open CenteredMomentRetainedProfile CenteredMomentAllocatedNaturalSource
open EisensteinSchwartzPoisson CenteredMomentLattice

def sourcePlain (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) : Plain :=
  ⟨W,a,b,ha,hs,W.smooth ⊤⟩

theorem sourcePlain_support (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (U:ℝ) (hU:0<U) (t:ℝ) :
    Function.support ((sourcePlain a b ha W hs).profile U hU t:ℝ→ℂ)⊆
      Set.Icc (a/max 1 b) b := by
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    exact retainedProfile_support W a b ha hs (W.smooth ⊤) U hU hret t
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simp

theorem plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S ((sourcePlain a b ha W hs).profile U hU t)≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hsource⟩ := normPowerProfile_source_control a b ha S
  refine ⟨n,T,(max 1 b)^(S.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs U hU t
  have hp:=sourceControl_nonneg T W
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    have hd:=normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation U)
      ha (le_max_left _ _) (clipDilation_ge_one U hU) (clipDilation_le b U hU hret)
      hs (W.smooth ⊤) t S
    exact hd.trans ((mul_le_mul_of_nonneg_left (hsource W hs t) (by positivity)).trans_eq (by dsimp only [sourceControl]; ring))
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simpa only [sourceControl,map_zero] using
      (show 0≤(max 1 b)^(S.sup Prod.snd)*C*sourceControl T W*(1+‖t‖)^n by positivity)

theorem scale_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (DetectorDictionaryInverseUniform.scaleCLM W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control DetectorDictionaryInverseUniform.scaleCLM S

theorem scale_source_support (a b:ℝ) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) :
    Function.support (DetectorDictionaryInverseUniform.scaleCLM W:ℝ→ℂ)⊆Set.Icc a b := by
  have he:(DetectorDictionaryInverseUniform.scaleCLM W:ℝ→ℂ)=
      HeckeInverseAmplification.scaleProfile W :=
    funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)
  rw [he]
  exact HeckeInverseAmplification.scaleProfile_support W a b hs

theorem fourier_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ)) W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ))) S

def logWindowMultiply : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ
    (CenteredMomentReflectedAnnuli.logWindowSchwartz:ℝ→ℂ)).restrictScalars ℝ

theorem logWindowMultiply_apply (W:𝓢(ℝ,ℂ)) (x:ℝ) :
    logWindowMultiply W x=CenteredMomentReflectedAnnuli.logWindow x*W x := by
  change (SchwartzMap.smulLeftCLM ℂ
    (CenteredMomentReflectedAnnuli.logWindowSchwartz:ℝ→ℂ) W) x=_
  rw [SchwartzMap.smulLeftCLM_apply_apply
    CenteredMomentReflectedAnnuli.logWindowSchwartz.hasTemperateGrowth]
  rfl

theorem logWindow_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (logWindowMultiply W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control logWindowMultiply S

theorem window_fourier_twist_source_control (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),∀t:ℝ,
      sourceControl S (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ))
        (logWindowMultiply (JointLogSeparation.frequencyTwist W t)))≤
      C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=fourier_source_control S
  obtain ⟨S₂,C₂,hC₂,h₂⟩:=logWindow_source_control S₁
  obtain ⟨n,T,C₃,hC₃,h₃⟩:=frequencyTwist_source_control S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W t
  exact (h₁ _).trans ((mul_le_mul_of_nonneg_left
    ((h₂ _).trans (mul_le_mul_of_nonneg_left (h₃ W t) hC₂.le)) hC₁.le).trans_eq (by dsimp only [sourceControl]; ring))

theorem scaled_plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S (DetectorDictionaryInverseUniform.scaleCLM
        ((sourcePlain a b ha W hs).profile U hU t))≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=scale_source_control S
  obtain ⟨n,T,C₂,hC₂,h₂⟩:=plain_profile_source_control a b ha S₁
  refine ⟨n,T,C₁*C₂,by positivity,?_⟩
  intro W hs U hU t
  exact (h₁ _).trans ((mul_le_mul_of_nonneg_left (h₂ W hs U hU t) hC₁.le).trans_eq (by ring))

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule2281

/-! Original module: OAI.NumberTheory.DirichletL.Energy.Profiles
Source SHA256: 7bf50954f7b7f7c960e59270564daebf6d878af2ed25565e9d56f3e94607be9e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2282



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

structure Test (a b:ℝ) where
  profile : 𝓢(ℝ,ℂ)
  support : Function.support (profile:ℝ→ℂ)⊆Set.Icc a b

def lower (a b:ℝ):ℕ→ℝ
  | 0=>a
  | n+1=>lower a b n/max 1 b

lemma lower_pos (a b:ℝ)(ha:0<a)(n:ℕ):0<lower a b n:=by
  induction n with
  | zero=>exact ha
  | succ n ih=>exact div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

def derivativeChoice (W:𝓢(ℝ,ℂ))(j:Fin 2):𝓢(ℝ,ℂ):=
  if j=0 then W else DetectorDictionaryInverseUniform.scaleCLM W

lemma derivativeChoice_apply (W:𝓢(ℝ,ℂ))(j:Fin 2):
    (derivativeChoice W j:ℝ→ℂ)=scaleTest W j:=by
  unfold derivativeChoice scaleTest
  split_ifs
  · rfl
  · exact funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)

lemma derivativeChoice_support (a b:ℝ)(W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(j:Fin 2):
    Function.support (derivativeChoice W j:ℝ→ℂ)⊆Set.Icc a b:=by
  rw [derivativeChoice_apply]
  exact scaleTest_support W a b hs j

def step (a b:ℝ)(ha:0<a)(W:Test a b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Test (a/max 1 b) b where
  profile:=derivativeChoice ((sourcePlain a b ha W.profile W.support).profile U hU t) j
  support:=derivativeChoice_support _ _ _ (sourcePlain_support a b ha W.profile W.support U hU t) j

theorem step_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀U:ℝ,∀hU:0<U,∀t:ℝ,∀j:Fin 2,
      sourceControl S (step a b ha W U hU t j).profile≤
        C*sourceControl T W.profile*(1+‖t‖)^n:=by
  obtain ⟨n₀,T₀,C₀,hC₀,h₀⟩:=plain_profile_source_control a b ha S
  obtain ⟨n₁,T₁,C₁,hC₁,h₁⟩:=scaled_plain_profile_source_control a b ha S
  refine ⟨n₀+n₁,T₀∪T₁,C₀+C₁,add_pos hC₀ hC₁,?_⟩
  intro W U hU t j
  have hT₀:sourceControl T₀ W.profile≤sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : T₀⊆T₀∪T₁)) W.profile
  have hT₁:sourceControl T₁ W.profile≤sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : T₁⊆T₀∪T₁)) W.profile
  have hH:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have hR:=sourceControl_nonneg (T₀∪T₁) W.profile
  by_cases hj:j=0
  · have hh:=h₀ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤_
    rw [ite_eq_left hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_right hC₁.le) hT₀ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_right _ _)) (by positivity) (by positivity)
  · have hh:=h₁ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤_
    rw [ite_eq_right hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_left hC₀.le) hT₁ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_left _ _)) (by positivity) (by positivity)

inductive Path (a b:ℝ)(ha:0<a)(T:ℝ)(W:Test a b):
    (n:ℕ)→Test (lower a b n) b→Prop
  | base : Path a b ha T W 0 W
  | next {n:ℕ}{V:Test (lower a b n) b}
      (path:Path a b ha T W n V)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2)(ht:‖t‖≤T):
      Path a b ha T W (n+1) (step _ b (lower_pos a b ha n) V U hU t j)

theorem path_control (a b:ℝ)(ha:0<a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀T:ℝ,0≤T→∀V:Test (lower a b d) b,Path a b ha T W d V→
      sourceControl S V.profile≤C*sourceControl R W.profile*(1+T)^n:=by
  induction d generalizing S with
  | zero=>
    refine ⟨0,S,1,zero_lt_one,?_⟩
    intro W T hT V hpath
    cases hpath
    simp
  | succ d ih=>
    obtain ⟨ns,Rs,Cs,hCs,hs⟩:=step_control (lower a b d) b (lower_pos a b ha d) S
    obtain ⟨np,R,Cp,hCp,hp⟩:=ih Rs
    refine ⟨np+ns,R,Cs*Cp,mul_pos hCs hCp,?_⟩
    intro W T hT V hpath
    cases hpath with
    | next old U hU t j ht=>
      rename_i V
      have h1:=hs V U hU t j
      have h2:=hp W T hT V old
      have hR:=sourceControl_nonneg R W.profile
      have h3:(1+‖t‖)^ns≤(1+T)^ns:=pow_le_pow_left₀ (by positivity) (by linarith) ns
      apply h1.trans
      apply (mul_le_mul (mul_le_mul_of_nonneg_left h2 hCs.le) h3 (by positivity) (by positivity)).trans_eq
      rw [pow_add]
      ring

lemma lower_antitone (a b:ℝ)(ha:0<a):Antitone (lower a b):=by
  apply antitone_nat_of_succ_le
  intro n
  exact div_le_self (lower_pos a b ha n).le (le_max_left _ _)

lemma support_at_depth (a b:ℝ)(ha:0<a)(d n:ℕ)(hn:n≤d)
    (V:Test (lower a b n) b):
    Function.support (V.profile:ℝ→ℂ)⊆Set.Icc (lower a b d) b:=by
  intro x hx
  exact ⟨(lower_antitone a b ha hn).trans (V.support hx).1,(V.support hx).2⟩

theorem paths_upto_control (a b:ℝ)(ha:0<a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀T:ℝ,0≤T→∀k:ℕ,k≤d→∀V:Test (lower a b k) b,
      Path a b ha T W k V→
      sourceControl S V.profile≤C*sourceControl R W.profile*(1+T)^n:=by
  choose J R C hC hbound using fun k:Fin (d+1)=>path_control a b ha k.val S
  let Rs:Finset (ℕ×ℕ):=Finset.univ.biUnion R
  let Cs:ℝ:=1+∑k,C k
  have hCs:0<Cs:=by
    have hh:=Finset.sum_nonneg (fun k (_:k∈(Finset.univ:Finset (Fin (d+1))))=>(hC k).le)
    dsimp [Cs];linarith
  refine ⟨∑k,J k,Rs,Cs,hCs,?_⟩
  intro W T hT k hk V hpath
  let l:Fin (d+1):=⟨k,by omega⟩
  have he:=hbound l W T hT V hpath
  have hR:R l⊆Rs:=by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hi⟩
  have hcontrol:sourceControl (R l) W.profile≤sourceControl Rs W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono hR) W.profile
  have hconst:C l≤Cs:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>(hC j).le)
      (Finset.mem_univ l)
    dsimp [Cs];linarith
  have hdegree:J l≤∑j,J j:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>Nat.zero_le _) (Finset.mem_univ l)
  have hRpos:=sourceControl_nonneg Rs W.profile
  apply he.trans
  exact mul_le_mul (mul_le_mul hconst hcontrol (sourceControl_nonneg _ _) hCs.le)
    (pow_le_pow_right₀ (by linarith) hdegree) (by positivity) (by positivity)

open CenteredMomentSectorLocalization in
lemma annulus_support : Function.support (fun x:ℝ=>(annulus x:ℂ))⊆Set.Icc (1/4:ℝ) 1:=by
  intro x hx
  have hn:annulus x≠0:=by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

def annulusTemplate:Test (1/4) 1 where
  profile:=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc annulus_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp CenteredMomentSectorLocalization.annulus_smooth)
  support:=annulus_support

lemma annulusTemplate_apply (x:ℝ):annulusTemplate.profile x=(CenteredMomentSectorLocalization.annulus x:ℂ):=rfl

def annulusSeed (a b:ℝ)(ha:a≤1/4)(hb:1≤b):Test a b where
  profile:=annulusTemplate.profile
  support:=fun _x hx=>⟨ha.trans (annulusTemplate.support hx).1,
    (annulusTemplate.support hx).2.trans hb⟩

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
end OAIOriginalModule2282

/-! Original module: OAI.NumberTheory.DirichletL.Energy.AllocatedProfiles
Source SHA256: e72bcb1dc265f756946435a977c11e578b701c34f673b9ca24a8bc0a1f3ec5ee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2283


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedProfiles
open CenteredMomentFiniteProfileExceptional

def retainedPair (a b:ℝ)(ha:0<a)(p:Profiles a b)
    (U:Fin 2→ℝ)(hU:∀i,0<U i)(t:ℝ):Profiles (a/max 1 b) b where
  profile:=fun i=>(sourcePlain a b ha (p.profile i) (p.support i)).profile (U i) (hU i) t
  support:=fun i=>sourcePlain_support a b ha (p.profile i) (p.support i) (U i) (hU i) t

theorem retained_pair_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀p:Profiles a b,∀U:Fin 2→ℝ,∀hU:∀i,0<U i,∀t:ℝ,
      (retainedPair a b ha p U hU t).control S≤
        C*p.control T*(1+‖t‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hbound⟩:=plain_profile_source_control a b ha S
  refine ⟨n,T,C^2,sq_pos_of_pos hC,?_⟩
  intro p U hU t
  have h₀:=hbound (p.profile 0) (p.support 0) (U 0) (hU 0) t
  have h₁:=hbound (p.profile 1) (p.support 1) (U 1) (hU 1) t
  have hp₀:=sourceControl_nonneg T (p.profile 0)
  change sourceControl S _*sourceControl S _≤_
  apply (mul_le_mul h₀ h₁ (sourceControl_nonneg _ _) (by positivity)).trans_eq
  simp only [Profiles.control,show 2*n=n+n by omega,pow_add]
  ring

end SevenEighths.CenteredMomentEnergyAllocatedProfiles

end

end OAI
end OAIOriginalModule2283

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
Source SHA256: cb7993964732415f9b8a13fd409b6b9ef3fb2576efa47098107ab7c497cf4944
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2284




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def weight (x:ℝ):ℝ:=cutoff (x/2)*(1-cutoff (4*x))

lemma weight_bounds (x:ℝ):0≤weight x ∧ weight x≤1:=by
  have h₁:=cutoff_bounds (x/2)
  have h₂:=cutoff_bounds (4*x)
  unfold weight
  constructor
  · exact mul_nonneg h₁.1 (sub_nonneg.mpr h₂.2)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ h₂.1) h₁.1).trans
      (by simpa only [mul_one] using h₁.2)

lemma weight_zero_low (x:ℝ)(hx:x≤1/8):weight x=0:=by
  rw [weight,cutoff_one (4*x) (by linarith),sub_self,mul_zero]

lemma weight_zero_high (x:ℝ)(hx:2≤x):weight x=0:=by
  rw [weight,cutoff_zero (x/2) (by linarith),zero_mul]

lemma weight_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):weight x=1:=by
  rw [weight,cutoff_one (x/2) (by linarith),cutoff_zero (4*x) (by linarith)]
  norm_num

lemma weight_support:Function.support weight⊆Set.Icc (1/8:ℝ) 2:=by
  intro x hx
  exact ⟨(lt_of_not_ge (fun h=>hx (weight_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hx (weight_zero_high x h))).le⟩

lemma weight_smooth:ContDiff ℝ ∞ weight:=by
  have hc:ContDiff ℝ ∞ cutoff:=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact (hc.comp (contDiff_id.div_const 2)).mul
    (contDiff_const.sub (hc.comp (contDiff_const.mul contDiff_id)))

def profile:𝓢(ℝ,ℂ):=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (show Function.support (fun x:ℝ=>(weight x:ℂ))⊆Set.Icc (1/8:ℝ) 2 from by
      intro x hx
      apply weight_support
      intro hz
      apply hx
      change (weight x:ℂ)=0
      rw [hz]
      rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp weight_smooth)

lemma profile_apply (x:ℝ):profile x=(weight x:ℂ):=rfl
lemma profile_nonneg (x:ℝ):0≤(profile x).re:=(weight_bounds x).1
lemma profile_le_one (x:ℝ):(profile x).re≤1:=(weight_bounds x).2
lemma profile_zero:profile 0=0:=by rw [profile_apply,weight_zero_low 0 (by norm_num)];rfl
lemma profile_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):profile x=1:=by
  rw [profile_apply,weight_one x hx hx'];rfl

lemma scaled_majorant (H q:ℝ)(hH:0<H)(hlo:H/4≤q)(hhi:q≤H):
    (profile (q/H)).re=1:=by
  rw [profile_one (q/H) ((le_div_iff₀ hH).mpr (by linarith))
    ((div_le_one hH).mpr hhi)]
  rfl

def bands (H:ℝ):Finset ℤ:=indices (H/8) (2*H)

lemma bands_scale (H:ℝ)(hH:0<H)(j:ℤ)(hj:j∈bands H):
    H/8≤dyadicScale j ∧ dyadicScale j≤8*H:=by
  have h:=(mem_indices_iff_scale (H/8) (2*H) (by positivity) (by positivity) j).mp hj
  constructor
  · exact h.1
  · linarith [h.2]

lemma bands_card (H:ℝ)(hH:0<H):((bands H).card:ℝ)≤7:=by
  have h:=indices_card_bound (H/8) (2*H) (by positivity) (by linarith)
  have he:(2*H)/(H/8)=16:=by field_simp;ring
  rw [he,show (16:ℝ)=(2:ℝ)^4 by norm_num,Real.logb_pow] at h
  norm_num [Real.logb_self_eq_one] at h
  change ((indices (H/8) (2*H)).card:ℝ)≤7
  exact_mod_cast h

lemma weighted_partition (H q:ℝ)(hH:0<H):
    (profile (q/H)).re=(∑j∈bands H,dyadicWeight j q)*(profile (q/H)).re:=by
  by_cases h:weight (q/H)=0
  · simp only [profile_apply,Complex.ofReal_re,h,mul_zero]
  · have hx:=weight_support h
    have hq:q∈Set.Icc (H/8) (2*H):=⟨by linarith [(le_div_iff₀ hH).mp hx.1],
      (div_le_iff₀ hH).mp hx.2⟩
    rw [bands,dyadic_partition_on_interval (H/8) (2*H) q (by positivity) hq]
    exact (one_mul _).symm

end SevenEighths.CenteredMomentFirstAnnularMajorant

end

end OAI
end OAIOriginalModule2284

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularEnergy
Source SHA256: 6f5ad12d32d3ab1dc8472661eb5997e0a3910456cd650d2f32930b846981e843
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2285



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSmoothedWindowEnergy
local notation "O"=>HeckeFamily.O

variable {α:Type*}

lemma dyadic_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2):=by
  have hs:=gaussEnergy_hasSum_re S a ha c CenteredMomentEnergyProfiles.annulusTemplate.profile
    (dyadicScale j) (dyadicScale_pos j)
  simpa only [CenteredMomentEnergyProfiles.annulusTemplate_apply,Complex.ofReal_re,
    dyadicWeight,normValue_eq_embedding,mul_comm] using hs.summable

lemma weighted_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    Summable (fun z:O=>‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  simpa only [normValue_eq_embedding] using (gaussEnergy_hasSum_re S a ha c profile H hH).summable

theorem energy_partition (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re=
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  have hs:=weighted_summable S a ha c H hH
  have hj (j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=by
    apply hs.of_nonneg_of_le
    · intro z
      exact mul_nonneg (dyadicWeight_bounds j _).1 (mul_nonneg (sq_nonneg _) (profile_nonneg _))
    · intro z
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (profile_nonneg _)) (dyadicWeight_bounds j _).2
  have he (z:O):‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re=
      ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
    rw [←Finset.sum_mul]
    calc
      _=‖gaussPolynomial S a ha c z‖^2*
          ((∑j∈bands H,dyadicWeight j (normValue z))*(profile (normValue z/H)).re):=by
        rw [←weighted_partition H (normValue z) hH]
      _=_:=by ring
  have hsum:=gaussEnergy_hasSum_re S a ha c profile H hH
  rw [←hsum.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  calc
    _ = ∑'z:O, ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re) :=
      tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun j _=>hj j)

theorem energy_le_dyadic (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re≤
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=by
  rw [energy_partition S a ha c H hH]
  apply Finset.sum_le_sum
  intro j hj
  have hs:=dyadic_summable S a ha c j
  have hdom (z:O):dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)≤
      dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (profile_le_one _))
      (dyadicWeight_bounds j _).1
  have hl:Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=
    hs.of_nonneg_of_le (fun z=>mul_nonneg (dyadicWeight_bounds j _).1
      (mul_nonneg (sq_nonneg _) (profile_nonneg _))) hdom
  exact hl.tsum_le_tsum hdom hs

end SevenEighths.CenteredMomentFirstAnnularEnergy

end

end OAI
end OAIOriginalModule2285

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularGeometry
Source SHA256: 52496b2a7103d44e416e86bbf3574f0c72d305843aa47af0ced0d39a488ecf6a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2286



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentFirstAnnularGeometry
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAnnularEnergy CenteredMomentGaussEnergy CanonicalQuadraticSieve

local notation "O"=>HeckeFamily.O

lemma retained_of_scale_le (j:ℤ)(R:ℝ)(h:dyadicScale j≤R):Retained R j:=by
  refine ⟨dyadicScale j/2, by exact div_pos (dyadicScale_pos j) (by norm_num), by linarith [dyadicScale_pos j], ?_⟩
  apply subset_closure
  change dyadicWeight j (dyadicScale j/2)≠0
  have he:(dyadicScale j/2)/dyadicScale j=(1/2:ℝ):=by
    field_simp [ne_of_gt (dyadicScale_pos j)]
  rw [dyadicWeight,he,annulus,cutoff_one _ (by norm_num)]
  norm_num [cutoff_zero]

lemma bands_retained (H R:ℝ)(hH:0<H)(hR:8*H≤R)(j:ℤ)(hj:j∈bands H):
    Retained R j:=retained_of_scale_le j R ((bands_scale H hH j hj).2.trans hR)

lemma bands_log_cap (H Z A:ℝ)(hH:0<H)(hZ:1<Z)(hcap:8*H≤Z^A)
    (j:ℤ)(hj:j∈bands H):Real.logb Z (dyadicScale j)≤A:=by
  have he:Real.logb Z (Z^A)=A:=Real.logb_rpow (by positivity) (ne_of_gt hZ)
  rw [←he]
  exact Real.logb_le_logb_of_le hZ (dyadicScale_pos j) ((bands_scale H hH j hj).2.trans hcap)

lemma bands_nonempty (H:ℝ)(hH:0<H):(bands H).Nonempty:=by
  by_contra hn
  have he:bands H=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  have hp:=weighted_partition H (H/2) hH
  have hr:(H/2)/H=(1/2:ℝ):=by field_simp
  rw [hr,profile_one _ (by norm_num) (by norm_num),he] at hp
  norm_num at hp

theorem common_bound {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)(hB:0≤B)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  apply (energy_le_dyadic S a ha c H hH).trans
  calc
    _≤∑j∈bands H,B:=Finset.sum_le_sum hb
    _=((bands H).card:ℝ)*B:=by simp
    _≤7*B:=mul_le_mul_of_nonneg_right (bands_card H hH) hB

theorem common_bound_auto {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  obtain ⟨j,hj⟩:=bands_nonempty H hH
  have hB:0≤B:=(tsum_nonneg (fun z=>mul_nonneg (dyadicWeight_bounds j _).1 (sq_nonneg _))).trans (hb j hj)
  exact common_bound S a ha c H B hH hB hb

end SevenEighths.CenteredMomentFirstAnnularGeometry

end

end OAI
end OAIOriginalModule2286

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularAmplification
Source SHA256: 8be1689793eebd5b897ded9e1413ce597c7797f6293de94aa021c11df1c6c983
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2287



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularAmplification
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

theorem eventually_annular_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi →
          8*H0≤Z^Mmax →
          (gaussEnergy Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            CenteredMomentFirstAnnularMajorant.profile H0).re≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentAmplificationRadicalChoice.eventually_original_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta (32*Csec) xi reserve
    hsigma hloss hM hb hgap (by linarith) hxi hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩:=hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have hsec' :32*Tsec≤(32*Csec)*firstNominalScale I J E K X:=by nlinarith
  have hfreq:8*H0≤frequencyRadius (32*Tsec) Z xi:=by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hbnd:=CenteredMomentFirstAnnularGeometry.common_bound_auto Finset.univ
    (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) H0 _ hH0 (fun j hj=>
      henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
        I J E hE K X (32*Tsec) hK hX hsec' j
        (CenteredMomentFirstAnnularGeometry.bands_retained H0 _ hH0 hfreq j hj)
        (CenteredMomentFirstAnnularGeometry.bands_log_cap H0 Z Mmax hH0 hZ hcap j hj))
  convert hbnd using 1 ; ring

end SevenEighths.CenteredMomentFirstAnnularAmplification

end

end OAI
end OAIOriginalModule2287

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput
Source SHA256: 90511d6127417660495d03f0d0f19a5dc8581b08547a64d29e829c070a94e820
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2288



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal HeckeFamily.O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

theorem normalized_child_coefficient (s:Input ι)(C R seed:Ideal HeckeFamily.O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original (child s C R B τ t) (R*C) seed).columns)
      (sourceGenerator_supported (original (child s C R B τ t) (R*C) seed).columns)
      ((original (child s C R B τ t) (R*C) seed).coefficient τ fixedBadMask t
        (volume (child s C R B τ t))) W H).re=
      childNormalizedGaussSource s C R seed B τ t W H:=
  normalized_input_coefficient (child s C R B τ t) (R*C) seed W H

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end OAIOriginalModule2288

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
Source SHA256: d2d5ca37824458061a1340d77320299902146c3a9033437fd26e1429ed696241
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2289


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=>s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=>s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=>s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

lemma original_active (s:Input ι)(R seed:Ideal HeckeFamily.O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

lemma active_volume (s:Input ι):volume (activeInput s)=volume s:=rfl

lemma active_normalized (s:Input ι)(R seed:Ideal HeckeFamily.O)(W:𝓢(ℝ,ℂ))(H:ℝ):
    normalizedGaussSource (activeInput s) R seed W H=normalizedGaussSource s R seed W H:=by
  rw [←normalized_input_coefficient,←normalized_input_coefficient,original_active]
  exact congrArg Complex.re ((original s R seed).active_gaussEnergy s.η fixedBadMask s.t (volume s) W H)

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end OAIOriginalModule2289

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification
Source SHA256: 9bf65d46e104703b3cc13d35f1d615f5eae73f1a1581803a84ca93bc57430ed4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2290



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularInput
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

theorem eventually_input_amplification {ι : Type*} [Fintype ι]
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
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                normalizedGaussSource s R seed ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)+
                ∑p : elementPool P,∑i : Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
                    ∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools
                        ((Ideal.span {p.val})^(errorIndex i+1)),
                      childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                        R seed B (τ p i χ) s.t ballProfile
                        (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                          (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
    hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have he:=henergy (original s R seed) s.pools_ne s.prime hsupp z hz hlen hR0 hs0 hR hs
    s.t (volume s) d cLog (volume_pos s) I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  rw [←hsη,normalized_input_coefficient,normalized_input_coefficient] at he
  convert he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
    (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
  have hcop:∀i,∀Q∈(activeInput s).slots i,IsCoprime (Ideal.span {p.val}) Q:=by
    exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
      hsupp (original s R seed).active_slot
      (fun i Q hQ=>s.prime i Q ((original s R seed).active_subset _ hQ))
      (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [←original_active]
  exact (original_childEnergy_eq_inputs (activeInput s) R seed (τ p i) p.val hd.1.ne_zero hcop
    (errorIndex i) s.t _).symm

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
end OAIOriginalModule2290

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstChildLower
Source SHA256: 90227d0e3bf00fb500fcf3e470b5feb4bfa3a5f27a44935243003cb631b0b21a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2291



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstChildLower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem child_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

theorem twice_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s C R B τ t).pools (Q^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=twiceChild s C R B τ t Q k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hp:=child_lower (child s C R B τ t) (Q^k) (R*C) (pow_ne_zero k hQ)
    Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hnorm:(Q.absNorm:ℝ)>0:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  have he:Real.logb Z ((Q^k).absNorm:ℝ)=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ):=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
  simpa only [he,twiceChild] using hp

theorem removed_width_cap (L c w:ℝ):
    (2/3:ℝ)*(c+w)+(2/3:ℝ)*max (L-c-w) 0≥(2/3:ℝ)*L:=by
  have h:=le_max_left (L-c-w) 0
  linarith

theorem paired_removed_width_cap (L c₁ w₁ c₂ w₂:ℝ):
    ((c₁+w₁)+(c₂+w₂))/3+
      (max (L-c₁-w₁) 0+max (L-c₂-w₂) 0)/3≥(2/3:ℝ)*L:=by
  have h₁:=le_max_left (L-c₁-w₁) 0
  have h₂:=le_max_left (L-c₂-w₂) 0
  linarith

end SevenEighths.CenteredMomentFirstChildLower

end

end OAI
end OAIOriginalModule2291

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstExceptionalChildPaid
Source SHA256: 301e5d9ba5bcb15e3e1eb5f1e24b10dd4c77f84d49c4c1fc03e0dad6549d1e28
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2292



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalChildPaid
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildLower
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstExceptionalPaidScales CenteredMomentCompleteCommon
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def inputCap (Z:ℝ)(s:Input ι):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

lemma input_cap_lower (Z r:ℝ)(hZ:1<Z)(s:Input ι)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    r ≤ inputCap Z s:=by
  have h (x:ℝ)(hx:Z^r≤x):r≤Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

lemma input_cap_scales (Z:ℝ)(hZ:1<Z)(s:Input ι):
    Z^(inputCap Z s)≤s.X₁ ∧ Z^(inputCap Z s)≤s.X₂ ∧
      Z^(inputCap Z s)≤s.Y₁ ∧ Z^(inputCap Z s)≤s.Y₂:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have h (x:ℝ)(hx:0<x)(hl:inputCap Z s≤Real.logb Z x):Z^(inputCap Z s)≤x:=by
    calc
      _≤Z^(Real.logb Z x):=Real.rpow_le_rpow_of_exponent_le hZ.le hl
      _=x:=Real.rpow_logb hz hZ.ne' hx
  refine ⟨h _ s.X₁_pos ?_,h _ s.X₂_pos ?_,h _ s.Y₁_pos ?_,h _ s.Y₂_pos ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem main_child_stage (Z A M:ℝ)(hZ:1<Z)(b:Branch Z)(hb:b.w=0)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=child s (commonPart b.I b.J) R B τ t
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤A-M+loss b:=by
  have hh:=child_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (child s (commonPart b.I b.J) R B τ t)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hb] at hs
  dsimp only
  linarith

theorem error_child_stage (Z A M:ℝ)(hZ:1<Z)(b:Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s (commonPart b.I b.J) R B τ t).pools (Q^k))
    (υ:Character)(v:ℝ)(hw:b.w=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤A-M+loss b:=by
  have hh:=twice_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Q hQ k Bp υ v Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hw] at hs
  dsimp only at hr ⊢
  linarith

theorem actual_error_pair (Z A M:ℝ)(hZ:1<Z)(b:Fin 2→Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:∀j,actualAllocations s.pools (commonPart (b j).I (b j).J))
    (τ:Fin 2→Character)(t:Fin 2→ℝ)(Q:Fin 2→Ideal O)(hQ:∀j,Q j≠0)(k:Fin 2→ℕ)
    (Bp:∀j,actualAllocations
      (child s (commonPart (b j).I (b j).J) R (B j) (τ j) (t j)).pools ((Q j)^(k j)))
    (υ:Fin 2→Character)(v:Fin 2→ℝ)
    (hw:∀j,(b j).w=(k j:ℝ)*Real.logb Z ((Q j).absNorm:ℝ))
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=fun j=>twiceChild s (commonPart (b j).I (b j).J) R
      (B j) (τ j) (t j) (Q j) (k j) (Bp j) (υ j) (v j)
    A-5*M/6-(saving (b 0)+saving (b 1))/2-
      (max (inputCap Z (d 0)) 0+max (inputCap Z (d 1)) 0)/3≤
      max (A-M) 0+(loss (b 0)+loss (b 1))/2:=by
  have h₀:=error_child_stage Z A M hZ (b 0) s R (B 0) (τ 0) (t 0) (Q 0) (hQ 0)
    (k 0) (Bp 0) (υ 0) (v 0) (hw 0) hX₁ hX₂ hY₁ hY₂
  have h₁:=error_child_stage Z A M hZ (b 1) s R (B 1) (τ 1) (t 1) (Q 1) (hQ 1)
    (k 1) (Bp 1) (υ 1) (v 1) (hw 1) hX₁ hX₂ hY₁ hY₂
  have hm:=le_max_left (A-M) (0:ℝ)
  dsimp only at h₀ h₁ ⊢
  linarith

end SevenEighths.CenteredMomentFirstExceptionalChildPaid

end

end OAI
end OAIOriginalModule2292

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedChild
Source SHA256: 61e85836ef0acf01d3ffe10f0ac08c012a4cf0b27523a9626741025e21179829
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2293



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedChild
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedCommonRadius
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool ConcreteTraceCRT
open CenteredMomentRankinRadical ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem actual_main_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (hX₁:Z^(parentM/4)≤s.X₁)(hX₂:Z^(parentM/4)≤s.X₂)
    (hY₁:Z^(parentM/4)≤s.Y₁)(hY₂:Z^(parentM/4)≤s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3≤
      parentA-parentM+4*sigma/3+5*(delta+reserve)/6 := by
  have hs:=actual_main_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  have hh:=child_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (child s (commonPart I J) Rmask B τ t)) (0:ℝ)
  dsimp only at hs hr ⊢
  linarith

theorem actual_error_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^(parentM/4)≤s.X₁)(hX₂:Z^(parentM/4)≤s.X₂)
    (hY₁:Z^(parentM/4)≤s.Y₁)(hY₂:Z^(parentM/4)≤s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3≤
      parentA-parentM+3*sigma/2+5*(delta+reserve)/6 := by
  have hs:=actual_error_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hQ:Ideal.span {p0}≠0:=Ideal.span_singleton_eq_bot.not.mpr hd.1.ne_zero
  have hh:=twice_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t (Ideal.span {p0}) hQ k Bp υ v Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) (0:ℝ)
  dsimp only at hs hr ⊢
  unfold errorRemoval normValue at hs ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedChild

end

end OAI
end OAIOriginalModule2293

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource
Source SHA256: 0929669644247a0b5dd291acbc2cfc7efec9d35298a6d506fd701fd031b232dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2294




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_frequency_radius_cap (I J:Ideal O)(E:Finset (CommonIndex I J))
    (K V Z B ξ:ℝ)(hK:0<K)(hV:0≤V)(hZ:1≤Z)
    (hVcap:V≤Z^B)(hKcap:K⁻¹≤Z^B):
    frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K V) Z ξ≤Z^(3*B+ξ/2) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hT:V^2/K≤Z^(3*B):=by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV hVcap 2) hKcap
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  unfold frequencyRadius
  calc
    _≤Z^(3*B)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      ((first_nominal_scale_le I J E K V hK).trans hT) (Real.rpow_nonneg hz.le _)
    _=_:=by rw [←Real.rpow_add hz]

theorem original_local_blocks_subpower (B Hcap ξ ε:ℝ)
    (hB:0≤B)(hHcap:0≤Hcap)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K V H:ℝ),
      0<K→0≤V→0<H→V≤Z^B→K⁻¹≤Z^B→H≤Z^Hcap→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K V) Z ξ)
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_blocks_subpower Hcap (3*B+ξ/2) 1 ε
    hHcap (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro C D hC hD E K V H hK hV hH hVcap hKcap hHbound
  exact hcount C D hC hD E K _ H hK hH
    (by simpa only [one_mul] using (local_frequency_radius_cap C D E K V Z B ξ
      hK hV hZ hVcap hKcap)) hHbound

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤hi i)(hb₁:|s.b₁|≤b₁)(hb₂:|s.b₂|≤b₂)
    (hZ:1≤Z)(hfixed:(∏i,hi i)*b₁*b₂≤Z)
    (hV:volume s.toData≤Z^B):sourceRadius s≤Z^(B+1) := by
  have hVol:0<volume s.toData:=volume_pos s.toData
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s.toData:=by
    unfold sourceRadius volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hhi i)
  have hb₁0:0≤b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

theorem original_input_local_blocks_subpower {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (volume s.toData)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_local_blocks_subpower B (B+1) ξ ε
    hB (by positivity) hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hcount hZ hfixed
  intro s hhi hb₁ hb₂ hH C D hC hD E K hK hV hKi
  exact hcount C D hC hD E K _ _ hK (volume_pos s.toData).le hH hV hKi
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)

lemma input_radius_pos_of_live {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hlive:coefficient s R seed I≠0):0<sourceRadius s := by
  obtain ⟨hI,hcap⟩:=original_column_norm s R seed I hz₁ hz₂ hlive
  exact (CenteredMomentFirstScale.norm_pos I hI).trans_le hcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
end OAIOriginalModule2294

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport
Source SHA256: 61723b988685667e0f50f90f47fbd118a46da7df132c16cdd4090c5a6b80e7e1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2295





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSourceSupport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem nonzero_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ∃a:columns C C hC.1 S,∃b:columns C D hD.1 S,
      c (C*(a:Ideal O))≠0 ∧ c (D*(b:Ideal O))≠0 ∧
      V 2 (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))≠0 ∧
      V 3 (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))≠0 := by
  unfold block at hn
  have hs:=right_ne_zero_of_mul hn
  obtain ⟨z,hz,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨a,ha,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨b,hb,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  dsimp only at hs
  split_ifs at hs with hab
  · have hprod:=left_ne_zero_of_mul (left_ne_zero_of_mul hs)
    have hc:=right_ne_zero_of_mul hprod
    have hw:=right_ne_zero_of_mul (left_ne_zero_of_mul hs)
    refine ⟨a,b,?_,?_,?_,?_⟩
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
    · have hh:=right_ne_zero_of_mul hc
      rw [star_ne_zero] at hh
      exact left_ne_zero_of_mul hh
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    · exact right_ne_zero_of_mul hw
  · exact False.elim (hs rfl)

theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(a₁ a₂:ℝ)(ha₁:0≤a₁)(ha₂:0≤a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hn:CenteredMomentOriginalCommonHarmonic.coefficient s R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  have hh:=profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ (Fintype.piFinset s.pools) I (by
      simpa only [CenteredMomentOriginalCommonHarmonic.coefficient] using hn)
  simpa only [map_one,Nat.cast_one,mul_one,div_one,volume,mul_assoc] using hh

lemma log_window_upper (N H M:ℝ)(hN:0<N)(hH:0<H)
    (hlog:|Real.log (N/H)|≤M):N≤Real.exp M*H := by
  have hl:Real.log (N/H)≤M:=(le_abs_self _).trans hlog
  have he:=Real.exp_le_exp.mpr hl
  rw [Real.exp_log (div_pos hN hH)] at he
  exact (div_le_iff₀ hH).mp he

theorem block_reference_lower (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ a T M:ℝ)
    (hA:0<A₀)(hB:0<B₀)(hsource:∀I,c I≠0→a*T≤(I.absNorm:ℝ))
    (hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    a*T≤(C.absNorm:ℝ)*Real.exp M*A₀ ∧
      a*T≤(D.absNorm:ℝ)*Real.exp M*B₀ := by
  obtain ⟨i,j,hi,hj,hwi,hwj⟩:=nonzero_columns η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀ hn
  have hiN:(0:ℝ)<(i:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C C hC.1 S i).1)
  have hjN:(0:ℝ)<(j:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD.1 S j).1)
  have hni:‖eisEmbedding (element C C hC.1 S i)‖^2=((i:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hnj:‖eisEmbedding (element C D hD.1 S j)‖^2=((j:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hli:=hwin 2 _ hwi
  have hlj:=hwin 3 _ hwj
  rw [hni] at hli
  rw [hnj] at hlj
  have hsi:=hsource _ hi
  have hsj:=hsource _ hj
  simp only [map_mul,Nat.cast_mul] at hsi hsj
  constructor
  · exact hsi.trans (by nlinarith [log_window_upper _ _ M hiN hA hli])
  · exact hsj.trans (by nlinarith [log_window_upper _ _ M hjN hB hlj])

lemma reference_sqrt_lower (NC ND A₀ B₀ a T M:ℝ)
    (hNC:0≤NC)(hND:0≤ND)(hA:0≤A₀)(_hB:0≤B₀)(ha:0≤a)(hT:0≤T)
    (hl:a*T≤NC*Real.exp M*A₀)(hr:a*T≤ND*Real.exp M*B₀):
    a*T≤Real.exp M*Real.sqrt (NC*ND)*(Real.sqrt A₀*Real.sqrt B₀) := by
  have hh:=mul_le_mul hl hr (mul_nonneg ha hT) (by positivity : 0≤NC*Real.exp M*A₀)
  have hs:(a*T)^2≤(NC*ND)*(Real.exp M)^2*(A₀*B₀):=by nlinarith [hh]
  have hsqrt:=Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (mul_nonneg ha hT),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hNC hND) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hNC hND),Real.sqrt_sq (Real.exp_pos M).le,
    Real.sqrt_mul hA] at hsqrt
  nlinarith [hsqrt]

theorem scalar_volume_bound (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0≤a)(hT:0≤T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*(a*T)≤
      Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha hT hl hr
  have hden:0<Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:(a*T)/(Real.sqrt A₀*Real.sqrt B₀)≤Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm):=
    (div_le_iff₀ hden).mpr hs
  have hmu:‖inactiveWeight C D E‖≤1:=QuadraticInitialBound.norm_ideal_moebius_le_one _
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*((a*T)/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _≤_:=by
      have hh:=mul_le_mul_of_nonneg_right hmu (show 0≤K/(‖eisEmbedding
        (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖)*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)) by positivity)
      convert hh using 1 <;> ring

theorem original_scalar_volume {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ M:ℝ)
    (hK:0<K)(hA:0<A₀)(hB:0<B₀)(hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData≤
      (Real.exp M/((∏i,s.lo i)*a₁*a₂))*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  let a:ℝ:=(∏i,s.lo i)*a₁*a₂
  have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  have hV:0<volume s.toData:=volume_pos s.toData
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ a (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  have hh:=scalar_volume_bound C D hC E K A₀ B₀ a (volume s.toData) M hK hA hB ha.le hV.le hl hr
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*(a*volume s.toData))/a:=by field_simp
    _≤(Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))/a:=div_le_div_of_nonneg_right hh ha.le
    _=_:=by dsimp only [a];ring

end SevenEighths.CenteredMomentFirstPhysicalSourceSupport

end

end OAI
end OAIOriginalModule2295

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
Source SHA256: 95ca8bf1c6f3692ebb2c7d1f55a3f71b0304ce0d95126be146277705b9ea03bc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2296



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstNonexceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalSourceSupport
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstActiveRadicalBudget CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSupportedCorrelation
local notation "O"=>ActualEisensteinCubic.O

lemma pair_conductor_root (q₁ q₂ B:ℝ)(_h₁:0≤q₁)(h₂:0≤q₂)
    (hB:0≤B)(hb₁:q₁≤B)(hb₂:q₂≤B):Real.sqrt (q₁*q₂)≤B := by
  have hh:=mul_le_mul hb₁ hb₂ h₂ hB
  have hs:=Real.sqrt_le_sqrt hh
  simpa only [←pow_two,Real.sqrt_sq hB] using hs

lemma scalar_conductor_algebra (s μ K T N E r C F q q₁ q₂:ℝ)
    (_hs:0≤s)(hμ:0≤μ)(hK:0≤K)(_hT:0<T)(hN:0<N)(hE:0<E)(hr:0<r)
    (hC:0≤C)(hF:0≤F)(hq:0≤q)(h₁:0≤q₁)(h₂:0≤q₂)
    (hscalar:s*T≤μ*C*K*Real.sqrt N/(E*r))
    (hc₁:q₁≤F*q*E*r^2)(hc₂:q₂≤F*q*E*r^2):
    s*T/N*Real.sqrt (q₁*q₂)≤μ*C*F*K*q*(r/Real.sqrt N) := by
  have hroot:=pair_conductor_root q₁ q₂ (F*q*E*r^2) h₁ h₂ (by positivity) hc₁ hc₂
  calc
    _≤(μ*C*K*Real.sqrt N/(E*r))/N*(F*q*E*r^2):=
      mul_le_mul (div_le_div_of_nonneg_right hscalar hN.le) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _=μ*C*F*K*q*(r/Real.sqrt N):=by
      have hn:Real.sqrt N≠0:=ne_of_gt (Real.sqrt_pos.mpr hN)
      have hn2:=Real.sq_sqrt hN.le
      field_simp
      linear_combination μ*C*K*F*q*hn2

theorem weighted_scalar_volume (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha.le hT.le hl hr
  have hden:0<Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:T/(Real.sqrt A₀*Real.sqrt B₀)≤Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a:=by
    apply (div_le_div_iff₀ hden ha).mpr
    nlinarith [hs]
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(T/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _=_:=by ring

theorem actual_scalar_conductors (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(η τ₁ τ₂:Character)
    (K A₀ B₀ a T M F:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)(hF:0≤F)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*F*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have hN:0<(C.absNorm:ℝ)*D.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hh:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) F (η.modulus.absNorm:ℝ)
    (τ₁.modulus.absNorm:ℝ) (τ₂.modulus.absNorm:ℝ) (norm_nonneg _) (norm_nonneg _)
    hK.le hT hN (sq_pos_of_pos he) hrpos (by positivity) hF (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr) hc₁ hc₂
  have hroot:=active_root_le_radical C D hC.1 hD.1
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at hroot
  exact hh.trans ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))

theorem original_scalar_conductors {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M F:ℝ)(τ₁ τ₂:Character)
    (hK:0<K)(hA:0<A₀)(hB:0<B₀)(hF:0≤F)(hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_conductors C D hC hD E s.η τ₁ τ₂ K A₀ B₀ _ _ M F hK hA hB
    ha (volume_pos s.toData) hF hl hr hc₁ hc₂

end SevenEighths.CenteredMomentFirstNonexceptionalPrefactor

end

end OAI
end OAIOriginalModule2296

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
Source SHA256: 56d6766b447d60e60cdfb92c43edb06f05da2de3cded37266b5b20d903f7dfac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2297



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentFirstScale IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

lemma commonPart_of_equal_support (C D:Ideal O)(hC:C≠0)
    (hCD:primeSupport C=primeSupport D):commonPart C D=C := by
  have he:commonPart C D=commonPart C C:=by
    simp only [commonPart,commonSupport,←hCD]
  exact he.trans (commonPart_self C hC)

lemma nominal_equal_support (C D E:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(K V:ℝ):
    firstNominalScale C D E K V=
      (E.absNorm:ℝ)*(Ideal.span {activeConductor C D}).absNorm*V^2/
        (K*(C.absNorm:ℝ)*D.absNorm) := by
  rw [firstNominalScale,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

theorem actual_scalar_exceptional (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a V M Z j g:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)
    (ha:0<a)(hV:0<V)(hZ:1<Z)
    (hl:a*V≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*V≤(D.absNorm:ℝ)*Real.exp M*B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let NE:ℝ:=(Ideal.span {e}).absNorm;
    let NR:ℝ:=(Ideal.span {activeConductor C D}).absNorm;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (V/(C.absNorm:ℝ))^((2:ℝ)/3)*(V/(D.absNorm:ℝ))^((2:ℝ)/3)*
        (Z^(j+g))^((5:ℝ)/6) ≤
    ‖inactiveWeight C D E‖*(Real.exp M/a)*
      (V*K^((1:ℝ)/6)*NR^((1:ℝ)/3)/(NE^((1:ℝ)/6)*(C.absNorm:ℝ)*D.absNorm)*
        Z^(5*(j-Real.logb Z (firstNominalScale C D (Ideal.span {e}) K V)+g)/6)) := by
  dsimp only
  have hNE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hNR:=active_norm_pos C D
  have hNC:=norm_pos C hC.1
  have hND:=norm_pos D hD.1
  have hroot:Real.sqrt ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      ‖eisEmbedding (activeConductor C D)‖:=by
    rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  have hs:=weighted_scalar_volume C D hC E K A₀ B₀ a V M hK hA hB ha hV hl hr
  rw [eisEmbedding_norm_sq_eq_absNorm_span,←hroot] at hs
  have hh:=scalar_exceptional_bound _ _ (Real.exp M/a) K V _ _ _ _ Z j g
    hK hV hNE hNR hNC hND hZ hs
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_scalar_exceptional {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z j g:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let NE:ℝ:=(Ideal.span {e}).absNorm;
    let NR:ℝ:=(Ideal.span {activeConductor C D}).absNorm;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (V/(C.absNorm:ℝ))^((2:ℝ)/3)*(V/(D.absNorm:ℝ))^((2:ℝ)/3)*
        (Z^(j+g))^((5:ℝ)/6) ≤
    ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*
      (V*K^((1:ℝ)/6)*NR^((1:ℝ)/3)/(NE^((1:ℝ)/6)*(C.absNorm:ℝ)*D.absNorm)*
        Z^(5*(j-Real.logb Z (firstNominalScale C D (Ideal.span {e}) K V)+g)/6)) := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_exceptional C D hC hD hCD E K A₀ B₀ _ _ M Z j g
    hK hA hB ha (volume_pos s.toData) hZ hl hr

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI
end OAIOriginalModule2297

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
Source SHA256: 7d222fa3b564c52b72034c04dc7688bd5dee383c5a18c800f0413d6826cc4a4f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2298




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedRoot
open CanonicalQuadraticSieve CenteredMomentFirstMixedAllowance
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CenteredMomentFirstScale CenteredMomentSupportedCorrelation
local notation "O"=>HeckeFamily.O

lemma active_span_swap (C D:Ideal O):
    Ideal.span {activeConductor D C}=Ideal.span {activeConductor C D}:=by
  rw [activeConductor_span_filter,activeConductor_span_filter,
    CenteredMomentCompleteCommon.commonSupport_comm D C]
  congr 1
  apply Finset.filter_congr
  intro P hP
  simp only [CenteredMomentActive.netExponent]
  omega

lemma allowance_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+allowance D C Z≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=by
  have hh:=actual_allowance_sum C D hC hD hCD Z hZ
  simpa only [allowance,active_span_swap C D] using hh

lemma allowance_root (Z C D P R b:ℝ)(hZ:1<Z)(hC:0<C)(hD:0<D)(hP:0<P)(hR:0<R)
    (hb:b≤Real.logb Z C+Real.logb Z D-2*Real.logb Z P-Real.logb Z R):
    Real.sqrt R/Real.sqrt (C*D)*Z^(b/2)≤1/P:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hlz:0<Real.log Z:=Real.log_pos hZ
  have hb':b≤(Real.log C+Real.log D-2*Real.log P-Real.log R)/Real.log Z:=by
    convert hb using 1 ; simp only [Real.logb] ; ring
  have hh: b*Real.log Z≤Real.log C+Real.log D-2*Real.log P-Real.log R:=
    (le_div_iff₀ hlz).mp hb'
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_sqrt,
    Real.log_rpow,Real.log_one]
  nlinarith

lemma paired_reference_root (qL qR V C D Z bL bR EL ER:ℝ)
    (hqL:0<qL)(hqR:0<qR)(hV:0<V)(hC:0<C)(hD:0<D)(hZ:0<Z)
    (_hEL:0≤EL)(_hER:0≤ER):
    Real.sqrt ((qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2)*Real.sqrt (EL*ER):=by
  have hbase:Real.sqrt ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))=
      V^2/(C*D)*Real.sqrt (qL*qR)*Z^((bL+bR)/2):=by
    apply Real.log_injOn_pos
    · simp only [Set.mem_Ioi];positivity
    · simp only [Set.mem_Ioi];positivity
    · simp (disch := positivity) only [Real.log_sqrt,Real.log_mul,Real.log_div,
        Real.log_pow,Real.log_rpow]
      ring
  rw [show (qL*(V/C)^2*Z^bL*EL)*(qR*(V/D)^2*Z^bR*ER)=
    ((qL*(V/C)^2*Z^bL)*(qR*(V/D)^2*Z^bR))*(EL*ER) by ring,
    Real.sqrt_mul (by positivity),hbase]

theorem actual_fixed_reference_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(η:Character)(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair η C D hC E ξ₁ ξ₂)
    (K A₀ B₀ a T M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)
    (ha:0<a)(hT:0<T)(hZ:1<Z)(hEL:0≤EL)(hER:0≤ER)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖/T*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(T/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(T/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have hF:0<fixedPresentationCost:=fixedPresentationCost_pos
  have hNC:0<(C.absNorm:ℝ):=norm_pos C hC.1
  have hND:0<(D.absNorm:ℝ):=norm_pos D hD.1
  have hNR:0<((Ideal.span {activeConductor C D}).absNorm:ℝ):=active_norm_pos C D
  have hP:0<((commonRadical C D).absNorm:ℝ):=norm_pos _ (commonRadical_ne_zero C D)
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hs:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) fixedPresentationCost
    (η.modulus.absNorm:ℝ) (F.left.modulus.absNorm:ℝ) (F.right.modulus.absNorm:ℝ)
    (norm_nonneg _) (norm_nonneg _) hK.le hT (mul_pos hNC hND)
    (sq_pos_of_pos he) hrpos (by positivity) fixedPresentationCost_pos.le (Nat.cast_nonneg _)
    hqL.le hqR.le (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr)
    F.conductor_caps.1 F.conductor_caps.2
  have haR:=allowance_root Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((commonRadical C D).absNorm:ℝ) ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    (allowance C D Z+allowance D C Z) hZ hNC hND hP hNR
    (allowance_pair C D hC hD hCD Z hZ)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at haR
  rw [paired_reference_root _ _ T _ _ Z _ _ EL ER hqL hqR hT hNC hND
    (zero_lt_one.trans hZ) hEL hER]
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=by
      field_simp
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)*
        (‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _=(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        ((‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*
          Z^((allowance C D Z+allowance D C Z)/2))*Real.sqrt (EL*ER):=by ring
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        (1/(commonRadical C D).absNorm)*Real.sqrt (EL*ER):=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR (by positivity))
        (Real.sqrt_nonneg _)
    _=_:=by ring

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

theorem original_fixed_reference_pair {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:0≤EL)(hER:0≤ER)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E s.η ξ₁ ξ₂ F
    K A₀ B₀ _ _ M Z EL ER hK hA hB ha (volume_pos s.toData) hZ hEL hER hl hr

end SevenEighths.CenteredMomentFirstMixedRoot

end

end OAI
end OAIOriginalModule2298

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual
Source SHA256: a5fd935a10f3b2b825f3c7754b0b5a22996d9ad6affbb3f4a908b167d2ae3587
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2299



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalizationActual
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedAllowance
open CenteredMomentDescentLedger CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O"=>HeckeFamily.O

theorem actual_reference_width (η τ:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(K Z:ℝ)(_hK:0<K)(_hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    Real.logb Z K+Real.logb Z (τ.modulus.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost:=by
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hq:=norm_pos _ η.modulus_ne_bot
  have hfixed:=fixedPresentationCost_pos
  rw [fixed_presentation_norm η τ C D E hmod]
  simp only [eisEmbedding_norm_sq_eq_absNorm_span]
  simp (disch := positivity) only [Real.logb_mul]
  ring

theorem actual_exceptional_reference (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g w wo ell:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*Z^(-wo)*(V/(C.absNorm:ℝ)/Z^w)^((1:ℝ)/3)*
      (Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo (allowance C D Z) g ell):=by
  have hh:=exceptional_reference_identity Z V (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)
    ((Ideal.span {activeConductor C D}).absNorm:ℝ) K (τ.modulus.absNorm:ℝ)
    w wo (allowance C D Z) j g ell hZ hV (norm_pos C hC.1) (norm_pos D hD.1)
    (norm_pos _ (subsetGenerator_supported C D hC E).1) (active_norm_pos C D) hK
    (norm_pos _ τ.modulus_ne_bot)
  dsimp only at hh ⊢
  rw [actual_reference_width η τ C D hC E K Z hK hZ hmod] at hh
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

theorem actual_error_reference_le (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*
      (V/(C.absNorm:ℝ)/(normValue p)^k)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) (errorRemoval p Z k) q
        (errorMoving p Z k) (allowance C D Z) g 0):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hCpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hnpos:=normValue_pos p hp
  have hh:=actual_exceptional_reference η τ C D hC hD hCD E K V Z j g
    (errorRemoval p Z k) (errorMoving p Z k) 0 hK hV hZ hmod
  dsimp only at hh ⊢
  rw [errorRemoval_power p hp Z hZ k,neg_zero,Real.rpow_zero,mul_one] at hh
  rw [←hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (actual_error_weight p hp Z hZ k hk) (by positivity)

end SevenEighths.CenteredMomentFirstMixedNormalizationActual

end

end OAI
end OAIOriginalModule2299

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityRadius
Source SHA256: f3c9be97833a1e5c8d78894c0c784815071f12145050d9e451012fbd19d1e640
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2300



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacityRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstPhysicalSource
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstCanonicalFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadiusSaving
local notation "O"=>HeckeFamily.O

lemma enlarged_gain_extraction (c d w wo sigma branch delta reserve:ℝ)
    (_hw:0≤w)(hwo:wo≤2*w):
    -d+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve≤
      -min c d+branch*sigma+delta+reserve := by
  have h:max (d-c-2*w+wo) 0≤d-min c d:=by
    apply max_le <;> linarith [min_le_left c d,min_le_right c d]
  linarith

theorem actual_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red w wo cost gain:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0<red)(hcost:0<cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (Z^(K0+gain))-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^wo)-Real.logb Z (V/(red*Z^w))=
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        Real.logb Z red-c-d+gain+w-wo-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hc:=norm_pos C hC.1
  have hd:=norm_pos D hD.1
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hE:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR:=active_norm_pos C D
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  dsimp only
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
    Real.logb_rpow hz hZ.ne'] at hh ⊢
  norm_num at hh ⊢
  linarith

theorem actual_main_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0<red)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-
      Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z (V/red)≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+2*sigma+delta+reserve-
        Real.logb Z fixedPresentationCost := by
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red 0 0 1
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)) 0+2*sigma+delta+reserve)
    hK hV hZ hred (by norm_num) hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) 0 0 sigma 2 delta reserve (by norm_num) (by norm_num)
  dsimp only at hh ⊢
  simp only [Real.rpow_zero,mul_one,one_mul,Real.logb_one,add_zero,sub_zero] at hh hg
  change _≤_
  rw [mainCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  norm_num at hg
  linarith

theorem actual_error_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve cost:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hred:0<red)(hcost:0<cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p)):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (V/(red*Z^(errorRemoval p Z k)))≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+6*errorRemoval p Z k+delta+reserve-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hw:0≤errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:errorMoving p Z k≤2*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have he:sigma+errorRemoval p Z k-errorMoving p Z k≤6*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red
    (errorRemoval p Z k) (errorMoving p Z k) cost
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-
      2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+delta+reserve)
    hK hV hZ hred hcost hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
    sigma 1 delta reserve hw hwo
  dsimp only at hh ⊢
  simp only [one_mul] at hg
  rw [errorCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacityRadius

end

end OAI
end OAIOriginalModule2300

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalCap
Source SHA256: a1b901062818d310d81792ad776617ba7ca8963055748707dc2186e3609c89b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2301



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalCap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma fixed_presentation_log_nonneg (Z:ℝ)(hZ:1<Z):0≤Real.logb Z fixedPresentationCost:=by
  have h₁:(1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h₂:(1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
  apply Real.logb_nonneg hZ
  unfold fixedPresentationCost
  nlinarith

lemma extracted_allowance_eq (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(Z:ℝ):extractedAllowance C D Z=allowance C D Z:=by
  simp only [extractedAllowance,allowance,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

theorem actual_main_exceptional_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t:ℝ)(hK:0<K)(hX:0<X)(_hvolume:X=volume s)
    (hX₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₁)(hX₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₂)
    (hY₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₁)(hY₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₂) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_child_stage η τ fixedBadMask I J E hI hJ A K X Z j sigma delta reserve hZ hmod s Rmask B t (Real.logb Z X) (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)) hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0<mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t:ℝ)(hK:0<K)(hX:0<X)(_hvolume:X=volume s)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₁)(hX₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₂)
    (hY₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₁)(hY₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₂) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_child_stage η τ fixedBadMask I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk s Rmask B t (Real.logb Z X) (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)) Bp υ v hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedExceptionalCap

end

end OAI
end OAIOriginalModule2301

/-! Original module: OAI.NumberTheory.DirichletL.Energy.FirstHighExceptionalPowers
Source SHA256: 5df9067a2160c6b1ed5072998c0df2c8dedc83410d6ad41526cff9315d943a79
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2302




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstHighExceptionalPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

theorem actual_main_exceptional_uniform_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve Mdecl : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0 := le_max_right _ _
  have hrLower:=le_max_left (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) (0:ℝ)
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0<mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_uniform_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve Mdecl : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0 := le_max_right _ _
  have hrLower:=le_max_left (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) (0:ℝ)
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end SevenEighths.CenteredMomentEnergyFirstHighExceptionalPowers

end

end OAI
end OAIOriginalModule2302

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedDiagonal
Source SHA256: fa9cccf093fa2b95cce0312b24265a3e6f333660d8241ba29bbc973592325a67
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2303


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedDiagonal
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedExceptionalCap
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstExceptionalPrefactor CenteredMomentDescentLedger
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O

theorem actual_common_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z w wo branch sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hw:0≤w)(hwo:0≤wo)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=nominalLog C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    (V/(C.absNorm:ℝ))*Z^(-wo)*
      Z^(K0+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve)*
      (V/(C.absNorm:ℝ)/Z^w)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        branch*sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hnc:=norm_pos C hC.1
  have hnd:=norm_pos D hD.1
  have hne:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hnr:=active_norm_pos C D
  have hnq:=norm_pos _ τ.modulus_ne_bot
  have hη:=norm_pos _ η.modulus_ne_bot
  have hf:=fixedPresentationCost_pos
  have hc:0≤Real.logb Z (C.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
  have hd:0≤Real.logb Z (D.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have hallow:=allowance_nonneg C D Z
  have hfix:=fixed_presentation_log_nonneg Z hZ
  have hm:max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-2*w+wo) 0≤
      Real.logb Z (D.absNorm:ℝ)+wo:=max_le (by linarith) (by linarith)
  have he:eps*(Real.logb Z (C.absNorm:ℝ)+w)≥0:=mul_nonneg heps (add_nonneg hc hw)
  have hq:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  have hnom:nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z=
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+2*Real.logb Z V-
      Real.logb Z K-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ):=by
    rw [nominalLog,nominal_equal_support C D _ hC.1 hD.1 hCD K V]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
    ring
  dsimp only
  apply (Real.logb_le_iff_le_rpow hZ (by positivity)).mp
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_rpow hz hZ.ne',Real.logb_rpow_eq_mul_logb_of_pos,Real.logb_pow]
  rw [hnom]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hq,hm,he,hfix,hallow]

theorem actual_main_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (V/(C.absNorm:ℝ))*mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve*(V/(C.absNorm:ℝ))^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve+eps*Real.logb Z V):=by
  simpa only [mainCommonRadius,zero_mul,mul_zero,sub_zero,add_zero,neg_zero,
    Real.rpow_zero,mul_one,div_one] using
    actual_common_diagonal η τ C D hC hD hCD E K V Z 0 0 2 sigma delta reserve eps
      hK hV hZ (le_refl _) (le_refl _) heps hmod

theorem actual_error_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k*(V/(C.absNorm:ℝ)/(normValue p)^k)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hcpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hl:0≤Real.logb Z (normValue p):=Real.logb_nonneg hZ (normValue_ge_one p hp)
  have hw:0≤errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:0≤errorMoving p Z k:=by unfold errorMoving;split_ifs <;> positivity
  have hh:=actual_common_diagonal η τ C D hC hD hCD E K V Z
    (errorRemoval p Z k) (errorMoving p Z k) 1 sigma delta reserve eps hK hV hZ hw hwo heps hmod
  dsimp only at hh
  rw [one_mul,errorRemoval_power p hp Z hZ k] at hh
  apply le_trans ?_ hh
  unfold errorCommonRadius
  gcongr
  exact actual_error_weight p hp Z hZ k hk

end SevenEighths.CenteredMomentFirstMixedDiagonal

end

end OAI
end OAIOriginalModule2303

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalLow
Source SHA256: d03293d9714f49143b6f572d4282894481d7a3ccfc6419948d77076546943d5f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2304




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalLow
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

theorem actual_main_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0<mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_main_exceptional_low (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (hLow : Real.logb Z X ≤ 5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(4*sigma/3+5*(delta+reserve)/6) := by
  apply (actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX).trans
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem actual_error_exceptional_low (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (hLow : Real.logb Z X ≤ 5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(3*sigma/2+5*(delta+reserve)/6) := by
  apply (actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX).trans
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

end SevenEighths.CenteredMomentFirstMixedExceptionalLow

end

end OAI
end OAIOriginalModule2304

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalDeclared
Source SHA256: a7853dd0c5962258178ce8f28982430b72d96a70f6769a75008580761a424282
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2305


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalDeclared
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

open CenteredMomentFirstMixedExceptionalLow

theorem actual_main_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+4*sigma/3+5*(delta+reserve)/6) := by
  have hh:=actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+3*sigma/2+5*(delta+reserve)/6) := by
  have hh:=actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

end SevenEighths.CenteredMomentFirstMixedExceptionalDeclared

end

end OAI
end OAIOriginalModule2305

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedMainError
Source SHA256: 6994139a70973718f33a9a7e86ffbda4d5ce013517390b012ab004b0b3a6e740
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2306



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedMainError
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstMixedNormalization CenteredMomentFirstSourceConductorCaps
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_error_conductor_weight (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)):
    localErrorCost p n*(υ.modulus.absNorm:ℝ)≤rayCost*(ρ.modulus.absNorm:ℝ):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hcap:(υ.modulus.absNorm:ℝ)≤
      rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
    apply hN.trans
    have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
        (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
    calc
      _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          Z^(errorMoving p Z (n+1)):=by gcongr
      _=_:=by unfold rayCost fixedPresentationCost;ring
  have hk:n+1=1 ∨ n+1=6 ∨ n+1=7:=by omega
  have hc:=actual_error_weight p hp Z hZ (n+1) hk
  simp only [Nat.add_sub_cancel] at hc
  have hh:=mul_le_mul hc hcap (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  apply hh.trans_eq
  calc
    _=(rayCost*(ρ.modulus.absNorm:ℝ))*(Z^(-errorMoving p Z (n+1))*Z^(errorMoving p Z (n+1))):=by ring
    _=_:=by rw [←Real.rpow_add (zero_lt_one.trans hZ),neg_add_cancel,Real.rpow_zero,mul_one]

theorem actual_main_error_reference (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z V C B E:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hE:0≤E)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)):
    (V/C)*localErrorCost p n*(υ.modulus.absNorm:ℝ)*(V/C/(normValue p)^(n+1))*E/
      ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B)≤
      rayCost*Z^(-errorRemoval p Z (n+1)-B)*E:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hq:0<(ρ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ρ.modulus_ne_bot)
  have hh:=actual_error_conductor_weight ρ υ χ p hp n hn Z hZ hυ
  calc
    _=((V/C)*(localErrorCost p n*(υ.modulus.absNorm:ℝ))*(V/C/(normValue p)^(n+1))*E)/
        ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B):=by ring
    _≤((V/C)*(rayCost*(ρ.modulus.absNorm:ℝ))*(V/C/(normValue p)^(n+1))*E)/
        ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B):=by gcongr
    _=rayCost*Z^(-errorRemoval p Z (n+1)-B)*E:=by
      rw [Real.rpow_sub hz,Real.rpow_neg hz.le,errorRemoval_power p hp Z hZ (n+1)]
      field_simp

end SevenEighths.CenteredMomentFirstMixedMainError

end

end OAI
end OAIOriginalModule2306

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport
Source SHA256: 261bd6f4d5c0ab7c91d371225f547f14312399d21ff5f3a02699ac930e6fbb83
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2307




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedRightTransport
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstPhysicalSource CenteredMomentFirstMixedRoot
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstMixedCommonRadius CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius CenteredMomentDescentLedger
local notation "O" => ActualEisensteinCubic.O

def swapIndex (C D : Ideal O) : CommonIndex C D ≃ CommonIndex D C where
  toFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  invFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma swapIndex_val (C D : Ideal O) (P : CommonIndex C D) :
    (swapIndex C D P).val=P.val := rfl

def swapSubset (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Finset (CommonIndex D C) := E.map (swapIndex C D).toEmbedding

lemma swapSubset_product (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    (∏P∈swapSubset C D E,P.val)=∏P∈E,P.val := by
  simp only [swapSubset,Finset.prod_map,Equiv.toEmbedding_apply,swapIndex_val]

lemma swapSubset_generator (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    primeSubsetGenerator (fun P : CommonIndex D C=>P.val) (swapSubset C D E)=
      primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E := by
  unfold primeSubsetGenerator
  rw [swapSubset_product]

lemma swapSubset_inactive (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    swapSubset C D E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets D C ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D := by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp := h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (CenteredExceptionalCount.valuation D P.val + 5 * CenteredExceptionalCount.valuation C P.val) % 6 = 0 at hp'
    change (CenteredExceptionalCount.valuation C P.val + 5 * CenteredExceptionalCount.valuation D P.val) % 6 = 0
    omega
  · intro h P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_map.mp hP
    have hq := (Finset.mem_filter.mp (h hQ)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (CenteredExceptionalCount.valuation C Q.val + 5 * CenteredExceptionalCount.valuation D Q.val) % 6 = 0 at hq
    change (CenteredExceptionalCount.valuation D Q.val + 5 * CenteredExceptionalCount.valuation C Q.val) % 6 = 0
    omega

lemma swapped_modulus_factor (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
      (swapSubset C D E)*activeConductor D C}=
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} := by
  rw [swapSubset_generator,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_mul_span_singleton,active_span_swap]

theorem right_modulus (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayFourExpansion.RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    F.right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
        (swapSubset C D E)*activeConductor D C} := by
  rw [swapped_modulus_factor]
  exact F.right_modulus

lemma nominal_swap (C D E : Ideal O) (K X : ℝ) :
    firstNominalScale D C E K X=firstNominalScale C D E K X := by
  unfold firstNominalScale
  rw [active_span_swap]
  congr 1
  ring

lemma nominalLog_swap (C D E : Ideal O) (K X Z : ℝ) :
    nominalLog D C E K X Z=nominalLog C D E K X Z := by
  unfold nominalLog
  rw [nominal_swap]

theorem right_main_saving (η : Character) (C D E0 : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z) :
    let c := Real.logb Z ((commonPart D C).absNorm:ℝ)
    let d := Real.logb Z ((commonPart C D).absNorm:ℝ)
    let K0 := nominalLog C D E0 K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (F.right.modulus.absNorm:ℝ)) 0
        (extractedAllowance D C Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  simpa only [nominalLog_swap] using
    actual_main_column_saving η F.right fixedBadMask D C E0 hD hC (swapSubset C D E)
      K X Z j sigma delta reserve hZ (right_modulus η C D hC E ξ₁ ξ₂ F)

theorem right_error_saving (η : Character) (C D E0 : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayFourExpansion.RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart D C).absNorm:ℝ)
    let d := Real.logb Z ((commonPart C D).absNorm:ℝ)
    let K0 := nominalLog C D E0 K X Z
    2*(c+errorRemoval p Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p Z k) (Real.logb Z (F.right.modulus.absNorm:ℝ))
        (errorMoving p Z k) (extractedAllowance D C Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j) 0 := by
  simpa only [nominalLog_swap] using
    actual_error_column_saving η F.right fixedBadMask D C E0 hD hC (swapSubset C D E)
      K X Z j sigma delta reserve hZ (right_modulus η C D hC E ξ₁ ξ₂ F)
      M H Sbad hbad p hp k hk

end SevenEighths.CenteredMomentFirstMixedRightTransport

end

end OAI
end OAIOriginalModule2307

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalWeightSum
Source SHA256: 2f80e52f9690763995f2ee57a316d63b7bec6f39605e38359198a1d305c8a21a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2308



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

def weight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):ℝ:=
  let h:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  if block s.η m A t (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) p.val.1 p.val.2 h.1 h.2 E
      (CenteredMomentSecondRetainedRows.retainedRows r 1) W V K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0 then 0
  else ‖scalar p.val.1 p.val.2 h.1 E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*
    volume s.toData/((p.val.1.absNorm:ℝ)*p.val.2.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)

theorem weight_le (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r a₁ a₂ M F:ℝ)(hK:0<K)(ha₁:0<a₁)(ha₂:0<a₂)(hF:0≤F)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hwin:∀i y,V i y≠0→|y|≤M)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(τ₁ τ₂:Character)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):
    weight s R seed m A t W V K r p E τ₁ τ₂ n≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
        (CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
          (commonRadical p.val.1 p.val.2).absNorm):=by
  have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  unfold weight
  dsimp only
  split_ifs with hn
  · exact mul_nonneg (by positivity)
      (div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _)
        (Nat.cast_nonneg _))
  · have hh:=original_scalar_conductors s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ m A t _
      p.val.1 p.val.2 hp.1 hp.2 E _ W V K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) M F τ₁ τ₂ hK
      (dyadicScale_pos _) (dyadicScale_pos _) hF hwin hn hc₁ hc₂
    convert hh using 1 ;
      simp only [CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,
        div_one,CenteredMomentFirstPhysicalSource.inactiveWeight] ; ring

def sectorWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character):ℝ:=
  ∑n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
    weight s R seed m A t W V K r p E τ₁ τ₂ n

def sumWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K:ℝ)(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
    (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character):ℝ:=
  ∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
    sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)

theorem original_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M F:ℝ),
      0<K→0<a₁→0<a₂→0≤F→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
      (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character),
      (∀p E,radius p E≤Cr*Z^L)→
      (∀p E,((τ₁ p E).modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
        ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
        ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)→
      (∀p E,((τ₂ p E).modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
        ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
        ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)→
      sumWeight s R seed m A t W V K radius τ₁ τ₂≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨Cd,hCd,hd⟩:=original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=CenteredMomentFirstInactiveRadicalMass.actual_inactive_radical_mass
    B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M F
    hK ha₁ ha₂ hF hs₁ hs₂ hwin radius τ₁ τ₂ hr hc₁ hc₂
  let P:ℝ:=(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  have hP:0≤P:=by dsimp [P];positivity
  let f:=fun (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))=>
    CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
      (commonRadical p.val.1 p.val.2).absNorm
  have hf:∀p E,0≤f p E:=by
    intro p E
    exact div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)
  have hb (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
      sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)≤
        (Cd*Z^(ε/2)*P)*f p E:=by
    unfold sectorWeight
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd p.val.1 p.val.2 hp.1.1 hp.2.1 E K (radius p E) (sourceRadius s)
      hK hH (hr p E) hHcap
    calc
      _≤∑_n:Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),P*f p E:=by
        apply Finset.sum_le_sum
        intro n hn
        exact weight_le s R seed m A t W V K (radius p E) a₁ a₂ M F hK ha₁ ha₂ hF
          hs₁ hs₂ hwin p E (τ₁ p E) (τ₂ p E) (hc₁ p E) (hc₂ p E) n
      _≤_:=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        convert mul_le_mul_of_nonneg_right hcard (mul_nonneg hP (hf p E)) using 1 ; ring
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hHcap) 0 le_rfl
  calc
    _≤∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*P)*f p E:=by
      unfold sumWeight
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro E hE
      exact hb p E
    _=(Cd*Z^(ε/2)*P)*
        (∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,f p E):=by
      simp only [Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*P)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=P*((Cd*Cm)*Z^ε/(seed.absNorm:ℝ)):=by
      have hz:0<Z:=by linarith
      have he:Z^(ε/2)*Z^(ε/2)=Z^ε:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=P*(Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ):=by ring
        _=_:=by rw [he];ring

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
end OAIOriginalModule2308

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalFixedWeightSum
Source SHA256: 2841ad2a1ffbae515168569b645e24c648be2a963953daf3fce9335e70f2dd57
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2309



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalSource
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Families (s:Input ι)(R seed:Ideal O)(ξ₁ ξ₂:RayCharacter):=
  (p:Labels s R seed)→(E:Finset (CommonIndex p.val.1 p.val.2))→
    FixedPair s.η p.val.1 p.val.2
      (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
        (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1 E ξ₁ ξ₂

theorem original_fixed_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ),
      (∀p E,radius p E≤Cr*Z^L)→∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K radius (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_weight_sum B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound] with Z hbound
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  exact hbound ι s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    fixedPresentationCost hK ha₁ ha₂ fixedPresentationCost_pos.le hs₁ hs₂ hwin radius
    (fun p E=>(F p E).left) (fun p E=>(F p E).right) hr
    (fun p E=>(F p E).conductor_caps.1) (fun p E=>(F p E).conductor_caps.2)

end SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum

end

end OAI
end OAIOriginalModule2309

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalLocalWeightSum
Source SHA256: 6e1d95d84278ab9109e85331433bd2eef936b1ac4a78e3bc956de9d8146683de
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2310



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

theorem original_local_fixed_weight_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(s:Input ι)(R seed:Ideal O),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K (localRadius s R seed K Z ξ)
        (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
        (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_fixed_weight_sum (B+1) (3*B+ξ/2) 1 ε
    (by positivity) (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hbound hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hV hKi hs₁ hs₂ hwin ξ₁ ξ₂ F
  apply hbound ι s R seed hs hs0 hz₁ hz₂ hH
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)
    m A t W V K a₁ a₂ M hK ha₁ ha₂ hs₁ hs₂ hwin
    (localRadius s R seed K Z ξ) _ ξ₁ ξ₂ F
  intro p E
  simpa only [localRadius,one_mul] using
    local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z B ξ
      hK (volume_pos s.toData).le hZ hV hKi

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI
end OAIOriginalModule2310

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedSource
Source SHA256: 440445529fa18742648459c1e9ae97d34db4fa0cf4567a8d3cb8513db6e7e469
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2311




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentCommonSupport CenteredMomentConjugateWindow
open CenteredMomentChildAssembly RayFourExpansion CompletedGauss CenteredMomentGaussEnergy FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstFixedSourceDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_column (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)(t:ℝ)(L:Ideal O)
    (I:columns C C hC.1 s.columns):
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta C a*
        leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem FixedPair.right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

theorem FixedPair.original_data (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L z=
      allocatedPolynomial s C L F.left t T z ∧
    (Real.sqrt T:ℂ)⁻¹*rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L (-z)=
      allocatedPolynomial s D L F.right t T (-z):=by
  constructor
  · exact first_column_original_data s hS hp C hC hsC F.left t T L _ (F.left_column s t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD F.right t T L _
      (F.right_column hD s t L) (-z)

theorem FixedPair.window_integrals (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T θ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁:ℝ→ℂ)(hV₁c:HasCompactSupport V₁)(hV₁s:ContDiff ℝ ∞ V₁)
    (V₂:ℝ→ℂ)(hV₂c:HasCompactSupport V₂)(hV₂s:ContDiff ℝ ∞ V₂)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L θ X V₁ z=
      (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*logPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L F.left (t+2*Real.pi*(w-θ)) T z) ∧
    (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ Y V₂ (-z)=
      (∫w:ℝ,columnDensity (fun x=>star (V₂ x)) (conjugate_compact V₂ hV₂c)
        (conjugate_smooth V₂ hV₂s) w*logPhase (-θ-w) (Real.log Y)*
        allocatedPolynomial s D L F.right (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC F.left t T θ X hX
      V₁ hV₁c hV₁s L _ (F.left_column s t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD F.right t T θ Y hY
      V₂ hV₂c hV₂s L _ (F.right_column hD s t L) z

theorem FixedPair.scalar_conductors (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0<a)(hT:0<T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)(hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (CenteredMomentRankinRadical.commonRadical C D).absNorm:=by
  exact actual_scalar_conductors C D hC hD E η F.left F.right K A₀ B₀ a T M fixedPresentationCost
    hK hA hB ha hT fixedPresentationCost_pos.le hl hr F.conductor_caps.1 F.conductor_caps.2

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2311

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
Source SHA256: 58f61a07cc1a0c681cf0693b8c3fc9061f11a04f441ccde9688baed84fd73b03
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2312



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖leftChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s C hC F.left t L U K:=by
  change gaussEnergy Finset.univ (element C C hC.1 s.columns)
    (element_supported C C hC.1 s.columns) _ U K=_
  rw [funext (F.left_column s t L)]
  exact column_unwindowed_energy s C C hC.1 hC rfl F.left t L U K

theorem FixedPair.right_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  change gaussEnergy Finset.univ (element C D hD.1 s.columns)
    (element_supported C D hD.1 s.columns) _ U K=_
  rw [funext (F.right_column hD s t L)]
  exact column_unwindowed_energy s C D hC.1 hD hCD F.right t L U K

theorem FixedPair.right_reflected_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L (-z)‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  rw [←F.right_common_energy hD hCD s t L U K]
  simpa only [Equiv.neg_apply,map_neg,norm_neg] using (Equiv.neg O).tsum_eq
    (fun z:O=>((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))

theorem FixedPair.left_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t θ X:ℝ)(hX:0<X)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)(J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s C hC F.left v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖leftWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_dyadic_window_energy s C C hC.1 hC rfl F.left t θ X hX L _
    (F.left_column s t L) U K hK hU J B hB hsource

theorem FixedPair.right_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s D hD F.right v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_star_dyadic_window_energy s C D hC.1 hD hCD F.right t θ X hX L _
    (F.right_column hD s t L) U K hK hU J B hB hsource

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2312

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocatedInput
Source SHA256: 13243e36df80a67295f1e8a43c4ce3e747e0ea0168d329cae2c885d2ca67d520
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2313




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow ConcretePrimeRowBridge
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocatedInputDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma commonEnergy_real (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (commonEnergy D C hC τ t L W K).re =
      CenteredMomentFirstAllocationGaussEnergy.commonEnergy D C hC τ t L W K := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm
